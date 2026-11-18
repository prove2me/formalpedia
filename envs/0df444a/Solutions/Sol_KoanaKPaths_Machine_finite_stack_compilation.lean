-- Prove2me | solution 1 for KoanaKPaths.Machine.finite_stack_compilation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T00:55:50.685839+00:00
-- url     : https://prove2.me/submissions/b6fc8e89-a331-4e5b-9a0a-92998f143e8d

import Definitions.Def_KoanaKPaths_BitStackAdapter

open scoped BigOperators
namespace KoanaKPaths.Machine.CoinUse
open Turing HypergraphUnreliability.FPRAS

/-- An upper bound on the number of stack pops in a finite instruction fragment. -/
def popCount {K Λ σ : Type} {Γ : K → Type} : TM2.Stmt Γ Λ σ → ℕ
  | .push _ _ q | .peek _ _ q | .load _ q => popCount q
  | .pop _ _ q => popCount q + 1
  | .branch _ q r => popCount q + popCount r
  | .goto _ | .halt => 0

lemma stepAux_bound {K Λ σ : Type} [DecidableEq K] {Γ : K → Type}
    (coin : K) (q : TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k)) :
    (S coin).length ≤ ((TM2.stepAux q v S).stk coin).length + popCount q := by
  induction q generalizing v S with
  | push k f q ih =>
    have h := ih v (Function.update S k (f v :: S k))
    have hu : (S coin).length ≤ (Function.update S k (f v :: S k) coin).length := by
      by_cases hk : coin = k
      · subst coin; simp
      · simp [Function.update_of_ne hk]
    exact hu.trans h
  | pop k f q ih =>
    have h := ih (f v (S k).head?) (Function.update S k (S k).tail)
    have hu : (S coin).length ≤ (Function.update S k (S k).tail coin).length + 1 := by
      by_cases hk : coin = k
      · subst coin
        simp only [Function.update_self]
        rw [List.length_tail]
        omega
      · simp [Function.update_of_ne hk]
    change (S coin).length ≤ ((TM2.stepAux q (f v (S k).head?) (Function.update S k (S k).tail)).stk coin).length + (popCount q+1)
    omega
  | peek k f q ih => exact ih _ _
  | load f q ih => exact ih _ _
  | branch f q r ihq ihr =>
    simp only [TM2.stepAux,popCount]
    cases h : f v
    · simp only [Bool.cond_false]
      have := ihr v S
      omega
    · simp only [Bool.cond_true]
      have := ihq v S
      omega
  | goto f => simp [TM2.stepAux,popCount]
  | halt => simp [TM2.stepAux,popCount]

lemma exists_step_bound (M : CoinMachine) : ∃ C : ℕ,
    ∀ v v' : M.tm.Cfg, M.tm.step v = some v' →
      (v.stk M.kCoin).length ≤ (v'.stk M.kCoin).length + C := by
  letI : Fintype M.tm.Λ := M.tm.ΛFin
  let C := ∑ l : M.tm.Λ, popCount (M.tm.m l)
  refine ⟨C,?_⟩
  intro v v' hv
  rcases v with ⟨l,s,S⟩
  cases l with
  | none => simp [FinTM2.step,TM2.step] at hv
  | some l =>
    change some (TM2.stepAux (M.tm.m l) s S) = some v' at hv
    cases hv
    have h := stepAux_bound M.kCoin (M.tm.m l) s S
    have hC : popCount (M.tm.m l) ≤ C := by
      dsimp [C]
      exact Finset.single_le_sum (fun j _ => Nat.zero_le (popCount (M.tm.m j))) (Finset.mem_univ l)
    exact h.trans (Nat.add_le_add_left hC _)

lemma exists_use_factor (M : CoinMachine) : ∃ C : ℕ,
    ∀ (input tape : List Bool) (s : ℕ) (v : M.tm.Cfg),
      M.cfgAt input tape s = some v →
        tape.length ≤ (v.stk M.kCoin).length + C*s := by
  obtain ⟨C,hC⟩ := exists_step_bound M
  refine ⟨C,?_⟩
  intro input tape s
  induction s with
  | zero =>
    intro v hv
    simp only [CoinMachine.cfgAt,Function.iterate_zero_apply] at hv
    cases hv
    simp [CoinMachine.initCfg,M.coin_ne_input]
  | succ s ih =>
    intro v hv
    have hsucc : M.cfgAt input tape (s+1) = (M.cfgAt input tape s).bind M.tm.step := by
      simp only [CoinMachine.cfgAt,Function.iterate_succ_apply']
    rw [hsucc] at hv
    cases hs : M.cfgAt input tape s with
    | none => simp [hs,Option.bind] at hv
    | some u =>
      have hstep : M.tm.step u = some v := by simpa only [hs,Option.bind_some] using hv
      have hprev := ih u hs
      have hnext := hC u v hstep
      calc
        tape.length ≤ (u.stk M.kCoin).length + C*s := hprev
        _ ≤ ((v.stk M.kCoin).length+C)+C*s := Nat.add_le_add_right hnext _
        _ = _ := by ring


lemma exists_budget_factor (M : CoinMachine) : ∃ A : ℕ, 0 < A ∧
    ∀ (input tape out : List Bool) (s : ℕ) (v : M.tm.Cfg),
      M.cfgAt input tape s = some v → v.l = none →
      (v.stk M.tm.k₁).map M.outputAlphabet = out → M.RunsWithin input tape (A*s) out := by
  obtain ⟨C,hC⟩ := exists_use_factor M
  refine ⟨C+1,by omega,?_⟩
  intro input tape out s v hcfg hhalt hout
  refine ⟨s,v,?_,hcfg,hhalt,hout,?_⟩
  · have h := Nat.mul_le_mul_right s (show 1 ≤ C+1 by omega)
    simpa using h
  · intro j hj w hw
    have h := hC input tape j w hw
    have hm : C*j ≤ (C+1)*s :=
      (Nat.mul_le_mul_left C hj).trans (Nat.mul_le_mul_right s (Nat.le_succ C))
    exact h.trans (Nat.add_le_add_left hm _)

end KoanaKPaths.Machine.CoinUse

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
namespace KoanaKPaths.Machine
open Turing HypergraphUnreliability.FPRAS

lemma address_val {L e : ℕ} (h : e < L+1) : (address L e).val = e :=
  Nat.mod_eq_of_lt h

lemma step_instruction {S L entry : ℕ} {code : ℕ → NLogN.Instr S}
    (v : (flatMachine L entry code).tm.Cfg) (pc : ℕ) (hp : pc < L+1)
    (hl : v.l = some (next L pc)) :
    (flatMachine L entry code).tm.step v =
      some (TM2.stepAux (instruction (code pc)) v.var v.stk) := by
  rcases v with ⟨l,s,stks⟩
  dsimp only at hl
  subst l
  change some (TM2.stepAux (instruction (code (pc % (L+1)))) s stks) = _
  rw [Nat.mod_eq_of_lt hp]

lemma init_represents {S L entry : ℕ} {code : ℕ → NLogN.Instr S}
    (he : entry < L+1) (input tape : List Bool) :
    Represents input tape (⟨entry,NLogN.St.init S,[]⟩ : NLogN.Cfg S)
      ((flatMachine L entry code).initCfg input tape) := by
  refine {
    pc_lt := he
    returns_lt := ?_
    label := rfl
    phase := ?_
    input_stack := ?_
    coin_stack := ?_
    output_stack := ?_
    buffer_stack := ?_
    control_stack := ?_
    work_stack := ?_
  }
  · simp
  · simp [CoinMachine.initCfg,NLogN.St.init,flatMachine,Equiv.refl_symm,Equiv.coe_refl]
  · simp [CoinMachine.initCfg,NLogN.St.init,flatMachine,Equiv.refl_symm,Equiv.coe_refl]
    change input.map id = input
    simp
  · simp [CoinMachine.initCfg,NLogN.St.init,flatMachine,Equiv.refl_symm,Equiv.coe_refl]
    change tape.map id = tape
    simp
  · simp [CoinMachine.initCfg,NLogN.St.init,flatMachine,Equiv.refl_symm,Equiv.coe_refl]
  · simp [CoinMachine.initCfg,NLogN.St.init,flatMachine,Equiv.refl_symm,Equiv.coe_refl]
  · simp [CoinMachine.initCfg,NLogN.St.init,flatMachine,Equiv.refl_symm,Equiv.coe_refl]
  · intro i
    simp [CoinMachine.initCfg,NLogN.St.init,flatMachine,Equiv.refl_symm,Equiv.coe_refl]

lemma simulate_jump {S L entry : ℕ} {code : ℕ → NLogN.Instr S}
    (input tape : List Bool) (c : NLogN.Cfg S) (v : (flatMachine L entry code).tm.Cfg)
    (hv : Represents input tape c v) (e : ℕ) (he : e < L+1)
    (hc : code c.pc = .jmp e) :
    Represents input tape (⟨e,c.σ,c.ctl⟩ : NLogN.Cfg S)
      (TM2.stepAux (instruction (code c.pc)) v.var v.stk) := by
  rw [hc]
  refine {
    pc_lt := he
    returns_lt := hv.returns_lt
    label := rfl
    phase := hv.phase
    input_stack := hv.input_stack
    coin_stack := hv.coin_stack
    output_stack := hv.output_stack
    buffer_stack := hv.buffer_stack
    control_stack := hv.control_stack
    work_stack := hv.work_stack
  }

lemma simulate_push {S L entry : ℕ} {code : ℕ → NLogN.Instr S}
    (input tape : List Bool) (c : NLogN.Cfg S) (v : (flatMachine L entry code).tm.Cfg)
    (hv : Represents input tape c v) (i : Fin S) (a : NLogN.Sym) (e : ℕ) (he : e < L+1)
    (hc : code c.pc = .push i a e) :
    Represents input tape (⟨e,c.σ.push i a,c.ctl⟩ : NLogN.Cfg S)
      (TM2.stepAux (instruction (code c.pc)) v.var v.stk) := by
  rw [hc]
  refine {
    pc_lt := he
    returns_lt := hv.returns_lt
    label := rfl
    phase := hv.phase
    input_stack := ?_
    coin_stack := ?_
    output_stack := ?_
    buffer_stack := ?_
    control_stack := ?_
    work_stack := ?_
  }
  · simpa [instruction,TM2.stepAux,NLogN.St.push] using hv.input_stack
  · simpa [instruction,TM2.stepAux,NLogN.St.push] using hv.coin_stack
  · simpa [instruction,TM2.stepAux,NLogN.St.push] using hv.output_stack
  · simpa [instruction,TM2.stepAux,NLogN.St.push] using hv.buffer_stack
  · simpa [instruction,TM2.stepAux,NLogN.St.push] using hv.control_stack
  · intro j
    by_cases hij : j = i
    · subst j
      simp [instruction,TM2.stepAux,NLogN.St.push,hv.work_stack,Function.update_apply]
    · have hstack : Stack.work j ≠ Stack.work i := by simpa
      simpa [instruction,TM2.stepAux,NLogN.St.push,Function.update_of_ne hij,
        Function.update_of_ne hstack] using hv.work_stack j


lemma simulate_pop {S L entry : ℕ} {code : ℕ → NLogN.Instr S}
    (input tape : List Bool) (c : NLogN.Cfg S) (v : (flatMachine L entry code).tm.Cfg)
    (hv : Represents input tape c v) (i : Fin S) (e : ℕ) (he : e < L+1)
    (hc : code c.pc = .pop i e) :
    Represents input tape (⟨e,c.σ.pop i,c.ctl⟩ : NLogN.Cfg S)
      (TM2.stepAux (instruction (code c.pc)) v.var v.stk) := by
  rw [hc]
  refine {
    pc_lt := he
    returns_lt := hv.returns_lt
    label := rfl
    phase := hv.phase
    input_stack := ?_
    coin_stack := ?_
    output_stack := ?_
    buffer_stack := ?_
    control_stack := ?_
    work_stack := ?_
  }
  · simpa [instruction,TM2.stepAux,NLogN.St.pop,Function.update_apply] using hv.input_stack
  · simpa [instruction,TM2.stepAux,NLogN.St.pop,Function.update_apply] using hv.coin_stack
  · simpa [instruction,TM2.stepAux,NLogN.St.pop,Function.update_apply] using hv.output_stack
  · simpa [instruction,TM2.stepAux,NLogN.St.pop,Function.update_apply] using hv.buffer_stack
  · simpa [instruction,TM2.stepAux,NLogN.St.pop,Function.update_apply] using hv.control_stack
  · intro j
    by_cases hij : j = i
    · subst j
      simp [instruction,TM2.stepAux,NLogN.St.pop,hv.work_stack,Function.update_apply]
    · have hstack : Stack.work j ≠ Stack.work i := by simpa
      simpa [instruction,TM2.stepAux,NLogN.St.pop,Function.update_of_ne hij,
        Function.update_of_ne hstack] using hv.work_stack j

lemma simulate_out {S L entry : ℕ} {code : ℕ → NLogN.Instr S}
    (input tape : List Bool) (c : NLogN.Cfg S) (v : (flatMachine L entry code).tm.Cfg)
    (hv : Represents input tape c v) (b : Bool) (e : ℕ) (he : e < L+1)
    (hc : code c.pc = .out b e) :
    Represents input tape (⟨e,c.σ.outB b,c.ctl⟩ : NLogN.Cfg S)
      (TM2.stepAux (instruction (code c.pc)) v.var v.stk) := by
  rw [hc]
  refine {
    pc_lt := he
    returns_lt := hv.returns_lt
    label := rfl
    phase := hv.phase
    input_stack := ?_
    coin_stack := ?_
    output_stack := ?_
    buffer_stack := ?_
    control_stack := ?_
    work_stack := ?_
  }
  · simpa [instruction,TM2.stepAux,NLogN.St.outB,Function.update_apply] using hv.input_stack
  · simpa [instruction,TM2.stepAux,NLogN.St.outB,Function.update_apply] using hv.coin_stack
  · simpa [instruction,TM2.stepAux,NLogN.St.outB,Function.update_apply] using hv.output_stack
  · simp [instruction,TM2.stepAux,NLogN.St.outB,Function.update_apply,hv.buffer_stack]
  · simpa [instruction,TM2.stepAux,NLogN.St.outB,Function.update_apply] using hv.control_stack
  · intro j
    simpa [instruction,TM2.stepAux,NLogN.St.outB,Function.update_apply] using hv.work_stack j

lemma simulate_call {S L entry : ℕ} {code : ℕ → NLogN.Instr S}
    (input tape : List Bool) (c : NLogN.Cfg S) (v : (flatMachine L entry code).tm.Cfg)
    (hv : Represents input tape c v) (t e : ℕ) (ht : t < L+1) (he : e < L+1)
    (hc : code c.pc = .call t e) :
    Represents input tape (⟨t,c.σ,e::c.ctl⟩ : NLogN.Cfg S)
      (TM2.stepAux (instruction (code c.pc)) v.var v.stk) := by
  rw [hc]
  refine {
    pc_lt := ht
    returns_lt := ?_
    label := rfl
    phase := hv.phase
    input_stack := ?_
    coin_stack := ?_
    output_stack := ?_
    buffer_stack := ?_
    control_stack := ?_
    work_stack := ?_
  }
  · intro j hj
    rcases List.mem_cons.mp hj with rfl | hj
    · exact he
    · exact hv.returns_lt _ hj
  · simpa [instruction,TM2.stepAux,Function.update_apply] using hv.input_stack
  · simpa [instruction,TM2.stepAux,Function.update_apply] using hv.coin_stack
  · simpa [instruction,TM2.stepAux,Function.update_apply] using hv.output_stack
  · simpa [instruction,TM2.stepAux,Function.update_apply] using hv.buffer_stack
  · simp [instruction,TM2.stepAux,Function.update_apply,hv.control_stack]
  · intro j
    simpa [instruction,TM2.stepAux,Function.update_apply] using hv.work_stack j

lemma simulate_branch {S L entry : ℕ} {code : ℕ → NLogN.Instr S}
    (input tape : List Bool) (c : NLogN.Cfg S) (v : (flatMachine L entry code).tm.Cfg)
    (hv : Represents input tape c v) (i : Fin S) (f : Option NLogN.Sym → Bool)
    (y n : ℕ) (hy : y < L+1) (hn : n < L+1) (hc : code c.pc = .br i f y n) :
    Represents input tape (⟨if f (c.σ.top i) then y else n,c.σ,c.ctl⟩ : NLogN.Cfg S)
      (TM2.stepAux (instruction (code c.pc)) v.var v.stk) := by
  rw [hc]
  have htop : (v.stk (.work i)).head? = c.σ.top i := by rw [hv.work_stack]; rfl
  cases hf : f (c.σ.top i)
  all_goals simp only [hf,Bool.false_eq_true,↓reduceIte]
  all_goals refine {
    pc_lt := by assumption
    returns_lt := hv.returns_lt
    label := ?_
    phase := ?_
    input_stack := ?_
    coin_stack := ?_
    output_stack := ?_
    buffer_stack := ?_
    control_stack := ?_
    work_stack := ?_
  }
  all_goals dsimp only [NLogN.St.top] at hf
  all_goals simp [instruction,TM2.stepAux,htop,hf,hv.phase,hv.input_stack,hv.coin_stack,
    hv.output_stack,hv.buffer_stack,hv.control_stack,hv.work_stack]


lemma simulate_return {S L entry : ℕ} {code : ℕ → NLogN.Instr S}
    (input tape : List Bool) (c : NLogN.Cfg S) (v : (flatMachine L entry code).tm.Cfg)
    (hv : Represents input tape c v) (e : ℕ) (rest : List ℕ)
    (hc : code c.pc = .ret) (hctl : c.ctl = e::rest) :
    Represents input tape (⟨e,c.σ,rest⟩ : NLogN.Cfg S)
      (TM2.stepAux (instruction (code c.pc)) v.var v.stk) := by
  have he : e < L+1 := hv.returns_lt e (by rw [hctl]; simp)
  have hstack : v.stk .control = address L e :: rest.map (address L) := by
    rw [hv.control_stack,hctl,List.map_cons]
  rw [hc]
  refine {
    pc_lt := he
    returns_lt := ?_
    label := ?_
    phase := ?_
    input_stack := ?_
    coin_stack := ?_
    output_stack := ?_
    buffer_stack := ?_
    control_stack := ?_
    work_stack := ?_
  }
  · intro j hj
    exact hv.returns_lt j (by rw [hctl]; exact List.mem_cons_of_mem _ hj)
  all_goals simp [instruction,TM2.stepAux,hstack,Function.update_apply,next,hv.phase,hv.input_stack,
    hv.coin_stack,hv.output_stack,hv.buffer_stack,hv.work_stack]


lemma logical_read_input (input tape : List Bool) (p : ℕ) (hp : p ≤ input.length) :
    (logicalInput input tape).getD p NLogN.codeEnd =
      (((input.drop p).head?).map NLogN.codeBit).getD NLogN.codeSep := by
  unfold logicalInput
  by_cases h : p < input.length
  · rw [List.getD_append _ _ _ _ (by simpa using h)]
    simp only [List.getD_eq_getElem?_getD,List.getElem?_map,List.head?_drop,
      List.getElem?_eq_getElem h,Option.map_some,Option.getD_some]
  · have he : p = input.length := by omega
    subst p
    rw [List.getD_append_right _ _ _ _ (by simp)]
    simp

lemma logical_read_coin (input tape : List Bool) (p : ℕ) (hp : input.length < p) :
    (logicalInput input tape).getD p NLogN.codeEnd =
      (((tape.drop (p-input.length-1)).head?).map NLogN.codeBit).getD NLogN.codeEnd := by
  unfold logicalInput
  rw [List.getD_append_right _ _ _ _ (by simp only [List.length_map]; omega)]
  simp only [List.length_map]
  have hi : p-input.length = (p-input.length-1)+1 := by omega
  rw [hi,List.getD_cons_succ]
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map,List.head?_drop,Nat.add_sub_cancel]

lemma input_phase_next (input : List Bool) (p : ℕ) :
    (input.drop p).head?.isSome = decide (p+1 ≤ input.length) := by
  rw [List.head?_drop]
  by_cases h : p < input.length
  · rw [List.getElem?_eq_getElem h]
    simp [show p+1 ≤ input.length by omega]
  · rw [List.getElem?_eq_none_iff.mpr (by omega)]
    simp [show ¬ p+1 ≤ input.length by omega]

lemma simulate_read_input {S L entry : ℕ} {code : ℕ → NLogN.Instr S}
    (input tape : List Bool) (c : NLogN.Cfg S) (v : (flatMachine L entry code).tm.Cfg)
    (hv : Represents input tape c v) (i : Fin S) (e : ℕ) (he : e < L+1)
    (hc : code c.pc = .inRd i e) (hp : c.σ.ip ≤ input.length) :
    Represents input tape (⟨e,c.σ.inRd (logicalInput input tape) i,c.ctl⟩ : NLogN.Cfg S)
      (TM2.stepAux (instruction (code c.pc)) v.var v.stk) := by
  have hphase : v.var.phase = true := by rw [hv.phase]; simp [hp]
  have hread := logical_read_input input tape c.σ.ip hp
  simp only [List.getD_eq_getElem?_getD,List.head?_drop] at hread
  have hnext := input_phase_next input c.σ.ip
  have hz : c.σ.ip-input.length-1 = 0 := by omega
  have hz' : (c.σ.ip+1)-input.length-1 = 0 := by omega
  rw [hc]
  refine {
    pc_lt := he
    returns_lt := hv.returns_lt
    label := ?_
    phase := ?_
    input_stack := ?_
    coin_stack := ?_
    output_stack := ?_
    buffer_stack := ?_
    control_stack := ?_
    work_stack := ?_
  }
  · simp [instruction,TM2.stepAux,hphase]
  · simp only [instruction,TM2.stepAux,hphase,Bool.cond_true]
    change (v.stk .input).head?.isSome = decide (c.σ.ip+1 ≤ input.length)
    rw [hv.input_stack]
    exact hnext
  · simp [instruction,TM2.stepAux,hphase,Function.update_apply,NLogN.St.inRd,hv.input_stack,List.tail_drop]
  · simpa [instruction,TM2.stepAux,hphase,Function.update_apply,NLogN.St.inRd,hz,hz'] using hv.coin_stack
  · simpa [instruction,TM2.stepAux,hphase,Function.update_apply,NLogN.St.inRd] using hv.output_stack
  · simpa [instruction,TM2.stepAux,hphase,Function.update_apply,NLogN.St.inRd] using hv.buffer_stack
  · simpa [instruction,TM2.stepAux,hphase,Function.update_apply,NLogN.St.inRd] using hv.control_stack
  · intro j
    by_cases hij : j = i
    · subst j
      simp [instruction,TM2.stepAux,hphase,Function.update_apply,NLogN.St.inRd,
        hv.work_stack,hv.input_stack,hread]
      rfl
    · have hstack : Stack.work j ≠ Stack.work i := by simpa
      simpa [instruction,TM2.stepAux,hphase,Function.update_apply,NLogN.St.inRd,
        hij,hstack] using hv.work_stack j


lemma simulate_read_coin {S L entry : ℕ} {code : ℕ → NLogN.Instr S}
    (input tape : List Bool) (c : NLogN.Cfg S) (v : (flatMachine L entry code).tm.Cfg)
    (hv : Represents input tape c v) (i : Fin S) (e : ℕ) (he : e < L+1)
    (hc : code c.pc = .inRd i e) (hp : input.length < c.σ.ip) :
    Represents input tape (⟨e,c.σ.inRd (logicalInput input tape) i,c.ctl⟩ : NLogN.Cfg S)
      (TM2.stepAux (instruction (code c.pc)) v.var v.stk) := by
  have hphase : v.var.phase = false := by rw [hv.phase]; simp [show ¬ c.σ.ip ≤ input.length by omega]
  have hread := logical_read_coin input tape c.σ.ip hp
  simp only [List.getD_eq_getElem?_getD,List.head?_drop] at hread
  have hdrop : input.drop c.σ.ip = [] := List.drop_eq_nil_iff.mpr (by omega)
  have hdrop' : input.drop (c.σ.ip+1) = [] := List.drop_eq_nil_iff.mpr (by omega)
  have hnext : ¬ c.σ.ip+1 ≤ input.length := by omega
  have hidx : (c.σ.ip+1)-input.length-1 = (c.σ.ip-input.length-1)+1 := by omega
  rw [hc]
  refine {
    pc_lt := he
    returns_lt := hv.returns_lt
    label := ?_
    phase := ?_
    input_stack := ?_
    coin_stack := ?_
    output_stack := ?_
    buffer_stack := ?_
    control_stack := ?_
    work_stack := ?_
  }
  · simp [instruction,TM2.stepAux,hphase]
  · simp [instruction,TM2.stepAux,hphase,NLogN.St.inRd,hnext]
  · simpa [instruction,TM2.stepAux,hphase,Function.update_apply,NLogN.St.inRd,hdrop,hdrop'] using hv.input_stack
  · simp [instruction,TM2.stepAux,hphase,Function.update_apply,NLogN.St.inRd,
      hv.coin_stack,List.tail_drop,hidx]
  · simpa [instruction,TM2.stepAux,hphase,Function.update_apply,NLogN.St.inRd] using hv.output_stack
  · simpa [instruction,TM2.stepAux,hphase,Function.update_apply,NLogN.St.inRd] using hv.buffer_stack
  · simpa [instruction,TM2.stepAux,hphase,Function.update_apply,NLogN.St.inRd] using hv.control_stack
  · intro j
    by_cases hij : j = i
    · subst j
      simp [instruction,TM2.stepAux,hphase,Function.update_apply,NLogN.St.inRd,
        hv.work_stack,hv.coin_stack,hread]
      rfl
    · have hstack : Stack.work j ≠ Stack.work i := by simpa
      simpa [instruction,TM2.stepAux,hphase,Function.update_apply,NLogN.St.inRd,
        hij,hstack] using hv.work_stack j


lemma simulate_step {S L entry : ℕ} {code : ℕ → NLogN.Instr S}
    (input tape : List Bool) (c c' : NLogN.Cfg S) (v : (flatMachine L entry code).tm.Cfg)
    (hv : Represents input tape c v) (hvalid : NLogN.Instr.Valid (L+1) (code c.pc))
    (hstep : NLogN.fstep (logicalInput input tape) code c = some c') :
    ∃ v', (flatMachine L entry code).tm.step v = some v' ∧ Represents input tape c' v' := by
  refine ⟨TM2.stepAux (instruction (code c.pc)) v.var v.stk,
    step_instruction v c.pc hv.pc_lt hv.label,?_⟩
  cases hc : code c.pc with
  | jmp e =>
    rw [hc] at hvalid
    simp only [NLogN.fstep,hc,Option.some.injEq] at hstep
    subst c'
    simpa only [hc] using simulate_jump input tape c v hv e hvalid hc
  | push i a e =>
    rw [hc] at hvalid
    simp only [NLogN.fstep,hc,Option.some.injEq] at hstep
    subst c'
    simpa only [hc] using simulate_push input tape c v hv i a e hvalid hc
  | pop i e =>
    rw [hc] at hvalid
    simp only [NLogN.fstep,hc,Option.some.injEq] at hstep
    subst c'
    simpa only [hc] using simulate_pop input tape c v hv i e hvalid hc
  | inRd i e =>
    rw [hc] at hvalid
    simp only [NLogN.fstep,hc,Option.some.injEq] at hstep
    subst c'
    by_cases hp : c.σ.ip ≤ input.length
    · simpa only [hc] using simulate_read_input input tape c v hv i e hvalid hc hp
    · simpa only [hc] using simulate_read_coin input tape c v hv i e hvalid hc (by omega)
  | out b e =>
    rw [hc] at hvalid
    simp only [NLogN.fstep,hc,Option.some.injEq] at hstep
    subst c'
    simpa only [hc] using simulate_out input tape c v hv b e hvalid hc
  | br i f y n =>
    rw [hc] at hvalid
    simp only [NLogN.fstep,hc,Option.some.injEq] at hstep
    subst c'
    simpa only [hc] using simulate_branch input tape c v hv i f y n hvalid.1 hvalid.2 hc
  | call t e =>
    rw [hc] at hvalid
    simp only [NLogN.fstep,hc,Option.some.injEq] at hstep
    subst c'
    simpa only [hc] using simulate_call input tape c v hv t e hvalid.1 hvalid.2 hc
  | ret =>
    cases hctl : c.ctl with
    | nil => simp [NLogN.fstep,hc,hctl] at hstep
    | cons e rest =>
      simp only [NLogN.fstep,hc,hctl,Option.some.injEq] at hstep
      subst c'
      simpa only [hc] using simulate_return input tape c v hv e rest hc hctl

lemma simulate_steps {S L entry : ℕ} {code : ℕ → NLogN.Instr S}
    (input tape : List Bool) (hvalid : ∀ pc < L+1, NLogN.Instr.Valid (L+1) (code pc))
    {c c' : NLogN.Cfg S} {t : ℕ}
    (hsteps : NLogN.Steps (logicalInput input tape) code c t c')
    (v : (flatMachine L entry code).tm.Cfg) (hv : Represents input tape c v) :
    ∃ v', ((fun o => o.bind (flatMachine L entry code).tm.step)^[t] (some v)) = some v' ∧
      Represents input tape c' v' := by
  induction hsteps generalizing v with
  | refl c => exact ⟨v,rfl,hv⟩
  | step hs ht ih =>
    obtain ⟨v1,hv1,hr1⟩ := simulate_step input tape _ _ v hv (hvalid _ hv.pc_lt) hs
    obtain ⟨v2,hv2,hr2⟩ := ih v1 hr1
    refine ⟨v2,?_,hr2⟩
    rw [Function.iterate_succ_apply]
    change (fun o => o.bind (flatMachine L entry code).tm.step)^[ _ ]
      ((flatMachine L entry code).tm.step v) = _
    rw [hv1]
    exact hv2


lemma step_reverse {S L entry : ℕ} {code : ℕ → NLogN.Instr S}
    (v : (flatMachine L entry code).tm.Cfg) (hl : v.l = some (finish L)) :
    (flatMachine L entry code).tm.step v = some (TM2.stepAux reverseOutput v.var v.stk) := by
  rcases v with ⟨l,s,stks⟩
  dsimp only at hl
  subst l
  rfl

lemma reverse_halts {S L entry : ℕ} {code : ℕ → NLogN.Instr S}
    (v : (flatMachine L entry code).tm.Cfg) (hl : v.l = some (finish L)) :
    ∃ v', (fun o => o.bind (flatMachine L entry code).tm.step)^[ (v.stk .buffer).length+1 ] (some v) = some v' ∧
      v'.l = none ∧ (v'.stk .output : List Bool) = List.append (α := Bool) (List.reverse (α := Bool) (v.stk .buffer)) (v.stk .output) := by
  have aux : ∀ (buf : List Bool) (v : (flatMachine L entry code).tm.Cfg),
      v.l = some (finish L) → v.stk .buffer = buf →
      ∃ v', (fun o => o.bind (flatMachine L entry code).tm.step)^[ buf.length+1 ] (some v) = some v' ∧
        v'.l = none ∧ (v'.stk .output : List Bool) = List.append (α := Bool) buf.reverse (v.stk .output) := by
    intro buf
    induction buf with
    | nil =>
      intro v hl hb
      refine ⟨TM2.stepAux reverseOutput v.var v.stk,?_,?_,?_⟩
      · simpa only [List.length_nil,zero_add,Function.iterate_one,Option.bind_some] using step_reverse v hl
      · simp [reverseOutput,TM2.stepAux,hb]
      · simp [reverseOutput,TM2.stepAux,hb,Function.update_apply]
    | cons b buf ih =>
      intro v hl hb
      let v1 := TM2.stepAux reverseOutput v.var v.stk
      have h1 : (flatMachine L entry code).tm.step v = some v1 := step_reverse v hl
      have hl1 : v1.l = some (finish L) := by simp [v1,reverseOutput,TM2.stepAux,hb]
      have hb1 : v1.stk .buffer = buf := by simp [v1,reverseOutput,TM2.stepAux,hb,Function.update_apply]
      have ho1 : (v1.stk .output : List Bool) = b :: (v.stk .output : List Bool) := by simp [v1,reverseOutput,TM2.stepAux,hb,Function.update_apply]
      obtain ⟨v2,h2,hhalt,hout⟩ := ih v1 hl1 hb1
      refine ⟨v2,?_,hhalt,?_⟩
      · rw [List.length_cons,show buf.length+1+1 = (buf.length+1)+1 by omega,Function.iterate_succ_apply]
        change (fun o => o.bind (flatMachine L entry code).tm.step)^[buf.length+1]
          ((flatMachine L entry code).tm.step v) = _
        rw [h1]
        exact h2
      · rw [hout,ho1]
        simp [List.reverse_cons,List.append_assoc]
  exact aux (v.stk .buffer) v hl rfl


lemma cfgAt_succ (M : CoinMachine) (input tape : List Bool) (t : ℕ) :
    M.cfgAt input tape (t+1) = (M.cfgAt input tape t).bind M.tm.step := by
  simp only [CoinMachine.cfgAt,Function.iterate_succ_apply']

lemma halts_of_flat_steps {S : ℕ} (L entry : ℕ) (code : ℕ → NLogN.Instr S)
    (he : entry < L+1) (hvalid : ∀ pc < L+1, NLogN.Instr.Valid (L+1) (code pc))
    (input tape : List Bool) (c : NLogN.Cfg S) (t : ℕ)
    (hsteps : NLogN.Steps (logicalInput input tape) code ⟨entry,NLogN.St.init S,[]⟩ t c)
    (hret : code c.pc = .ret) (hctl : c.ctl = []) :
    ∃ v : (flatMachine L entry code).tm.Cfg,
      (flatMachine L entry code).cfgAt input tape (t+c.σ.out.length+2) = some v ∧
        v.l = none ∧ v.stk .output = c.σ.out := by
  let M := flatMachine L entry code
  obtain ⟨v,hv,hr⟩ := simulate_steps input tape hvalid hsteps (M.initCfg input tape)
    (init_represents he input tape)
  have hcfg : M.cfgAt input tape t = some v := hv
  have hcontrol : v.stk .control = [] := by rw [hr.control_stack,hctl]; rfl
  let u := TM2.stepAux (instruction (code c.pc)) v.var v.stk
  have hstep : M.tm.step v = some u := step_instruction v c.pc hr.pc_lt hr.label
  have hu : u.l = some (finish L) := by simp [u,hret,instruction,TM2.stepAux,hcontrol]
  have hbuf : u.stk .buffer = c.σ.out.reverse := by
    simpa [u,hret,instruction,TM2.stepAux,hcontrol,Function.update_apply] using hr.buffer_stack
  have hout0 : u.stk .output = [] := by
    simpa [u,hret,instruction,TM2.stepAux,hcontrol,Function.update_apply] using hr.output_stack
  obtain ⟨v2,hrev,hhalt,hout⟩ := reverse_halts u hu
  rw [hbuf,List.length_reverse] at hrev
  have hcfg1 : M.cfgAt input tape (t+1) = some u := by
    rw [cfgAt_succ,hcfg]
    exact hstep
  have hjoin : M.cfgAt input tape ((c.σ.out.length+1)+(t+1)) = some v2 := by
    unfold CoinMachine.cfgAt
    rw [Function.iterate_add_apply]
    change (fun o => o.bind M.tm.step)^[c.σ.out.length+1] (M.cfgAt input tape (t+1)) = _
    rw [hcfg1]
    exact hrev
  refine ⟨v2,?_,hhalt,?_⟩
  · convert hjoin using 1 <;> congr 1 <;> omega
  · rw [hout,hbuf,hout0]
    simp

lemma flat_runsWithin {S : ℕ} (L entry : ℕ) (code : ℕ → NLogN.Instr S)
    (he : entry < L+1) (hvalid : ∀ pc < L+1, NLogN.Instr.Valid (L+1) (code pc)) :
    ∃ A : ℕ, 0 < A ∧ ∀ (input tape : List Bool) (c : NLogN.Cfg S) (t : ℕ),
      NLogN.Steps (logicalInput input tape) code ⟨entry,NLogN.St.init S,[]⟩ t c →
      code c.pc = .ret → c.ctl = [] →
      (flatMachine L entry code).RunsWithin input tape (A*(t+c.σ.out.length+2)) c.σ.out := by
  obtain ⟨A,hA,hbound⟩ := CoinUse.exists_budget_factor (flatMachine L entry code)
  refine ⟨A,hA,?_⟩
  intro input tape c t hsteps hret hctl
  obtain ⟨v,hv,hh,ho⟩ := halts_of_flat_steps L entry code he hvalid input tape c t hsteps hret hctl
  apply hbound input tape c.σ.out (t+c.σ.out.length+2) v hv hh
  change List.map id (v.stk .output) = c.σ.out
  simpa using ho

end KoanaKPaths.Machine

theorem solution (S L entry : ℕ)
    (code : ℕ → NLogN.Instr S) (he : entry < L+1)
    (hvalid : ∀ pc < L+1, NLogN.Instr.Valid (L+1) (code pc)) :
    ∃ A : ℕ, 0 < A ∧ ∀ (input tape : List Bool) (c : NLogN.Cfg S) (t : ℕ),
      NLogN.Steps (KoanaKPaths.Machine.logicalInput input tape) code
        ⟨entry,NLogN.St.init S,[]⟩ t c → code c.pc = .ret → c.ctl = [] →
      (KoanaKPaths.Machine.flatMachine L entry code).RunsWithin input tape
        (A*(t+c.σ.out.length+2)) c.σ.out := by
  exact KoanaKPaths.Machine.flat_runsWithin L entry code he hvalid
