-- Prove2me | solution 1 for ITPIRPreproc.MatchVec.WordRAM.readNatProgram_correct
-- status  : ACCEPTED   (prove)
-- author  : @Jesko
-- created : 2026-11-13T17:54:00.979774+00:00
-- url     : https://prove2.me/submissions/00043b8d-f69f-44a6-9c87-51f5baedc476

import Definitions.Def_ITPIRPreproc_MatchVec_RAMEncoding
import Definitions.Def_ITPIRPreproc_MatchVec_Machine
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

namespace ITPIRPreproc.MatchVec.WordRAM

def eraseCost (s : State) : State := {s with cost := 0}

noncomputable def shapeStep (P : Program) (inp : List Bool) (ω : ℕ → Bool) (s : State) : State :=
  eraseCost (step P inp ω s)

@[simp] theorem eraseCost_idem (s : State) : eraseCost (eraseCost s) = eraseCost s := rfl

theorem eraseCost_step (P : Program) (inp : List Bool) (ω : ℕ → Bool) (s : State) :
    eraseCost (step P inp ω s) = eraseCost (step P inp ω (eraseCost s)) := by
  unfold step
  by_cases hs : s.halted = true
  · simp [hs, eraseCost]
  · simp only [hs, Bool.false_eq_true, ↓reduceIte, eraseCost]
    cases hf : P[s.pc]? with
    | none => rfl
    | some op => cases op <;> rfl

theorem eraseCost_iterate (P : Program) (inp : List Bool) (ω : ℕ → Bool)
    (s : State) (k : ℕ) :
    eraseCost ((step P inp ω)^[k] s) = (shapeStep P inp ω)^[k] (eraseCost s) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
    exact eraseCost_step P inp ω _

theorem run_shape (P : Program) (inp : List Bool) (ω : ℕ → Bool) (k : ℕ) :
    eraseCost (run P inp ω k) = (shapeStep P inp ω)^[k] initState :=
  eraseCost_iterate P inp ω initState k

theorem step_of_halted (P : Program) (inp : List Bool) (ω : ℕ → Bool)
    (s : State) (hs : s.halted = true) : step P inp ω s = s := by
  simp [step, hs]

theorem run_succ (P : Program) (inp : List Bool) (ω : ℕ → Bool) (k : ℕ) :
    run P inp ω (k+1) = step P inp ω (run P inp ω k) :=
  Function.iterate_succ_apply' _ _ _

theorem run_add (P : Program) (inp : List Bool) (ω : ℕ → Bool) (a b : ℕ) :
    run P inp ω (a+b) = (step P inp ω)^[b] (run P inp ω a) := by
  simp only [run, Nat.add_comm a b, Function.iterate_add_apply]

theorem run_stable (P : Program) (inp : List Bool) (ω : ℕ → Bool) (k : ℕ)
    (hk : (run P inp ω k).halted = true) (j : ℕ) :
    run P inp ω (k+j) = run P inp ω k := by
  rw [run_add]
  exact Function.iterate_fixed (step_of_halted P inp ω _ hk) j

theorem haltStep_le (P : Program) (inp : List Bool) (ω : ℕ → Bool) (k : ℕ)
    (hk : (run P inp ω k).halted = true) : haltStep P inp ω ≤ k := by
  have hh : ∃ j, (run P inp ω j).halted = true := ⟨k, hk⟩
  simp only [haltStep, dif_pos hh]
  exact Nat.find_min' hh hk

theorem finalState_eq_run (P : Program) (inp : List Bool) (ω : ℕ → Bool) (k : ℕ)
    (hk : (run P inp ω k).halted = true) : finalState P inp ω = run P inp ω k := by
  have hh : ∃ j, (run P inp ω j).halted = true := ⟨k, hk⟩
  have hhalt : (run P inp ω (haltStep P inp ω)).halted = true := by
    simp only [haltStep, dif_pos hh]
    exact Nat.find_spec hh
  have hle := haltStep_le P inp ω k hk
  obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hle
  rw [hj]
  exact (run_stable P inp ω _ hhalt j).symm

theorem cost_eq_run (P : Program) (inp : List Bool) (ω : ℕ → Bool) (k : ℕ)
    (hk : (run P inp ω k).halted = true) : cost P inp ω = (run P inp ω k).cost := by
  unfold cost
  rw [finalState_eq_run P inp ω k hk]

theorem output_eq_run (P : Program) (inp : List Bool) (ω : ℕ → Bool) (k : ℕ)
    (hk : (run P inp ω k).halted = true) : output P inp ω = (run P inp ω k).out := by
  unfold output
  rw [finalState_eq_run P inp ω k hk]

theorem workingBits_le_of_trace (P : Program) (inp : List Bool) (ω : ℕ → Bool)
    (k B : ℕ) (hk : (run P inp ω k).halted = true)
    (hb : ∀ j ≤ k, space (run P inp ω j) ≤ B) : workingBits P inp ω ≤ B := by
  unfold workingBits
  apply Finset.sup_le
  intro j hj
  exact hb j (le_trans (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
    (haltStep_le P inp ω k hk))

theorem words_le_size (w x : ℕ) (hw : 1 ≤ w) : words w x ≤ Nat.size x := by
  unfold words
  apply (Nat.div_le_iff_le_mul_add_pred (by omega)).mpr
  have hm : Nat.size x ≤ w * Nat.size x := by
    simpa [Nat.mul_comm] using Nat.mul_le_mul_left (Nat.size x) hw
  omega

theorem wordSize_pos (inp : List Bool) (s : State) : 1 ≤ wordSize inp s :=
  le_max_left _ _

theorem step_cost_bound (P : Program) (inp : List Bool) (ω : ℕ → Bool)
    (s : State) (B : ℕ)
    (hr : ∀ i, Nat.size (s.regs i) ≤ B)
    (hm : ∀ i, Nat.size (s.mem i) ≤ B)
    (hc : ∀ d k, Instr.const d k ∈ P → Nat.size k ≤ B) :
    (step P inp ω s).cost ≤ s.cost + (1+2*B) := by
  have hwr (i : ℕ) : words (wordSize inp s) (s.regs i) ≤ B :=
    (words_le_size _ _ (wordSize_pos inp s)).trans (hr i)
  have hwm (i : ℕ) : words (wordSize inp s) (s.mem i) ≤ B :=
    (words_le_size _ _ (wordSize_pos inp s)).trans (hm i)
  by_cases hs : s.halted = true
  · rw [step_of_halted P inp ω s hs]
    omega
  · cases hf : P[s.pc]? with
    | none => simp [step, hs, hf]
    | some op =>
      have hop : op ∈ P := List.mem_of_getElem? hf
      cases op with
      | const d k =>
        have hwk := (words_le_size (wordSize inp s) k (wordSize_pos inp s)).trans (hc d k hop)
        simp only [step, hs, Bool.false_eq_true, ↓reduceIte, hf]
        omega
      | _ => simp only [step, hs, Bool.false_eq_true, ↓reduceIte, hf] <;>
        grind only

theorem space_le_of_registers (s : State) (R B : ℕ)
    (hmem : s.mem = 0) (hout : s.out = [])
    (hsupp : s.regs.support ⊆ Finset.range R)
    (hbits : ∀ r, Nat.size (s.regs r) ≤ B) : space s ≤ R*B := by
  simp only [space, hmem, hout, Finsupp.sum_zero_index, List.length_nil, add_zero]
  unfold Finsupp.sum
  calc
    _ ≤ ∑ r ∈ s.regs.support, B := Finset.sum_le_sum (fun r _ => hbits r)
    _ = s.regs.support.card * B := by simp
    _ ≤ R*B := Nat.mul_le_mul_right B (by simpa using Finset.card_le_card hsupp)

theorem cost_le_of_step_bound (P : Program) (inp : List Bool) (ω : ℕ → Bool)
    (k M : ℕ) (hb : ∀ j < k,
      (step P inp ω (run P inp ω j)).cost ≤ (run P inp ω j).cost + M) :
    (run P inp ω k).cost ≤ k*M := by
  induction k with
  | zero => simp [run, initState]
  | succ k ih =>
    rw [run_succ]
    have hp := ih (fun j hj => hb j (by omega))
    have hq := hb k (by omega)
    nlinarith

end ITPIRPreproc.MatchVec.WordRAM


set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 3000

namespace ITPIRPreproc.MatchVec.WordRAM.ReadNatProof

def value : List Bool → ℕ := List.foldr Nat.bit 0

@[simp] theorem value_nil : value [] = 0 := rfl
@[simp] theorem value_cons (b : Bool) (bs : List Bool) :
    value (b::bs) = b.toNat + 2*value bs := by simp [value, Nat.bit_val]; omega

theorem value_bits (n : ℕ) : value n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => simp
  | bit b n hn ih =>
    rw [Nat.bits_append_bit n b hn, value_cons, ih]
    simp [Nat.bit_val, Nat.add_comm]

noncomputable def regs (a w f t : ℕ) : ℕ →₀ ℕ :=
  Finsupp.single 0 a + Finsupp.single 1 w + Finsupp.single 2 f +
    Finsupp.single 3 t + Finsupp.single 4 1

@[simp] theorem regs_zero (a w f t : ℕ) : regs a w f t 0 = a := by simp [regs]
@[simp] theorem regs_one (a w f t : ℕ) : regs a w f t 1 = w := by simp [regs]
@[simp] theorem regs_two (a w f t : ℕ) : regs a w f t 2 = f := by simp [regs]
@[simp] theorem regs_three (a w f t : ℕ) : regs a w f t 3 = t := by simp [regs]
@[simp] theorem regs_four (a w f t : ℕ) : regs a w f t 4 = 1 := by simp [regs]

theorem regs_ge_five (a w f t i : ℕ) (hi : 5 ≤ i) : regs a w f t i = 0 := by
  simp only [regs, Finsupp.add_apply, Finsupp.single_apply]
  split_ifs <;> omega

@[simp] theorem regs_five (a w f t : ℕ) : regs a w f t 5 = 0 := regs_ge_five _ _ _ _ _ le_rfl

@[simp] theorem regs_update_zero (a w f t v : ℕ) : (regs a w f t).update 0 v = regs v w f t := by
  ext i
  by_cases hi : i < 5
  · interval_cases i <;> simp [Finsupp.update_apply]
  · simp [Finsupp.update_apply, show i ≠ 0 by omega, regs_ge_five _ _ _ _ i (by omega)]

@[simp] theorem regs_update_one (a w f t v : ℕ) : (regs a w f t).update 1 v = regs a v f t := by
  ext i
  by_cases hi : i < 5
  · interval_cases i <;> simp [Finsupp.update_apply]
  · simp [Finsupp.update_apply, show i ≠ 1 by omega, regs_ge_five _ _ _ _ i (by omega)]

@[simp] theorem regs_update_two (a w f t v : ℕ) : (regs a w f t).update 2 v = regs a w v t := by
  ext i
  by_cases hi : i < 5
  · interval_cases i <;> simp [Finsupp.update_apply]
  · simp [Finsupp.update_apply, show i ≠ 2 by omega, regs_ge_five _ _ _ _ i (by omega)]

@[simp] theorem regs_update_three (a w f t v : ℕ) : (regs a w f t).update 3 v = regs a w f v := by
  ext i
  by_cases hi : i < 5
  · interval_cases i <;> simp [Finsupp.update_apply]
  · simp [Finsupp.update_apply, show i ≠ 3 by omega, regs_ge_five _ _ _ _ i (by omega)]

noncomputable def state (pc pos a w f t : ℕ) (halted : Bool := false) : State :=
  ⟨pc, regs a w f t, 0, pos, [], 0, halted, 0⟩

theorem flag_step (inp : List Bool) (ω : ℕ → Bool) (pos a w f t : ℕ) :
    shapeStep readNatProgram inp ω (state 3 pos a w f t) =
      state 4 (pos+1) a w (inputVal inp[pos]?) t := by
  simp [shapeStep, eraseCost, step, readNatProgram, state]

theorem branch_zero (inp : List Bool) (ω : ℕ → Bool) (pos a w t : ℕ) :
    shapeStep readNatProgram inp ω (state 4 pos a w 0 t) = state 5 pos a w 0 t := by
  simp [shapeStep, eraseCost, step, readNatProgram, state]

theorem branch_one (inp : List Bool) (ω : ℕ → Bool) (pos a w t : ℕ) :
    shapeStep readNatProgram inp ω (state 4 pos a w 1 t) = state 6 pos a w 1 t := by
  simp [shapeStep, eraseCost, step, readNatProgram, state]

theorem halt_step (inp : List Bool) (ω : ℕ → Bool) (pos a w f t : ℕ) :
    shapeStep readNatProgram inp ω (state 5 pos a w f t) = state 6 pos a w f t true := by
  simp [shapeStep, eraseCost, step, readNatProgram, state]

theorem bit_step (inp : List Bool) (ω : ℕ → Bool) (pos a w f t : ℕ) :
    shapeStep readNatProgram inp ω (state 6 pos a w f t) =
      state 7 (pos+1) a w f (inputVal inp[pos]?) := by
  simp [shapeStep, eraseCost, step, readNatProgram, state]

theorem mul_step (inp : List Bool) (ω : ℕ → Bool) (pos a w f t : ℕ) :
    shapeStep readNatProgram inp ω (state 7 pos a w f t) = state 8 pos a w f (t*w) := by
  simp [shapeStep, eraseCost, step, readNatProgram, state]

theorem add_step (inp : List Bool) (ω : ℕ → Bool) (pos a w f t : ℕ) :
    shapeStep readNatProgram inp ω (state 8 pos a w f t) = state 9 pos (a+t) w f t := by
  simp [shapeStep, eraseCost, step, readNatProgram, state]

theorem weight_step (inp : List Bool) (ω : ℕ → Bool) (pos a w f t : ℕ) :
    shapeStep readNatProgram inp ω (state 9 pos a w f t) = state 10 pos a (w+w) f t := by
  simp [shapeStep, eraseCost, step, readNatProgram, state]

theorem back_step (inp : List Bool) (ω : ℕ → Bool) (pos a w f t : ℕ) :
    shapeStep readNatProgram inp ω (state 10 pos a w f t) = state 3 pos a w f t := by
  simp [shapeStep, eraseCost, step, readNatProgram, state]

def Bounded (R : ℕ) (s : State) : Prop :=
  s.mem = 0 ∧ s.out = [] ∧ s.regs.support ⊆ Finset.range 5 ∧ ∀ i, s.regs i ≤ R

theorem bounded_state (R pc pos a w f t : ℕ) (halted : Bool)
    (hR : 1 ≤ R) (ha : a ≤ R) (hw : w ≤ R) (hf : f ≤ R) (ht : t ≤ R) :
    Bounded R (state pc pos a w f t halted) := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · intro i hi
    by_contra hn
    have hig : 5 ≤ i := by simpa using hn
    have hz : (state pc pos a w f t halted).regs i = 0 := regs_ge_five _ _ _ _ _ hig
    exact (Finsupp.mem_support_iff.mp hi) hz
  · intro i
    change regs a w f t i ≤ R
    by_cases hi : i < 5
    · interval_cases i <;> simp_all
    · rw [regs_ge_five _ _ _ _ i (by omega)]
      omega

theorem trace_append {α : Type*} (f : α → α) (Q : α → Prop) (s : α) (a b : ℕ)
    (ha : ∀ j ≤ a, Q (f^[j] s)) (hb : ∀ j ≤ b, Q (f^[j] (f^[a] s))) :
    ∀ j ≤ a+b, Q (f^[j] s) := by
  intro j hj
  by_cases hja : j ≤ a
  · exact ha j hja
  · have hab : a ≤ j := by omega
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hab
    rw [Nat.add_comm a r, Function.iterate_add_apply]
    exact hb r (by omega)

theorem body_run (inp : List Bool) (ω : ℕ → Bool) (pos a w f t : ℕ) (b : Bool)
    (h0 : inp[pos]? = some true) (h1 : inp[pos+1]? = some b) :
    (shapeStep readNatProgram inp ω)^[7] (state 3 pos a w f t) =
      state 3 (pos+2) (a+b.toNat*w) (w+w) 1 (b.toNat*w) := by
  norm_num only [Function.iterate_succ_apply', Function.iterate_zero, id_eq,
    flag_step, branch_one, bit_step, mul_step, add_step, weight_step, back_step,
    h0, h1, inputVal]
  cases b <;> rfl

theorem body_trace (inp : List Bool) (ω : ℕ → Bool) (R pos a w f t : ℕ) (b : Bool)
    (h0 : inp[pos]? = some true) (h1 : inp[pos+1]? = some b)
    (hR : 1 ≤ R) (ha : a < w) (hw : w+w ≤ R) (hf : f ≤ R) (ht : t ≤ R) :
    ∀ j ≤ 7, Bounded R ((shapeStep readNatProgram inp ω)^[j] (state 3 pos a w f t)) := by
  intro j hj
  interval_cases j <;>
    norm_num only [Function.iterate_succ_apply', Function.iterate_zero, id_eq,
      flag_step, branch_one, bit_step, mul_step, add_step, weight_step, back_step,
      h0, h1, inputVal]
  all_goals cases b <;> apply bounded_state <;> simp_all <;> omega

theorem stop_run (inp : List Bool) (ω : ℕ → Bool) (pos a w f t : ℕ)
    (h0 : inp[pos]? = some false) :
    (shapeStep readNatProgram inp ω)^[3] (state 3 pos a w f t) =
      state 6 (pos+1) a w 0 t true := by
  norm_num only [Function.iterate_succ_apply', Function.iterate_zero, id_eq,
    flag_step, branch_zero, halt_step, h0, inputVal]

theorem stop_trace (inp : List Bool) (ω : ℕ → Bool) (R pos a w f t : ℕ)
    (h0 : inp[pos]? = some false) (hR : 1 ≤ R) (ha : a ≤ R)
    (hw : w ≤ R) (hf : f ≤ R) (ht : t ≤ R) :
    ∀ j ≤ 3, Bounded R ((shapeStep readNatProgram inp ω)^[j] (state 3 pos a w f t)) := by
  intro j hj
  interval_cases j <;>
    norm_num only [Function.iterate_succ_apply', Function.iterate_zero, id_eq,
      flag_step, branch_zero, halt_step, h0, inputVal]
  all_goals apply bounded_state <;> omega

theorem loop_run_and_trace (inp : List Bool) (ω : ℕ → Bool) (R : ℕ)
    (bs tail : List Bool) (pos a w f t : ℕ)
    (hinp : inp.drop pos = encBits bs ++ tail)
    (hwp : 0 < w) (ha : a < w) (hf : f ≤ 1) (ht : t ≤ w)
    (hcap : w * 2^bs.length ≤ R) :
    (∃ tf, (shapeStep readNatProgram inp ω)^[7*bs.length+3] (state 3 pos a w f t) =
      state 6 (pos+2*bs.length+1) (a+w*value bs) (w*2^bs.length) 0 tf true) ∧
    (∀ j ≤ 7*bs.length+3,
      Bounded R ((shapeStep readNatProgram inp ω)^[j] (state 3 pos a w f t))) := by
  induction bs generalizing pos a w f t with
  | nil =>
    have h0 : inp[pos]? = some false := by
      have hx := congrArg (fun xs : List Bool => xs[0]?) hinp
      simpa [encBits] using hx
    have hwR : w ≤ R := by simpa using hcap
    constructor
    · refine ⟨t, ?_⟩
      simpa using stop_run inp ω pos a w f t h0
    · simpa using stop_trace inp ω R pos a w f t h0 (by omega) (by omega)
        hwR (by omega) (by omega)
  | cons b bs ih =>
    have h0 : inp[pos]? = some true := by
      have hx := congrArg (fun xs : List Bool => xs[0]?) hinp
      simpa [encBits] using hx
    have h1 : inp[pos+1]? = some b := by
      have hx := congrArg (fun xs : List Bool => xs[1]?) hinp
      simpa [encBits] using hx
    have hrest : inp.drop (pos+2) = encBits bs ++ tail := by
      have hx := congrArg (List.drop 2) hinp
      simpa [encBits, List.drop_drop, List.append_assoc, Nat.add_comm] using hx
    have hcap' : (w+w) * 2^bs.length ≤ R := by
      calc
        (w+w)*2^bs.length = w*2^(b::bs).length := by simp only [List.length_cons, pow_succ]; ring
        _ ≤ R := hcap
    have hwR : w+w ≤ R := by
      have hp : 0 < 2^bs.length := by positivity
      nlinarith only [hcap', hp]
    have ha' : a+b.toNat*w < w+w := by cases b <;> simp_all <;> omega
    have ht' : b.toNat*w ≤ w+w := by cases b <;> simp <;> omega
    obtain ⟨⟨tf, he⟩, hb⟩ := ih (pos+2) (a+b.toNat*w) (w+w) 1 (b.toNat*w)
      hrest (by omega) ha' le_rfl ht' hcap'
    have hbody := body_run inp ω pos a w f t b h0 h1
    constructor
    · refine ⟨tf, ?_⟩
      rw [List.length_cons,
        show 7*(bs.length+1)+3 = (7*bs.length+3)+7 by omega,
        Function.iterate_add_apply, hbody, he]
      congr 1
      · omega
      · rw [value_cons]
        ring
      · rw [pow_succ]
        ring
    · have hfirst := body_trace inp ω R pos a w f t b h0 h1
        (by omega) ha hwR (by omega) (by omega)
      have hlast : ∀ j ≤ 7*bs.length+3, Bounded R
          ((shapeStep readNatProgram inp ω)^[j]
            ((shapeStep readNatProgram inp ω)^[7] (state 3 pos a w f t))) := by
        rw [hbody]
        exact hb
      have hc := trace_append (shapeStep readNatProgram inp ω) (Bounded R)
        (state 3 pos a w f t) 7 (7*bs.length+3) hfirst hlast
      simpa [List.length_cons, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hc

theorem initial_run (inp : List Bool) (ω : ℕ → Bool) :
    (shapeStep readNatProgram inp ω)^[3] initState = state 3 0 0 1 0 0 := by
  simp [Function.iterate_succ_apply', shapeStep, eraseCost, step, readNatProgram,
    initState, state, regs]
  ext i
  simp [Finsupp.update_apply, Finsupp.single_apply]
  split_ifs <;> omega

theorem initial_trace (inp : List Bool) (ω : ℕ → Bool) (R : ℕ) (hR : 1 ≤ R) :
    ∀ j ≤ 3, Bounded R ((shapeStep readNatProgram inp ω)^[j] initState) := by
  intro j hj
  interval_cases j <;>
    simp [Function.iterate_succ_apply', shapeStep, eraseCost, step, readNatProgram,
      initState, Bounded]
  all_goals simp [Finsupp.support_update, Finsupp.single_apply, Function.update_apply]
  all_goals try (refine ⟨by decide, ?_⟩)
  all_goals intro i; split_ifs <;> omega

theorem full_shape (n : ℕ) (tail : List Bool) (ω : ℕ → Bool) :
    (∃ tf, (shapeStep readNatProgram (encNat n ++ tail) ω)^[7*n.size+6] initState =
      state 6 (2*n.size+1) n (2^n.size) 0 tf true) ∧
    (∀ j ≤ 7*n.size+6,
      Bounded (2^n.size) ((shapeStep readNatProgram (encNat n ++ tail) ω)^[j] initState)) := by
  have hinp : (encNat n ++ tail).drop 0 = encBits n.bits ++ tail := by rfl
  obtain ⟨⟨tf, he⟩, hb⟩ := loop_run_and_trace (encNat n ++ tail) ω (2^n.size)
    n.bits tail 0 0 1 0 0 hinp (by omega) (by omega) (by omega) (by omega)
    (by simp [Nat.size_eq_bits_len])
  have he' : (shapeStep readNatProgram (encNat n ++ tail) ω)^[7*n.size+3]
      (state 3 0 0 1 0 0) = state 6 (2*n.size+1) n (2^n.size) 0 tf true := by
    simpa [Nat.size_eq_bits_len, value_bits] using he
  constructor
  · refine ⟨tf, ?_⟩
    rw [show 7*n.size+6 = (7*n.size+3)+3 by omega, Function.iterate_add_apply,
      initial_run, he']
  · have hfirst := initial_trace (encNat n ++ tail) ω (2^n.size)
        (by
          have hp : 0 < 2^n.size := by positivity
          omega)
    have hlast : ∀ j ≤ 7*n.size+3, Bounded (2^n.size)
        ((shapeStep readNatProgram (encNat n ++ tail) ω)^[j]
          ((shapeStep readNatProgram (encNat n ++ tail) ω)^[3] initState)) := by
      rw [initial_run]
      simpa [Nat.size_eq_bits_len] using hb
    have hc := trace_append (shapeStep readNatProgram (encNat n ++ tail) ω)
      (Bounded (2^n.size)) initState 3 (7*n.size+3) hfirst hlast
    simpa only [show 3+(7*n.size+3) = 7*n.size+6 by omega] using hc

theorem encNat_length (n : ℕ) : (encNat n).length = 2*n.size+1 := by
  simp [encNat, List.length_flatMap, Nat.size_eq_bits_len, Nat.mul_comm]

theorem program_deterministic : Deterministic readNatProgram := by
  intro op hop d
  simp [readNatProgram] at hop
  rcases hop with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem program_streaming : Streaming readNatProgram := by
  intro op hop d a
  simp [readNatProgram] at hop
  rcases hop with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem readNat_correct (n : ℕ) (tail : List Bool) (ω : ℕ → Bool) :
    Halts readNatProgram (encNat n ++ tail) ω ∧
    (finalState readNatProgram (encNat n ++ tail) ω).regs 0 = n ∧
    (finalState readNatProgram (encNat n ++ tail) ω).inPos = (encNat n).length ∧
    output readNatProgram (encNat n ++ tail) ω = [] ∧
    haltStep readNatProgram (encNat n ++ tail) ω ≤ 7*n.size+6 ∧
    cost readNatProgram (encNat n ++ tail) ω ≤ 20*(n.size+1)^2 ∧
    workingBits readNatProgram (encNat n ++ tail) ω ≤ 5*(n.size+1) := by
  obtain ⟨⟨tf, he⟩, ht⟩ := full_shape n tail ω
  have hs : eraseCost (run readNatProgram (encNat n ++ tail) ω (7*n.size+6)) =
      state 6 (2*n.size+1) n (2^n.size) 0 tf true := by
    rw [run_shape]
    exact he
  have hh : (run readNatProgram (encNat n ++ tail) ω (7*n.size+6)).halted = true := by
    exact congrArg State.halted hs
  have hfinal := finalState_eq_run readNatProgram (encNat n ++ tail) ω (7*n.size+6) hh
  have hbound (j : ℕ) (hj : j ≤ 7*n.size+6) :
      Bounded (2^n.size) (run readNatProgram (encNat n ++ tail) ω j) := by
    have hb := ht j hj
    rw [← run_shape] at hb
    exact hb
  have hbits (j : ℕ) (hj : j ≤ 7*n.size+6) (i : ℕ) :
      Nat.size ((run readNatProgram (encNat n ++ tail) ω j).regs i) ≤ n.size+1 := by
    have hr := Nat.size_le_size ((hbound j hj).2.2.2 i)
    simpa [Nat.size_pow] using hr
  refine ⟨⟨7*n.size+6, hh⟩, ?_, ?_, ?_, haltStep_le _ _ _ _ hh, ?_, ?_⟩
  · rw [hfinal]
    simpa [eraseCost, state] using congrArg (fun s : State => s.regs 0) hs
  · rw [hfinal, encNat_length]
    exact congrArg State.inPos hs
  · rw [output_eq_run _ _ _ _ hh]
    exact congrArg State.out hs
  · rw [cost_eq_run _ _ _ _ hh]
    have hc := cost_le_of_step_bound readNatProgram (encNat n ++ tail) ω
      (7*n.size+6) (1+2*(n.size+1)) (by
        intro j hj
        apply step_cost_bound _ _ _ _ _ (hbits j (by omega))
        · intro i
          rw [(hbound j (by omega)).1]
          simp
        · intro d k hk
          simp [readNatProgram] at hk
          rcases hk with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp)
    nlinarith
  · apply workingBits_le_of_trace _ _ _ (7*n.size+6) _ hh
    intro j hj
    obtain ⟨hm, ho, hr, hv⟩ := hbound j hj
    exact space_le_of_registers _ 5 (n.size+1) hm ho hr (hbits j hj)

end ITPIRPreproc.MatchVec.WordRAM.ReadNatProof

open ITPIRPreproc.MatchVec ITPIRPreproc.MatchVec.WordRAM

theorem solution :
    Deterministic readNatProgram ∧ Streaming readNatProgram ∧
    ∀ (n : ℕ) (tail : List Bool) (ω : ℕ → Bool),
    Halts readNatProgram (encNat n ++ tail) ω ∧
    (finalState readNatProgram (encNat n ++ tail) ω).regs 0 = n ∧
    (finalState readNatProgram (encNat n ++ tail) ω).inPos = (encNat n).length ∧
    output readNatProgram (encNat n ++ tail) ω = [] ∧
    haltStep readNatProgram (encNat n ++ tail) ω ≤ 7*n.size+6 ∧
    cost readNatProgram (encNat n ++ tail) ω ≤ 20*(n.size+1)^2 ∧
    workingBits readNatProgram (encNat n ++ tail) ω ≤ 5*(n.size+1) := by
  exact ⟨ReadNatProof.program_deterministic, ReadNatProof.program_streaming, ReadNatProof.readNat_correct⟩
