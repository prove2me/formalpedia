-- Prove2me | solution 1 for InfoLossLAR.WorstCase.poly_program_first_bit_qpt
-- status  : ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-20T12:19:53.618079+00:00
-- url     : https://prove2.me/submissions/811c4ef9-2ae4-4739-bc97-c700d6e7a0a2

import Definitions.Def_InfoLossLAR_WorstCase_Laws
import Definitions.Def_InfoLossLAR_WorstCase_QPT
import Definitions.Def_QuantumMaxCutFiniteNumericRuntime

set_option linter.all false

namespace CurrentAFT
end CurrentAFT

namespace InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator
end InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator

namespace InfoLossLAR.WorstCase.TM2Boolean.RPN
end InfoLossLAR.WorstCase.TM2Boolean.RPN

namespace Integration9_9.TM2OutputLength
end Integration9_9.TM2OutputLength

namespace Integration9_9.TM2PlatformSerialization
end Integration9_9.TM2PlatformSerialization

namespace Integration9_9.TM2PolynomialBudget
end Integration9_9.TM2PolynomialBudget

namespace Integration9_9.TM2Simulation
end Integration9_9.TM2Simulation

namespace OAI.MetricKMedian.Binary
end OAI.MetricKMedian.Binary

namespace OAI.MetricKMedian.Binary.Automatic
end OAI.MetricKMedian.Binary.Automatic

namespace OAI.MetricKMedian.Binary.Automatic.Poly
end OAI.MetricKMedian.Binary.Automatic.Poly

namespace QMCNumericRuntime
end QMCNumericRuntime

/- Helper module Integration9_9.TM2OutputLength. -/
section P2MDyadicModule0

set_option autoImplicit false

namespace Integration9_9.TM2OutputLength

open Turing StateTransition

variable {K Λ σ : Type} {Γ : K → Type} [Fintype K] [DecidableEq K]

/-- Largest stack length; unlike a total-size bound it needs no common stack alphabet. -/
def stackSize (S : ∀ k, List (Γ k)) : ℕ := Finset.univ.sup fun k => (S k).length

omit [DecidableEq K] in
theorem length_le_stackSize (S : ∀ k, List (Γ k)) (k : K) :
    (S k).length ≤ stackSize S :=
  by
    unfold stackSize
    exact Finset.le_sup (f := fun j => (S j).length) (Finset.mem_univ k)

theorem stackSize_update_le (S : ∀ k, List (Γ k)) (k : K) (v : List (Γ k)) (n : ℕ)
    (hS : stackSize S ≤ n) (hv : v.length ≤ n) :
    stackSize (Function.update S k v) ≤ n := by
  apply Finset.sup_le
  intro j hj
  by_cases h : j = k
  · subst j
    simpa using hv
  · simpa [Function.update_of_ne h] using (length_le_stackSize S j).trans hS

/-- The maximum number of pushes along one branch of a single TM2 statement. -/
def pushBound : TM2.Stmt Γ Λ σ → ℕ
  | .push _ _ q => pushBound q + 1
  | .peek _ _ q => pushBound q
  | .pop _ _ q => pushBound q
  | .load _ q => pushBound q
  | .branch _ q r => max (pushBound q) (pushBound r)
  | .goto _ => 0
  | .halt => 0

theorem stepAux_stackSize_le (q : TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k)) :
    stackSize (TM2.stepAux q v S).stk ≤ stackSize S + pushBound q := by
  induction q generalizing v S with
  | push k f q ih =>
    have h := ih v (Function.update S k (f v :: S k))
    have hu : stackSize (Function.update S k (f v :: S k)) ≤ stackSize S + 1 :=
      stackSize_update_le S k _ _ (Nat.le_add_right _ _) (by
        simpa using Nat.succ_le_succ (length_le_stackSize S k))
    simpa only [TM2.stepAux, pushBound] using h.trans (by omega)
  | peek k f q ih => simpa only [TM2.stepAux, pushBound] using ih (f v (S k).head?) S
  | pop k f q ih =>
    have h := ih (f v (S k).head?) (Function.update S k (S k).tail)
    have hu : stackSize (Function.update S k (S k).tail) ≤ stackSize S :=
      stackSize_update_le S k _ _ (le_refl _) (by
        simp only [List.length_tail]
        exact (Nat.sub_le _ _).trans (length_le_stackSize S k))
    simpa only [TM2.stepAux, pushBound] using h.trans (Nat.add_le_add_right hu _)
  | load f q ih => simpa only [TM2.stepAux, pushBound] using ih (f v) S
  | branch f q r iq ir =>
    cases h : f v with
    | false => simpa only [TM2.stepAux, h, Bool.cond_false, pushBound] using
        (ir v S).trans (Nat.add_le_add_left (le_max_right _ _) _)
    | true => simpa only [TM2.stepAux, h, Bool.cond_true, pushBound] using
        (iq v S).trans (Nat.add_le_add_left (le_max_left _ _) _)
  | goto f => simp [TM2.stepAux, pushBound]
  | halt => simp [TM2.stepAux, pushBound]

variable [Fintype Λ]

/-- A constant depending only on the finite machine, not on its input. -/
def programPushBound (M : Λ → TM2.Stmt Γ Λ σ) : ℕ :=
  Finset.univ.sup fun l => pushBound (M l)

theorem step_stackSize_le (M : Λ → TM2.Stmt Γ Λ σ) (a b : TM2.Cfg Γ Λ σ)
    (h : TM2.step M a = some b) :
    stackSize b.stk ≤ stackSize a.stk + programPushBound M := by
  rcases a with ⟨l,v,S⟩
  cases l with
  | none => simp [TM2.step] at h
  | some l =>
    simp only [TM2.step, Option.some.injEq] at h
    subst b
    have hp : pushBound (M l) ≤ programPushBound M := by
      unfold programPushBound
      exact Finset.le_sup (f := fun j => pushBound (M j)) (Finset.mem_univ l)
    exact (stepAux_stackSize_le (M l) v S).trans (Nat.add_le_add_left hp _)

/-- Abstract accumulation of a one-step size bound through a bounded execution. -/
theorem iterate_size_bound {C : Type} (step : C → Option C) (size : C → ℕ) (cost : ℕ)
    (hstep : ∀ a b, step a = some b → size b ≤ size a + cost) :
    ∀ n a b, ((fun x : Option C => x.bind step)^[n]) (some a) = some b →
      size b ≤ size a + cost * n := by
  intro n
  induction n with
  | zero =>
    intro a b h
    simp only [Function.iterate_zero, id_eq, Option.some.injEq] at h
    subst b
    simp
  | succ n ih =>
    intro a b h
    rw [Function.iterate_succ_apply] at h
    cases hs : step a with
    | none =>
      have hn : ∀ k, ((fun x : Option C => x.bind step)^[k]) none = none := by
        intro k
        induction k with
        | zero => rfl
        | succ k hk => simpa only [Function.iterate_succ_apply, Option.bind_none] using hk
      simp only [Option.bind_some, hs, hn] at h
      contradiction
    | some a' =>
      simp only [Option.bind_some, hs] at h
      have hi := ih a' b h
      have hlocal := hstep a a' hs
      calc
        size b ≤ size a' + cost * n := hi
        _ ≤ size a + cost * (n+1) := by rw [Nat.mul_add, Nat.mul_one]; omega

theorem evalsToInTime_stackSize_le (M : Λ → TM2.Stmt Γ Λ σ)
    (a b : TM2.Cfg Γ Λ σ) (m : ℕ)
    (h : EvalsToInTime (TM2.step M) a (some b) m) :
    stackSize b.stk ≤ stackSize a.stk + programPushBound M * m := by
  have hs := iterate_size_bound (TM2.step M) (fun c => stackSize c.stk)
    (programPushBound M) (step_stackSize_le M) h.steps a b h.evals_in_steps
  exact hs.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ h.steps_le_m) _)

local instance tmStacksFintype (tm : FinTM2) : Fintype tm.K := tm.kFin

local instance tmLabelsFintype (tm : FinTM2) : Fintype tm.Λ := tm.ΛFin

/-- The initialized machine has no stack longer than its input. -/
theorem initList_stackSize_le (tm : FinTM2) (input : List (tm.Γ tm.k₀)) :
    stackSize (initList tm input).stk ≤ input.length := by
  apply Finset.sup_le
  intro k hk
  by_cases h : k = tm.k₀
  · subst k
    simp [initList]
  · simp [initList, h]

/-- A machine cannot emit more symbols than it initially receives plus its
fixed per-step push capacity times the allowed number of steps. -/
theorem output_length_le (tm : FinTM2) (input : List (tm.Γ tm.k₀))
    (output : List (tm.Γ tm.k₁)) (time : ℕ)
    (h : TM2OutputsInTime tm input (some output) time) :
    output.length ≤ input.length + programPushBound tm.m * time := by
  have hs := evalsToInTime_stackSize_le tm.m (initList tm input) (haltList tm output) time h
  calc
    output.length = ((haltList tm output).stk tm.k₁).length := by simp [haltList]
    _ ≤ stackSize (haltList tm output).stk := length_le_stackSize _ _
    _ ≤ stackSize (initList tm input).stk + programPushBound tm.m * time := hs
    _ ≤ input.length + programPushBound tm.m * time :=
      Nat.add_le_add_right (initList_stackSize_le tm input) _

end Integration9_9.TM2OutputLength

end P2MDyadicModule0

/- Helper module Integration9_9.TM2Simulation. -/
section P2MDyadicModule1

set_option autoImplicit false

set_option maxHeartbeats 1600000

namespace Integration9_9.TM2Simulation

open Turing StateTransition Function

/-- A finite-control lens. This contains only finite-state operations when the
source and target control types are finite; it cannot inspect a whole stack. -/
structure ControlLens (σ τ : Type) where
  read : τ → σ
  write : τ → σ → τ
  read_write : ∀ t s, read (write t s) = s
  write_read : ∀ t, write t (read t) = t
  write_write : ∀ t s r, write (write t s) r = write t r

namespace ControlLens

variable {σ τ : Type}

def fst : ControlLens σ (σ × τ) where
  read := Prod.fst
  write t s := (s,t.2)
  read_write _ _ := rfl
  write_read _ := rfl
  write_write _ _ _ := rfl

def snd : ControlLens τ (σ × τ) where
  read := Prod.snd
  write t s := (t.1,s)
  read_write _ _ := rfl
  write_read _ := rfl
  write_write _ _ _ := rfl

end ControlLens

variable {K J Λ L σ τ : Type} {Γ : K → Type} {Δ : J → Type}

variable [DecidableEq K] [DecidableEq J]

/-- Translate every concrete stack action to an injectively embedded stack.
Halting may either halt the containing machine or jump to a continuation. -/
def statement (i : K → J) (e : ∀ k, Γ k ≃ Δ (i k))
    (v : ControlLens σ τ) (label : Λ → L) (finish : Option L) :
    TM2.Stmt Γ Λ σ → TM2.Stmt Δ L τ
  | .push k f q => .push (i k) (fun t => e k (f (v.read t))) (statement i e v label finish q)
  | .peek k f q => .peek (i k) (fun t a => v.write t (f (v.read t) (a.map (e k).symm)))
      (statement i e v label finish q)
  | .pop k f q => .pop (i k) (fun t a => v.write t (f (v.read t) (a.map (e k).symm)))
      (statement i e v label finish q)
  | .load f q => .load (fun t => v.write t (f (v.read t))) (statement i e v label finish q)
  | .branch f q r => .branch (fun t => f (v.read t))
      (statement i e v label finish q) (statement i e v label finish r)
  | .goto f => .goto (fun t => label (f (v.read t)))
  | .halt => match finish with | none => .halt | some l => .goto (fun _ => l)

/-- The source stacks are encoded, while stacks outside their image are framed. -/
def StacksRel (i : K → J) (e : ∀ k, Γ k ≃ Δ (i k))
    (S : ∀ k, List (Γ k)) (T : ∀ j, List (Δ j)) : Prop :=
  ∀ k, T (i k) = (S k).map (e k)

theorem stacksRel_update (i : K → J) (hi : Injective i) (e : ∀ k, Γ k ≃ Δ (i k))
    {S : ∀ k, List (Γ k)} {T : ∀ j, List (Δ j)} (h : StacksRel i e S T)
    (k : K) (x : List (Γ k)) :
    StacksRel i e (update S k x) (update T (i k) (x.map (e k))) := by
  intro j
  by_cases hj : j = k
  · subst j
    simp
  · have hij : i j ≠ i k := fun hh => hj (hi hh)
    simpa [update_of_ne hj, update_of_ne hij] using h j

theorem stepAux_simulation (i : K → J) (hi : Injective i)
    (e : ∀ k, Γ k ≃ Δ (i k)) (v : ControlLens σ τ) (label : Λ → L) (finish : Option L)
    (q : TM2.Stmt Γ Λ σ) (s : σ) (t : τ) (S : ∀ k, List (Γ k)) (T : ∀ j, List (Δ j))
    (hv : v.read t = s) (hS : StacksRel i e S T) :
    let a := TM2.stepAux q s S
    let b := TM2.stepAux (statement i e v label finish q) t T
    b.l = a.l.elim finish (fun l => some (label l)) ∧
      b.var = v.write t a.var ∧ StacksRel i e a.stk b.stk ∧
      ∀ j, (∀ k, i k ≠ j) → b.stk j = T j := by
  induction q generalizing s t S T with
  | push k f q ih =>
    simp only [statement, TM2.stepAux, hv]
    have hu := stacksRel_update i hi e hS k (f s :: S k)
    simp only [List.map_cons, ← hS k] at hu
    obtain ⟨hl,hv',hs,hfr⟩ := ih s t _ _ hv hu
    refine ⟨hl,hv',hs,?_⟩
    intro j hj
    rw [hfr j hj, update_of_ne (Ne.symm (hj k))]
  | peek k f q ih =>
    have hh : (T (i k)).head?.map (e k).symm = (S k).head? := by
      rw [hS k, List.head?_map, Option.map_map]
      simp
    simp only [statement, TM2.stepAux, hv, hh]
    obtain ⟨hl,hv',hs,hfr⟩ := ih _ _ S T (v.read_write _ _) hS
    exact ⟨hl, hv'.trans (v.write_write _ _ _),hs,hfr⟩
  | pop k f q ih =>
    have hh : (T (i k)).head?.map (e k).symm = (S k).head? := by
      rw [hS k, List.head?_map, Option.map_map]
      simp
    have hu := stacksRel_update i hi e hS k (S k).tail
    rw [List.map_tail, ← hS k] at hu
    simp only [statement, TM2.stepAux, hv, hh]
    obtain ⟨hl,hv',hs,hfr⟩ := ih _ _ _ _ (v.read_write _ _) hu
    refine ⟨hl,hv'.trans (v.write_write _ _ _),hs,?_⟩
    intro j hj
    rw [hfr j hj, update_of_ne (Ne.symm (hj k))]
  | load f q ih =>
    simp only [statement, TM2.stepAux, hv]
    obtain ⟨hl,hv',hs,hfr⟩ := ih _ _ S T (v.read_write _ _) hS
    exact ⟨hl,hv'.trans (v.write_write _ _ _),hs,hfr⟩
  | branch f q r iq ir =>
    cases hf : f s <;> simp only [statement, TM2.stepAux, hv, hf, Bool.cond_false, Bool.cond_true]
    · exact ir s t S T hv hS
    · exact iq s t S T hv hS
  | goto f =>
    simp only [statement, TM2.stepAux, Option.elim_some, hv]
    exact ⟨trivial,by simpa only [hv] using (v.write_read t).symm,hS,fun _ _ => trivial⟩
  | halt =>
    cases finish <;> simp only [statement, TM2.stepAux, Option.elim_none]
    all_goals exact ⟨trivial,by simpa only [hv] using (v.write_read t).symm,hS,fun _ _ => trivial⟩

/-- Simulation of successful transitions needs no assertion about what happens
after a source machine halts. This permits a halt to become a continuation. -/
theorem iterate_simulation {A B : Type} (f : A → Option A) (g : B → Option B)
    (R : A → B → Prop)
    (hstep : ∀ a a' b, f a = some a' → R a b → ∃ b', g b = some b' ∧ R a' b') :
    ∀ n a a' b, ((fun c : Option A => c.bind f)^[n]) (some a) = some a' → R a b →
      ∃ b', ((fun c : Option B => c.bind g)^[n]) (some b) = some b' ∧ R a' b' := by
  intro n
  induction n with
  | zero =>
    intro a a' b hn hr
    simp only [iterate_zero, id_eq, Option.some.injEq] at hn
    subst a'
    exact ⟨b,rfl,hr⟩
  | succ n ih =>
    intro a a' b hn hr
    rw [iterate_succ_apply] at hn
    cases hf : f a with
    | none =>
      have hnone : ∀ m, ((fun c : Option A => c.bind f)^[m]) none = none := by
        intro m
        induction m with
        | zero => rfl
        | succ m hm => simpa only [iterate_succ_apply, Option.bind_none] using hm
      simp only [Option.bind_some, hf, hnone] at hn
      contradiction
    | some a1 =>
      simp only [Option.bind_some, hf] at hn
      obtain ⟨b1,hb1,hr1⟩ := hstep a a1 b hf hr
      obtain ⟨b',hb',hr'⟩ := ih a1 a' b1 hn hr1
      refine ⟨b',?_,hr'⟩
      simpa only [iterate_succ_apply, Option.bind_some, hb1] using hb'

theorem evalsToInTime_simulation {A B : Type} (f : A → Option A) (g : B → Option B)
    (R : A → B → Prop)
    (hstep : ∀ a a' b, f a = some a' → R a b → ∃ b', g b = some b' ∧ R a' b')
    (a a' : A) (b : B) (m : ℕ) (h : EvalsToInTime f a (some a') m) (hr : R a b) :
    ∃ b', Nonempty (EvalsToInTime g b (some b') m) ∧ R a' b' := by
  obtain ⟨b',hb',hr'⟩ := iterate_simulation f g R hstep h.steps a a' b h.evals_in_steps hr
  exact ⟨b',⟨⟨⟨h.steps,hb'⟩,h.steps_le_m⟩⟩,hr'⟩

/-- A stack store containing a list on just one typed stack. -/
def singleStack (k : K) (x : List (Γ k)) (j : K) : List (Γ j) :=
  if h : j = k then by rw [h]; exact x else []

omit [DecidableEq K] [DecidableEq J] in
theorem stacksRel_ext (i : K → J) (e : ∀ k, Γ k ≃ Δ (i k))
    (S : ∀ k, List (Γ k)) (T U : ∀ j, List (Δ j))
    (hT : StacksRel i e S T) (hU : StacksRel i e S U)
    (hTf : ∀ j, (∀ k, i k ≠ j) → T j = [])
    (hUf : ∀ j, (∀ k, i k ≠ j) → U j = []) : T = U := by
  classical
  funext j
  by_cases h : ∃ k, i k = j
  · obtain ⟨k,rfl⟩ := h
    exact (hT k).trans (hU k).symm
  · have hn : ∀ k, i k ≠ j := by simpa only [not_exists] using h
    exact (hTf j hn).trans (hUf j hn).symm

/-- A whole configuration embedding, with empty unused stacks. The anchor fixes
the other component of the finite control state throughout one machine phase. -/
def ConfigRel (i : K → J) (e : ∀ k, Γ k ≃ Δ (i k)) (v : ControlLens σ τ)
    (label : Λ → L) (finish : Option L) (anchor : τ)
    (a : TM2.Cfg Γ Λ σ) (b : TM2.Cfg Δ L τ) : Prop :=
  b.l = a.l.elim finish (fun l => some (label l)) ∧
  b.var = v.write anchor a.var ∧ StacksRel i e a.stk b.stk ∧
  ∀ j, (∀ k, i k ≠ j) → b.stk j = []

theorem configuration_step (i : K → J) (hi : Injective i)
    (e : ∀ k, Γ k ≃ Δ (i k)) (v : ControlLens σ τ) (label : Λ → L) (finish : Option L)
    (M : Λ → TM2.Stmt Γ Λ σ) (N : L → TM2.Stmt Δ L τ)
    (hN : ∀ l, N (label l) = statement i e v label finish (M l)) (anchor : τ)
    (a a' : TM2.Cfg Γ Λ σ) (b : TM2.Cfg Δ L τ)
    (ha : TM2.step M a = some a') (hr : ConfigRel i e v label finish anchor a b) :
    ∃ b', TM2.step N b = some b' ∧ ConfigRel i e v label finish anchor a' b' := by
  rcases a with ⟨al,av,as⟩
  cases al with
  | none => simp [TM2.step] at ha
  | some l =>
    simp only [TM2.step, Option.some.injEq] at ha
    subst a'
    obtain ⟨hl,hv,hs,hfr⟩ := hr
    have hb : b.l = some (label l) := hl
    have hvread : v.read b.var = av := by rw [hv,v.read_write]
    obtain ⟨hl',hv',hs',hfr'⟩ := stepAux_simulation i hi e v label finish
      (M l) av b.var as b.stk hvread hs
    refine ⟨TM2.stepAux (statement i e v label finish (M l)) b.var b.stk,?_,
      hl',?_,hs',?_⟩
    · cases b with
      | mk bl bv bs =>
        change bl = some (label l) at hb
        subst bl
        simp only [TM2.step,hN]
    · rw [hv',hv,v.write_write]
    · intro j hj
      exact (hfr' j hj).trans (hfr j hj)

theorem bounded_configuration_simulation (i : K → J) (hi : Injective i)
    (e : ∀ k, Γ k ≃ Δ (i k)) (v : ControlLens σ τ) (label : Λ → L) (finish : Option L)
    (M : Λ → TM2.Stmt Γ Λ σ) (N : L → TM2.Stmt Δ L τ)
    (hN : ∀ l, N (label l) = statement i e v label finish (M l)) (anchor : τ)
    (a a' : TM2.Cfg Γ Λ σ) (b : TM2.Cfg Δ L τ) (m : ℕ)
    (h : EvalsToInTime (TM2.step M) a (some a') m)
    (hr : ConfigRel i e v label finish anchor a b) :
    ∃ b', Nonempty (EvalsToInTime (TM2.step N) b (some b') m) ∧
      ConfigRel i e v label finish anchor a' b' :=
  evalsToInTime_simulation (TM2.step M) (TM2.step N)
    (ConfigRel i e v label finish anchor)
    (configuration_step i hi e v label finish M N hN anchor) a a' b m h hr

end Integration9_9.TM2Simulation

end P2MDyadicModule1

/- Helper module Integration9_9.TM2Composition. -/
section P2MDyadicModule2

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option backward.isDefEq.respectTransparency false

namespace Integration9_9.TM2Composition

open Turing StateTransition Function TM2Simulation

local instance stackFinite (tm : FinTM2) : Fintype tm.K := tm.kFin

local instance labelFinite (tm : FinTM2) : Fintype tm.Λ := tm.ΛFin

local instance stateFinite (tm : FinTM2) : Fintype tm.σ := tm.σFin

local instance inputFinite (tm : FinTM2) : Fintype (tm.Γ tm.k₀) := tm.Γk₀Fin

abbrev Extra (b : FinTM2) := {k : b.K // k ≠ b.k₀}

abbrev Stack (a b : FinTM2) := a.K ⊕ Extra b

def Alphabet (a b : FinTM2) : Stack a b → Type
  | .inl k => a.Γ k
  | .inr k => b.Γ k.val

def leftStack (a b : FinTM2) (k : a.K) : Stack a b := .inl k

def leftSymbol (a b : FinTM2) (k : a.K) : a.Γ k ≃ Alphabet a b (leftStack a b k) :=
  Equiv.refl _

def rightStack (a b : FinTM2) (k : b.K) : Stack a b :=
  if h : k = b.k₀ then .inl a.k₁ else .inr ⟨k,h⟩

@[simp] theorem rightStack_input (a b : FinTM2) : rightStack a b b.k₀ = .inl a.k₁ := by
  simp [rightStack]

theorem rightStack_injective (a b : FinTM2) : Injective (rightStack a b) := by
  intro k j h
  by_cases hk : k = b.k₀ <;> by_cases hj : j = b.k₀
  · exact hk.trans hj.symm
  · simp [rightStack,hk,hj] at h
  · simp [rightStack,hk,hj] at h
  · simpa [rightStack,hk,hj,Subtype.ext_iff] using h

/-- The sole alphabet conversion occurs at the shared interface stack. -/
def rightSymbol (a b : FinTM2) (e : b.Γ b.k₀ ≃ a.Γ a.k₁) (k : b.K) :
    b.Γ k ≃ Alphabet a b (rightStack a b k) := by
  unfold rightStack
  split_ifs with hk
  · subst k; exact e
  · exact Equiv.refl _

/-- The first halt is a jump to the second program. Its stack is already the
second program's input stack, so this introduces no copying loop. -/
def program (a b : FinTM2) (e : b.Γ b.k₀ ≃ a.Γ a.k₁) :
    a.Λ ⊕ b.Λ → TM2.Stmt (Alphabet a b) (a.Λ ⊕ b.Λ) (a.σ × b.σ)
  | .inl l => statement (leftStack a b) (leftSymbol a b) ControlLens.fst
      Sum.inl (some (.inr b.main)) (a.m l)
  | .inr l => statement (rightStack a b) (rightSymbol a b e) ControlLens.snd
      Sum.inr none (b.m l)

def machine (a b : FinTM2) (e : b.Γ b.k₀ ≃ a.Γ a.k₁) : FinTM2 where
  K := Stack a b
  k₀ := .inl a.k₀
  k₁ := rightStack a b b.k₁
  Γ := Alphabet a b
  Λ := a.Λ ⊕ b.Λ
  main := .inl a.main
  σ := a.σ × b.σ
  initialState := (a.initialState,b.initialState)
  m := program a b e
  Γk₀Fin := a.Γk₀Fin

/-- An exact canonical configuration, with a single nonempty stack. -/
def canonical (a b : FinTM2) (l : Option (a.Λ ⊕ b.Λ)) (s : a.σ × b.σ)
    (k : Stack a b) (x : List (Alphabet a b k)) :
    TM2.Cfg (Alphabet a b) (a.Λ ⊕ b.Λ) (a.σ × b.σ) :=
  ⟨l,s,singleStack k x⟩

/-- A configuration relation uniquely specifies canonical stack contents. -/
theorem configRel_unique {K J Λ L σ τ : Type} {Γ : K → Type} {Δ : J → Type}
    [DecidableEq K] [DecidableEq J] (i : K → J) (e : ∀ k, Γ k ≃ Δ (i k))
    (v : ControlLens σ τ) (label : Λ → L) (finish : Option L) (anchor : τ)
    (a : TM2.Cfg Γ Λ σ) (b c : TM2.Cfg Δ L τ)
    (hb : ConfigRel i e v label finish anchor a b)
    (hc : ConfigRel i e v label finish anchor a c) : b = c := by
  obtain ⟨hbl,hbv,hbs,hbf⟩ := hb
  obtain ⟨hcl,hcv,hcs,hcf⟩ := hc
  have hl := hbl.trans hcl.symm
  have hv := hbv.trans hcv.symm
  have hs := stacksRel_ext i e a.stk b.stk c.stk hbs hcs hbf hcf
  cases b; cases c
  simp only [TM2.Cfg.mk.injEq] at *
  exact ⟨hl,hv,hs⟩

theorem left_initial (a b : FinTM2) (e : b.Γ b.k₀ ≃ a.Γ a.k₁)
    (x : List (a.Γ a.k₀)) :
    ConfigRel (leftStack a b) (leftSymbol a b) ControlLens.fst Sum.inl
      (some (.inr b.main)) (a.initialState,b.initialState)
      (initList a x) (initList (machine a b e) x) := by
  refine ⟨rfl,rfl,?_,?_⟩
  · intro k
    by_cases hk : k = a.k₀
    · subst k; simp [initList,machine,leftStack,leftSymbol,Alphabet]
    · simp [initList,machine,leftStack,leftSymbol,Alphabet,hk]
  · intro j hj
    cases j with
    | inl k => exact (hj k rfl).elim
    | inr k => simp [initList,machine]

/-- Interface between the two phases, expressed in the first output alphabet. -/
def middle (a b : FinTM2) (x : List (a.Γ a.k₁)) :
    TM2.Cfg (Alphabet a b) (a.Λ ⊕ b.Λ) (a.σ × b.σ) :=
  canonical a b (some (.inr b.main)) (a.initialState,b.initialState) (.inl a.k₁) x

theorem left_terminal (a b : FinTM2) (x : List (a.Γ a.k₁)) :
    ConfigRel (leftStack a b) (leftSymbol a b) ControlLens.fst Sum.inl
      (some (.inr b.main)) (a.initialState,b.initialState)
      (haltList a x) (middle a b x) := by
  refine ⟨rfl,rfl,?_,?_⟩
  · intro k
    by_cases hk : k = a.k₁
    · subst k; simp [haltList,middle,canonical,singleStack,leftStack,leftSymbol,Alphabet]
    · simp [haltList,middle,canonical,singleStack,leftStack,leftSymbol,Alphabet,hk]
  · intro j hj
    cases j with
    | inl k => exact (hj k rfl).elim
    | inr k => simp [middle,canonical,singleStack]

private theorem map_cast_equiv {A B C : Type} (h : B = C) (e : A ≃ B) (x : List A) :
    cast (congrArg List h) (x.map e) =
      x.map (fun a => (cast (congrArg (fun D => A ≃ D) h) e : A ≃ C) a) := by
  subst C
  rfl

theorem right_initial (a b : FinTM2) (e : b.Γ b.k₀ ≃ a.Γ a.k₁)
    (x : List (b.Γ b.k₀)) :
    ConfigRel (rightStack a b) (rightSymbol a b e) ControlLens.snd Sum.inr
      none (a.initialState,b.initialState)
      (initList b x) (middle a b (x.map e)) := by
  refine ⟨rfl,rfl,?_,?_⟩
  · intro k
    by_cases hk : k = b.k₀
    · subst k
      simp only [initList,middle,canonical,singleStack,rightSymbol,rightStack,Alphabet,
        dite_true,eq_self]
      exact map_cast_equiv (by simp) e x
    · simp [initList,middle,canonical,singleStack,rightSymbol,rightStack,Alphabet,hk]
  · intro j hj
    cases j with
    | inl k =>
      by_cases hk : k = a.k₁
      · subst k
        exact (hj b.k₀ (rightStack_input a b)).elim
      · simp [middle,canonical,singleStack,hk]
    | inr k =>
      exact (hj k.val (by simp [rightStack,k.property])).elim

theorem right_terminal (a b : FinTM2) (e : b.Γ b.k₀ ≃ a.Γ a.k₁)
    (x : List (b.Γ b.k₁)) :
    ConfigRel (rightStack a b) (rightSymbol a b e) ControlLens.snd Sum.inr
      none (a.initialState,b.initialState)
      (haltList b x) (haltList (machine a b e) (x.map (rightSymbol a b e b.k₁))) := by
  refine ⟨rfl,rfl,?_,?_⟩
  · intro k
    by_cases hk : k = b.k₁
    · subst k; simp [haltList,machine]
    · have hi : rightStack a b k ≠ rightStack a b b.k₁ :=
        fun h => hk (rightStack_injective a b h)
      simp [haltList,machine,hk,hi]
  · intro j hj
    have hi := Ne.symm (hj b.k₁)
    simp [haltList,machine,hi]

/-- Exact sequential running time for the shared-stack composite. The two
interface words coincide after the fixed letterwise alphabet conversion. -/
theorem outputsInTime (a b : FinTM2) (e : b.Γ b.k₀ ≃ a.Γ a.k₁)
    (input : List (a.Γ a.k₀)) (interface : List (b.Γ b.k₀))
    (output : List (b.Γ b.k₁)) (m n : ℕ)
    (ha : TM2OutputsInTime a input (some (interface.map e)) m)
    (hb : TM2OutputsInTime b interface (some output) n) :
    Nonempty (TM2OutputsInTime (machine a b e) input
      (some (output.map (rightSymbol a b e b.k₁))) (n+m)) := by
  obtain ⟨c,⟨hc⟩,hr⟩ := bounded_configuration_simulation
    (leftStack a b) Sum.inl_injective (leftSymbol a b) ControlLens.fst Sum.inl
    (some (.inr b.main)) a.m (program a b e) (fun _ => rfl)
    (a.initialState,b.initialState) (initList a input) (haltList a (interface.map e))
    (initList (machine a b e) input) m ha (left_initial a b e input)
  have heq : c = middle a b (interface.map e) :=
    configRel_unique _ _ _ _ _ _ _ _ _ hr (left_terminal a b (interface.map e))
  subst c
  obtain ⟨d,⟨hd⟩,hr'⟩ := bounded_configuration_simulation
    (rightStack a b) (rightStack_injective a b) (rightSymbol a b e) ControlLens.snd Sum.inr
    none b.m (program a b e) (fun _ => rfl)
    (a.initialState,b.initialState) (initList b interface) (haltList b output)
    (middle a b (interface.map e)) n hb (right_initial a b e interface)
  have heq : d = haltList (machine a b e) (output.map (rightSymbol a b e b.k₁)) :=
    configRel_unique _ _ _ _ _ _ _ _ _ hr' (right_terminal a b e output)
  subst d
  exact ⟨EvalsToInTime.trans (machine a b e).step m n _ _ _ hc hd⟩

/-- Evaluation of a natural-coefficient time polynomial is monotone. -/
theorem polynomial_eval_monotone (p : Polynomial ℕ) : Monotone p.eval := by
  intro x y hxy
  simp only [Polynomial.eval_eq_sum,Polynomial.sum_def]
  apply Finset.sum_le_sum
  intro i hi
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hxy i)

/-- A concrete witness for closure of Mathlib's exact TM2 polynomial-time model
under composition. The machine uses a shared typed interface stack. -/
noncomputable def computableInPolyTime
    {α β γ αΓ βΓ γΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ}
    {ec : γ → List γΓ} {f : α → β} {g : β → γ}
    (h1 : TM2ComputableInPolyTime ea eb f) (h2 : TM2ComputableInPolyTime eb ec g) :
    TM2ComputableInPolyTime ea ec (g ∘ f) := by
  let e : h2.tm.Γ h2.tm.k₀ ≃ h1.tm.Γ h1.tm.k₁ :=
    h2.inputAlphabet.trans h1.outputAlphabet.symm
  let size : Polynomial ℕ := Polynomial.X +
    Polynomial.C (TM2OutputLength.programPushBound h1.tm.m) * h1.time
  refine {
    tm := machine h1.tm h2.tm e
    inputAlphabet := h1.inputAlphabet
    outputAlphabet := (rightSymbol h1.tm h2.tm e h2.tm.k₁).symm.trans h2.outputAlphabet
    time := h1.time + h2.time.comp size
    outputsFun := ?_
  }
  intro x
  have hconnect : ((eb (f x)).map h2.inputAlphabet.invFun).map e =
      (eb (f x)).map h1.outputAlphabet.invFun := by
    simp [e,List.map_map,Equiv.coe_trans,Function.comp_def]
  have hrun := outputsInTime h1.tm h2.tm e
    ((ea x).map h1.inputAlphabet.invFun) ((eb (f x)).map h2.inputAlphabet.invFun)
    ((ec (g (f x))).map h2.outputAlphabet.invFun)
    (h1.time.eval (ea x).length) (h2.time.eval (eb (f x)).length)
    (by simpa only [hconnect] using h1.outputsFun x) (h2.outputsFun (f x))
  have hlen := TM2OutputLength.output_length_le h1.tm
    ((ea x).map h1.inputAlphabet.invFun) ((eb (f x)).map h1.outputAlphabet.invFun)
    (h1.time.eval (ea x).length) (h1.outputsFun x)
  simp only [List.length_map] at hlen
  have hsize : (eb (f x)).length ≤ size.eval (ea x).length := by
    simpa only [size,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_mul,
      Polynomial.eval_C] using hlen
  have htime : h2.time.eval (eb (f x)).length + h1.time.eval (ea x).length ≤
      (h1.time + h2.time.comp size).eval (ea x).length := by
    rw [Polynomial.eval_add,Polynomial.eval_comp]
    exact (Nat.add_le_add_right (polynomial_eval_monotone h2.time hsize) _).trans_eq
      (Nat.add_comm _ _)
  let run := Classical.choice hrun
  have result : TM2OutputsInTime (machine h1.tm h2.tm e)
      ((ea x).map h1.inputAlphabet.invFun)
      (some (((ec (g (f x))).map h2.outputAlphabet.invFun).map
        (rightSymbol h1.tm h2.tm e h2.tm.k₁)))
      ((h1.time+h2.time.comp size).eval (ea x).length) :=
    ⟨run.toEvalsTo,run.steps_le_m.trans htime⟩
  convert result using 1
  simp only [List.map_map,Equiv.coe_trans,Equiv.invFun_as_coe,
      Equiv.symm_trans,Equiv.symm_symm,Function.comp_def,Function.comp_apply]
  rfl

/-- The missing Mathlib closure theorem, proved without importing its
`proof_wanted` declaration or treating a reported work count as execution time. -/
theorem comp
    {α β γ αΓ βΓ γΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ}
    {ec : γ → List γΓ} {f : α → β} {g : β → γ}
    (h1 : TM2ComputableInPolyTime ea eb f) (h2 : TM2ComputableInPolyTime eb ec g) :
    Nonempty (TM2ComputableInPolyTime ea ec (g ∘ f)) :=
  ⟨computableInPolyTime h1 h2⟩

end Integration9_9.TM2Composition

end P2MDyadicModule2

/- Helper module Integration9_9.TM2NativePrime. -/
section P2MDyadicModule3

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option maxRecDepth 4096

set_option backward.isDefEq.respectTransparency false

namespace Integration9_9.TM2NativePrime

open OAI.MetricKMedian.Binary

open OAI.MetricKMedian.Binary.Automatic

open CurrentAFT

open scoped BigOperators

/-- A fixed-degree polynomial unary budget generated from the actual input tape. -/
def powerSlots : ℕ → List Unit → List Unit
  | 0, _ => [()]
  | k+1, xs => xs.flatMap (fun _ => powerSlots k xs)

@[fun_prop] theorem powerSlots_poly (k : ℕ) : Poly (powerSlots k) := by
  induction k with
  | zero => exact OAI.MetricKMedian.Binary.Automatic.Poly.const [()]
  | succ k ih =>
    change Poly (fun xs : List Unit => xs.flatMap (fun _ => powerSlots k xs))
    apply Poly.list_flatMap
    · exact Poly.comp ih Poly.fst
    · exact Poly.identity

theorem powerSlots_length (k : ℕ) (xs : List Unit) : (powerSlots k xs).length = xs.length ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp [powerSlots, List.length_flatMap, ih, List.map_const, List.sum_replicate, pow_succ, Nat.mul_comm]

attribute [local irreducible] powerSlots

end Integration9_9.TM2NativePrime

end P2MDyadicModule3

/- Helper module Integration9_9.TM2PlatformSerialization. -/
section P2MDyadicModule4

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace Integration9_9.TM2PlatformSerialization

open OAI.MetricKMedian.Binary

open OAI.MetricKMedian.Binary.Automatic

open OAI.MetricKMedian.Binary.Automatic.Poly

open QMCNumericRuntime

open QAlgorithms.Complexity

open Polynomial

/-- A concrete Boolean-list program is a platform string-time certificate. -/
theorem polyTime_of_poly {f : Str → Str} (h : Poly f) : PolyTimeComputable f := by
  let P := (BooleanLists.packProgram.comp h.program).comp BooleanLists.unpackProgram
  exact ⟨(P.congr f (fun _ => rfl)).stock⟩

/-- Keep both the unary token and the untouched suffix. -/
def readUnary (xs : Str) : Str × Str :=
  (xs.take (inputWidth xs + 1), xs.drop (inputWidth xs + 1))

@[fun_prop] theorem readUnary_poly : Poly readUnary := by
  unfold readUnary
  have h : Poly (fun xs : Str => (xs, inputWidth xs + 1)) := by fun_prop
  exact Poly.pair (Poly.comp parser_take_poly h) (Poly.comp parser_drop_poly h)

@[simp] theorem readUnary_append (n : ℕ) (xs : Str) :
    readUnary (encNat n ++ xs) = (encNat n, xs) := by
  have h : inputWidth (encNat n ++ xs) = n := by
    simpa only [encNat, List.append_assoc, List.singleton_append] using inputWidth_prefix n xs
  simp only [readUnary, h]
  have hl : (encNat n).length = n + 1 := by simp [encNat]
  rw [← hl, List.take_left, List.drop_left]

theorem readUnary_rest_length (xs : Str) : (readUnary xs).2.length ≤ xs.length := by
  simp only [readUnary, List.length_drop]
  omega

/-- Slots are read from the unary prefix, so malformed words still give a bounded loop. -/
def unarySlots (xs : Str) : List Unit :=
  (xs.take (inputWidth xs)).map (fun _ => ())

@[fun_prop] theorem unarySlots_poly : Poly unarySlots := by
  unfold unarySlots
  apply Poly.list_map
  · fun_prop
  · have h : Poly (fun xs : Str => (xs, inputWidth xs)) := by fun_prop
    exact Poly.comp parser_take_poly h

@[simp] theorem unarySlots_append (n : ℕ) (xs : Str) :
    unarySlots (encNat n ++ xs) = List.replicate n () := by
  have h : inputWidth (encNat n ++ xs) = n := by
    simpa only [encNat, List.append_assoc, List.singleton_append] using inputWidth_prefix n xs
  simp only [unarySlots, h]
  simp [encNat, List.append_assoc]

/-- Serialize the length of a supplied list, never expand a binary integer as unary. -/
def lengthToken {α : Type} (xs : List α) : Str := xs.map (fun _ => true) ++ [false]

@[simp] theorem lengthToken_eq {α : Type} (xs : List α) : lengthToken xs = encNat xs.length := by
  simp [lengthToken, encNat, List.map_const']

@[fun_prop] theorem lengthToken_poly {α : Type} [Coding α] [Inhabited α] :
    Poly (lengthToken : List α → Str) := by
  unfold lengthToken
  fun_prop

/-- Serialize a list of already encoded entries using the platform's unary list format. -/
def serializeWords (xs : List Str) : Str := lengthToken xs ++ xs.flatten

@[fun_prop] theorem serializeWords_poly : Poly serializeWords := by
  unfold serializeWords
  have hf : Poly (List.flatten : List Str → Str) := ⟨PolyProgram.listFlatten encodeBool false⟩
  exact Poly.comp Poly.list_append (Poly.pair lengthToken_poly hf)

@[simp] theorem serializeWords_eq (xs : List Str) : serializeWords xs = encStr xs := by
  rw [serializeWords, lengthToken_eq]
  rfl

section RepeatedParser

variable {α : Type} [Coding α] [Inhabited α]

variable (read : Str → Str × α)

abbrev ParserState (α : Type) := Str × List α

lemma parserState_encoding_length (state : ParserState α) :
    (enc state).length = 6 * state.1.length + 1 + (encodeList enc state.2).length := by
  change (encodePair (encodeList encodeBool) (encodeList enc) state).length = _
  simp only [encodePair_length, BooleanLists.length]
  omega

def parseStep (state : ParserState α) (_ : Unit) : ParserState α :=
  let result := read state.1
  (result.1, result.2 :: state.2)

@[fun_prop] theorem parseStep_poly (hr : Poly read) :
    Poly (fun x : ParserState α × Unit => parseStep read x.1 x.2) := by
  unfold parseStep
  fun_prop

noncomputable def parserElementBound (hr : Poly read) : Polynomial ℕ :=
  hr.program.sizeBound.comp (3 * X)

lemma parser_element_bound (hr : Poly read) (xs : Str) :
    (enc (read xs).2).length ≤ (parserElementBound read hr).eval xs.length := by
  have h := hr.program.length_bound xs
  change (encodePair (encodeList encodeBool) enc (read xs)).length ≤
    hr.program.sizeBound.eval (encodeList encodeBool xs).length at h
  simp only [encodePair_length, BooleanLists.length] at h
  simp only [parserElementBound, eval_comp, eval_mul, eval_ofNat, eval_X]
  omega

lemma parser_fold_bounds (hr : Poly read)
    (hrest : ∀ xs, (read xs).1.length ≤ xs.length)
    (slots : List Unit) (xs : Str) (acc : List α) :
    (slots.foldl (parseStep read) (xs,acc)).1.length ≤ xs.length ∧
    (encodeList enc (slots.foldl (parseStep read) (xs,acc)).2).length ≤
      (encodeList enc acc).length + slots.length * (2 * (parserElementBound read hr).eval xs.length + 1) := by
  induction slots generalizing xs acc with
  | nil => simp only [List.foldl_nil, List.length_nil, zero_mul, add_zero, le_refl, and_self]
  | cons slot slots ih =>
    have hi := ih (read xs).1 ((read xs).2 :: acc)
    have hrx := hrest xs
    have hp := polynomial_eval_mono (parserElementBound read hr) hrx
    have he := parser_element_bound read hr xs
    constructor
    · simpa only [List.foldl_cons, parseStep] using hi.1.trans hrx
    · change (encodeList enc
        (slots.foldl (parseStep read) ((read xs).1, (read xs).2 :: acc)).2).length ≤ _
      have hm : slots.length * (2 * (parserElementBound read hr).eval (read xs).1.length + 1) ≤
          slots.length * (2 * (parserElementBound read hr).eval xs.length + 1) :=
        Nat.mul_le_mul_left _ (by omega)
      simp only [EncodedList.cons_length] at hi
      simp only [List.length_cons]
      nlinarith

noncomputable def parserFoldBound (hr : Poly read) : Polynomial ℕ :=
  X + X * (2 * parserElementBound read hr + 1)

lemma parser_fold_state_bound (hr : Poly read)
    (hrest : ∀ xs, (read xs).1.length ≤ xs.length)
    (as : List Unit) (b : ParserState α) (pre suf : List Unit) (he : as = pre ++ suf) :
    (enc (pre.foldl (parseStep read) b)).length ≤
      (parserFoldBound read hr).eval (encodePair (encodeList (enc : Unit → Str)) enc (as,b)).length := by
  let N := (encodePair (encodeList (enc : Unit → Str)) enc (as,b)).length
  have hN : N = 2 * (encodeList (enc : Unit → Str) as).length + 1 +
      (6 * b.1.length + 1 + (encodeList enc b.2).length) := by
    simp only [N, encodePair_length, parserState_encoding_length]
  have hslots : pre.length ≤ N := by
    have h := EncodedList.length_le (enc : Unit → Str) as
    have hl : pre.length ≤ as.length := by simp only [he, List.length_append]; omega
    omega
  have hx : b.1.length ≤ N := by omega
  have hh := parser_fold_bounds read hr hrest pre b.1 b.2
  simp only [Prod.eta] at hh
  have hp := polynomial_eval_mono (parserElementBound read hr) hx
  have hm : pre.length * (2 * (parserElementBound read hr).eval b.1.length + 1) ≤
      N * (2 * (parserElementBound read hr).eval N + 1) := Nat.mul_le_mul hslots (by omega)
  change (enc (pre.foldl (parseStep read) b)).length ≤ (parserFoldBound read hr).eval N
  rw [parserState_encoding_length]
  simp only [parserFoldBound, eval_add, eval_mul, eval_X, eval_ofNat, eval_one]
  omega

@[fun_prop] theorem parserFold_poly (hr : Poly read)
    (hrest : ∀ xs, (read xs).1.length ≤ xs.length) :
    Poly (fun x : List Unit × ParserState α => x.1.foldl (parseStep read) x.2) :=
  ⟨(parseStep_poly read hr).program.listFold () (parserFoldBound read hr)
    (parser_fold_state_bound read hr hrest)⟩

/-- Parse a unary-counted list; reverse only the parser's accumulator. -/
def readList (xs : Str) : Str × List α :=
  let state := (unarySlots xs).foldl (parseStep read) ((readUnary xs).2, [])
  (state.1, state.2.reverse)

@[fun_prop] theorem readList_poly (hr : Poly read)
    (hrest : ∀ xs, (read xs).1.length ≤ xs.length) : Poly (readList read) := by
  unfold readList
  have hs : Poly (fun xs : Str =>
      (unarySlots xs).foldl (parseStep read) ((readUnary xs).2, ([] : List α))) :=
    by
      have h : Poly (fun xs : Str => (unarySlots xs, ((readUnary xs).2, ([] : List α)))) :=
        Poly.pair unarySlots_poly (Poly.pair (Poly.comp Poly.snd readUnary_poly) (OAI.MetricKMedian.Binary.Automatic.Poly.const (α := Str) ([] : List α)))
      exact Poly.comp (parserFold_poly read hr hrest) h
  exact Poly.pair (Poly.comp Poly.fst hs)
    (Poly.comp parser_reverse_poly (Poly.comp Poly.snd hs))

lemma parseStep_fold_mapped {β : Type} (code : β → Str) (value : β → α)
    (hread : ∀ a xs, read (code a ++ xs) = (xs,value a))
    (as : List β) (xs : Str) (acc : List α) :
    (List.replicate as.length ()).foldl (parseStep read) (as.flatMap code ++ xs, acc) =
      (xs, (as.map value).reverse ++ acc) := by
  induction as generalizing acc with
  | nil => rfl
  | cons a as ih =>
    simp only [List.length_cons, List.replicate_succ, List.foldl_cons, List.flatMap_cons,
      List.append_assoc, parseStep, hread]
    rw [ih]
    simp [List.reverse_cons, List.append_assoc]

@[simp] theorem readList_append_mapped {β : Type} (code : β → Str) (value : β → α)
    (hread : ∀ a xs, read (code a ++ xs) = (xs,value a)) (as : List β) (xs : Str) :
    readList read (encStr (as.map code) ++ xs) = (xs, as.map value) := by
  have he : encStr (as.map code) ++ xs = encNat as.length ++ (as.flatMap code ++ xs) := by
    simp [encStr, List.flatMap_def, List.append_assoc]
  rw [he, readList, unarySlots_append, readUnary_append,
    parseStep_fold_mapped read code value hread]
  simp

end RepeatedParser

end Integration9_9.TM2PlatformSerialization

end P2MDyadicModule4

/- Helper module Integration9_9.TM2PolynomialBudget. -/
section P2MDyadicModule5

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace Integration9_9.TM2PolynomialBudget

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Polynomial

theorem unitList_eq (xs ys : List Unit) (h : xs.length = ys.length) : xs = ys := by
  apply List.ext_getElem h
  intro i hi hj
  exact Subsingleton.elim _ _

@[fun_prop] theorem polynomialSlots_poly (p : Polynomial ℕ) :
    Poly (fun xs : List Unit => List.replicate (p.eval xs.length) ()) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    have h : Poly (fun xs : List Unit =>
        List.replicate (p.eval xs.length) () ++ List.replicate (q.eval xs.length) ()) := by fun_prop
    simpa only [eval_add, List.replicate_add] using h
  | monomial n c =>
    have hf : Poly (fun xs : List Unit =>
        (List.replicate c ()).flatMap (fun _ => TM2NativePrime.powerSlots n xs)) := by
      fun_prop
    have he : (fun xs : List Unit => (List.replicate c ()).flatMap
        (fun _ => TM2NativePrime.powerSlots n xs)) =
        (fun xs : List Unit => List.replicate ((monomial n c).eval xs.length) ()) := by
      funext xs
      apply unitList_eq
      simp [List.length_flatMap, TM2NativePrime.powerSlots_length, eval_monomial]
    rw [← he]
    exact hf

end Integration9_9.TM2PolynomialBudget

end P2MDyadicModule5

/- Helper module Solutions.RegevBridgeToffoli. -/
section P2MDyadicModule6

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase

open QAlgorithms.Complexity

private theorem phase_composition {N : ℕ} (f g : QState N → QState N)
    (a b : Bits N → ℂ)
    (hf : ∀ φ x, f φ x = a x * φ x) (hg : ∀ φ x, g φ x = b x * φ x)
    (φ : QState N) (x : Bits N) : g (f φ) x = b x * a x * φ x := by
  rw [hg, hf, mul_assoc]

private theorem cnot_conj_phase_map {N : ℕ} (i j : Fin N) (hij : i ≠ j) (ψ : QState N)
    (F : QState N → QState N) (a : Bits N → ℂ)
    (hF : ∀ φ x, F φ x = a x * φ x) :
    cnotState i j hij (F (cnotState i j hij ψ)) =
      fun x => a (Function.update x j (xor (x j) (x i))) * ψ x := by
  funext x
  simp only [cnotState, hF, Function.update_self, Function.update_of_ne hij, Bool.xor_assoc,
    Bool.xor_self, Bool.xor_false, Function.update_idem, Function.update_eq_self]

private theorem apply1_tMat_eq_phase {N : ℕ} (i : Fin N) (ψ : QState N) :
    apply1 tMat i ψ = fun x => (if x i then Complex.exp (Complex.I * Real.pi / 4) else 1) * ψ x := by
  funext x
  simp [apply1, tMat]

private theorem inv_sqrt_two_mul_self :
    ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = 1 / 2 := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

/-- `shiTof_Ph F a`: `F` acts as multiplication by the diagonal phase `a`. -/
private abbrev shiTof_Ph {N : ℕ} (F : QState N → QState N) (a : Bits N → ℂ) : Prop :=
  ∀ (φ : QState N) (x : Bits N), F φ x = a x * φ x

private lemma shiTof_Ph_comp {N : ℕ} {f g : QState N → QState N} {a b : Bits N → ℂ}
    (hf : shiTof_Ph f a) (hg : shiTof_Ph g b) :
    shiTof_Ph (fun ψ => g (f ψ)) (fun x => b x * a x) := by
  intro ψ x
  exact phase_composition f g a b hf hg ψ x

private lemma shiTof_Ph_conj {N : ℕ} {F : QState N → QState N} {a : Bits N → ℂ}
    (i j : Fin N) (hij : i ≠ j) (hF : shiTof_Ph F a) :
    shiTof_Ph (fun ψ => cnotState i j hij (F (cnotState i j hij ψ)))
      (fun x => a (Function.update x j (xor (x j) (x i)))) := by
  intro ψ x
  exact congrFun (cnot_conj_phase_map i j hij ψ F a hF) x

private lemma shiTof_Ph_t {N : ℕ} (i : Fin N) :
    shiTof_Ph (apply1 tMat i)
      (fun x => if x i then Complex.exp (Complex.I * Real.pi / 4) else 1) := by
  intro φ x
  simp only [apply1_tMat_eq_phase]

/-- `T ^ 7` on one wire, as seven `T` gates. -/
private noncomputable def shiTof_T7 {N : ℕ} (i : Fin N) (ψ : QState N) : QState N :=
  apply1 tMat i (apply1 tMat i (apply1 tMat i (apply1 tMat i
    (apply1 tMat i (apply1 tMat i (apply1 tMat i ψ))))))

private lemma shiTof_Ph_T7 {N : ℕ} (i : Fin N) :
    shiTof_Ph (shiTof_T7 i)
      (fun x => if x i then Complex.exp (Complex.I * Real.pi / 4) ^ 7 else 1) := by
  intro φ x
  simp only [shiTof_T7, apply1_tMat_eq_phase]
  cases hx : x i with
  | false => simp [hx]
  | true =>
      simp only [hx, if_true]
      ring

/-- A `T^7` block conjugated by a CNOT: control `i`, target `j`. -/
private noncomputable def shiTof_cB {N : ℕ} (i j : Fin N) (hij : i ≠ j) (ψ : QState N) :
    QState N :=
  cnotState i j hij (shiTof_T7 j (cnotState i j hij ψ))

private lemma shiTof_Ph_cB {N : ℕ} (i j : Fin N) (hij : i ≠ j) :
    shiTof_Ph (shiTof_cB i j hij)
      (fun x => if xor (x j) (x i) then Complex.exp (Complex.I * Real.pi / 4) ^ 7 else 1) := by
  intro φ x
  have h := shiTof_Ph_conj i j hij (shiTof_Ph_T7 j) φ x
  simp only [Function.update_self] at h
  exact h

/-- The three-parity `T` block: `CNOT(p,r) CNOT(q,r) T_r CNOT(q,r) CNOT(p,r)`. -/
private noncomputable def shiTof_cB7 {N : ℕ} (p q r : Fin N) (hpr : p ≠ r) (hqr : q ≠ r)
    (ψ : QState N) : QState N :=
  cnotState p r hpr (cnotState q r hqr (apply1 tMat r
    (cnotState q r hqr (cnotState p r hpr ψ))))

private lemma shiTof_Ph_cB7 {N : ℕ} (p q r : Fin N) (hpr : p ≠ r) (hqr : q ≠ r) :
    shiTof_Ph (shiTof_cB7 p q r hpr hqr)
      (fun x => if xor (xor (x r) (x p)) (x q) then
        Complex.exp (Complex.I * Real.pi / 4) else 1) := by
  intro φ x
  have h := shiTof_Ph_conj p r hpr (shiTof_Ph_conj q r hqr (shiTof_Ph_t r)) φ x
  simp only [Function.update_self, Function.update_of_ne hqr] at h
  exact h

/-- The seven block phases multiply to the CCZ sign. -/
private lemma shiTof_phase_prod (a b c : Bool) :
    (if xor (xor c a) b then Complex.exp (Complex.I * Real.pi / 4) else 1) *
      ((if xor c a then Complex.exp (Complex.I * Real.pi / 4) ^ 7 else 1) *
        ((if xor c b then Complex.exp (Complex.I * Real.pi / 4) ^ 7 else 1) *
          ((if xor b a then Complex.exp (Complex.I * Real.pi / 4) ^ 7 else 1) *
            ((if c then Complex.exp (Complex.I * Real.pi / 4) else 1) *
              ((if b then Complex.exp (Complex.I * Real.pi / 4) else 1) *
                (if a then Complex.exp (Complex.I * Real.pi / 4) else 1))))))
      = if a && b && c then (-1 : ℂ) else 1 := by
  let w : ℂ := Complex.exp (Complex.I * Real.pi / 4)
  have h4 : w ^ 4 = -1 := by
    rw [show w ^ 4 = Complex.exp (4 * (Complex.I * Real.pi / 4)) from
      (Complex.exp_nat_mul _ 4).symm]
    convert Complex.exp_pi_mul_I using 1 <;> congr 1 <;> ring
  have h16 : w ^ 16 = 1 := by
    rw [show 16 = 4 * 4 from rfl, pow_mul, h4]
    norm_num
  change (if xor (xor c a) b then w else 1) *
      ((if xor c a then w ^ 7 else 1) *
        ((if xor c b then w ^ 7 else 1) *
          ((if xor b a then w ^ 7 else 1) *
            ((if c then w else 1) * ((if b then w else 1) * (if a then w else 1)))))) = _
  cases a <;> cases b <;> cases c <;> norm_num <;> ring_nf <;> first | exact h16 | exact h4

/-- The CCZ part of the circuit, as a composition of the seven diagonal blocks. -/
private noncomputable def shiTof_cczOp {N : ℕ} (p q r : Fin N) (hpq : p ≠ q) (hpr : p ≠ r)
    (hqr : q ≠ r) (ψ : QState N) : QState N :=
  shiTof_cB7 p q r hpr hqr (shiTof_cB p r hpr (shiTof_cB q r hqr (shiTof_cB p q hpq
    (apply1 tMat r (apply1 tMat q (apply1 tMat p ψ))))))

private lemma shiTof_Ph_ccz {N : ℕ} (p q r : Fin N) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    shiTof_Ph (shiTof_cczOp p q r hpq hpr hqr)
      (fun x => if x p && x q && x r then (-1 : ℂ) else 1) := by
  have c7 := shiTof_Ph_comp (shiTof_Ph_comp (shiTof_Ph_comp (shiTof_Ph_comp
      (shiTof_Ph_comp (shiTof_Ph_comp (shiTof_Ph_t p) (shiTof_Ph_t q)) (shiTof_Ph_t r))
      (shiTof_Ph_cB p q hpq)) (shiTof_Ph_cB q r hqr)) (shiTof_Ph_cB p r hpr))
      (shiTof_Ph_cB7 p q r hpr hqr)
  intro φ x
  first
    | exact (c7 φ x).trans
        (congrArg (fun z : ℂ => z * φ x) (shiTof_phase_prod (x p) (x q) (x r)))
    | (refine (c7 φ x).trans ?_
       rw [← shiTof_phase_prod (x p) (x q) (x r)])
    | (refine (c7 φ x).trans ?_
       beta_reduce
       rw [shiTof_phase_prod (x p) (x q) (x r)])

private lemma shiTof_hconj {N : ℕ} (p q r : Fin N) (hpr : p ≠ r) (hqr : q ≠ r)
    (F : QState N → QState N)
    (hF : ∀ (φ : QState N) (y : Bits N),
      F φ y = (if y p && y q && y r then (-1 : ℂ) else 1) * φ y)
    (ψ : QState N) :
    apply1 hMat r (F (apply1 hMat r ψ))
      = fun x => ψ (Function.update x r (xor (x r) (x p && x q))) := by
  have hs : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = 1 / 2 :=
    inv_sqrt_two_mul_self
  funext x
  have hup : ∀ b : Bool, F (apply1 hMat r ψ) (Function.update x r b)
      = (if x p && x q && b then (-1 : ℂ) else 1)
        * ∑ c : Bool, hMat b c * ψ (Function.update x r c) := by
    intro b
    have e1 : Function.update x r b p = x p := Function.update_of_ne hpr b x
    have e2 : Function.update x r b q = x q := Function.update_of_ne hqr b x
    have e3 : Function.update x r b r = b := Function.update_self r b x
    have e4 : apply1 hMat r ψ (Function.update x r b)
        = ∑ c : Bool, hMat b c * ψ (Function.update x r c) := by
      simp only [apply1, Function.update_self, Function.update_idem]
    simp only [hF, e1, e2, e3, e4]
  have main : apply1 hMat r (F (apply1 hMat r ψ)) x
      = ∑ b : Bool, hMat (x r) b * F (apply1 hMat r ψ) (Function.update x r b) := rfl
  rw [main]
  -- PHASE 1: split the outer Bool sum, `hMat` still FOLDED.
  simp only [Fintype.sum_bool]
  -- PHASE 2: expand `F` while `hMat` is still folded, so `hup`'s LHS still matches.
  -- Listing `hup` and `hMat` in one `simp only` unfolded `hMat` inside `F (apply1 hMat r ψ)`
  -- first, `hup` then matched nothing and was silently dropped ("unused simp argument"),
  -- leaving `ring` with two opaque `F …` atoms.
  first
    | rw [hup true, hup false]
    | simp only [hup]
  -- PHASE 3: only now unfold the matrix and split the two inner Bool sums.
  simp only [hMat, Matrix.of_apply, Fintype.sum_bool, Complex.ofReal_inv]
  -- PHASE 4: abstract the irrational AFTER all unfolding, so no `(↑√2)⁻¹` survives
  -- alongside `s` and `hs` applies to every quadratic term.
  set s : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ with hsdef
  -- `cases h : e` already substitutes the value, so `simp only [hr, hm]` has nothing to do,
  -- and a no-progress `simp only` is an ERROR in Lean 4 (it killed all four branches).
  cases hr : x r <;> cases hm : (x p && x q) <;> (try simp only [hr, hm]) <;> norm_num <;>
    first
      | linear_combination (2 * ψ (Function.update x r false)) * hs
      | linear_combination (2 * ψ (Function.update x r true)) * hs
      | linear_combination (-2 * ψ (Function.update x r false)) * hs
      | linear_combination (-2 * ψ (Function.update x r true)) * hs

/-- The 37 gates, in time order: `H_r`, then the CCZ sequence at `p,q,r`, then `H_r`. -/
def toffoliGates {N : ℕ} (p q r : Fin N) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    List (Instr N) :=
  [ Instr.h r,
    Instr.t p, Instr.t q, Instr.t r,
    Instr.cnot p q hpq,
    Instr.t q, Instr.t q, Instr.t q, Instr.t q, Instr.t q, Instr.t q, Instr.t q,
    Instr.cnot p q hpq,
    Instr.cnot q r hqr,
    Instr.t r, Instr.t r, Instr.t r, Instr.t r, Instr.t r, Instr.t r, Instr.t r,
    Instr.cnot q r hqr,
    Instr.cnot p r hpr,
    Instr.t r, Instr.t r, Instr.t r, Instr.t r, Instr.t r, Instr.t r, Instr.t r,
    Instr.cnot p r hpr,
    Instr.cnot p r hpr,
    Instr.cnot q r hqr,
    Instr.t r,
    Instr.cnot q r hqr,
    Instr.cnot p r hpr,
    Instr.h r ]

private lemma shiTof_layerOk_map {N : ℕ} (gs : List (Instr N)) :
    ∀ l ∈ gs.map (fun g => [g]), LayerOk l := by
  intro l hl
  simp only [List.mem_map] at hl
  obtain ⟨g, _, hg⟩ := hl
  subst hg
  exact List.pairwise_singleton _ g

private lemma shiTof_run_map {N : ℕ} (gs : List (Instr N)) (ψ : QState N) :
    runLayered (gs.map (fun g => [g])) ψ = gs.foldl (fun st g => Instr.apply g st) ψ := by
  induction gs generalizing ψ with
  | nil => rfl
  | cons g gs ih =>
      have hstep : runLayered ((g :: gs).map (fun z => [z])) ψ
          = runLayered (gs.map (fun z => [z])) (Instr.apply g ψ) := rfl
      rw [hstep, ih, List.foldl_cons]

private lemma shiTof_fold_eq {N : ℕ} (p q r : Fin N) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (ψ : QState N) :
    (toffoliGates p q r hpq hpr hqr).foldl (fun st g => Instr.apply g st) ψ
      = apply1 hMat r (shiTof_cczOp p q r hpq hpr hqr (apply1 hMat r ψ)) := by
  first
    | rfl
    | simp only [toffoliGates, shiTof_cczOp, shiTof_cB, shiTof_cB7, shiTof_T7,
        List.foldl_cons, List.foldl_nil, Instr.apply]

/-- The explicit finite-gate implementation used by the reversible compiler. -/
def toffoliCircuit {N : ℕ} (p q r : Fin N) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) : Layered N :=
  (toffoliGates p q r hpq hpr hqr).map (fun gate => [gate])

theorem toffoliCircuit_apply {N : ℕ} (p q r : Fin N) (hpq : p ≠ q) (hpr : p ≠ r)
    (hqr : q ≠ r) (ψ : QState N) :
    runLayered (toffoliCircuit p q r hpq hpr hqr) ψ =
      fun x => ψ (Function.update x r (xor (x r) (x p && x q))) := by
  rw [toffoliCircuit, shiTof_run_map, shiTof_fold_eq]
  exact shiTof_hconj p q r hpr hqr _ (fun φ y => shiTof_Ph_ccz p q r hpq hpr hqr φ y) ψ

theorem toffoliCircuit_wellFormed {N : ℕ} (p q r : Fin N)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    ∀ layer ∈ toffoliCircuit p q r hpq hpr hqr, LayerOk layer := shiTof_layerOk_map _

end InfoLossLAR.WorstCase

end P2MDyadicModule6

/- Helper module Solutions.RegevBridgeReversibleCircuit. -/
section P2MDyadicModule7

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase

open QAlgorithms.Complexity

open OAI.MetricKMedian.Binary

open OAI.MetricKMedian.Binary.Automatic

open OAI.MetricKMedian.Binary.Automatic.Poly

open QMCNumericRuntime

open Integration9_9.TM2PlatformSerialization

/-- Reversible Boolean instructions, with distinct control and target wires. -/
inductive ReversibleGate (n : ℕ) where
  | flip (i : Fin n)
  | controlled (i j : Fin n) (hij : i ≠ j)
  | toffoli (i j k : Fin n) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)

namespace ReversibleGate

def act {n : ℕ} : ReversibleGate n → Bits n → Bits n
  | .flip i, x => Function.update x i (!x i)
  | .controlled i j _, x => Function.update x j (xor (x j) (x i))
  | .toffoli i j k _ _ _, x => Function.update x k (xor (x k) (x i && x j))

theorem act_involutive {n : ℕ} (g : ReversibleGate n) : Function.Involutive g.act := by
  intro x
  cases g with
  | flip i => simp [act]
  | controlled i j hij =>
    simp [act, Function.update_of_ne hij, Bool.xor_assoc]
  | toffoli i j k hij hik hjk =>
    simp [act, Function.update_of_ne hik, Function.update_of_ne hjk, Bool.xor_assoc]

def equiv {n : ℕ} (g : ReversibleGate n) : Bits n ≃ Bits n := g.act_involutive.toPerm g.act

/-- Compile directly to the fixed Clifford+T alphabet. -/
def compile {n : ℕ} : ReversibleGate n → Layered n
  | .flip i => [[.x i]]
  | .controlled i j hij => [[.cnot i j hij]]
  | .toffoli i j k hij hik hjk => toffoliCircuit i j k hij hik hjk

theorem compile_apply {n : ℕ} (g : ReversibleGate n) (ψ : QState n) :
    runLayered g.compile ψ = fun x => ψ (g.act x) := by
  cases g with
  | flip i =>
    funext x
    simp only [compile, runLayered, runLayer, List.foldl_cons, List.foldl_nil, Instr.apply, apply1]
    cases hx : x i <;> simp [xMat, act, hx]
  | controlled i j hij => rfl
  | toffoli i j k hij hik hjk => exact toffoliCircuit_apply i j k hij hik hjk ψ

theorem compile_wellFormed {n : ℕ} (g : ReversibleGate n) :
    ∀ layer ∈ g.compile, LayerOk layer := by
  cases g with
  | flip i => simp [compile, LayerOk]
  | controlled i j hij => simp [compile, LayerOk]
  | toffoli i j k hij hik hjk => exact toffoliCircuit_wellFormed i j k hij hik hjk

theorem compile_depth {n : ℕ} (g : ReversibleGate n) : depth g.compile ≤ 37 := by
  cases g <;> simp [compile, depth, toffoliCircuit, toffoliGates]

def code {n : ℕ} : ReversibleGate n → Str
  | .flip i => encNat 0 ++ encNat i.val
  | .controlled i j _ => encNat 1 ++ encNat i.val ++ encNat j.val
  | .toffoli i j k _ _ _ => encNat 2 ++ encNat i.val ++ encNat j.val ++ encNat k.val

end ReversibleGate

/-- The forward classical action of a finite reversible program. -/
def reversibleAction {n : ℕ} : List (ReversibleGate n) → Bits n ≃ Bits n
  | [] => Equiv.refl _
  | g :: gs => g.equiv.trans (reversibleAction gs)

def compileReversible {n : ℕ} (gates : List (ReversibleGate n)) : Layered n :=
  gates.flatMap ReversibleGate.compile

private theorem runLayered_append {n : ℕ} (c d : Layered n) (ψ : QState n) :
    runLayered (c ++ d) ψ = runLayered d (runLayered c ψ) := List.foldl_append

/-- Amplitude semantics for every input state, including superpositions and garbage. -/
theorem compileReversible_apply {n : ℕ} (gates : List (ReversibleGate n)) (ψ : QState n) :
    runLayered (compileReversible gates) ψ = fun x => ψ ((reversibleAction gates).symm x) := by
  induction gates generalizing ψ with
  | nil => rfl
  | cons g gs ih =>
    change runLayered (g.compile ++ compileReversible gs) ψ = _
    rw [runLayered_append, ih, g.compile_apply]
    rfl

theorem compileReversible_wellFormed {n : ℕ} (gates : List (ReversibleGate n)) :
    ∀ layer ∈ compileReversible gates, LayerOk layer := by
  intro layer hl
  obtain ⟨g, _, hgl⟩ := List.mem_flatMap.1 hl
  exact g.compile_wellFormed layer hgl

theorem compileReversible_depth {n : ℕ} (gates : List (ReversibleGate n)) :
    depth (compileReversible gates) ≤ 37 * gates.length := by
  induction gates with
  | nil => simp [compileReversible, depth]
  | cons g gs ih =>
    have hg := g.compile_depth
    change (g.compile ++ compileReversible gs).length ≤ _
    simp only [List.length_append, List.length_cons]
    change g.compile.length ≤ 37 at hg
    change (compileReversible gs).length ≤ _ at ih
    omega

/-- A computational basis input is sent to the exact classical output. -/
theorem compileReversible_basis {n : ℕ} (gates : List (ReversibleGate n)) (x : Bits n) :
    runLayered (compileReversible gates) (fun y => if y = x then (1 : ℂ) else 0) =
      fun y => if y = reversibleAction gates x then 1 else 0 := by
  rw [compileReversible_apply]
  funext y
  congr 1
  exact propext (Equiv.symm_apply_eq _)

end InfoLossLAR.WorstCase

end P2MDyadicModule7

/- Helper module Solutions.RegevBridgeReversibleUniform. -/
section P2MDyadicModule8

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase

open QAlgorithms.Complexity

open OAI.MetricKMedian.Binary

open OAI.MetricKMedian.Binary.Automatic

open OAI.MetricKMedian.Binary.Automatic.Poly

open QMCNumericRuntime

open Integration9_9.TM2PlatformSerialization

/-- The explicit Toffoli expansion at the level of unary wire tokens. -/
def toffoliInstructionWords (p q r : Str) : List Str :=
  let h (i : Str) := encNat 0 ++ i
  let t (i : Str) := encNat 2 ++ i
  let c (i j : Str) := encNat 4 ++ i ++ j
  [h r, t p, t q, t r, c p q,
   t q, t q, t q, t q, t q, t q, t q, c p q, c q r,
   t r, t r, t r, t r, t r, t r, t r, c q r, c p r,
   t r, t r, t r, t r, t r, t r, t r, c p r, c p r,
   c q r, t r, c q r, c p r, h r]

@[fun_prop] theorem toffoliInstructionWords_poly :
    Poly (fun x : Str × Str × Str => toffoliInstructionWords x.1 x.2.1 x.2.2) := by
  unfold toffoliInstructionWords
  fun_prop

/-- Read a reversible instruction and emit the literal list of Clifford+T gate codes. -/
def readReversibleInstruction (xs : Str) : Str × List Str :=
  let tag := readUnary xs
  let first := readUnary tag.2
  if inputWidth xs = 0 then
    (first.2, [encNat 3 ++ first.1])
  else
    let second := readUnary first.2
    if inputWidth xs = 1 then
      (second.2, [encNat 4 ++ first.1 ++ second.1])
    else
      let third := readUnary second.2
      (third.2, toffoliInstructionWords first.1 second.1 third.1)

@[fun_prop] theorem readReversibleInstruction_poly : Poly readReversibleInstruction := by
  unfold readReversibleInstruction
  fun_prop

theorem readReversibleInstruction_rest_length (xs : Str) :
    (readReversibleInstruction xs).1.length ≤ xs.length := by
  unfold readReversibleInstruction
  split_ifs
  · exact (readUnary_rest_length _).trans (readUnary_rest_length _)
  · exact (readUnary_rest_length _).trans ((readUnary_rest_length _).trans (readUnary_rest_length _))
  · exact (readUnary_rest_length _).trans ((readUnary_rest_length _).trans
      ((readUnary_rest_length _).trans (readUnary_rest_length _)))

private theorem reversibleUniformUnaryWidth (n : ℕ) (xs : Str) : inputWidth (encNat n ++ xs) = n := by
  simpa only [encNat, List.append_assoc, List.singleton_append] using inputWidth_prefix n xs

theorem readReversibleInstruction_append {n : ℕ} (g : ReversibleGate n) (xs : Str) :
    readReversibleInstruction (g.code ++ xs) = (xs, g.compile.flatten.map encInstr) := by
  cases g <;> simp only [ReversibleGate.code, List.append_assoc, readReversibleInstruction,
    reversibleUniformUnaryWidth, readUnary_append] <;> norm_num <;> rfl

def readReversibleProgram : Str → Str × List (List Str) := readList readReversibleInstruction

@[fun_prop] theorem readReversibleProgram_poly : Poly readReversibleProgram :=
  readList_poly readReversibleInstruction readReversibleInstruction_poly readReversibleInstruction_rest_length

theorem readReversibleProgram_append {n : ℕ} (gates : List (ReversibleGate n)) (xs : Str) :
    readReversibleProgram (encStr (gates.map ReversibleGate.code) ++ xs) =
      (xs, gates.map (fun g => g.compile.flatten.map encInstr)) :=
  readList_append_mapped readReversibleInstruction ReversibleGate.code
    (fun g => g.compile.flatten.map encInstr) readReversibleInstruction_append gates xs

private theorem compiledWords {n : ℕ} (gates : List (ReversibleGate n)) :
    ((gates.map (fun g => g.compile.flatten.map encInstr)).flatten).map (fun word => [word]) =
      (compileReversible gates).map (List.map encInstr) := by
  induction gates with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons, List.flatten_cons, List.map_append, compileReversible,
      List.flatMap_cons] at ih ⊢
    rw [ih]
    congr 1
    cases g <;> rfl

/-- Convert a unary-counted reversible program description, preserving its header. -/
def compileReversibleDescription (xs : Str) : Str :=
  let anc := readUnary xs
  let out := readUnary anc.2
  let pieces := (readReversibleProgram out.2).2
  anc.1 ++ out.1 ++ serializeWords (pieces.flatten.map (fun word => serializeWords [word]))

@[fun_prop] theorem compileReversibleDescription_poly : Poly compileReversibleDescription := by
  unfold compileReversibleDescription
  have hf : Poly (List.flatten : List (List Str) → List Str) :=
    ⟨PolyProgram.listFlatten (encodeList encodeBool) []⟩
  fun_prop

theorem compileReversibleDescription_polyTime : PolyTimeComputable compileReversibleDescription :=
  polyTime_of_poly compileReversibleDescription_poly

/-- A family of ordinary finite reversible Boolean circuits. -/
structure ReversibleFamily where
  anc : ℕ → ℕ
  gates : (n : ℕ) → List (ReversibleGate (n + (anc n + 1)))
  out : (n : ℕ) → Fin (n + (anc n + 1))

def ReversibleFamily.code (F : ReversibleFamily) (n : ℕ) : Str :=
  encNat (F.anc n) ++ encNat (F.out n).val ++ encStr ((F.gates n).map ReversibleGate.code)

def ReversibleFamily.compile (F : ReversibleFamily) : Family where
  anc := F.anc
  circ n := compileReversible (F.gates n)
  out := F.out

def ReversibleFamily.Uniform (F : ReversibleFamily) : Prop :=
  ∃ f : Str → Str, PolyTimeComputable f ∧ ∀ n, f (unary n) = F.code n

def ReversibleFamily.PolyBounded (F : ReversibleFamily) : Prop :=
  ∃ p : Polynomial ℕ, ∀ n, (F.gates n).length ≤ p.eval n ∧ F.anc n ≤ p.eval n

theorem compileReversibleDescription_code (F : ReversibleFamily) (n : ℕ) :
    compileReversibleDescription (F.code n) = encFamilyAt F.compile n := by
  unfold ReversibleFamily.code compileReversibleDescription
  simp only [List.append_assoc, readUnary_append]
  have h := readReversibleProgram_append (F.gates n) []
  simp only [List.append_nil] at h
  rw [h]
  have hh := congrArg (fun xs : List (List Str) => serializeWords (xs.map serializeWords))
    (compiledWords (F.gates n))
  simp only [List.map_map, Function.comp_def] at hh
  rw [hh]
  simp only [serializeWords_eq, encFamilyAt, ReversibleFamily.compile, encCirc, List.append_assoc]
  rfl

/-- The compiler itself is uniform, not just the pointwise gate expansion. -/
theorem ReversibleFamily.compile_uniform (F : ReversibleFamily) (h : F.Uniform) :
    QAlgorithms.Complexity.Uniform F.compile := by
  obtain ⟨f, ⟨hf⟩, hcode⟩ := h
  obtain ⟨hg⟩ := compileReversibleDescription_polyTime
  refine ⟨compileReversibleDescription ∘ f, Integration9_9.TM2Composition.comp hf hg, ?_⟩
  intro n
  rw [Function.comp_apply, hcode, compileReversibleDescription_code]

theorem ReversibleFamily.compile_isQPT (F : ReversibleFamily)
    (hu : F.Uniform) (hp : F.PolyBounded) : IsQPT F.compile := by
  refine ⟨F.compile_uniform hu, ?_, ?_⟩
  · intro n
    exact compileReversible_wellFormed (F.gates n)
  · obtain ⟨p, hp⟩ := hp
    refine ⟨37 * p + p, ?_, ?_⟩
    · intro n
      have h := (compileReversible_depth (F.gates n)).trans (Nat.mul_le_mul_left 37 (hp n).1)
      simpa only [ReversibleFamily.compile, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_ofNat] using h.trans (Nat.le_add_right _ (p.eval n))
    · intro n
      simpa only [ReversibleFamily.compile, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_ofNat] using (hp n).2.trans (Nat.le_add_left (p.eval n) (37 * p.eval n))

end InfoLossLAR.WorstCase

end P2MDyadicModule8

/- Helper module Solutions.RegevBridgeBooleanCircuit. -/
section P2MDyadicModule9

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase

open QAlgorithms.Complexity

/-- Boolean assignment instructions with a destination distinct from each source.
The two sources may coincide. -/
inductive BooleanGate (n : ℕ) where
  | constant (target : Fin n) (value : Bool)
  | copy (source target : Fin n) (h : source ≠ target)
  | negate (source target : Fin n) (h : source ≠ target)
  | xor (first second target : Fin n) (hf : first ≠ target) (hs : second ≠ target)
  | and (first second target : Fin n) (hf : first ≠ target) (hs : second ≠ target)

namespace BooleanGate

def target {n : ℕ} : BooleanGate n → Fin n
  | .constant t _ => t
  | .copy _ t _ => t
  | .negate _ t _ => t
  | .xor _ _ t _ _ => t
  | .and _ _ t _ _ => t

def value {n : ℕ} : BooleanGate n → Bits n → Bool
  | .constant _ b, _ => b
  | .copy s _ _, x => x s
  | .negate s _ _, x => !x s
  | .xor a b _ _ _, x => Bool.xor (x a) (x b)
  | .and a b _ _ _, x => x a && x b

def assign {n : ℕ} (g : BooleanGate n) (x : Bits n) : Bits n :=
  Function.update x g.target (g.value x)

theorem assign_other {n : ℕ} (g : BooleanGate n) (x : Bits n) (i : Fin n)
    (hi : i ≠ g.target) : g.assign x i = x i := Function.update_of_ne hi _ _

/-- The fresh target stores the Boolean value while the input wires are retained. -/
def compile {n : ℕ} : BooleanGate n → List (ReversibleGate n)
  | .constant t b => if b then [.flip t] else []
  | .copy s t h => [.controlled s t h]
  | .negate s t h => [.flip t, .controlled s t h]
  | .xor a b t ha hb => [.controlled a t ha, .controlled b t hb]
  | .and a b t ha hb =>
    if hab : a = b then [.controlled a t ha]
    else [.toffoli a b t hab ha hb]

theorem compile_length {n : ℕ} (g : BooleanGate n) : g.compile.length ≤ 2 := by
  cases g <;> simp only [compile] <;> (try split_ifs) <;> simp

theorem compile_action {n : ℕ} (g : BooleanGate n) (x : Bits n)
    (hz : x g.target = false) : reversibleAction g.compile x = g.assign x := by
  cases g with
  | constant t b =>
    cases b <;> simp_all [compile, reversibleAction, ReversibleGate.equiv, ReversibleGate.act, assign, target, value]
  | copy s t h =>
    simp_all [compile, reversibleAction, ReversibleGate.equiv, ReversibleGate.act, assign, target, value]
  | negate s t h =>
    funext i
    by_cases hi : i = t
    · subst i
      cases hv : x s <;>
        simp_all [compile, reversibleAction, ReversibleGate.equiv, ReversibleGate.act, assign, target, value,
          Function.update_of_ne h]
    · simp_all [compile, reversibleAction, ReversibleGate.equiv, ReversibleGate.act, assign, target, value,
        Function.update_of_ne hi]
  | xor a b t ha hb =>
    simp_all [compile, reversibleAction, ReversibleGate.equiv, ReversibleGate.act, assign, target, value,
      Function.update_of_ne hb]
  | and a b t ha hb =>
    by_cases hab : a = b
    · subst b
      simp_all [compile, reversibleAction, ReversibleGate.equiv, ReversibleGate.act, assign, target, value]
    · simp_all [compile, reversibleAction, ReversibleGate.equiv, ReversibleGate.act, assign, target, value]

end BooleanGate

/-- Every assignment gets a distinct fresh destination. -/
def BooleanFresh {n : ℕ} (gates : List (BooleanGate n)) : Prop :=
  gates.Pairwise (fun a b => a.target ≠ b.target)

def booleanRun {n : ℕ} (gates : List (BooleanGate n)) (x : Bits n) : Bits n :=
  gates.foldl (fun state g => g.assign state) x

def booleanToReversible {n : ℕ} (gates : List (BooleanGate n)) : List (ReversibleGate n) :=
  gates.flatMap BooleanGate.compile

theorem reversibleAction_append {n : ℕ} (a b : List (ReversibleGate n)) :
    reversibleAction (a ++ b) = (reversibleAction a).trans (reversibleAction b) := by
  induction a with
  | nil => rfl
  | cons g a ih =>
    simp only [List.cons_append, reversibleAction, ih]
    rfl

/-- Complete Boolean-program semantics, with all intermediate values retained. -/
theorem booleanToReversible_action {n : ℕ} (gates : List (BooleanGate n))
    (hf : BooleanFresh gates) (x : Bits n)
    (hz : ∀ g ∈ gates, x g.target = false) :
    reversibleAction (booleanToReversible gates) x = booleanRun gates x := by
  induction gates generalizing x with
  | nil => rfl
  | cons g gates ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.1 hf
    have hzero : ∀ h ∈ gates, g.assign x h.target = false := by
      intro h hh
      rw [g.assign_other x h.target (Ne.symm (hhead h hh))]
      exact hz h (by simp [hh])
    change reversibleAction (g.compile ++ booleanToReversible gates) x = _
    rw [reversibleAction_append]
    change reversibleAction (booleanToReversible gates) (reversibleAction g.compile x) = _
    rw [g.compile_action x (hz g (by simp)), ih htail _ hzero]
    rfl

theorem booleanToReversible_length {n : ℕ} (gates : List (BooleanGate n)) :
    (booleanToReversible gates).length ≤ 2 * gates.length := by
  induction gates with
  | nil => simp [booleanToReversible]
  | cons g gates ih =>
    have hg := g.compile_length
    change (g.compile ++ booleanToReversible gates).length ≤ _
    simp only [List.length_append, List.length_cons]
    omega

end InfoLossLAR.WorstCase

end P2MDyadicModule9

/- Helper module Solutions.AdvantageBridgeDisjointCircuit. -/
section P2MDyadicModule10

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase

open QAlgorithms.Complexity

open scoped BigOperators

/-- Consecutive physical registers, retaining their original wire order. -/
def leftRegister {n m : ℕ} (state : Bits (n+m)) : Bits n := fun i => state (Fin.castAdd m i)

def rightRegister {n m : ℕ} (state : Bits (n+m)) : Bits m := fun i => state (Fin.natAdd n i)

end InfoLossLAR.WorstCase

end P2MDyadicModule10

/- Helper module Solutions.AdvantageBridgeCoinPreparation. -/
section P2MDyadicModule11

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase

open QAlgorithms.Complexity

open scoped BigOperators

/-- A literal computational basis vector, including all workspace bits. -/
def computationalBasis {n : ℕ} (input : Bits n) : QState n := fun output => if output=input then 1 else 0

private theorem append_registers_iff {n m : ℕ} (state : Bits (n+m)) (left : Bits n) (right : Bits m) :
    state=Fin.append left right ↔ leftRegister state=left ∧ rightRegister state=right := by
  constructor
  · rintro rfl
    exact ⟨by funext i; simp [leftRegister],by funext i; simp [rightRegister]⟩
  · rintro ⟨hl,hr⟩
    funext index
    refine Fin.addCases ?_ ?_ index
    · intro i
      simpa only [Fin.append_left,leftRegister] using congrArg (fun word => word i) hl
    · intro i
      simpa only [Fin.append_right,rightRegister] using congrArg (fun word => word i) hr

/-- The actual platform input state is exactly the full computational-basis
word consisting of its input followed by the required zero ancillas. -/
theorem basisInput_eq_computationalBasis {n a : ℕ} (input : Bits n) :
    basisInput (a := a) input=computationalBasis (Fin.append input (fun _ => false)) := by
  funext state
  unfold basisInput computationalBasis
  congr 1
  apply propext
  rw [append_registers_iff]
  simp only [funext_iff,leftRegister,rightRegister]

end InfoLossLAR.WorstCase

end P2MDyadicModule11

/- Helper module Solutions.RegevBridgeBooleanUniform. -/
section P2MDyadicModule12

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase

open QAlgorithms.Complexity

open OAI.MetricKMedian.Binary

open OAI.MetricKMedian.Binary.Automatic

open OAI.MetricKMedian.Binary.Automatic.Poly

open QMCNumericRuntime

open Integration9_9.TM2PlatformSerialization

def BooleanGate.code {n : ℕ} : BooleanGate n → Str
  | .constant t b => encNat (if b then 1 else 0) ++ encNat t.val
  | .copy s t _ => encNat 2 ++ encNat s.val ++ encNat t.val
  | .negate s t _ => encNat 3 ++ encNat s.val ++ encNat t.val
  | .xor a b t _ _ => encNat 4 ++ encNat a.val ++ encNat b.val ++ encNat t.val
  | .and a b t _ _ => encNat 5 ++ encNat a.val ++ encNat b.val ++ encNat t.val

def readBooleanInstruction (xs : Str) : Str × List Str :=
  let tag := readUnary xs
  let first := readUnary tag.2
  if inputWidth xs = 0 then (first.2, [])
  else if inputWidth xs = 1 then (first.2, [encNat 0 ++ first.1])
  else
    let second := readUnary first.2
    if inputWidth xs = 2 then (second.2, [encNat 1 ++ first.1 ++ second.1])
    else if inputWidth xs = 3 then
      (second.2, [encNat 0 ++ second.1, encNat 1 ++ first.1 ++ second.1])
    else
      let third := readUnary second.2
      if inputWidth xs = 4 then
        (third.2, [encNat 1 ++ first.1 ++ third.1, encNat 1 ++ second.1 ++ third.1])
      else if inputWidth first.1 = inputWidth second.1 then
        (third.2, [encNat 1 ++ first.1 ++ third.1])
      else (third.2, [encNat 2 ++ first.1 ++ second.1 ++ third.1])

@[fun_prop] theorem readBooleanInstruction_poly : Poly readBooleanInstruction := by
  unfold readBooleanInstruction
  fun_prop

theorem readBooleanInstruction_rest_length (xs : Str) :
    (readBooleanInstruction xs).1.length ≤ xs.length := by
  unfold readBooleanInstruction
  dsimp only
  split_ifs <;>
    first
      | exact (readUnary_rest_length _).trans (readUnary_rest_length _)
      | exact (readUnary_rest_length _).trans ((readUnary_rest_length _).trans (readUnary_rest_length _))
      | exact (readUnary_rest_length _).trans ((readUnary_rest_length _).trans
          ((readUnary_rest_length _).trans (readUnary_rest_length _)))

private theorem unaryWidth_append (n : ℕ) (xs : Str) : inputWidth (encNat n ++ xs) = n := by
  simpa only [encNat, List.append_assoc, List.singleton_append] using inputWidth_prefix n xs

private theorem unaryWidth (n : ℕ) : inputWidth (encNat n) = n := by
  simpa using unaryWidth_append n []

theorem readBooleanInstruction_append {n : ℕ} (g : BooleanGate n) (xs : Str) :
    readBooleanInstruction (g.code ++ xs) = (xs, g.compile.map ReversibleGate.code) := by
  cases g with
  | constant t b =>
    cases b <;> simp only [BooleanGate.code, Bool.false_eq_true, ite_false, ite_true,
      readBooleanInstruction, List.append_assoc, readUnary_append, unaryWidth_append] <;> norm_num <;> rfl
  | copy s t h =>
    simp only [BooleanGate.code, readBooleanInstruction, List.append_assoc, readUnary_append,
      unaryWidth_append] <;> norm_num <;> rfl
  | negate s t h =>
    simp only [BooleanGate.code, readBooleanInstruction, List.append_assoc, readUnary_append,
      unaryWidth_append] <;> norm_num <;> rfl
  | xor a b t ha hb =>
    simp only [BooleanGate.code, readBooleanInstruction, List.append_assoc, readUnary_append,
      unaryWidth_append] <;> norm_num <;> rfl
  | and a b t ha hb =>
    by_cases hab : a = b
    · subst b
      simp [BooleanGate.code, readBooleanInstruction, List.append_assoc, readUnary_append,
        unaryWidth_append, unaryWidth, BooleanGate.compile, ReversibleGate.code]
    · have habv : a.val ≠ b.val := fun h => hab (Fin.ext h)
      simp [BooleanGate.code, readBooleanInstruction, List.append_assoc, readUnary_append,
        unaryWidth_append, unaryWidth, BooleanGate.compile, ReversibleGate.code, hab, habv]

def readBooleanProgram : Str → Str × List (List Str) := readList readBooleanInstruction

@[fun_prop] theorem readBooleanProgram_poly : Poly readBooleanProgram :=
  readList_poly readBooleanInstruction readBooleanInstruction_poly readBooleanInstruction_rest_length

theorem readBooleanProgram_append {n : ℕ} (gates : List (BooleanGate n)) (xs : Str) :
    readBooleanProgram (encStr (gates.map BooleanGate.code) ++ xs) =
      (xs, gates.map (fun g => g.compile.map ReversibleGate.code)) :=
  readList_append_mapped readBooleanInstruction BooleanGate.code
    (fun g => g.compile.map ReversibleGate.code) readBooleanInstruction_append gates xs

def compileBooleanDescription (xs : Str) : Str :=
  let anc := readUnary xs
  let out := readUnary anc.2
  let pieces := (readBooleanProgram out.2).2
  anc.1 ++ out.1 ++ serializeWords pieces.flatten

@[fun_prop] theorem compileBooleanDescription_poly : Poly compileBooleanDescription := by
  unfold compileBooleanDescription
  have hf : Poly (List.flatten : List (List Str) → List Str) :=
    ⟨PolyProgram.listFlatten (encodeList encodeBool) []⟩
  fun_prop

theorem compileBooleanDescription_polyTime : PolyTimeComputable compileBooleanDescription :=
  polyTime_of_poly compileBooleanDescription_poly

structure BooleanFamily where
  anc : ℕ → ℕ
  gates : (n : ℕ) → List (BooleanGate (n + (anc n + 1)))
  out : (n : ℕ) → Fin (n + (anc n + 1))

def BooleanFamily.code (F : BooleanFamily) (n : ℕ) : Str :=
  encNat (F.anc n) ++ encNat (F.out n).val ++ encStr ((F.gates n).map BooleanGate.code)

def BooleanFamily.reversible (F : BooleanFamily) : ReversibleFamily where
  anc := F.anc
  gates n := booleanToReversible (F.gates n)
  out := F.out

def BooleanFamily.Uniform (F : BooleanFamily) : Prop :=
  ∃ f : Str → Str, PolyTimeComputable f ∧ ∀ n, f (unary n) = F.code n

def BooleanFamily.PolyBounded (F : BooleanFamily) : Prop :=
  ∃ p : Polynomial ℕ, ∀ n, (F.gates n).length ≤ p.eval n ∧ F.anc n ≤ p.eval n

theorem compileBooleanDescription_code (F : BooleanFamily) (n : ℕ) :
    compileBooleanDescription (F.code n) = F.reversible.code n := by
  unfold BooleanFamily.code compileBooleanDescription
  simp only [List.append_assoc, readUnary_append]
  have h := readBooleanProgram_append (F.gates n) []
  simp only [List.append_nil] at h
  rw [h, serializeWords_eq]
  have hh : (List.map (fun g => List.map ReversibleGate.code g.compile) (F.gates n)).flatten =
      (booleanToReversible (F.gates n)).map ReversibleGate.code := by
    simp only [booleanToReversible, List.flatMap_def, List.map_flatten, List.map_map, Function.comp_def]
  rw [hh]
  simp only [ReversibleFamily.code, BooleanFamily.reversible, List.append_assoc]

theorem BooleanFamily.reversible_uniform (F : BooleanFamily) (h : F.Uniform) :
    F.reversible.Uniform := by
  obtain ⟨f, ⟨hf⟩, hcode⟩ := h
  obtain ⟨hg⟩ := compileBooleanDescription_polyTime
  refine ⟨compileBooleanDescription ∘ f, Integration9_9.TM2Composition.comp hf hg, ?_⟩
  intro n
  rw [Function.comp_apply, hcode, compileBooleanDescription_code]

theorem BooleanFamily.reversible_polyBounded (F : BooleanFamily) (h : F.PolyBounded) :
    F.reversible.PolyBounded := by
  obtain ⟨p, hp⟩ := h
  refine ⟨2 * p + p, ?_⟩
  intro n
  constructor
  · have hb := (booleanToReversible_length (F.gates n)).trans (Nat.mul_le_mul_left 2 (hp n).1)
    simpa only [BooleanFamily.reversible, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_ofNat] using hb.trans (Nat.le_add_right _ (p.eval n))
  · simpa only [BooleanFamily.reversible, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_ofNat] using (hp n).2.trans (Nat.le_add_left (p.eval n) (2 * p.eval n))

/-- Actual TM2 description generation and actual fixed-gate QPT compilation. -/
theorem BooleanFamily.compile_isQPT (F : BooleanFamily) (hu : F.Uniform) (hp : F.PolyBounded) :
    IsQPT F.reversible.compile :=
  F.reversible.compile_isQPT (F.reversible_uniform hu) (F.reversible_polyBounded hp)

end InfoLossLAR.WorstCase

end P2MDyadicModule12

/- Helper module Solutions.RegevBridgeBooleanProgram. -/
section P2MDyadicModule13

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase

open QAlgorithms.Complexity

/-- A natural-addressed Boolean instruction. The destination is the next fresh wire. -/
inductive BooleanOp where
  | constant (value : Bool)
  | copy (source : ℕ)
  | negate (source : ℕ)
  | xor (first second : ℕ)
  | and (first second : ℕ)
  deriving DecidableEq

namespace BooleanOp

def sources : BooleanOp → List ℕ
  | .constant _ => []
  | .copy a | .negate a => [a]
  | .xor a b | .and a b => [a, b]

def Valid (bound : ℕ) (op : BooleanOp) : Prop := ∀ i ∈ op.sources, i < bound

def eval (op : BooleanOp) (state : ℕ → Bool) : Bool :=
  match op with
  | .constant b => b
  | .copy a => state a
  | .negate a => !state a
  | .xor a b => Bool.xor (state a) (state b)
  | .and a b => state a && state b

def assign (op : BooleanOp) (target : ℕ) (state : ℕ → Bool) : ℕ → Bool :=
  Function.update state target (op.eval state)

/-- Invalid references produce a zero instruction; on valid programs the fallback is unused. -/
def toGate {total : ℕ} (op : BooleanOp) (target : Fin total) : BooleanGate total :=
  match op with
  | .constant b => .constant target b
  | .copy a => if h : a < target.val then
      .copy ⟨a, h.trans target.isLt⟩ target (by intro he; have hv := congrArg Fin.val he; simp only [Fin.val_mk] at hv; omega)
    else .constant target false
  | .negate a => if h : a < target.val then
      .negate ⟨a, h.trans target.isLt⟩ target (by intro he; have hv := congrArg Fin.val he; simp only [Fin.val_mk] at hv; omega)
    else .constant target false
  | .xor a b => if h : a < target.val ∧ b < target.val then
      .xor ⟨a, h.1.trans target.isLt⟩ ⟨b, h.2.trans target.isLt⟩ target
        (by intro he; have hv := congrArg Fin.val he; simp only [Fin.val_mk] at hv; omega)
        (by intro he; have hv := congrArg Fin.val he; simp only [Fin.val_mk] at hv; omega)
    else .constant target false
  | .and a b => if h : a < target.val ∧ b < target.val then
      .and ⟨a, h.1.trans target.isLt⟩ ⟨b, h.2.trans target.isLt⟩ target
        (by intro he; have hv := congrArg Fin.val he; simp only [Fin.val_mk] at hv; omega)
        (by intro he; have hv := congrArg Fin.val he; simp only [Fin.val_mk] at hv; omega)
    else .constant target false

theorem toGate_target {total : ℕ} (op : BooleanOp) (target : Fin total) :
    (op.toGate target).target = target := by
  cases op <;> simp only [toGate] <;> (try split_ifs) <;> rfl

theorem toGate_value {total : ℕ} (op : BooleanOp) (target : Fin total)
    (hv : op.Valid target.val) (s : ℕ → Bool) :
    (op.toGate target).value (fun i => s i.val) = op.eval s := by
  cases op <;> simp_all [Valid, sources, toGate, BooleanGate.value, eval]

theorem toGate_assign {total : ℕ} (op : BooleanOp) (target : Fin total)
    (hv : op.Valid target.val) (s : ℕ → Bool) :
    (op.toGate target).assign (fun i => s i.val) = fun i => op.assign target.val s i.val := by
  funext i
  rw [BooleanGate.assign, toGate_target, toGate_value op target hv]
  by_cases hi : i = target
  · subst i; simp [assign]
  · have hval : i.val ≠ target.val := fun h => hi (Fin.ext h)
    simp [assign, Function.update_of_ne hi, Function.update_of_ne hval]

end BooleanOp

namespace BooleanProgram

def run : ℕ → List BooleanOp → (ℕ → Bool) → (ℕ → Bool)
  | _, [], s => s
  | start, op :: rest, s => run (start + 1) rest (op.assign start s)

def Valid : ℕ → List BooleanOp → Prop
  | _, [] => True
  | start, op :: rest => op.Valid start ∧ Valid (start + 1) rest

/-- Instantiate a fresh-address program on a finite register large enough for its writes. -/
def gates {total : ℕ} (start : ℕ) (ops : List BooleanOp)
    (h : start + ops.length ≤ total) : List (BooleanGate total) :=
  match ops with
  | [] => []
  | op :: rest =>
      op.toGate ⟨start, by simp only [List.length_cons] at h; omega⟩ ::
        gates (start + 1) rest (by simp only [List.length_cons] at h; omega)

@[simp] theorem gates_length {total start : ℕ} (ops : List BooleanOp)
    (h : start + ops.length ≤ total) : (gates start ops h).length = ops.length := by
  induction ops generalizing start with
  | nil => rfl
  | cons op rest ih => simp only [gates, List.length_cons, ih]

theorem target_range {total start : ℕ} (ops : List BooleanOp)
    (h : start + ops.length ≤ total) (g : BooleanGate total) (hg : g ∈ gates start ops h) :
    start ≤ g.target.val ∧ g.target.val < start + ops.length := by
  induction ops generalizing start with
  | nil => simp [gates] at hg
  | cons op rest ih =>
    simp only [gates, List.mem_cons] at hg
    rcases hg with rfl | hg
    · simp only [BooleanOp.toGate_target, List.length_cons]; omega
    · have hh := ih (start := start + 1) _ hg
      simp only [List.length_cons]; omega

theorem fresh {total start : ℕ} (ops : List BooleanOp)
    (h : start + ops.length ≤ total) : BooleanFresh (gates start ops h) := by
  induction ops generalizing start with
  | nil => exact List.Pairwise.nil
  | cons op rest ih =>
    apply List.pairwise_cons.2
    constructor
    · intro g hg heq
      have hh := (target_range rest _ g hg).1
      rw [BooleanOp.toGate_target] at heq
      have hv := congrArg Fin.val heq
      simp only [Fin.val_mk] at hv
      omega
    · exact ih _

theorem run_below (start : ℕ) (ops : List BooleanOp) (s : ℕ → Bool)
    (i : ℕ) (hi : i < start) : run start ops s i = s i := by
  induction ops generalizing start s with
  | nil => rfl
  | cons op rest ih =>
    rw [run, ih (start + 1) (op.assign start s) (by omega)]
    exact Function.update_of_ne (by omega) _ _

theorem run_append (start : ℕ) (a b : List BooleanOp) (s : ℕ → Bool) :
    run start (a ++ b) s = run (start + a.length) b (run start a s) := by
  induction a generalizing start s with
  | nil => simp [run]
  | cons op a ih =>
    simp only [List.cons_append, run, ih, List.length_cons]
    rw [show start + 1 + a.length = start + (a.length + 1) by omega]

theorem valid_append (start : ℕ) (a b : List BooleanOp) :
    Valid start (a ++ b) ↔ Valid start a ∧ Valid (start + a.length) b := by
  induction a generalizing start with
  | nil => simp [Valid]
  | cons op a ih =>
    simp only [List.cons_append, Valid, ih, List.length_cons]
    have he : start + 1 + a.length = start + (a.length + 1) := by omega
    rw [he]; tauto

theorem semantics {total start : ℕ} (ops : List BooleanOp)
    (h : start + ops.length ≤ total) (hv : Valid start ops) (s : ℕ → Bool) :
    booleanRun (gates start ops h) (fun i => s i.val) = fun i => run start ops s i.val := by
  induction ops generalizing start s with
  | nil => rfl
  | cons op rest ih =>
    change booleanRun (gates (start + 1) rest _) ((op.toGate _).assign (fun i => s i.val)) = _
    rw [BooleanOp.toGate_assign op _ hv.1, ih _ hv.2]
    rfl

theorem reversible_semantics {total start : ℕ} (ops : List BooleanOp)
    (h : start + ops.length ≤ total) (hv : Valid start ops) (s : ℕ → Bool)
    (hz : ∀ i, start ≤ i → i < start + ops.length → s i = false) :
    reversibleAction (booleanToReversible (gates start ops h)) (fun i => s i.val) =
      fun i => run start ops s i.val := by
  rw [booleanToReversible_action _ (fresh ops h)]
  · exact semantics ops h hv s
  · intro g hg
    obtain ⟨hl, hu⟩ := target_range ops h g hg
    exact hz _ hl hu

/-- The literal Clifford+T implementation has exactly the fresh-program basis semantics. -/
theorem circuit_basis {total start : ℕ} (ops : List BooleanOp)
    (h : start + ops.length ≤ total) (hv : Valid start ops) (s : ℕ → Bool)
    (hz : ∀ i, start ≤ i → i < start + ops.length → s i = false) :
    runLayered (compileReversible (booleanToReversible (gates start ops h)))
      (fun x => if x = (fun i => s i.val) then (1 : ℂ) else 0) =
        fun x => if x = (fun i => run start ops s i.val) then 1 else 0 := by
  rw [compileReversible_basis, reversible_semantics ops h hv s hz]

end BooleanProgram

end InfoLossLAR.WorstCase

end P2MDyadicModule13

/- Helper module Solutions.RegevBridgeBooleanExpr. -/
section P2MDyadicModule14

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase

/-- Boolean formula syntax used to compile a fixed finite-state transition. -/
inductive BooleanExpr where
  | input (wire : ℕ)
  | constant (value : Bool)
  | negate (arg : BooleanExpr)
  | xor (first second : BooleanExpr)
  | and (first second : BooleanExpr)
  deriving DecidableEq

namespace BooleanExpr

def eval : BooleanExpr → (ℕ → Bool) → Bool
  | .input i, s => s i
  | .constant b, _ => b
  | .negate a, s => !(a.eval s)
  | .xor a b, s => Bool.xor (a.eval s) (b.eval s)
  | .and a b, s => a.eval s && b.eval s

def Valid (bound : ℕ) : BooleanExpr → Prop
  | .input i => i < bound
  | .constant _ => True
  | .negate a => a.Valid bound
  | .xor a b | .and a b => a.Valid bound ∧ b.Valid bound

def size : BooleanExpr → ℕ
  | .input _ => 0
  | .constant _ => 1
  | .negate a => a.size + 1
  | .xor a b | .and a b => a.size + b.size + 1

theorem valid_mono {bound upper : ℕ} (e : BooleanExpr) (h : e.Valid bound)
    (hle : bound ≤ upper) : e.Valid upper := by
  induction e with
  | input i => exact h.trans_le hle
  | constant b => trivial
  | negate a ih => exact ih h
  | xor a b ia ib | and a b ia ib => exact ⟨ia h.1, ib h.2⟩

theorem eval_congr {bound : ℕ} (e : BooleanExpr) (hv : e.Valid bound)
    {s t : ℕ → Bool} (h : ∀ i, i < bound → s i = t i) : e.eval s = e.eval t := by
  induction e with
  | input i => exact h i hv
  | constant b => rfl
  | negate a ih => exact congrArg Bool.not (ih hv)
  | xor a b ia ib => exact congrArg₂ Bool.xor (ia hv.1) (ib hv.2)
  | and a b ia ib => exact congrArg₂ Bool.and (ia hv.1) (ib hv.2)

/-- Postorder compilation retains each intermediate result on a fresh wire. -/
def compile (start : ℕ) : BooleanExpr → List BooleanOp × ℕ
  | .input i => ([], i)
  | .constant b => ([.constant b], start)
  | .negate a =>
      let ca := a.compile start
      (ca.1 ++ [.negate ca.2], start + ca.1.length)
  | .xor a b =>
      let ca := a.compile start
      let cb := b.compile (start + ca.1.length)
      (ca.1 ++ cb.1 ++ [.xor ca.2 cb.2], start + ca.1.length + cb.1.length)
  | .and a b =>
      let ca := a.compile start
      let cb := b.compile (start + ca.1.length)
      (ca.1 ++ cb.1 ++ [.and ca.2 cb.2], start + ca.1.length + cb.1.length)

@[simp] theorem compile_length (e : BooleanExpr) (start : ℕ) :
    (e.compile start).1.length = e.size := by
  induction e generalizing start <;> simp_all [compile, size, Nat.add_assoc]

theorem compile_valid (e : BooleanExpr) (start : ℕ) (hv : e.Valid start) :
    BooleanProgram.Valid start (e.compile start).1 ∧ (e.compile start).2 < start + e.size := by
  induction e generalizing start with
  | input i => exact ⟨trivial, by simpa only [compile, size, Valid, Nat.add_zero] using hv⟩
  | constant b => exact ⟨⟨by simp [BooleanOp.Valid, BooleanOp.sources], trivial⟩, by simp [compile, size]⟩
  | negate a ih =>
    obtain ⟨ha, hout⟩ := ih start hv
    simp only [compile, compile_length, size]
    constructor
    · apply (BooleanProgram.valid_append _ _ _).2
      exact ⟨ha, ⟨by simpa [BooleanOp.Valid, BooleanOp.sources] using hout, trivial⟩⟩
    · omega
  | xor a b ia ib | and a b ia ib =>
    obtain ⟨ha, hoa⟩ := ia start hv.1
    obtain ⟨hb, hob⟩ := ib (start + a.size) (b.valid_mono hv.2 (by omega))
    simp only [compile, compile_length, size]
    constructor
    · apply (BooleanProgram.valid_append _ _ _).2
      constructor
      · exact (BooleanProgram.valid_append _ _ _).2 ⟨ha, by simpa only [compile_length] using hb⟩
      · simp only [List.length_append, compile_length]
        constructor
        · simp only [BooleanOp.Valid, BooleanOp.sources, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp]
          exact ⟨by omega, by omega⟩
        · trivial
    · omega

private theorem singleton_at (start : ℕ) (op : BooleanOp) (s : ℕ → Bool) :
    BooleanProgram.run start [op] s start = op.eval s := by
  simp [BooleanProgram.run, BooleanOp.assign]

private theorem append_singleton_at (start : ℕ) (ops : List BooleanOp) (op : BooleanOp)
    (s : ℕ → Bool) :
    BooleanProgram.run start (ops ++ [op]) s (start + ops.length) =
      op.eval (BooleanProgram.run start ops s) := by
  rw [BooleanProgram.run_append, singleton_at]

theorem compile_eval (e : BooleanExpr) (start : ℕ) (hv : e.Valid start) (s : ℕ → Bool) :
    BooleanProgram.run start (e.compile start).1 s (e.compile start).2 = e.eval s := by
  induction e generalizing start s with
  | input i => rfl
  | constant b => exact singleton_at start (.constant b) s
  | negate a ih =>
    simp only [compile, append_singleton_at, BooleanOp.eval, eval]
    rw [ih start hv]
  | xor a b ia ib | and a b ia ib =>
    have hca := (a.compile_valid start hv.1).2
    have hcb := b.valid_mono hv.2 (Nat.le_add_right start a.size)
    have hb := ib (start + a.size) hcb (BooleanProgram.run start (a.compile start).1 s)
    have heq : b.eval (BooleanProgram.run start (a.compile start).1 s) = b.eval s :=
      b.eval_congr hv.2 (fun i hi => BooleanProgram.run_below _ _ _ i hi)
    rw [heq] at hb
    simp only [compile, compile_length]
    rw [show start + a.size + b.size = start +
      ((a.compile start).1 ++ (b.compile (start + a.size)).1).length by simp; omega,
      append_singleton_at, BooleanProgram.run_append]
    simp only [BooleanOp.eval, compile_length, eval]
    rw [BooleanProgram.run_below _ _ _ _ hca, ia start hv.1, hb]

def or (a b : BooleanExpr) : BooleanExpr := .negate (.and (.negate a) (.negate b))

def select (c a b : BooleanExpr) : BooleanExpr := or (.and c a) (.and (.negate c) b)

@[simp] theorem eval_or (a b : BooleanExpr) (s : ℕ → Bool) :
    (or a b).eval s = (a.eval s || b.eval s) := by
  cases ha : a.eval s <;> cases hb : b.eval s <;> simp [or, eval, ha, hb]

@[simp] theorem eval_select (c a b : BooleanExpr) (s : ℕ → Bool) :
    (select c a b).eval s = if c.eval s then a.eval s else b.eval s := by
  cases hc : c.eval s <;> cases ha : a.eval s <;> cases hb : b.eval s <;>
    simp [select, eval_or, eval, hc, ha, hb]

end BooleanExpr

end InfoLossLAR.WorstCase

end P2MDyadicModule14

/- Helper module Solutions.RegevBridgeBooleanBundle. -/
section P2MDyadicModule15

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase

namespace BooleanExpr

def any : List BooleanExpr → BooleanExpr
  | [] => .constant false
  | a :: rest => or a (any rest)

@[simp] theorem eval_any_true (es : List BooleanExpr) (s : ℕ → Bool) :
    (any es).eval s = true ↔ ∃ e ∈ es, e.eval s = true := by
  induction es with
  | nil => simp [any, eval]
  | cons e es ih => simp [any, eval_or, ih]

theorem valid_any {bound : ℕ} (es : List BooleanExpr)
    (h : ∀ e ∈ es, e.Valid bound) : (any es).Valid bound := by
  induction es with
  | nil => trivial
  | cons e es ih =>
    exact ⟨h e (by simp), ih (fun a ha => h a (by simp [ha]))⟩

/-- A fixed finite truth table is a disjunction of selected one-hot input wires. -/
noncomputable def lookup {α : Type} [Fintype α]
    (table : α → Bool) (inputs : α → BooleanExpr) : BooleanExpr :=
  any ((Finset.univ.toList.filter table).map inputs)

theorem lookup_eval {α : Type} [Fintype α] [DecidableEq α]
    (table : α → Bool) (inputs : α → BooleanExpr) (s : ℕ → Bool) (actual : α)
    (h : ∀ a, (inputs a).eval s = decide (a = actual)) :
    (lookup table inputs).eval s = table actual := by
  rw [Bool.eq_iff_iff]
  simp only [lookup, eval_any_true, List.mem_map, List.mem_filter,
    Finset.mem_toList, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, he⟩
    have heq : a = actual := by simpa only [h, decide_eq_true_eq] using he
    simpa only [heq] using ha
  · intro ha
    exact ⟨inputs actual, ⟨actual, ha, rfl⟩, by simp [h]⟩

theorem valid_lookup {α : Type} [Fintype α] {bound : ℕ}
    (table : α → Bool) (inputs : α → BooleanExpr)
    (h : ∀ a, (inputs a).Valid bound) : (lookup table inputs).Valid bound := by
  apply valid_any
  intro e he
  obtain ⟨a, _, rfl⟩ := List.mem_map.1 he
  exact h a

/-- Compile several outputs without duplicating the expressions from previous simulation steps. -/
def compileMany (start : ℕ) : List BooleanExpr → List BooleanOp × List ℕ
  | [] => ([], [])
  | e :: rest =>
      let first := e.compile start
      let tail := compileMany (start + first.1.length) rest
      (first.1 ++ tail.1, first.2 :: tail.2)

@[simp] theorem compileMany_length (start : ℕ) (es : List BooleanExpr) :
    (compileMany start es).1.length = (es.map size).sum := by
  induction es generalizing start with
  | nil => rfl
  | cons e es ih => simp only [compileMany, List.length_append, compile_length, ih,
      List.map_cons, List.sum_cons]

@[simp] theorem compileMany_outputs_length (start : ℕ) (es : List BooleanExpr) :
    (compileMany start es).2.length = es.length := by
  induction es generalizing start with
  | nil => rfl
  | cons e es ih => simp only [compileMany, List.length_cons, ih]

theorem compileMany_valid (start : ℕ) (es : List BooleanExpr)
    (h : ∀ e ∈ es, e.Valid start) :
    BooleanProgram.Valid start (compileMany start es).1 ∧
      ∀ i ∈ (compileMany start es).2, i < start + (es.map size).sum := by
  induction es generalizing start with
  | nil => exact ⟨trivial, by simp [compileMany]⟩
  | cons e es ih =>
    obtain ⟨he, hout⟩ := e.compile_valid start (h e (by simp))
    obtain ⟨ht, houts⟩ := ih (start + e.size)
      (fun a ha => a.valid_mono (h a (by simp [ha])) (Nat.le_add_right _ _))
    simp only [compileMany, compile_length]
    constructor
    · exact (BooleanProgram.valid_append _ _ _).2 ⟨he, by simpa only [compile_length] using ht⟩
    · intro i hi
      simp only [List.mem_cons] at hi
      simp only [List.map_cons, List.sum_cons]
      rcases hi with rfl | hi
      · omega
      · have hh := houts i hi
        omega

theorem compileMany_eval (start : ℕ) (es : List BooleanExpr)
    (h : ∀ e ∈ es, e.Valid start) (s : ℕ → Bool) :
    (compileMany start es).2.map (BooleanProgram.run start (compileMany start es).1 s) =
      es.map (fun e => e.eval s) := by
  induction es generalizing start s with
  | nil => rfl
  | cons e es ih =>
    have he := h e (by simp)
    have hout := (e.compile_valid start he).2
    have ht := ih (start + e.size)
      (fun a ha => a.valid_mono (h a (by simp [ha])) (Nat.le_add_right _ _))
      (BooleanProgram.run start (e.compile start).1 s)
    have href : es.map (fun a => a.eval (BooleanProgram.run start (e.compile start).1 s)) =
        es.map (fun a => a.eval s) := by
      apply List.map_congr_left
      intro a ha
      exact a.eval_congr (h a (by simp [ha])) (fun i hi => BooleanProgram.run_below _ _ _ i hi)
    rw [href] at ht
    simp only [compileMany, compile_length, List.map_cons, BooleanProgram.run_append]
    rw [BooleanProgram.run_below _ _ _ _ hout, e.compile_eval start he, ht]

/-- A finite multiplexer, with one selected branch, on one-hot control bits. -/
noncomputable def multiplex {α : Type} [Fintype α]
    (control payload : α → BooleanExpr) : BooleanExpr :=
  any (Finset.univ.toList.map (fun a => .and (control a) (payload a)))

theorem multiplex_eval {α : Type} [Fintype α] [DecidableEq α]
    (control payload : α → BooleanExpr) (s : ℕ → Bool) (actual : α)
    (h : ∀ a, (control a).eval s = decide (a = actual)) :
    (multiplex control payload).eval s = (payload actual).eval s := by
  rw [Bool.eq_iff_iff]
  simp only [multiplex, eval_any_true, List.mem_map, Finset.mem_toList,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, he⟩
    simp only [eval, Bool.and_eq_true, h, decide_eq_true_eq] at he
    simpa only [he.1] using he.2
  · intro hp
    exact ⟨.and (control actual) (payload actual), ⟨actual, rfl⟩, by simp [eval, h, hp]⟩

theorem valid_multiplex {α : Type} [Fintype α] {bound : ℕ}
    (control payload : α → BooleanExpr)
    (hc : ∀ a, (control a).Valid bound) (hp : ∀ a, (payload a).Valid bound) :
    (multiplex control payload).Valid bound := by
  apply valid_any
  intro e he
  obtain ⟨a, _, rfl⟩ := List.mem_map.1 he
  exact ⟨hc a, hp a⟩

end BooleanExpr

end InfoLossLAR.WorstCase

end P2MDyadicModule15

/- Helper module Solutions.RegevBridgeBooleanRPN. -/
section P2MDyadicModule16

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean.RPN

open OAI.MetricKMedian.Binary

open OAI.MetricKMedian.Binary.Automatic

abbrev Token := ℕ × ℕ

abbrev Node := ℕ × (ℕ × ℕ)

/-- A unary fresh-address supply, an operand stack, and the emitted instruction list. -/
abbrev State := List Unit × (List ℕ × List Node)

def node : BooleanOp → Node
  | .constant false => (0, 0, 0)
  | .constant true => (1, 0, 0)
  | .copy a => (2, a, 0)
  | .negate a => (3, a, 0)
  | .xor a b => (4, a, b)
  | .and a b => (5, a, b)

def code : BooleanExpr → List Token
  | .input a => [(0, a)]
  | .constant false => [(1, 0)]
  | .constant true => [(2, 0)]
  | .negate a => code a ++ [(3, 0)]
  | .xor a b => code a ++ code b ++ [(4, 0)]
  | .and a b => code a ++ code b ++ [(5, 0)]

def emit (s : State) (instruction : Node) (rest : List ℕ) : State :=
  (s.1 ++ [()], s.1.length :: rest, s.2.2 ++ [instruction])

def step (s : State) (token : Token) : State :=
  if token.1 = 0 then (s.1, token.2 :: s.2.1, s.2.2)
  else if token.1 = 1 then emit s (0, 0, 0) s.2.1
  else if token.1 = 2 then emit s (1, 0, 0) s.2.1
  else if token.1 = 3 then emit s (3, (s.2.1[0]?).getD 0, 0) s.2.1.tail
  else if token.1 = 4 then emit s (4, (s.2.1[1]?).getD 0, (s.2.1[0]?).getD 0) s.2.1.tail.tail
  else emit s (5, (s.2.1[1]?).getD 0, (s.2.1[0]?).getD 0) s.2.1.tail.tail

@[fun_prop] theorem step_poly : Poly (fun x : State × Token => step x.1 x.2) := by
  unfold step emit
  fun_prop

def run (tokens : List Token) (s : State) : State := tokens.foldl step s

@[simp] theorem run_append (first second : List Token) (s : State) :
    run (first ++ second) s = run second (run first s) := List.foldl_append

/-- The literal stack transducer emits exactly the verified postorder Boolean compiler. -/
theorem run_code (e : BooleanExpr) (slots : List Unit) (operands : List ℕ) (output : List Node) :
    run (code e) (slots, operands, output) =
      (slots ++ List.replicate e.size (), (e.compile slots.length).2 :: operands,
        output ++ (e.compile slots.length).1.map node) := by
  induction e generalizing slots operands output with
  | input a => simp [code, run, step, BooleanExpr.compile, BooleanExpr.size]
  | constant b =>
    cases b <;> simp [code, run, step, emit, BooleanExpr.compile, BooleanExpr.size, node]
  | negate a ih =>
    rw [code, run_append, ih]
    simp only [run, List.foldl_cons, List.foldl_nil, step, emit, BooleanExpr.compile,
      BooleanExpr.size, BooleanExpr.compile_length, List.length_append, List.length_replicate]
    simp [node, List.map_append, List.replicate_add, List.append_assoc, -List.replicate_append_replicate]
  | xor a b ia ib | and a b ia ib =>
    rw [code, run_append, run_append, ia, ib]
    simp only [run, List.foldl_cons, List.foldl_nil, step, emit, BooleanExpr.compile,
      BooleanExpr.size, BooleanExpr.compile_length, List.length_append, List.length_replicate]
    simp [node, List.map_append, List.replicate_add, List.append_assoc, -List.replicate_append_replicate, Nat.add_assoc]

end InfoLossLAR.WorstCase.TM2Boolean.RPN

end P2MDyadicModule16

/- Helper module Solutions.RegevBridgeBooleanRPNRun. -/
section P2MDyadicModule17

set_option autoImplicit false

set_option maxHeartbeats 3000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean.RPN

open OAI.MetricKMedian.Binary

open OAI.MetricKMedian.Binary.Automatic

open Polynomial

def NodeBound (N : ℕ) (x : Node) : Prop :=
  x.1.bits.length ≤ N ∧ x.2.1.bits.length ≤ N ∧ x.2.2.bits.length ≤ N

structure Bounded (N : ℕ) (s : State) : Prop where
  slots : s.1.length ≤ N
  operands : s.2.1.length ≤ N
  nodes : s.2.2.length ≤ N
  refs : ∀ x ∈ s.2.1, x.bits.length ≤ N
  code : ∀ x ∈ s.2.2, NodeBound N x

theorem Bounded.mono {N M : ℕ} {s : State} (h : Bounded N s) (hm : N ≤ M) :
    Bounded M s := by
  exact ⟨h.slots.trans hm, h.operands.trans hm, h.nodes.trans hm,
    fun x hx => (h.refs x hx).trans hm,
    fun x hx => ⟨(h.code x hx).1.trans hm, (h.code x hx).2.1.trans hm,
      (h.code x hx).2.2.trans hm⟩⟩

theorem getD_bound (xs : List ℕ) (i N : ℕ) (h : ∀ x ∈ xs, x.bits.length ≤ N) :
    ((xs[i]?).getD 0).bits.length ≤ N := by
  by_cases hi : i < xs.length
  · simp only [List.getElem?_eq_getElem hi, Option.getD_some]
    exact h _ (List.getElem_mem hi)
  · rw [List.getElem?_eq_none (show xs.length ≤ i by omega)]
    simp

theorem emit_bounded {N : ℕ} {s : State} (h : Bounded N s) (x : Node)
    (hx : NodeBound (N+1) x) (rest : List ℕ) (hl : rest.length ≤ N)
    (hr : ∀ a ∈ rest, a.bits.length ≤ N+1) : Bounded (N+1) (emit s x rest) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [emit] using Nat.add_le_add_right h.slots 1
  · simpa [emit] using Nat.add_le_add_right hl 1
  · simpa [emit] using Nat.add_le_add_right h.nodes 1
  · intro a ha
    simp only [emit, List.mem_cons] at ha
    rcases ha with rfl | ha
    · exact (NatBinary.length_le_height (Nat.lt_two_pow_self.le)).trans (Nat.add_le_add_right h.slots 1)
    · exact hr a ha
  · intro a ha
    simp only [emit, List.mem_append, List.mem_singleton] at ha
    rcases ha with ha | rfl
    · exact (h.mono (Nat.le_succ N)).code a ha
    · exact hx

theorem step_bounded {N : ℕ} {s : State} (h : Bounded N s) (hN : 3 ≤ N)
    (token : Token) (ht : token.2.bits.length ≤ N+1) : Bounded (N+1) (step s token) := by
  have hh := h.mono (Nat.le_succ N)
  have h0 := getD_bound s.2.1 0 (N+1) hh.refs
  have h1 := getD_bound s.2.1 1 (N+1) hh.refs
  have tailLen : s.2.1.tail.length ≤ N := by rw [List.length_tail]; exact (Nat.sub_le _ _).trans h.operands
  have tailTailLen : s.2.1.tail.tail.length ≤ N :=
    by rw [List.length_tail]; omega
  have tailRefs : ∀ a ∈ s.2.1.tail, a.bits.length ≤ N+1 :=
    fun a ha => hh.refs a (List.mem_of_mem_tail ha)
  have tailTailRefs : ∀ a ∈ s.2.1.tail.tail, a.bits.length ≤ N+1 :=
    fun a ha => tailRefs a (List.mem_of_mem_tail ha)
  unfold step
  split
  · refine ⟨hh.slots, ?_, hh.nodes, ?_, hh.code⟩
    · simpa using Nat.add_le_add_right h.operands 1
    · intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact ht
      · exact hh.refs x hx
  · split
    · apply emit_bounded h _ _ _ h.operands hh.refs
      norm_num [NodeBound]
    · split
      · apply emit_bounded h _ _ _ h.operands hh.refs
        norm_num [NodeBound]
      · split
        · apply emit_bounded h _ _ _ tailLen tailRefs
          change (3:ℕ).bits.length ≤ N+1 ∧ _ ≤ N+1 ∧ 0 ≤ N+1
          rw [show (3:ℕ).bits.length = 2 by decide]
          exact ⟨by omega, h0, Nat.zero_le _⟩
        · split
          · apply emit_bounded h _ _ _ tailTailLen tailTailRefs
            change (_:ℕ).bits.length ≤ N+1 ∧ _ ≤ N+1 ∧ _ ≤ N+1
            norm_num only [show (4:ℕ).bits.length = 3 by decide, show (5:ℕ).bits.length = 3 by decide]
            exact ⟨by omega, h1, h0⟩
          · apply emit_bounded h _ _ _ tailTailLen tailTailRefs
            change (_:ℕ).bits.length ≤ N+1 ∧ _ ≤ N+1 ∧ _ ≤ N+1
            norm_num only [show (4:ℕ).bits.length = 3 by decide, show (5:ℕ).bits.length = 3 by decide]
            exact ⟨by omega, h1, h0⟩

theorem run_bounded (tokens : List Token) {N : ℕ} {s : State} (h : Bounded N s)
    (hN : 3 ≤ N) (ht : ∀ t ∈ tokens, t.2.bits.length ≤ N) :
    Bounded (N+tokens.length) (run tokens s) := by
  induction tokens generalizing N s with
  | nil => simpa [run] using h
  | cons t ts ih =>
    have hs := step_bounded h hN t ((ht t (by simp)).trans (Nat.le_succ N))
    have hh := ih hs (by omega) (fun u hu => (ht u (by simp [hu])).trans (Nat.le_succ N))
    simpa [run, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh

theorem encodedUnit_length (xs : List Unit) : (enc xs).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change (encodeList (fun _ : Unit => []) (x::xs)).length = _
    rw [EncodedList.cons_length]
    change (encodeList (fun _ : Unit => []) xs).length = xs.length at ih
    simp only [List.length_nil, Nat.mul_zero, Nat.zero_add, List.length_cons]
    omega

theorem bounded_of_encoding (s : State) : Bounded (enc s).length s := by
  have hs := encodedUnit_length s.1
  have ho := EncodedList.length_le Nat.bits s.2.1
  have hn := EncodedList.length_le (enc : Node → List Bool) s.2.2
  have he : (enc s).length = 2*(enc s.1).length+1+2*(enc s.2.1).length+1+(enc s.2.2).length := by
    simp only [enc, Coding.encode, encodePair_length]; omega
  change s.2.1.length ≤ (enc s.2.1).length at ho
  change s.2.2.length ≤ (enc s.2.2).length at hn
  refine ⟨by omega, by omega, by omega, ?_, ?_⟩
  · intro x hx
    have hh := EncodedList.member_length Nat.bits s.2.1 x hx
    change x.bits.length ≤ (enc s.2.1).length at hh
    omega
  · intro x hx
    have hh := EncodedList.member_length (enc : Node → List Bool) s.2.2 x hx
    change (enc x).length ≤ (enc s.2.2).length at hh
    have he' : (enc x).length = 2*x.1.bits.length+1+2*x.2.1.bits.length+1+x.2.2.bits.length := by
      simp only [enc, Coding.encode, encodePair_length]; omega
    exact ⟨by omega, by omega, by omega⟩

theorem encoding_bound {N : ℕ} {s : State} (h : Bounded N s) :
    (enc s).length ≤ 20*(N+1)^2 := by
  have hs := encodedUnit_length s.1
  have ho := EncodedList.length_bound Nat.bits s.2.1 N h.refs
  have hn := EncodedList.length_bound (enc : Node → List Bool) s.2.2 (5*N+2) (by
    intro x hx
    have hb := h.code x hx
    rcases hb with ⟨hb1, hb2, hb3⟩
    change (encodePair Nat.bits (encodePair Nat.bits Nat.bits) x).length ≤ _
    simp only [encodePair_length]
    omega)
  have ho' : (enc s.2.1).length ≤ N*(2*N+1) := ho.trans (Nat.mul_le_mul_right _ h.operands)
  have hn' : (enc s.2.2).length ≤ N*(2*(5*N+2)+1) := hn.trans (Nat.mul_le_mul_right _ h.nodes)
  change (encodePair (enc : List Unit → List Bool) (encodePair enc enc) s).length ≤ _
  simp only [encodePair_length]
  nlinarith [h.slots]

theorem run_partial_bound (tokens : List Token) (s : State) (pre suf : List Token)
    (he : tokens = pre ++ suf) :
    (enc (run pre s)).length ≤ 20*(2*(enc (tokens,s)).length+4)^2 := by
  let L := (enc (tokens,s)).length
  have heL : L = 2*(enc tokens).length+1+(enc s).length := encodePair_length _ _ _
  have hpenc : (enc pre).length ≤ (enc tokens).length := by
    change (encodeList enc pre).length ≤ (encodeList enc tokens).length
    rw [he, EncodedList.append, List.length_append]; omega
  have hplen : pre.length ≤ L := by
    have hh := EncodedList.length_le (enc : Token → List Bool) pre
    change pre.length ≤ (enc pre).length at hh
    omega
  have hs := (bounded_of_encoding s).mono (show (enc s).length ≤ L+3 by omega)
  have ht : ∀ t ∈ pre, t.2.bits.length ≤ L+3 := by
    intro t ht
    have hh := EncodedList.member_length (enc : Token → List Bool) pre t ht
    change (enc t).length ≤ (enc pre).length at hh
    have hte : (enc t).length = 2*t.1.bits.length+1+t.2.bits.length := encodePair_length _ _ _
    omega
  have hb := run_bounded pre hs (by omega) ht
  have hb' := hb.mono (show L+3+pre.length ≤ 2*L+3 by omega)
  have hh := encoding_bound hb'
  simpa [L, Nat.add_assoc] using hh

@[fun_prop] theorem run_poly : Poly (fun x : List Token × State => run x.1 x.2) := by
  apply Poly.of_program
  exact step_poly.program.listFold (0,0) (20*(2*X+4)^2) (by
    intro tokens s pre suf he
    simp only [eval_mul, eval_ofNat, eval_pow, eval_add, eval_X]
    change (enc (run pre s)).length ≤ 20*(2*(enc (tokens,s)).length+4)^2
    exact run_partial_bound tokens s pre suf he)

end InfoLossLAR.WorstCase.TM2Boolean.RPN

end P2MDyadicModule17

/- Helper module Solutions.RegevBridgeBooleanCodePoly. -/
section P2MDyadicModule18

set_option autoImplicit false

set_option maxHeartbeats 3000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean.RPN

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

def CodePoly {α : Type} [Coding α] (f : α → BooleanExpr) : Prop :=
  Poly (fun a => code (f a))

namespace CodePoly

variable {α β : Type} [Coding α] [Coding β]

theorem comp {f : β → BooleanExpr} {g : α → β} (hf : CodePoly f) (hg : Poly g) :
    CodePoly (fun a => f (g a)) := Automatic.Poly.comp (f := fun b => code (f b)) (g := g) hf hg

theorem input {f : α → ℕ} (hf : Poly f) : CodePoly (fun a => .input (f a)) := by
  unfold CodePoly code
  fun_prop

theorem constant (b : Bool) : CodePoly (fun _ : α => .constant b) := by
  unfold CodePoly
  exact Automatic.Poly.const _

theorem negate {f : α → BooleanExpr} (hf : CodePoly f) : CodePoly (fun a => .negate (f a)) := by
  unfold CodePoly at hf ⊢
  change Poly (fun a => code (f a) ++ [(3,0)])
  fun_prop

theorem and {f g : α → BooleanExpr} (hf : CodePoly f) (hg : CodePoly g) :
    CodePoly (fun a => .and (f a) (g a)) := by
  unfold CodePoly at hf hg ⊢
  change Poly (fun a => code (f a) ++ code (g a) ++ [(5,0)])
  fun_prop

theorem or {f g : α → BooleanExpr} (hf : CodePoly f) (hg : CodePoly g) :
    CodePoly (fun a => BooleanExpr.or (f a) (g a)) := by
  exact (hf.negate.and hg.negate).negate

theorem select {f g h : α → BooleanExpr} (hf : CodePoly f) (hg : CodePoly g) (hh : CodePoly h) :
    CodePoly (fun a => BooleanExpr.select (f a) (g a) (h a)) := by
  exact (hf.and hg).or (hf.negate.and hh)

theorem ite {p : α → Bool} {f g : α → BooleanExpr} (hp : Poly p)
    (hf : CodePoly f) (hg : CodePoly g) :
    CodePoly (fun a => if p a then f a else g a) := by
  change Poly (fun a => code (if p a then f a else g a))
  have he : (fun a => code (if p a then f a else g a)) =
      (fun a => if p a then code (f a) else code (g a)) := by funext a; split <;> rfl
  rw [he]
  exact Poly.ite hp hf hg

theorem any {ι : Type} (indices : List ι) (f : ι → α → BooleanExpr)
    (hf : ∀ i ∈ indices, CodePoly (f i)) :
    CodePoly (fun a => BooleanExpr.any (indices.map (fun i => f i a))) := by
  induction indices with
  | nil => exact constant false
  | cons i is ih =>
    exact (hf i (by simp)).or (ih (fun j hj => hf j (by simp [hj])))

theorem lookup {ι : Type} [Fintype ι] (table : ι → Bool) (f : ι → α → BooleanExpr)
    (hf : ∀ i, CodePoly (f i)) :
    CodePoly (fun a => BooleanExpr.lookup table (fun i => f i a)) :=
  any _ f (fun i _ => hf i)

theorem multiplex {ι : Type} [Fintype ι] (f g : ι → α → BooleanExpr)
    (hf : ∀ i, CodePoly (f i)) (hg : ∀ i, CodePoly (g i)) :
    CodePoly (fun a => BooleanExpr.multiplex (fun i => f i a) (fun i => g i a)) :=
  any _ _ (fun i _ => (hf i).and (hg i))

end CodePoly

theorem run_codes (es : List BooleanExpr) (slots : List Unit) (operands : List ℕ) (output : List Node) :
    run (es.flatMap code) (slots, operands, output) =
      (slots ++ List.replicate (es.map BooleanExpr.size).sum (),
        (BooleanExpr.compileMany slots.length es).2.reverse ++ operands,
        output ++ (BooleanExpr.compileMany slots.length es).1.map node) := by
  induction es generalizing slots operands output with
  | nil => simp [run, BooleanExpr.compileMany]
  | cons e es ih =>
    simp only [List.flatMap_cons, run_append, run_code, ih]
    simp only [List.map_cons, List.sum_cons, BooleanExpr.compileMany,
      BooleanExpr.compile_length, List.length_append, List.length_replicate]
    simp [List.map_append, List.replicate_add, List.append_assoc, -List.replicate_append_replicate]

def compileTokens (tokens : List Token) (slots : List Unit) : List Node × List ℕ :=
  let result := run tokens (slots, [], [])
  (result.2.2, result.2.1.reverse)

@[fun_prop] theorem compileTokens_poly :
    Poly (fun x : List Token × List Unit => compileTokens x.1 x.2) := by
  unfold compileTokens
  fun_prop

theorem compileTokens_codes (es : List BooleanExpr) (slots : List Unit) :
    compileTokens (es.flatMap code) slots =
      ((BooleanExpr.compileMany slots.length es).1.map node,
        (BooleanExpr.compileMany slots.length es).2) := by
  simp [compileTokens, run_codes]

end InfoLossLAR.WorstCase.TM2Boolean.RPN

end P2MDyadicModule18

/- Helper module Solutions.RegevBridgeTM2Symbolic. -/
section P2MDyadicModule19

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean

open Turing

variable {K Λ σ : Type} [DecidableEq K] [DecidableEq Λ] [DecidableEq σ] [Fintype σ]

/-- One-hot finite control and fixed-capacity Boolean stacks. -/
structure Symbolic (K Λ σ : Type) (width : ℕ) where
  label : Option Λ → BooleanExpr
  state : σ → BooleanExpr
  stack : K → Fin width → Option Bool → BooleanExpr

abbrev Configuration (K Λ σ : Type) := TM2.Cfg (fun _ : K => Bool) Λ σ

structure Encodes {width : ℕ} (sym : Symbolic K Λ σ width)
    (cfg : Configuration K Λ σ) (bits : ℕ → Bool) : Prop where
  label : ∀ l, (sym.label l).eval bits = decide (l = cfg.l)
  state : ∀ v, (sym.state v).eval bits = decide (v = cfg.var)
  stack : ∀ k i b, (sym.stack k i b).eval bits = decide (b = (cfg.stk k)[i.val]?)

namespace Symbolic

variable {width : ℕ}

noncomputable def load (sym : Symbolic K Λ σ width) (f : σ → σ) : Symbolic K Λ σ width :=
  {sym with state v := BooleanExpr.lookup (fun a => decide (v = f a)) sym.state}

noncomputable def push (sym : Symbolic K Λ σ width) (k : K) (f : σ → Bool) :
    Symbolic K Λ σ width :=
  {sym with stack j i b := if j = k then
    if hz : i.val = 0 then BooleanExpr.lookup (fun a => decide (b = some (f a))) sym.state
    else sym.stack k ⟨i.val - 1, by omega⟩ b
    else sym.stack j i b}

noncomputable def read (sym : Symbolic K Λ σ width) (hw : 0 < width)
    (k : K) (f : σ → Option Bool → σ) : Symbolic K Λ σ width :=
  {sym with
    state v := BooleanExpr.lookup (fun a : σ × Option Bool => decide (v = f a.1 a.2))
      (fun a => .and (sym.state a.1) (sym.stack k ⟨0, hw⟩ a.2))}

def pop (sym : Symbolic K Λ σ width) (k : K) : Symbolic K Λ σ width :=
  {sym with stack j i b := if j = k then
    if h : i.val + 1 < width then sym.stack k ⟨i.val + 1, h⟩ b
    else .constant (decide (b = none))
    else sym.stack j i b}

noncomputable def jump (sym : Symbolic K Λ σ width) (f : σ → Λ) : Symbolic K Λ σ width :=
  {sym with label l := BooleanExpr.lookup (fun a => decide (l = some (f a))) sym.state}

def halt (sym : Symbolic K Λ σ width) : Symbolic K Λ σ width :=
  {sym with label l := .constant (decide (l = none))}

def select (condition : BooleanExpr) (a b : Symbolic K Λ σ width) : Symbolic K Λ σ width where
  label l := BooleanExpr.select condition (a.label l) (b.label l)
  state v := BooleanExpr.select condition (a.state v) (b.state v)
  stack k i x := BooleanExpr.select condition (a.stack k i x) (b.stack k i x)

theorem load_encodes (sym : Symbolic K Λ σ width) (cfg : Configuration K Λ σ)
    (bits : ℕ → Bool) (h : Encodes sym cfg bits) (f : σ → σ) :
    Encodes (sym.load f) {cfg with var := f cfg.var} bits := by
  refine ⟨h.label, ?_, h.stack⟩
  intro v
  exact BooleanExpr.lookup_eval _ _ _ cfg.var h.state

theorem push_encodes (sym : Symbolic K Λ σ width) (cfg : Configuration K Λ σ)
    (bits : ℕ → Bool) (h : Encodes sym cfg bits) (k : K) (f : σ → Bool) :
    Encodes (sym.push k f) {cfg with stk := Function.update cfg.stk k (f cfg.var :: cfg.stk k)} bits := by
  refine ⟨h.label, h.state, ?_⟩
  intro j i b
  by_cases hj : j = k
  · subst j
    simp only [push, Function.update_self, ↓reduceIte]
    by_cases hi : i.val = 0
    · simp only [hi, ↓reduceDIte, List.getElem?_cons_zero]
      exact BooleanExpr.lookup_eval _ _ _ cfg.var h.state
    · simp only [hi, ↓reduceDIte]
      rw [h.stack]
      congr 1
      have he : i.val = (i.val - 1) + 1 := by omega
      conv_rhs => rw [he]
      simp only [List.getElem?_cons_succ]
  · simpa only [push, hj, ↓reduceIte, Function.update_of_ne hj] using h.stack j i b

theorem read_encodes (sym : Symbolic K Λ σ width) (cfg : Configuration K Λ σ)
    (bits : ℕ → Bool) (h : Encodes sym cfg bits) (hw : 0 < width)
    (k : K) (f : σ → Option Bool → σ) :
    Encodes (sym.read hw k f) {cfg with var := f cfg.var (cfg.stk k).head?} bits := by
  refine ⟨h.label, ?_, h.stack⟩
  intro v
  apply BooleanExpr.lookup_eval _ _ _ (cfg.var, (cfg.stk k).head?)
  intro a
  simp only [BooleanExpr.eval, h.state, h.stack]
  simp [Prod.ext_iff, List.head?_eq_getElem?]

theorem pop_encodes (sym : Symbolic K Λ σ width) (cfg : Configuration K Λ σ)
    (bits : ℕ → Bool) (h : Encodes sym cfg bits) (k : K)
    (hsize : (cfg.stk k).length ≤ width) :
    Encodes (sym.pop k) {cfg with stk := Function.update cfg.stk k (cfg.stk k).tail} bits := by
  refine ⟨h.label, h.state, ?_⟩
  intro j i b
  by_cases hj : j = k
  · subst j
    simp only [pop, Function.update_self, ↓reduceIte]
    by_cases hi : i.val + 1 < width
    · simp only [hi, ↓reduceDIte, h.stack]
      congr 1
      simp
    · simp only [hi, ↓reduceDIte, BooleanExpr.eval]
      have he : (cfg.stk k).tail[i.val]? = none :=
        List.getElem?_eq_none (by simp only [List.length_tail]; omega)
      rw [he]
  · simpa only [pop, hj, ↓reduceIte, Function.update_of_ne hj] using h.stack j i b

theorem jump_encodes (sym : Symbolic K Λ σ width) (cfg : Configuration K Λ σ)
    (bits : ℕ → Bool) (h : Encodes sym cfg bits) (f : σ → Λ) :
    Encodes (sym.jump f) {cfg with l := some (f cfg.var)} bits := by
  refine ⟨?_, h.state, h.stack⟩
  intro l
  exact BooleanExpr.lookup_eval _ _ _ cfg.var h.state

theorem halt_encodes (sym : Symbolic K Λ σ width) (cfg : Configuration K Λ σ)
    (bits : ℕ → Bool) (h : Encodes sym cfg bits) :
    Encodes sym.halt {cfg with l := none} bits := ⟨fun _ => rfl, h.state, h.stack⟩

theorem select_encodes (condition : BooleanExpr) (a b : Symbolic K Λ σ width)
    (cfgA cfgB : Configuration K Λ σ) (bits : ℕ → Bool)
    (ha : Encodes a cfgA bits) (hb : Encodes b cfgB bits) :
    Encodes (select condition a b) (if condition.eval bits then cfgA else cfgB) bits := by
  cases hc : condition.eval bits
  · refine ⟨?_, ?_, ?_⟩
    · intro l; simpa only [select, BooleanExpr.eval_select, hc, Bool.false_eq_true, ↓reduceIte] using hb.label l
    · intro v; simpa only [select, BooleanExpr.eval_select, hc, Bool.false_eq_true, ↓reduceIte] using hb.state v
    · intro k i b; simpa only [select, BooleanExpr.eval_select, hc, Bool.false_eq_true, ↓reduceIte] using hb.stack k i b
  · refine ⟨?_, ?_, ?_⟩
    · intro l; simpa only [select, BooleanExpr.eval_select, hc, ↓reduceIte] using ha.label l
    · intro v; simpa only [select, BooleanExpr.eval_select, hc, ↓reduceIte] using ha.state v
    · intro k i b; simpa only [select, BooleanExpr.eval_select, hc, ↓reduceIte] using ha.stack k i b

end Symbolic

end InfoLossLAR.WorstCase.TM2Boolean

end P2MDyadicModule19

/- Helper module Solutions.RegevBridgeTM2Transition. -/
section P2MDyadicModule20

set_option autoImplicit false

set_option maxHeartbeats 2500000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean

open Turing

open Integration9_9.TM2OutputLength

variable {K Λ σ : Type} [DecidableEq K] [Fintype K]
  [DecidableEq Λ] [Fintype Λ] [DecidableEq σ] [Fintype σ]

variable {width : ℕ}

/-- Every finite TM2 statement is translated to explicit Boolean formulas. -/
noncomputable def auxiliary (hw : 0 < width) :
    TM2.Stmt (fun _ : K => Bool) Λ σ → Symbolic K Λ σ width → Symbolic K Λ σ width
  | .push k f q, sym => auxiliary hw q (sym.push k f)
  | .peek k f q, sym => auxiliary hw q (sym.read hw k f)
  | .pop k f q, sym => auxiliary hw q ((sym.read hw k f).pop k)
  | .load f q, sym => auxiliary hw q (sym.load f)
  | .branch f q r, sym =>
      Symbolic.select (BooleanExpr.lookup f sym.state) (auxiliary hw q sym) (auxiliary hw r sym)
  | .goto f, sym => sym.jump f
  | .halt, sym => sym.halt

/-- The stack-size premise is precisely the allocated capacity, including all pushes in this step. -/
theorem auxiliary_encodes (hw : 0 < width) (q : TM2.Stmt (fun _ : K => Bool) Λ σ)
    (sym : Symbolic K Λ σ width) (cfg : Configuration K Λ σ) (bits : ℕ → Bool)
    (h : Encodes sym cfg bits) (hsize : stackSize cfg.stk + pushBound q ≤ width) :
    Encodes (auxiliary hw q sym) (TM2.stepAux q cfg.var cfg.stk) bits := by
  induction q generalizing sym cfg with
  | push k f q ih =>
    have hs : stackSize (Function.update cfg.stk k (f cfg.var :: cfg.stk k)) ≤ stackSize cfg.stk + 1 :=
      stackSize_update_le cfg.stk k _ _ (Nat.le_add_right _ _)
        (by simpa only [List.length_cons] using Nat.succ_le_succ (length_le_stackSize cfg.stk k))
    exact ih (sym.push k f) {cfg with stk := Function.update cfg.stk k (f cfg.var :: cfg.stk k)}
      (sym.push_encodes cfg bits h k f) (by simp only [pushBound] at hsize; dsimp only; omega)
  | peek k f q ih =>
    exact ih (sym.read hw k f) {cfg with var := f cfg.var (cfg.stk k).head?}
      (sym.read_encodes cfg bits h hw k f) hsize
  | pop k f q ih =>
    have hs : stackSize (Function.update cfg.stk k (cfg.stk k).tail) ≤ stackSize cfg.stk :=
      stackSize_update_le cfg.stk k _ _ le_rfl
        (by simp only [List.length_tail]; exact (Nat.sub_le _ _).trans (length_le_stackSize cfg.stk k))
    have hr := sym.read_encodes cfg bits h hw k f
    have hp := (sym.read hw k f).pop_encodes {cfg with var := f cfg.var (cfg.stk k).head?}
      bits hr k ((length_le_stackSize cfg.stk k).trans (by simp only [pushBound] at hsize; omega))
    exact ih ((sym.read hw k f).pop k)
      {cfg with var := f cfg.var (cfg.stk k).head?, stk := Function.update cfg.stk k (cfg.stk k).tail}
      hp (by simp only [pushBound] at hsize; dsimp only; omega)
  | load f q ih =>
    exact ih (sym.load f) {cfg with var := f cfg.var} (sym.load_encodes cfg bits h f) hsize
  | branch f q r iq ir =>
    have hq := iq sym cfg h (by simp only [pushBound] at hsize; have := le_max_left (pushBound q) (pushBound r); omega)
    have hr := ir sym cfg h (by simp only [pushBound] at hsize; have := le_max_right (pushBound q) (pushBound r); omega)
    have he := Symbolic.select_encodes (BooleanExpr.lookup f sym.state)
      (auxiliary hw q sym) (auxiliary hw r sym) _ _ bits hq hr
    rw [BooleanExpr.lookup_eval f sym.state bits cfg.var h.state] at he
    cases hf : f cfg.var <;> simpa only [auxiliary, TM2.stepAux, hf, Bool.cond_false,
      Bool.cond_true, Bool.false_eq_true, ↓reduceIte] using he
  | goto f => exact sym.jump_encodes cfg bits h f
  | halt => exact sym.halt_encodes cfg bits h

noncomputable def multiplex {α : Type} [Fintype α]
    (control : α → BooleanExpr) (choices : α → Symbolic K Λ σ width) : Symbolic K Λ σ width where
  label l := BooleanExpr.multiplex control (fun a => (choices a).label l)
  state v := BooleanExpr.multiplex control (fun a => (choices a).state v)
  stack k i b := BooleanExpr.multiplex control (fun a => (choices a).stack k i b)

theorem multiplex_encodes {α : Type} [Fintype α] [DecidableEq α]
    (control : α → BooleanExpr) (choices : α → Symbolic K Λ σ width)
    (bits : ℕ → Bool) (actual : α) (cfg : Configuration K Λ σ)
    (hc : ∀ a, (control a).eval bits = decide (a = actual))
    (h : Encodes (choices actual) cfg bits) : Encodes (multiplex control choices) cfg bits := by
  constructor
  · intro l
    rw [multiplex, BooleanExpr.multiplex_eval control _ bits actual hc]
    exact h.label l
  · intro v
    rw [multiplex, BooleanExpr.multiplex_eval control _ bits actual hc]
    exact h.state v
  · intro k i b
    rw [multiplex, BooleanExpr.multiplex_eval control _ bits actual hc]
    exact h.stack k i b

/-- A halted configuration stays fixed, allowing a time-bounded circuit to run exactly its budget. -/
def stickyStep (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (cfg : Configuration K Λ σ) : Configuration K Λ σ :=
  cfg.l.elim cfg (fun l => TM2.stepAux (program l) cfg.var cfg.stk)

noncomputable def transition (hw : 0 < width)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) (sym : Symbolic K Λ σ width) :
    Symbolic K Λ σ width :=
  multiplex sym.label (fun l => l.elim sym (fun l => auxiliary hw (program l) sym))

theorem transition_encodes (hw : 0 < width)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (sym : Symbolic K Λ σ width) (cfg : Configuration K Λ σ) (bits : ℕ → Bool)
    (h : Encodes sym cfg bits) (hsize : stackSize cfg.stk + programPushBound program ≤ width) :
    Encodes (transition hw program sym) (stickyStep program cfg) bits := by
  apply multiplex_encodes sym.label _ bits cfg.l _ h.label
  cases hl : cfg.l with
  | none => simpa only [hl, Option.elim_none, stickyStep] using h
  | some l =>
    have hq : pushBound (program l) ≤ programPushBound program :=
      Finset.le_sup (f := fun l => pushBound (program l)) (Finset.mem_univ l)
    simpa only [hl, Option.elim_some, stickyStep] using
      auxiliary_encodes hw (program l) sym cfg bits h (by omega)

end InfoLossLAR.WorstCase.TM2Boolean

end P2MDyadicModule20

/- Helper module Solutions.RegevBridgeBooleanSize. -/
section P2MDyadicModule21

set_option autoImplicit false

set_option maxHeartbeats 1000000

namespace InfoLossLAR.WorstCase.BooleanExpr

@[simp] theorem size_or (a b : BooleanExpr) : (or a b).size = a.size + b.size + 4 := by
  simp only [or, size]; omega

@[simp] theorem size_select (c a b : BooleanExpr) :
    (select c a b).size = 2 * c.size + a.size + b.size + 7 := by
  simp only [select, size_or, size]; omega

theorem valid_select {bound : ℕ} (c a b : BooleanExpr)
    (hc : c.Valid bound) (ha : a.Valid bound) (hb : b.Valid bound) :
    (select c a b).Valid bound := ⟨⟨hc, ha⟩, ⟨hc, hb⟩⟩

theorem size_any_le (es : List BooleanExpr) (bound : ℕ)
    (h : ∀ e ∈ es, e.size ≤ bound) : (any es).size ≤ (bound + 4) * es.length + 1 := by
  induction es with
  | nil => simp [any, size]
  | cons e es ih =>
    have he := h e (by simp)
    have ht := ih (fun a ha => h a (by simp [ha]))
    simp only [any, size_or, List.length_cons]
    nlinarith

theorem size_lookup_le {α : Type} [Fintype α]
    (table : α → Bool) (inputs : α → BooleanExpr) (bound : ℕ)
    (h : ∀ a, (inputs a).size ≤ bound) :
    (lookup table inputs).size ≤ (bound + 4) * Fintype.card α + 1 := by
  have he := size_any_le ((Finset.univ.toList.filter table).map inputs) bound (by
    intro e he
    obtain ⟨a, _, rfl⟩ := List.mem_map.1 he
    exact h a)
  have hl : (Finset.univ.toList.filter table).length ≤ Fintype.card α := by
    simpa only [Finset.length_toList, Finset.card_univ] using
      List.length_filter_le table (Finset.univ.toList : List α)
  simp only [List.length_map] at he
  simpa only [lookup] using he.trans
    (Nat.add_le_add_right (Nat.mul_le_mul_left _ hl) 1)

theorem size_multiplex_le {α : Type} [Fintype α]
    (control payload : α → BooleanExpr) (controlBound payloadBound : ℕ)
    (hc : ∀ a, (control a).size ≤ controlBound)
    (hp : ∀ a, (payload a).size ≤ payloadBound) :
    (multiplex control payload).size ≤
      (controlBound + payloadBound + 5) * Fintype.card α + 1 := by
  have he := size_any_le (Finset.univ.toList.map (fun a => and (control a) (payload a)))
    (controlBound + payloadBound + 1) (by
      intro e he
      obtain ⟨a, _, rfl⟩ := List.mem_map.1 he
      simp only [size]
      have := hc a
      have := hp a
      omega)
  simpa only [multiplex, List.length_map, Finset.length_toList, Finset.card_univ, Nat.add_assoc]
    using he

end InfoLossLAR.WorstCase.BooleanExpr

end P2MDyadicModule21

/- Helper module Solutions.RegevBridgeTM2CompileStep. -/
section P2MDyadicModule22

set_option autoImplicit false

set_option maxHeartbeats 2500000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean

open Turing

variable {K Λ σ : Type} [DecidableEq K] [Fintype K]
  [DecidableEq Λ] [Fintype Λ] [DecidableEq σ] [Fintype σ]

variable {width : ℕ}

namespace Symbolic

structure Valid (bound : ℕ) (sym : Symbolic K Λ σ width) : Prop where
  label : ∀ l, (sym.label l).Valid bound
  state : ∀ v, (sym.state v).Valid bound
  stack : ∀ k i b, (sym.stack k i b).Valid bound

theorem load_valid (sym : Symbolic K Λ σ width) {bound : ℕ} (h : sym.Valid bound) (f : σ → σ) :
    (sym.load f).Valid bound := ⟨h.label, fun _ => BooleanExpr.valid_lookup _ _ h.state, h.stack⟩

theorem push_valid (sym : Symbolic K Λ σ width) {bound : ℕ} (h : sym.Valid bound) (k : K) (f : σ → Bool) :
    (sym.push k f).Valid bound := by
  refine ⟨h.label, h.state, ?_⟩
  intro j i b
  dsimp only [push]
  split_ifs
  · exact BooleanExpr.valid_lookup _ _ h.state
  · exact h.stack _ _ _
  · exact h.stack _ _ _

theorem read_valid (sym : Symbolic K Λ σ width) {bound : ℕ} (h : sym.Valid bound)
    (hw : 0 < width) (k : K) (f : σ → Option Bool → σ) : (sym.read hw k f).Valid bound := by
  refine ⟨h.label, ?_, h.stack⟩
  intro v
  apply BooleanExpr.valid_lookup
  intro a
  exact ⟨h.state a.1, h.stack _ _ _⟩

theorem pop_valid (sym : Symbolic K Λ σ width) {bound : ℕ} (h : sym.Valid bound) (k : K) :
    (sym.pop k).Valid bound := by
  refine ⟨h.label, h.state, ?_⟩
  intro j i b
  dsimp only [pop]
  split_ifs
  · exact h.stack _ _ _
  · trivial
  · exact h.stack _ _ _

theorem jump_valid (sym : Symbolic K Λ σ width) {bound : ℕ} (h : sym.Valid bound) (f : σ → Λ) :
    (sym.jump f).Valid bound := ⟨fun _ => BooleanExpr.valid_lookup _ _ h.state, h.state, h.stack⟩

theorem halt_valid (sym : Symbolic K Λ σ width) {bound : ℕ} (h : sym.Valid bound) :
    sym.halt.Valid bound := ⟨fun _ => trivial, h.state, h.stack⟩

theorem select_valid (condition : BooleanExpr) (a b : Symbolic K Λ σ width) {bound : ℕ}
    (hc : condition.Valid bound) (ha : a.Valid bound) (hb : b.Valid bound) :
    (select condition a b).Valid bound :=
  ⟨fun l => BooleanExpr.valid_select _ _ _ hc (ha.label l) (hb.label l),
    fun v => BooleanExpr.valid_select _ _ _ hc (ha.state v) (hb.state v),
    fun k i b => BooleanExpr.valid_select _ _ _ hc (ha.stack k i b) (hb.stack k i b)⟩

end Symbolic

theorem auxiliary_valid (hw : 0 < width) (q : TM2.Stmt (fun _ : K => Bool) Λ σ)
    (sym : Symbolic K Λ σ width) {bound : ℕ} (h : sym.Valid bound) :
    (auxiliary hw q sym).Valid bound := by
  induction q generalizing sym with
  | push k f q ih => exact ih _ (sym.push_valid h k f)
  | peek k f q ih => exact ih _ (sym.read_valid h hw k f)
  | pop k f q ih => exact ih _ ((sym.read hw k f).pop_valid (sym.read_valid h hw k f) k)
  | load f q ih => exact ih _ (sym.load_valid h f)
  | branch f q r iq ir =>
    exact Symbolic.select_valid _ _ _ (BooleanExpr.valid_lookup f sym.state h.state) (iq _ h) (ir _ h)
  | goto f => exact sym.jump_valid h f
  | halt => exact sym.halt_valid h

theorem transition_valid (hw : 0 < width)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (sym : Symbolic K Λ σ width) {bound : ℕ} (h : sym.Valid bound) :
    (transition hw program sym).Valid bound := by
  have hx : ∀ l : Option Λ, (l.elim sym (fun l => auxiliary hw (program l) sym)).Valid bound := by
    intro l
    cases l with
    | none => exact h
    | some l => exact auxiliary_valid hw (program l) sym h
  constructor
  · intro l
    exact BooleanExpr.valid_multiplex sym.label _ h.label (fun a => (hx a).label l)
  · intro v
    exact BooleanExpr.valid_multiplex sym.label _ h.label (fun a => (hx a).state v)
  · intro k i b
    exact BooleanExpr.valid_multiplex sym.label _ h.label (fun a => (hx a).stack k i b)

/-- Every component of a fixed-capacity machine configuration has an explicit slot. -/
abbrev Slot (K Λ σ : Type) (width : ℕ) := Option Λ ⊕ (σ ⊕ (K × Fin width × Option Bool))

/-- The order varies with capacity only through canonical sum/product indices.
The finite permutations for stack names and control states are fixed once for the machine. -/
noncomputable def slotEquiv (K Λ σ : Type) [Fintype K] [Fintype Λ] [Fintype σ] (width : ℕ) :
    Slot K Λ σ width ≃ Fin (Fintype.card (Slot K Λ σ width)) :=
  let cells := (Equiv.prodCongr (Equiv.refl (Fin width)) (Fintype.equivFin (Option Bool))).trans finProdFinEquiv
  let stacksEq := (Equiv.prodCongr (Fintype.equivFin K) cells).trans finProdFinEquiv
  let tail := (Equiv.sumCongr (Fintype.equivFin σ) stacksEq).trans finSumFinEquiv
  let all := (Equiv.sumCongr (Fintype.equivFin (Option Λ)) tail).trans finSumFinEquiv
  all.trans (finCongr (by simp only [Slot, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]))

namespace Symbolic

def get (sym : Symbolic K Λ σ width) : Slot K Λ σ width → BooleanExpr
  | .inl l => sym.label l
  | .inr (.inl v) => sym.state v
  | .inr (.inr (k, i, b)) => sym.stack k i b

def ofSlots (f : Slot K Λ σ width → BooleanExpr) : Symbolic K Λ σ width where
  label l := f (.inl l)
  state v := f (.inr (.inl v))
  stack k i b := f (.inr (.inr (k, i, b)))

@[simp] theorem get_ofSlots (f : Slot K Λ σ width → BooleanExpr) (i : Slot K Λ σ width) :
    (ofSlots f).get i = f i := by
  rcases i with l | v | ⟨k, i, b⟩ <;> rfl

theorem get_valid (sym : Symbolic K Λ σ width) {bound : ℕ} (h : sym.Valid bound)
    (i : Slot K Λ σ width) : (sym.get i).Valid bound := by
  rcases i with l | v | ⟨k, i, b⟩
  · exact h.label l
  · exact h.state v
  · exact h.stack k i b

noncomputable def formulas (sym : Symbolic K Λ σ width) : List BooleanExpr :=
  List.ofFn (fun i : Fin (Fintype.card (Slot K Λ σ width)) => sym.get ((slotEquiv K Λ σ width).symm i))

@[simp] theorem formulas_length (sym : Symbolic K Λ σ width) :
    sym.formulas.length = Fintype.card (Slot K Λ σ width) := List.length_ofFn

noncomputable def compiled (sym : Symbolic K Λ σ width) (start : ℕ) : List BooleanOp × List ℕ :=
  BooleanExpr.compileMany start sym.formulas

noncomputable def output (sym : Symbolic K Λ σ width) (start : ℕ) (i : Slot K Λ σ width) : ℕ :=
  (sym.compiled start).2[(slotEquiv K Λ σ width i).val]'(by
    simp only [compiled, BooleanExpr.compileMany_outputs_length, formulas_length]
    exact (slotEquiv K Λ σ width i).isLt)

noncomputable def rebound (sym : Symbolic K Λ σ width) (start : ℕ) : Symbolic K Λ σ width :=
  ofSlots (fun i => .input (sym.output start i))

theorem formulas_valid (sym : Symbolic K Λ σ width) {bound : ℕ} (h : sym.Valid bound) :
    ∀ e ∈ sym.formulas, e.Valid bound := by
  intro e he
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 he
  exact sym.get_valid h _

theorem compiled_valid (sym : Symbolic K Λ σ width) (start : ℕ) (h : sym.Valid start) :
    BooleanProgram.Valid start (sym.compiled start).1 :=
  (BooleanExpr.compileMany_valid start sym.formulas (sym.formulas_valid h)).1

theorem output_lt (sym : Symbolic K Λ σ width) (start : ℕ) (h : sym.Valid start)
    (i : Slot K Λ σ width) : sym.output start i < start + (sym.compiled start).1.length := by
  have hb := (BooleanExpr.compileMany_valid start sym.formulas (sym.formulas_valid h)).2
    (sym.output start i) (List.getElem_mem _)
  simpa only [compiled, BooleanExpr.compileMany_length] using hb

theorem rebound_valid (sym : Symbolic K Λ σ width) (start : ℕ) (h : sym.Valid start) :
    (sym.rebound start).Valid (start + (sym.compiled start).1.length) :=
  ⟨fun _ => sym.output_lt start h _, fun _ => sym.output_lt start h _,
    fun _ _ _ => sym.output_lt start h _⟩

/-- Each output reference evaluates to the formula it replaces after fresh compilation. -/
theorem output_eval (sym : Symbolic K Λ σ width) (start : ℕ) (h : sym.Valid start)
    (bits : ℕ → Bool) (i : Slot K Λ σ width) :
    BooleanProgram.run start (sym.compiled start).1 bits (sym.output start i) = (sym.get i).eval bits := by
  have he := BooleanExpr.compileMany_eval start sym.formulas (sym.formulas_valid h) bits
  have hi := congrArg (fun xs : List Bool => xs[(slotEquiv K Λ σ width i).val]?) he
  simp only [List.getElem?_map] at hi
  have ho : (sym.compiled start).2[(slotEquiv K Λ σ width i).val]? = some (sym.output start i) :=
    List.getElem?_eq_getElem _
  change (sym.compiled start).2[(slotEquiv K Λ σ width i).val]?.map
    (BooleanProgram.run start (sym.compiled start).1 bits) = _ at hi
  rw [ho] at hi
  simp only [formulas, List.getElem?_ofFn, dif_pos (slotEquiv K Λ σ width i).isLt,
    Fin.eta, Equiv.symm_apply_apply, Option.map_some, Option.some.injEq] at hi
  exact hi

theorem rebound_encodes (sym : Symbolic K Λ σ width) (start : ℕ) (h : sym.Valid start)
    (cfg : Configuration K Λ σ) (bits : ℕ → Bool) (he : Encodes sym cfg bits) :
    Encodes (sym.rebound start) cfg (BooleanProgram.run start (sym.compiled start).1 bits) := by
  constructor
  · intro l
    rw [rebound, ofSlots, BooleanExpr.eval, output_eval sym start h bits (.inl l)]
    exact he.label l
  · intro v
    rw [rebound, ofSlots, BooleanExpr.eval, output_eval sym start h bits (.inr (.inl v))]
    exact he.state v
  · intro k i b
    rw [rebound, ofSlots, BooleanExpr.eval, output_eval sym start h bits (.inr (.inr (k, i, b)))]
    exact he.stack k i b

end Symbolic

end InfoLossLAR.WorstCase.TM2Boolean

end P2MDyadicModule22

/- Helper module Solutions.RegevBridgeTM2SlotEnumeration. -/
section P2MDyadicModule23

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean

def enumerate {α : Type} {n : ℕ} (e : α ≃ Fin n) : List α := List.ofFn e.symm

theorem enumerate_cast {α : Type} {n m : ℕ} (e : α ≃ Fin n) (h : n=m) :
    enumerate (e.trans (finCongr h)) = enumerate e := by subst m; rfl

theorem enumerate_sum {α β : Type} {m n : ℕ} (e : α ≃ Fin m) (f : β ≃ Fin n) :
    enumerate ((Equiv.sumCongr e f).trans finSumFinEquiv) =
      (enumerate e).map Sum.inl ++ (enumerate f).map Sum.inr := by
  unfold enumerate
  rw [List.ofFn_add]
  simp only [Equiv.symm_trans, Equiv.sumCongr_symm, Equiv.trans_apply,
    finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd,
    Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, List.map_ofFn, Function.comp_def]
  congr 1
  apply congrArg List.ofFn
  funext i
  change Sum.map e.symm f.symm (finSumFinEquiv.symm (Fin.castAdd n i)) = Sum.inl (e.symm i)
  simp

theorem enumerate_prod {α β : Type} {m n : ℕ} (e : α ≃ Fin m) (f : β ≃ Fin n) :
    enumerate ((Equiv.prodCongr e f).trans finProdFinEquiv) =
      (enumerate e).flatMap (fun a => (enumerate f).map (fun b => (a,b))) := by
  unfold enumerate
  rw [List.ofFn_mul]
  rw [List.flatMap_def, List.map_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext i
  dsimp only [Function.comp_apply]
  rw [List.map_ofFn]
  apply congrArg List.ofFn
  funext j
  have hb : j.val+n*i.val < m*n := (finProdFinEquiv (i,j)).isLt
  have hb' : i.val*n+j.val < m*n := by simpa only [Nat.mul_comm, Nat.add_comm] using hb
  have he : (⟨i.val*n+j.val, hb'⟩ : Fin (m*n)) = finProdFinEquiv (i,j) := by
    apply Fin.ext
    change i.val*n+j.val = j.val+n*i.val
    ac_rfl
  rw [he]
  simp

theorem enumerate_refl (n : ℕ) : enumerate (Equiv.refl (Fin n)) = List.finRange n := by
  exact List.ofFn_id n

variable {K Λ σ : Type} [Fintype K] [Fintype Λ] [Fintype σ]

theorem enumerate_slots (width : ℕ) :
    enumerate (slotEquiv K Λ σ width) =
      (enumerate (Fintype.equivFin (Option Λ))).map Sum.inl ++
      (enumerate (Fintype.equivFin σ)).map (fun v => Sum.inr (Sum.inl v)) ++
      (enumerate (Fintype.equivFin K)).flatMap (fun k =>
        (List.finRange width).flatMap (fun i =>
          (enumerate (Fintype.equivFin (Option Bool))).map
            (fun b => Sum.inr (Sum.inr (k,i,b))))) := by
  unfold slotEquiv
  rw [enumerate_cast, enumerate_sum, enumerate_sum]
  simp only [List.map_append, List.map_map, Function.comp_def, List.append_assoc,
    enumerate_prod, enumerate_refl, List.map_flatMap, List.flatMap_map]

theorem Symbolic.formulas_enumerate {width : ℕ} (sym : Symbolic K Λ σ width) :
    sym.formulas = (enumerate (slotEquiv K Λ σ width)).map sym.get := by
  simp only [formulas, enumerate, List.map_ofFn, Function.comp_def]

theorem Symbolic.formulas_slots {width : ℕ} (sym : Symbolic K Λ σ width) :
    sym.formulas =
      (enumerate (Fintype.equivFin (Option Λ))).map sym.label ++
      (enumerate (Fintype.equivFin σ)).map sym.state ++
      (enumerate (Fintype.equivFin K)).flatMap (fun k =>
        (List.finRange width).flatMap (fun i =>
          (enumerate (Fintype.equivFin (Option Bool))).map (fun b => sym.stack k i b))) := by
  rw [formulas_enumerate, enumerate_slots]
  simp only [List.map_append, List.map_map, List.map_flatMap, Function.comp_def, get]

end InfoLossLAR.WorstCase.TM2Boolean

end P2MDyadicModule23

/- Helper module Solutions.RegevBridgeTM2CodeFamily. -/
section P2MDyadicModule24

set_option autoImplicit false

set_option maxHeartbeats 3000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean

open Turing

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open RPN

variable {K Λ σ α : Type} [DecidableEq K] [DecidableEq Λ] [DecidableEq σ] [Fintype σ]

/-- A symbolic configuration family with natural cell indices. Only the bounded
restriction is used semantically; the total family admits a single string algorithm. -/
structure CodeFamily (K Λ σ α : Type) where
  label : Option Λ → α → BooleanExpr
  state : σ → α → BooleanExpr
  stack : K → Option Bool → α × ℕ → BooleanExpr

namespace CodeFamily

def restrict (sym : CodeFamily K Λ σ α) (a : α) (width : ℕ) : Symbolic K Λ σ width where
  label l := sym.label l a
  state v := sym.state v a
  stack k i b := sym.stack k b (a,i.val)

structure IsPoly [Coding α] (sym : CodeFamily K Λ σ α) : Prop where
  label : ∀ l, CodePoly (sym.label l)
  state : ∀ v, CodePoly (sym.state v)
  stack : ∀ k b, CodePoly (sym.stack k b)

noncomputable def load (sym : CodeFamily K Λ σ α) (f : σ → σ) : CodeFamily K Λ σ α :=
  {sym with state v a := BooleanExpr.lookup (fun v' => decide (v = f v')) (fun v' => sym.state v' a)}

noncomputable def push (sym : CodeFamily K Λ σ α) (k : K) (f : σ → Bool) : CodeFamily K Λ σ α :=
  {sym with stack j b x := if j = k then
    if x.2 = 0 then BooleanExpr.lookup (fun v => decide (b = some (f v))) (fun v => sym.state v x.1)
    else sym.stack k b (x.1, x.2-1)
    else sym.stack j b x}

noncomputable def read (sym : CodeFamily K Λ σ α) (k : K) (f : σ → Option Bool → σ) : CodeFamily K Λ σ α :=
  {sym with
    state v a := BooleanExpr.lookup (fun u : σ × Option Bool => decide (v = f u.1 u.2))
      (fun u => .and (sym.state u.1 a) (sym.stack k u.2 (a,0)))}

def pop (sym : CodeFamily K Λ σ α) (width : α → ℕ) (k : K) : CodeFamily K Λ σ α :=
  {sym with stack j b x := if j = k then
    if x.2 + 1 < width x.1 then sym.stack k b (x.1, x.2+1)
    else .constant (decide (b = none))
    else sym.stack j b x}

noncomputable def jump (sym : CodeFamily K Λ σ α) (f : σ → Λ) : CodeFamily K Λ σ α :=
  {sym with label l a := BooleanExpr.lookup (fun v => decide (l = some (f v))) (fun v => sym.state v a)}

def halt (sym : CodeFamily K Λ σ α) : CodeFamily K Λ σ α :=
  {sym with label l _ := .constant (decide (l = none))}

def select (condition : α → BooleanExpr) (a b : CodeFamily K Λ σ α) : CodeFamily K Λ σ α where
  label l x := BooleanExpr.select (condition x) (a.label l x) (b.label l x)
  state v x := BooleanExpr.select (condition x) (a.state v x) (b.state v x)
  stack k v x := BooleanExpr.select (condition x.1) (a.stack k v x) (b.stack k v x)

theorem symbolic_ext {width : ℕ} {x y : Symbolic K Λ σ width}
    (hl : x.label = y.label) (hs : x.state = y.state) (ht : x.stack = y.stack) : x = y := by
  cases x; cases y; cases hl; cases hs; cases ht; rfl

theorem load_at (sym : CodeFamily K Λ σ α) (f : σ → σ) (a : α) (width : ℕ) :
    (sym.load f).restrict a width = (sym.restrict a width).load f := rfl

theorem push_at (sym : CodeFamily K Λ σ α) (k : K) (f : σ → Bool) (a : α) (width : ℕ) :
    (sym.push k f).restrict a width = (sym.restrict a width).push k f := rfl

theorem read_at (sym : CodeFamily K Λ σ α) (k : K) (f : σ → Option Bool → σ)
    (a : α) (width : ℕ) (hw : 0 < width) :
    (sym.read k f).restrict a width = (sym.restrict a width).read hw k f := rfl

theorem pop_at (sym : CodeFamily K Λ σ α) (width : α → ℕ) (k : K) (a : α) :
    (sym.pop width k).restrict a (width a) = (sym.restrict a (width a)).pop k := rfl

theorem select_at (condition : α → BooleanExpr) (x y : CodeFamily K Λ σ α) (a : α) (width : ℕ) :
    (select condition x y).restrict a width = Symbolic.select (condition a) (x.restrict a width) (y.restrict a width) := rfl

variable [Coding α]

theorem load_poly (sym : CodeFamily K Λ σ α) (h : sym.IsPoly) (f : σ → σ) : (sym.load f).IsPoly :=
  ⟨h.label, fun v => CodePoly.lookup _ sym.state h.state, h.stack⟩

theorem push_poly (sym : CodeFamily K Λ σ α) (h : sym.IsPoly) (k : K) (f : σ → Bool) :
    (sym.push k f).IsPoly := by
  refine ⟨h.label, h.state, ?_⟩
  intro j b
  by_cases hj : j = k
  · subst j
    simp only [push, ↓reduceIte]
    have hi : Poly (fun x : α × ℕ => decide (x.2 = 0)) := by fun_prop
    have hf := CodePoly.lookup (fun v => decide (b = some (f v)))
      (fun v (x : α × ℕ) => sym.state v x.1) (fun v => (h.state v).comp (by fun_prop))
    have ht := (h.stack k b).comp (show Poly (fun x : α × ℕ => (x.1,x.2-1)) by fun_prop)
    simpa only [decide_eq_true_eq] using CodePoly.ite hi hf ht
  · simpa only [push, hj, ↓reduceIte] using h.stack j b

theorem read_poly (sym : CodeFamily K Λ σ α) (h : sym.IsPoly) (k : K) (f : σ → Option Bool → σ) :
    (sym.read k f).IsPoly := by
  refine ⟨h.label, ?_, h.stack⟩
  intro v
  change CodePoly (fun a => BooleanExpr.lookup (fun u : σ × Option Bool => decide (v = f u.1 u.2)) (fun u => .and (sym.state u.1 a) (sym.stack k u.2 (a,0))))
  apply CodePoly.lookup
  intro u
  exact (h.state u.1).and ((h.stack k u.2).comp (by fun_prop))

theorem pop_poly (sym : CodeFamily K Λ σ α) (h : sym.IsPoly) (width : α → ℕ)
    (hw : Poly width) (k : K) : (sym.pop width k).IsPoly := by
  refine ⟨h.label, h.state, ?_⟩
  intro j b
  by_cases hj : j = k
  · subst j
    simp only [pop, ↓reduceIte]
    have hi : Poly (fun x : α × ℕ => decide (x.2+1 < width x.1)) := by fun_prop
    have ht := (h.stack k b).comp (show Poly (fun x : α × ℕ => (x.1,x.2+1)) by fun_prop)
    simpa only [decide_eq_true_eq] using CodePoly.ite hi ht (CodePoly.constant (decide (b=none)))
  · simpa only [pop, hj, ↓reduceIte] using h.stack j b

theorem jump_poly (sym : CodeFamily K Λ σ α) (h : sym.IsPoly) (f : σ → Λ) : (sym.jump f).IsPoly :=
  ⟨fun l => CodePoly.lookup _ sym.state h.state, h.state, h.stack⟩

theorem halt_poly (sym : CodeFamily K Λ σ α) (h : sym.IsPoly) : sym.halt.IsPoly :=
  ⟨fun l => CodePoly.constant (decide (l=none)), h.state, h.stack⟩

theorem select_poly (condition : α → BooleanExpr) (a b : CodeFamily K Λ σ α)
    (hc : CodePoly condition) (ha : a.IsPoly) (hb : b.IsPoly) : (select condition a b).IsPoly :=
  ⟨fun l => hc.select (ha.label l) (hb.label l),
    fun v => hc.select (ha.state v) (hb.state v),
    fun k v => (hc.comp (by fun_prop)).select (ha.stack k v) (hb.stack k v)⟩

end CodeFamily

end InfoLossLAR.WorstCase.TM2Boolean

end P2MDyadicModule24

/- Helper module Solutions.RegevBridgeTM2CodeTransition. -/
section P2MDyadicModule25

set_option autoImplicit false

set_option maxHeartbeats 3000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean.CodeFamily

open Turing

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open RPN

variable {K Λ σ α : Type} [DecidableEq K] [Fintype K]
  [DecidableEq Λ] [Fintype Λ] [DecidableEq σ] [Fintype σ]

noncomputable def auxiliaryCode (width : α → ℕ) :
    TM2.Stmt (fun _ : K => Bool) Λ σ → CodeFamily K Λ σ α → CodeFamily K Λ σ α
  | .push k f q, sym => auxiliaryCode width q (sym.push k f)
  | .peek k f q, sym => auxiliaryCode width q (sym.read k f)
  | .pop k f q, sym => auxiliaryCode width q ((sym.read k f).pop width k)
  | .load f q, sym => auxiliaryCode width q (sym.load f)
  | .branch f q r, sym =>
      select (fun a => BooleanExpr.lookup f (fun v => sym.state v a))
        (auxiliaryCode width q sym) (auxiliaryCode width r sym)
  | .goto f, sym => sym.jump f
  | .halt, sym => sym.halt

theorem auxiliaryCode_restrict (width : α → ℕ) (a : α) (hw : 0 < width a)
    (q : TM2.Stmt (fun _ : K => Bool) Λ σ) (sym : CodeFamily K Λ σ α) :
    (auxiliaryCode width q sym).restrict a (width a) =
      auxiliary hw q (sym.restrict a (width a)) := by
  induction q generalizing sym with
  | push k f q ih => simp only [auxiliaryCode, auxiliary, ih, push_at]
  | peek k f q ih => simp only [auxiliaryCode, auxiliary, ih, read_at _ _ _ _ _ hw]
  | pop k f q ih => simp only [auxiliaryCode, auxiliary, ih, pop_at, read_at _ _ _ _ _ hw]
  | load f q ih => simp only [auxiliaryCode, auxiliary, ih, load_at]
  | branch f q r iq ir =>
    simp only [auxiliaryCode, auxiliary, select_at, iq, ir]
    rfl
  | goto f => rfl
  | halt => rfl

noncomputable def multiplexCode {ι : Type} [Fintype ι]
    (control : ι → α → BooleanExpr) (choices : ι → CodeFamily K Λ σ α) : CodeFamily K Λ σ α where
  label l a := BooleanExpr.multiplex (fun i => control i a) (fun i => (choices i).label l a)
  state v a := BooleanExpr.multiplex (fun i => control i a) (fun i => (choices i).state v a)
  stack k b a := BooleanExpr.multiplex (fun i => control i a.1) (fun i => (choices i).stack k b a)

theorem multiplexCode_restrict {ι : Type} [Fintype ι]
    (control : ι → α → BooleanExpr) (choices : ι → CodeFamily K Λ σ α) (a : α) (width : ℕ) :
    (multiplexCode control choices).restrict a width =
      multiplex (fun i => control i a) (fun i => (choices i).restrict a width) := rfl

noncomputable def transitionCode (width : α → ℕ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) (sym : CodeFamily K Λ σ α) : CodeFamily K Λ σ α :=
  multiplexCode sym.label (fun l => l.elim sym (fun l => auxiliaryCode width (program l) sym))

theorem transitionCode_restrict (width : α → ℕ) (a : α) (hw : 0 < width a)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) (sym : CodeFamily K Λ σ α) :
    (transitionCode width program sym).restrict a (width a) =
      transition hw program (sym.restrict a (width a)) := by
  rw [transitionCode, multiplexCode_restrict]
  unfold transition
  congr 1
  funext l
  cases l with
  | none => rfl
  | some l => exact auxiliaryCode_restrict width a hw (program l) sym

variable [Coding α]

theorem auxiliaryCode_poly (width : α → ℕ) (hw : Poly width)
    (q : TM2.Stmt (fun _ : K => Bool) Λ σ) (sym : CodeFamily K Λ σ α) (h : sym.IsPoly) :
    (auxiliaryCode width q sym).IsPoly := by
  induction q generalizing sym with
  | push k f q ih => exact ih _ (sym.push_poly h k f)
  | peek k f q ih => exact ih _ (sym.read_poly h k f)
  | pop k f q ih => exact ih _ ((sym.read k f).pop_poly (sym.read_poly h k f) width hw k)
  | load f q ih => exact ih _ (sym.load_poly h f)
  | branch f q r iq ir =>
    exact select_poly _ _ _ (CodePoly.lookup f sym.state h.state) (iq _ h) (ir _ h)
  | goto f => exact sym.jump_poly h f
  | halt => exact sym.halt_poly h

theorem multiplexCode_poly {ι : Type} [Fintype ι]
    (control : ι → α → BooleanExpr) (choices : ι → CodeFamily K Λ σ α)
    (hc : ∀ i, CodePoly (control i)) (hp : ∀ i, (choices i).IsPoly) :
    (multiplexCode control choices).IsPoly :=
  ⟨fun l => CodePoly.multiplex _ _ hc (fun i => (hp i).label l),
    fun v => CodePoly.multiplex _ _ hc (fun i => (hp i).state v),
    fun k b => CodePoly.multiplex _ _ (fun i => (hc i).comp (by fun_prop)) (fun i => (hp i).stack k b)⟩

theorem transitionCode_poly (width : α → ℕ) (hw : Poly width)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) (sym : CodeFamily K Λ σ α) (h : sym.IsPoly) :
    (transitionCode width program sym).IsPoly := by
  apply multiplexCode_poly _ _ h.label
  intro l
  cases l with
  | none => exact h
  | some l => exact auxiliaryCode_poly width hw (program l) sym h

end InfoLossLAR.WorstCase.TM2Boolean.CodeFamily

end P2MDyadicModule25

/- Helper module Solutions.RegevBridgeTM2CodeEnumeration. -/
section P2MDyadicModule26

set_option autoImplicit false

set_option maxHeartbeats 3000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open RPN

theorem fixed_flatMap_poly {α β ι : Type} [Coding α] [Coding β] [Inhabited β]
    (indices : List ι) (f : ι → α → List β) (hf : ∀ i ∈ indices, Poly (f i)) :
    Poly (fun a => indices.flatMap (fun i => f i a)) := by
  induction indices with
  | nil => exact Automatic.Poly.const []
  | cons i is ih =>
    have hi := hf i (by simp)
    have ht := ih (fun j hj => hf j (by simp [hj]))
    change Poly (fun a => f i a ++ is.flatMap (fun j => f j a))
    fun_prop

theorem finRange_values (n : ℕ) : (List.finRange n).map Fin.val = List.range n := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

namespace CodeFamily

variable {K Λ σ α : Type} [Fintype K] [Fintype Λ] [Fintype σ]

noncomputable def codes (sym : CodeFamily K Λ σ α) (width : α → List Unit) (a : α) : List Token :=
  (enumerate (Fintype.equivFin (Option Λ))).flatMap (fun l => code (sym.label l a)) ++
  (enumerate (Fintype.equivFin σ)).flatMap (fun v => code (sym.state v a)) ++
  (enumerate (Fintype.equivFin K)).flatMap (fun k =>
    (List.range (width a).length).flatMap (fun i =>
      (enumerate (Fintype.equivFin (Option Bool))).flatMap (fun b => code (sym.stack k b (a,i)))))

theorem codes_eq (sym : CodeFamily K Λ σ α) (width : α → List Unit) (a : α) :
    sym.codes width a = (sym.restrict a (width a).length).formulas.flatMap code := by
  rw [Symbolic.formulas_slots]
  simp only [codes, List.flatMap_append, List.flatMap_map, List.flatMap_assoc, restrict]
  rw [← finRange_values (width a).length]
  simp only [List.flatMap_map]

theorem codes_poly [Coding α] (sym : CodeFamily K Λ σ α) (h : sym.IsPoly)
    (width : α → List Unit) (hw : Poly width) : Poly (sym.codes width) := by
  have hlabel := fixed_flatMap_poly (enumerate (Fintype.equivFin (Option Λ)))
    (fun l a => code (sym.label l a)) (fun l _ => h.label l)
  have hstate := fixed_flatMap_poly (enumerate (Fintype.equivFin σ))
    (fun v a => code (sym.state v a)) (fun v _ => h.state v)
  have hstack : ∀ k, Poly (fun a : α =>
      (List.range (width a).length).flatMap (fun i =>
        (enumerate (Fintype.equivFin (Option Bool))).flatMap (fun b => code (sym.stack k b (a,i))))) := by
    intro k
    have hcell := fixed_flatMap_poly (enumerate (Fintype.equivFin (Option Bool)))
      (fun b (x : α × ℕ) => code (sym.stack k b x)) (fun b _ => h.stack k b)
    apply Automatic.Poly.list_flatMap hcell
    exact Automatic.Poly.comp (f := fun xs : List Unit => List.range xs.length)
      (g := width) Automatic.Poly.list_indices hw
  have hstackAll := fixed_flatMap_poly (enumerate (Fintype.equivFin K)) _ (fun k _ => hstack k)
  unfold codes
  fun_prop

noncomputable def compile (sym : CodeFamily K Λ σ α) (width : α → List Unit)
    (slots : α → List Unit) (a : α) : List Node × List ℕ := compileTokens (sym.codes width a) (slots a)

theorem compile_poly [Coding α] (sym : CodeFamily K Λ σ α) (h : sym.IsPoly)
    (width slots : α → List Unit) (hw : Poly width) (hs : Poly slots) : Poly (sym.compile width slots) := by
  have hc := sym.codes_poly h width hw
  unfold compile
  fun_prop

theorem compile_eq (sym : CodeFamily K Λ σ α) (width slots : α → List Unit) (a : α) :
    sym.compile width slots a =
      (((sym.restrict a (width a).length).compiled (slots a).length).1.map node,
        ((sym.restrict a (width a).length).compiled (slots a).length).2) := by
  rw [compile, codes_eq, compileTokens_codes]
  rfl

end CodeFamily

end InfoLossLAR.WorstCase.TM2Boolean

end P2MDyadicModule26

/- Helper module Solutions.RegevBridgeTM2BoundedRun. -/
section P2MDyadicModule27

set_option autoImplicit false

set_option maxHeartbeats 2500000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean

open Turing StateTransition

open Integration9_9.TM2OutputLength

variable {K Λ σ : Type} [DecidableEq K] [Fintype K]
  [DecidableEq Λ] [Fintype Λ] [DecidableEq σ] [Fintype σ]

variable {width : ℕ}

noncomputable def compileRun (hw : 0 < width)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) :
    ℕ → ℕ → Symbolic K Λ σ width → List BooleanOp × Symbolic K Λ σ width
  | 0, _, sym => ([], sym)
  | ticks + 1, start, sym =>
      let formulas := transition hw program sym
      let first := formulas.compiled start
      let rest := compileRun hw program ticks (start + first.1.length) (formulas.rebound start)
      (first.1 ++ rest.1, rest.2)

theorem compileRun_valid (hw : 0 < width)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) (ticks start : ℕ)
    (sym : Symbolic K Λ σ width) (h : sym.Valid start) :
    BooleanProgram.Valid start (compileRun hw program ticks start sym).1 ∧
      (compileRun hw program ticks start sym).2.Valid
        (start + (compileRun hw program ticks start sym).1.length) := by
  induction ticks generalizing start sym with
  | zero => exact ⟨trivial, by simpa only [compileRun, List.length_nil, Nat.add_zero] using h⟩
  | succ ticks ih =>
    have ht := transition_valid hw program sym h
    have hf := (transition hw program sym).compiled_valid start ht
    have hr := (transition hw program sym).rebound_valid start ht
    obtain ⟨hc, hlast⟩ := ih _ _ hr
    constructor
    · exact (BooleanProgram.valid_append _ _ _).2 ⟨hf, hc⟩
    · simpa only [compileRun, List.length_append, Nat.add_assoc] using hlast

theorem stickyStep_size (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (cfg : Configuration K Λ σ) :
    stackSize (stickyStep program cfg).stk ≤ stackSize cfg.stk + programPushBound program := by
  cases hl : cfg.l with
  | none => simpa only [stickyStep, hl, Option.elim_none] using Nat.le_add_right (stackSize cfg.stk) _
  | some l =>
    have hc := stepAux_stackSize_le (program l) cfg.var cfg.stk
    have hb : pushBound (program l) ≤ programPushBound program :=
      Finset.le_sup (f := fun l => pushBound (program l)) (Finset.mem_univ l)
    simpa only [stickyStep, hl, Option.elim_some] using hc.trans (Nat.add_le_add_left hb _)

/-- Full bounded execution: each step is compiled and its formula outputs are rebound to fresh wires. -/
theorem compileRun_encodes (hw : 0 < width)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) (ticks start : ℕ)
    (sym : Symbolic K Λ σ width) (cfg : Configuration K Λ σ) (bits : ℕ → Bool)
    (hv : sym.Valid start) (he : Encodes sym cfg bits)
    (hsize : stackSize cfg.stk + programPushBound program * ticks ≤ width) :
    Encodes (compileRun hw program ticks start sym).2 ((stickyStep program)^[ticks] cfg)
      (BooleanProgram.run start (compileRun hw program ticks start sym).1 bits) := by
  induction ticks generalizing start sym cfg bits with
  | zero => exact he
  | succ ticks ih =>
    have ht := transition_valid hw program sym hv
    have hcap : stackSize cfg.stk + programPushBound program ≤ width := by nlinarith
    have hs := transition_encodes hw program sym cfg bits he hcap
    have hf := (transition hw program sym).rebound_encodes start ht _ bits hs
    have hv' := (transition hw program sym).rebound_valid start ht
    have hg := stickyStep_size program cfg
    have hremaining : stackSize (stickyStep program cfg).stk + programPushBound program * ticks ≤ width := by
      nlinarith
    have hh := ih _ _ _ _ hv' hf hremaining
    simpa only [compileRun, BooleanProgram.run_append, Function.iterate_succ_apply] using hh

theorem stickyStep_of_step (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (a b : Configuration K Λ σ) (h : TM2.step program a = some b) : stickyStep program a = b := by
  rcases a with ⟨l, v, stackStore⟩
  cases l with
  | none => simp [TM2.step] at h
  | some l => simpa only [TM2.step, Option.some.injEq, stickyStep, Option.elim_some] using h

theorem stickyStep_of_halted (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (a : Configuration K Λ σ) (h : a.l = none) : stickyStep program a = a := by
  simp only [stickyStep, h, Option.elim_none]

private theorem iterate_none {α : Type} (step : α → Option α) (n : ℕ) :
    ((fun c : Option α => c.bind step)^[n]) none = none := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [Function.iterate_succ_apply, Option.bind_none] using ih

theorem sticky_iterate_of_steps (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (steps : ℕ) (a b : Configuration K Λ σ)
    (h : ((fun c : Option (Configuration K Λ σ) => c.bind (TM2.step program))^[steps]) (some a) = some b) :
    (stickyStep program)^[steps] a = b := by
  induction steps generalizing a with
  | zero => simpa using h
  | succ steps ih =>
    rw [Function.iterate_succ_apply] at h
    cases hs : TM2.step program a with
    | none => simp only [Option.bind_some, hs, iterate_none] at h; contradiction
    | some next =>
      simp only [Option.bind_some, hs] at h
      rw [Function.iterate_succ_apply, stickyStep_of_step program a next hs]
      exact ih next h

/-- A successful machine's budget can be padded after halt without changing its output. -/
theorem sticky_iterate_of_outputs (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (a b : Configuration K Λ σ) (ticks : ℕ)
    (h : EvalsToInTime (TM2.step program) a (some b) ticks) (hb : b.l = none) :
    (stickyStep program)^[ticks] a = b := by
  have hs := sticky_iterate_of_steps program h.steps a b h.evals_in_steps
  have he : ticks = (ticks - h.steps) + h.steps := by have := h.steps_le_m; omega
  rw [he, Function.iterate_add_apply, hs]
  exact Function.iterate_fixed (stickyStep_of_halted program b hb) _

end InfoLossLAR.WorstCase.TM2Boolean

end P2MDyadicModule27

/- Helper module Solutions.RegevBridgeTM2Size. -/
section P2MDyadicModule28

set_option autoImplicit false

set_option maxHeartbeats 2500000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean

open Turing

variable {K Λ σ : Type} [DecidableEq K] [Fintype K]
  [DecidableEq Λ] [Fintype Λ] [DecidableEq σ] [Fintype σ]

variable {width : ℕ}

namespace Symbolic

structure Bounded (bound : ℕ) (sym : Symbolic K Λ σ width) : Prop where
  label : ∀ l, (sym.label l).size ≤ bound
  state : ∀ v, (sym.state v).size ≤ bound
  stack : ∀ k i b, (sym.stack k i b).size ≤ bound

theorem Bounded.mono {small big : ℕ} {sym : Symbolic K Λ σ width}
    (h : sym.Bounded small) (hle : small ≤ big) : sym.Bounded big :=
  ⟨fun l => (h.label l).trans hle, fun v => (h.state v).trans hle,
    fun k i b => (h.stack k i b).trans hle⟩

def lookupBound (σ : Type) [Fintype σ] (bound : ℕ) : ℕ :=
  (bound + 4) * Fintype.card σ + 1

def readBound (σ : Type) [Fintype σ] (bound : ℕ) : ℕ :=
  (2 * bound + 5) * Fintype.card (σ × Option Bool) + 1

def operationBound (σ : Type) [Fintype σ] (bound : ℕ) : ℕ :=
  bound + lookupBound σ bound + readBound σ bound

private theorem old_le_operation (bound : ℕ) : bound ≤ operationBound σ bound := by
  unfold operationBound; omega

private theorem lookup_le_operation (bound : ℕ) : lookupBound σ bound ≤ operationBound σ bound := by
  unfold operationBound; omega

private theorem read_le_operation (bound : ℕ) : readBound σ bound ≤ operationBound σ bound := by
  unfold operationBound; omega

theorem load_bounded (sym : Symbolic K Λ σ width) {bound : ℕ} (h : sym.Bounded bound) (f : σ → σ) :
    (sym.load f).Bounded (operationBound σ bound) := by
  refine ⟨fun l => (h.label l).trans (old_le_operation bound), ?_,
    fun k i b => (h.stack k i b).trans (old_le_operation bound)⟩
  intro v
  exact (BooleanExpr.size_lookup_le _ _ bound h.state).trans (lookup_le_operation bound)

theorem push_bounded (sym : Symbolic K Λ σ width) {bound : ℕ} (h : sym.Bounded bound) (k : K) (f : σ → Bool) :
    (sym.push k f).Bounded (operationBound σ bound) := by
  refine ⟨fun l => (h.label l).trans (old_le_operation bound),
    fun v => (h.state v).trans (old_le_operation bound), ?_⟩
  intro j i b
  dsimp only [push]
  split_ifs
  · exact (BooleanExpr.size_lookup_le _ _ bound h.state).trans (lookup_le_operation bound)
  · exact (h.stack _ _ _).trans (old_le_operation bound)
  · exact (h.stack _ _ _).trans (old_le_operation bound)

theorem read_bounded (sym : Symbolic K Λ σ width) {bound : ℕ} (h : sym.Bounded bound)
    (hw : 0 < width) (k : K) (f : σ → Option Bool → σ) :
    (sym.read hw k f).Bounded (operationBound σ bound) := by
  refine ⟨fun l => (h.label l).trans (old_le_operation bound), ?_,
    fun k i b => (h.stack k i b).trans (old_le_operation bound)⟩
  intro v
  have hi : ∀ a : σ × Option Bool,
      (BooleanExpr.and (sym.state a.1) (sym.stack k ⟨0, hw⟩ a.2)).size ≤ 2 * bound + 1 := by
    intro a
    simp only [BooleanExpr.size]
    have := h.state a.1
    have := h.stack k ⟨0, hw⟩ a.2
    omega
  have ht := BooleanExpr.size_lookup_le (fun a : σ × Option Bool => decide (v = f a.1 a.2)) _
    (2 * bound + 1) hi
  have hb : ((sym.read hw k f).state v).size ≤ readBound σ bound := by
    simpa only [read, readBound, Nat.add_assoc] using ht
  exact hb.trans (read_le_operation bound)

theorem pop_bounded (sym : Symbolic K Λ σ width) {bound : ℕ} (h : sym.Bounded bound)
    (hb : 1 ≤ bound) (k : K) : (sym.pop k).Bounded bound := by
  refine ⟨h.label, h.state, ?_⟩
  intro j i b
  dsimp only [pop]
  split_ifs
  · exact h.stack _ _ _
  · exact hb
  · exact h.stack _ _ _

theorem jump_bounded (sym : Symbolic K Λ σ width) {bound : ℕ} (h : sym.Bounded bound) (f : σ → Λ) :
    (sym.jump f).Bounded (operationBound σ bound) := by
  refine ⟨?_, fun v => (h.state v).trans (old_le_operation bound),
    fun k i b => (h.stack k i b).trans (old_le_operation bound)⟩
  intro l
  exact (BooleanExpr.size_lookup_le _ _ bound h.state).trans (lookup_le_operation bound)

theorem halt_bounded (sym : Symbolic K Λ σ width) {bound : ℕ} (h : sym.Bounded bound) :
    sym.halt.Bounded (bound + 1) :=
  ⟨fun _ => by simp only [halt, BooleanExpr.size]; omega,
    fun v => (h.state v).trans (Nat.le_add_right _ _),
    fun k i b => (h.stack k i b).trans (Nat.le_add_right _ _)⟩

theorem select_bounded (condition : BooleanExpr) (a b : Symbolic K Λ σ width)
    (conditionBound firstBound secondBound : ℕ)
    (hc : condition.size ≤ conditionBound) (ha : a.Bounded firstBound) (hb : b.Bounded secondBound) :
    (select condition a b).Bounded (2 * conditionBound + firstBound + secondBound + 7) := by
  have hh (e f : BooleanExpr) (he : e.size ≤ firstBound) (hf : f.size ≤ secondBound) :
      (BooleanExpr.select condition e f).size ≤ 2 * conditionBound + firstBound + secondBound + 7 := by
    rw [BooleanExpr.size_select]; omega
  exact ⟨fun l => hh _ _ (ha.label l) (hb.label l),
    fun v => hh _ _ (ha.state v) (hb.state v),
    fun k i b => hh _ _ (ha.stack k i b) (hb.stack k i b)⟩

@[simp] theorem rebound_bounded_zero (sym : Symbolic K Λ σ width) (start : ℕ) :
    (sym.rebound start).Bounded 0 := ⟨fun _ => le_rfl, fun _ => le_rfl, fun _ _ _ => le_rfl⟩

theorem compiled_length_le (sym : Symbolic K Λ σ width) (start bound : ℕ) (h : sym.Bounded bound) :
    (sym.compiled start).1.length ≤ bound * Fintype.card (Slot K Λ σ width) := by
  rw [compiled, BooleanExpr.compileMany_length]
  have hh : ∀ e ∈ sym.formulas, e.size ≤ bound := by
    intro e he
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 he
    generalize (slotEquiv K Λ σ width).symm i = slot
    rcases slot with l | v | ⟨k, i, b⟩
    · exact h.label l
    · exact h.state v
    · exact h.stack k i b
  have sumBound : ∀ es : List BooleanExpr, (∀ e ∈ es, e.size ≤ bound) →
      (es.map BooleanExpr.size).sum ≤ es.length * bound := by
    intro es
    induction es with
    | nil => simp
    | cons e es ih =>
      intro hx
      have he := hx e (by simp)
      have ht := ih (fun a ha => hx a (by simp [ha]))
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      nlinarith
  have hl := sumBound sym.formulas hh
  simpa only [formulas_length, Nat.mul_comm] using hl

end Symbolic

/-- A constant-size formula bound for each fixed machine statement. -/
def auxiliaryBound : TM2.Stmt (fun _ : K => Bool) Λ σ → ℕ → ℕ
  | .push _ _ q, b => auxiliaryBound q (Symbolic.operationBound σ b)
  | .peek _ _ q, b => auxiliaryBound q (Symbolic.operationBound σ b)
  | .pop _ _ q, b => auxiliaryBound q (Symbolic.operationBound σ b)
  | .load _ q, b => auxiliaryBound q (Symbolic.operationBound σ b)
  | .branch _ q r, b => 2 * Symbolic.lookupBound σ b + auxiliaryBound q b + auxiliaryBound r b + 7
  | .goto _, b => Symbolic.operationBound σ b
  | .halt, b => b + 1

theorem auxiliary_bounded (hw : 0 < width) (q : TM2.Stmt (fun _ : K => Bool) Λ σ)
    (sym : Symbolic K Λ σ width) (bound : ℕ) (h : sym.Bounded bound) :
    (auxiliary hw q sym).Bounded (auxiliaryBound q bound) := by
  induction q generalizing sym bound with
  | push k f q ih => exact ih _ _ (sym.push_bounded h k f)
  | peek k f q ih => exact ih _ _ (sym.read_bounded h hw k f)
  | pop k f q ih =>
    exact ih _ _ ((sym.read hw k f).pop_bounded (sym.read_bounded h hw k f)
      (by simp only [Symbolic.operationBound, Symbolic.lookupBound, Symbolic.readBound]; omega) k)
  | load f q ih => exact ih _ _ (sym.load_bounded h f)
  | branch f q r iq ir =>
    exact Symbolic.select_bounded _ _ _ _ _ _ (BooleanExpr.size_lookup_le f sym.state bound h.state)
      (iq _ _ h) (ir _ _ h)
  | goto f => exact sym.jump_bounded h f
  | halt => exact sym.halt_bounded h

noncomputable def transitionBound (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) (bound : ℕ) : ℕ :=
  (bound + (bound + Finset.univ.sup (fun l => auxiliaryBound (program l) bound)) + 5) *
    Fintype.card (Option Λ) + 1

theorem transition_bounded (hw : 0 < width)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (sym : Symbolic K Λ σ width) (bound : ℕ) (h : sym.Bounded bound) :
    (transition hw program sym).Bounded (transitionBound program bound) := by
  have hh : ∀ l : Option Λ,
      (l.elim sym (fun l => auxiliary hw (program l) sym)).Bounded
        (bound + Finset.univ.sup (fun l => auxiliaryBound (program l) bound)) := by
    intro l
    cases l with
    | none => exact h.mono (Nat.le_add_right _ _)
    | some l =>
      exact (auxiliary_bounded hw (program l) sym bound h).mono
        ((Finset.le_sup (f := fun l => auxiliaryBound (program l) bound) (Finset.mem_univ l)).trans
          (Nat.le_add_left _ _))
  exact ⟨fun l => BooleanExpr.size_multiplex_le _ _ _ _ h.label (fun a => (hh a).label l),
    fun v => BooleanExpr.size_multiplex_le _ _ _ _ h.label (fun a => (hh a).state v),
    fun k i b => BooleanExpr.size_multiplex_le _ _ _ _ h.label (fun a => (hh a).stack k i b)⟩

/-- After rebinding, every new step has constant formula size per configuration slot. -/
theorem compileRun_length_le (hw : 0 < width)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) (ticks start : ℕ)
    (sym : Symbolic K Λ σ width) (h : sym.Bounded 0) :
    (compileRun hw program ticks start sym).1.length ≤
      ticks * (transitionBound program 0 * Fintype.card (Slot K Λ σ width)) := by
  induction ticks generalizing start sym with
  | zero => simp [compileRun]
  | succ ticks ih =>
    have hf := (transition hw program sym).compiled_length_le start _ (transition_bounded hw program sym 0 h)
    have hr := ih (start + ((transition hw program sym).compiled start).1.length) _
      ((transition hw program sym).rebound_bounded_zero start)
    simp only [compileRun, List.length_append]
    nlinarith

end InfoLossLAR.WorstCase.TM2Boolean

end P2MDyadicModule28

/- Helper module Solutions.RegevBridgeTM2Initial. -/
section P2MDyadicModule29

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean

open Turing

open Integration9_9.TM2OutputLength

variable {K Λ σ : Type} [DecidableEq K] [Fintype K]
  [DecidableEq Λ] [Fintype Λ] [DecidableEq σ] [Fintype σ]

/-- Actual input bits give a one-hot nonempty Boolean stack cell. -/
def inputCell (wire : ℕ) : Option Bool → BooleanExpr
  | none => .constant false
  | some false => .negate (.input wire)
  | some true => .input wire

theorem inputCell_eval (wire : ℕ) (b : Option Bool) (bits : ℕ → Bool) :
    (inputCell wire b).eval bits = decide (b = some (bits wire)) := by
  cases b with
  | none => rfl
  | some b => cases b <;> cases h : bits wire <;> simp [inputCell, BooleanExpr.eval, h]

def initial (input : K) (main : Λ) (initialState : σ) (length width : ℕ) : Symbolic K Λ σ width where
  label l := .constant (decide (l = some main))
  state v := .constant (decide (v = initialState))
  stack k i b := if k = input ∧ i.val < length then inputCell i.val b
    else .constant (decide (b = none))

def initialConfiguration (input : K) (main : Λ) (initialState : σ) (word : List Bool) : Configuration K Λ σ :=
  ⟨some main, initialState, fun k => if k = input then word else []⟩

theorem initial_valid (input : K) (main : Λ) (initialState : σ) (length width : ℕ) :
    (initial input main initialState length width).Valid length := by
  refine ⟨fun _ => trivial, fun _ => trivial, ?_⟩
  intro k i b
  dsimp only [initial]
  split_ifs with h
  · cases b with
    | none => trivial
    | some b => cases b <;> exact h.2
  · trivial

theorem initial_bounded (input : K) (main : Λ) (initialState : σ) (length width : ℕ) :
    (initial input main initialState length width).Bounded 1 := by
  refine ⟨fun _ => le_rfl, fun _ => le_rfl, ?_⟩
  intro k i b
  dsimp only [initial]
  split_ifs
  · cases b with
    | none => exact le_rfl
    | some b => cases b <;> simp [inputCell, BooleanExpr.size]
  · exact le_rfl

theorem initial_encodes (input : K) (main : Λ) (initialState : σ) (width : ℕ)
    (word : List Bool) (bits : ℕ → Bool)
    (hbits : ∀ i, ∀ hi : i < word.length, bits i = word[i]) :
    Encodes (initial input main initialState word.length width)
      (initialConfiguration input main initialState word) bits := by
  refine ⟨fun _ => rfl, fun _ => rfl, ?_⟩
  intro k i b
  dsimp only [initial, initialConfiguration]
  by_cases hk : k = input
  · simp only [hk, ↓reduceIte, true_and]
    by_cases hi : i.val < word.length
    · simp only [hi, ↓reduceIte, inputCell_eval, hbits i.val hi, List.getElem?_eq_getElem hi]
    · simp only [hi, ↓reduceIte, BooleanExpr.eval, List.getElem?_eq_none (by omega : word.length ≤ i.val)]
  · simp [hk, BooleanExpr.eval]

theorem initial_size_le (input : K) (main : Λ) (initialState : σ) (word : List Bool) :
    stackSize (initialConfiguration input main initialState word).stk ≤ word.length := by
  apply Finset.sup_le
  intro k hk
  by_cases he : k = input
  · simp [initialConfiguration, he]
  · simp [initialConfiguration, he]

@[simp] theorem slot_count (width : ℕ) :
    Fintype.card (Slot K Λ σ width) = Fintype.card Λ + 1 + Fintype.card σ +
      Fintype.card K * width * 3 := by
  simp only [Slot, Fintype.card_sum, Fintype.card_option, Fintype.card_prod,
    Fintype.card_fin, Fintype.card_bool]
  ring

end InfoLossLAR.WorstCase.TM2Boolean

end P2MDyadicModule29

/- Helper module Solutions.RegevBridgeTM2CodeRegisters. -/
section P2MDyadicModule30

set_option autoImplicit false

set_option maxHeartbeats 3000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open RPN

variable {K Λ σ α : Type} [DecidableEq K] [Fintype K]
  [DecidableEq Λ] [Fintype Λ] [DecidableEq σ] [Fintype σ]

theorem slot_label_index (width : ℕ) (l : Option Λ) :
    (slotEquiv K Λ σ width (.inl l)).val = (Fintype.equivFin (Option Λ) l).val := rfl

theorem slot_state_index (width : ℕ) (v : σ) :
    (slotEquiv K Λ σ width (.inr (.inl v))).val =
      Fintype.card (Option Λ) + (Fintype.equivFin σ v).val := rfl

theorem slot_stack_index (width : ℕ) (k : K) (i : Fin width) (b : Option Bool) :
    (slotEquiv K Λ σ width (.inr (.inr (k,i,b)))).val =
      Fintype.card (Option Λ) + (Fintype.card σ +
        ((Fintype.equivFin (Option Bool) b).val + Fintype.card (Option Bool)*i.val +
          (width*Fintype.card (Option Bool))*(Fintype.equivFin K k).val)) := rfl

namespace CodeFamily

def initialCode (input : K) (main : Λ) (initialState : σ) (length : α → ℕ) : CodeFamily K Λ σ α where
  label l _ := .constant (decide (l = some main))
  state v _ := .constant (decide (v = initialState))
  stack k b x := if k = input ∧ x.2 < length x.1 then inputCell x.2 b
    else .constant (decide (b = none))

theorem initialCode_restrict (input : K) (main : Λ) (initialState : σ)
    (length : α → ℕ) (a : α) (width : ℕ) :
    (initialCode input main initialState length).restrict a width =
      initial input main initialState (length a) width := rfl

theorem initialCode_poly [Coding α] (input : K) (main : Λ) (initialState : σ)
    (length : α → ℕ) (hl : Poly length) : (initialCode input main initialState length).IsPoly := by
  refine ⟨fun l => CodePoly.constant _, fun v => CodePoly.constant _, ?_⟩
  intro k b
  have hc : CodePoly (fun x : α × ℕ => inputCell x.2 b) := by
    cases b with
    | none => exact CodePoly.constant false
    | some b => cases b
                · exact (CodePoly.input (show Poly (fun x : α × ℕ => x.2) by fun_prop)).negate
                · exact CodePoly.input (by fun_prop)
  by_cases hk : k = input
  · simp only [initialCode, hk, true_and]
    have hp : Poly (fun x : α × ℕ => decide (x.2 < length x.1)) := by fun_prop
    simpa only [decide_eq_true_eq] using CodePoly.ite hp hc (CodePoly.constant (decide (b=none)))
  · simpa only [initialCode, hk, false_and, ↓reduceIte] using
      (CodePoly.constant (α := α × ℕ) (decide (b=none)))

noncomputable def reboundCode (width : α → ℕ) (refs : α → List ℕ) : CodeFamily K Λ σ α where
  label l a := .input (((refs a)[(Fintype.equivFin (Option Λ) l).val]?).getD 0)
  state v a := .input (((refs a)[Fintype.card (Option Λ)+(Fintype.equivFin σ v).val]?).getD 0)
  stack k b x := .input (((refs x.1)[Fintype.card (Option Λ)+(Fintype.card σ+
    ((Fintype.equivFin (Option Bool) b).val+Fintype.card (Option Bool)*x.2+
      (width x.1*Fintype.card (Option Bool))*(Fintype.equivFin K k).val))]?).getD 0)

theorem reboundCode_poly [Coding α] (width : α → ℕ) (refs : α → List ℕ)
    (hw : Poly width) (hr : Poly refs) : (reboundCode (K := K) (Λ := Λ) (σ := σ) width refs).IsPoly := by
  constructor
  · intro l
    apply CodePoly.input
    fun_prop
  · intro v
    apply CodePoly.input
    fun_prop
  · intro k b
    apply CodePoly.input
    fun_prop

theorem reboundCode_get (width : α → ℕ) (refs : α → List ℕ) (a : α) (i : Slot K Λ σ (width a)) :
    ((reboundCode width refs).restrict a (width a)).get i =
      .input (((refs a)[(slotEquiv K Λ σ (width a) i).val]?).getD 0) := by
  rcases i with l | v | ⟨k,i,b⟩
  · rw [slot_label_index]; rfl
  · rw [slot_state_index]; rfl
  · rw [slot_stack_index]; rfl

theorem reboundCode_restrict (width : α → ℕ) (refs : α → List ℕ) (a : α)
    (sym : Symbolic K Λ σ (width a)) (start : ℕ) (hr : refs a = (sym.compiled start).2) :
    (reboundCode width refs).restrict a (width a) = sym.rebound start := by
  have hi : ∀ i : Slot K Λ σ (width a),
      ((reboundCode width refs).restrict a (width a)).get i = (sym.rebound start).get i := by
    intro i
    rw [reboundCode_get, hr]
    have hlt : (slotEquiv K Λ σ (width a) i).val < (sym.compiled start).2.length := by
      simp only [Symbolic.compiled, BooleanExpr.compileMany_outputs_length, Symbolic.formulas_length]
      exact (slotEquiv K Λ σ (width a) i).isLt
    simp only [List.getElem?_eq_getElem hlt, Option.getD_some, Symbolic.rebound,
      Symbolic.get_ofSlots, Symbolic.output]
  apply symbolic_ext
  · funext l; exact hi (.inl l)
  · funext v; exact hi (.inr (.inl v))
  · funext k i b; exact hi (.inr (.inr (k,i,b)))

end CodeFamily

end InfoLossLAR.WorstCase.TM2Boolean

end P2MDyadicModule30

/- Helper module Solutions.RegevBridgeBooleanRPNBounds. -/
section P2MDyadicModule31

set_option autoImplicit false

set_option maxHeartbeats 3000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean.RPN

theorem code_length (e : BooleanExpr) : (code e).length ≤ 2*e.size+1 := by
  induction e with
  | input i => simp [code, BooleanExpr.size]
  | constant b => cases b <;> simp [code, BooleanExpr.size]
  | negate a ih => simp only [code, List.length_append, List.length_singleton, BooleanExpr.size]; omega
  | xor a b ia ib | and a b ia ib =>
    simp only [code, List.length_append, List.length_singleton, BooleanExpr.size]; omega

theorem valid_code_bits (e : BooleanExpr) (N : ℕ) (h : e.Valid (2^N)) :
    ∀ t ∈ code e, t.2.bits.length ≤ N := by
  induction e with
  | input i =>
    intro t ht
    simp only [code, List.mem_singleton] at ht
    subst t
    change i.bits.length ≤ N
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le.mpr h
  | constant b => cases b <;> simp [code]
  | negate a ih =>
    intro t ht
    simp only [code, List.mem_append, List.mem_singleton] at ht
    rcases ht with ht | rfl
    · exact ih h t ht
    · simp
  | xor a b ia ib | and a b ia ib =>
    intro t ht
    simp only [code, List.mem_append, List.mem_singleton] at ht
    rcases ht with (ht | ht) | rfl
    · exact ia h.1 t ht
    · exact ib h.2 t ht
    · simp

theorem codes_length (es : List BooleanExpr) (C : ℕ) (h : ∀ e ∈ es, e.size ≤ C) :
    (es.flatMap code).length ≤ (2*C+1)*es.length := by
  induction es with
  | nil => simp
  | cons e es ih =>
    have he := (code_length e).trans (show 2*e.size+1 ≤ 2*C+1 by have := h e (by simp); omega)
    have hh := ih (fun f hf => h f (by simp [hf]))
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    nlinarith

theorem reverse_operands_bounded {N : ℕ} {s : State} (h : Bounded N s) :
    Bounded N (s.1, s.2.1.reverse, s.2.2) := by
  refine ⟨h.slots, ?_, h.nodes, ?_, h.code⟩
  · simpa only [List.length_reverse] using h.operands
  · intro x hx
    exact h.refs x (List.mem_reverse.mp hx)

theorem clear_operands_bounded {N : ℕ} {s : State} (h : Bounded N s) :
    Bounded N (s.1, [], s.2.2) := ⟨h.slots, Nat.zero_le _, h.nodes, by simp, h.code⟩

end InfoLossLAR.WorstCase.TM2Boolean.RPN

end P2MDyadicModule31

/- Helper module Solutions.RegevBridgeTM2CodeStep. -/
section P2MDyadicModule32

set_option autoImplicit false

set_option maxHeartbeats 3000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator

open Turing

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open RPN

variable {K Λ σ : Type} [DecidableEq K] [Fintype K]
  [DecidableEq Λ] [Fintype Λ] [DecidableEq σ] [Fintype σ]

abbrev Input := List Unit × RPN.State

noncomputable def registers : CodeFamily K Λ σ Input :=
  CodeFamily.reboundCode (fun x => x.1.length) (fun x => x.2.2.1)

theorem registers_poly : (registers (K := K) (Λ := Λ) (σ := σ)).IsPoly :=
  CodeFamily.reboundCode_poly _ _ (by fun_prop) (by fun_prop)

theorem registers_bounded (x : Input) :
    ((registers (K := K) (Λ := Λ) (σ := σ)).restrict x x.1.length).Bounded 0 := by
  exact ⟨fun _ => le_rfl, fun _ => le_rfl, fun _ _ _ => le_rfl⟩

theorem registers_valid (x : Input) (N : ℕ) (h : ∀ a ∈ x.2.2.1, a.bits.length ≤ N) :
    ((registers (K := K) (Λ := Λ) (σ := σ)).restrict x x.1.length).Valid (2^N) := by
  have hb : ∀ i : ℕ, ((x.2.2.1[i]?).getD 0) < 2^N := by
    intro i
    have hi := getD_bound x.2.2.1 i N h
    rw [Nat.size_eq_bits_len] at hi
    exact Nat.size_le.mp hi
  exact ⟨fun _ => hb _, fun _ => hb _, fun _ _ _ => hb _⟩

noncomputable def tokens (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) : Input → List Token :=
  (CodeFamily.transitionCode (fun x => x.1.length) program registers).codes Prod.fst

@[fun_prop] theorem tokens_poly (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) : Poly (tokens program) :=
  CodeFamily.codes_poly _ (CodeFamily.transitionCode_poly _ (by fun_prop) program _ registers_poly) _ (by fun_prop)

noncomputable def step (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) (x : Input) : Input :=
  if x.1.isEmpty then x else
    let result := RPN.run (tokens program x) (x.2.1, [], x.2.2.2)
    (x.1, result.1, result.2.1.reverse, result.2.2)

@[fun_prop] theorem step_poly (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) : Poly (step program) := by
  unfold step
  fun_prop

@[simp] theorem step_width (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) (x : Input) :
    (step program x).1 = x.1 := by unfold step; split <;> rfl

theorem tokens_eq (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) (x : Input) (hw : 0 < x.1.length) :
    tokens program x = (transition hw program (registers.restrict x x.1.length)).formulas.flatMap code := by
  rw [tokens, CodeFamily.codes_eq, CodeFamily.transitionCode_restrict (fun x : Input => x.1.length) x hw program registers]

noncomputable def tokenBound (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) (width : ℕ) : ℕ :=
  (2*transitionBound program 0+1) * Fintype.card (Slot K Λ σ width)

theorem tokens_length (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) (x : Input)
    (hw : 0 < x.1.length) : (tokens program x).length ≤ tokenBound program x.1.length := by
  rw [tokens_eq program x hw]
  have hb := transition_bounded hw program _ 0 (registers_bounded (K := K) (Λ := Λ) (σ := σ) x)
  have hh := codes_length (transition hw program (registers.restrict x x.1.length)).formulas
    (transitionBound program 0) (by
      intro e he
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp he
      rcases (slotEquiv K Λ σ x.1.length).symm i with l | v | ⟨k,i,b⟩
      · exact hb.label l
      · exact hb.state v
      · exact hb.stack k i b)
  simpa only [Symbolic.formulas_length, tokenBound] using hh

theorem tokens_bits (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) (x : Input)
    (hw : 0 < x.1.length) (N : ℕ) (h : ∀ a ∈ x.2.2.1, a.bits.length ≤ N) :
    ∀ t ∈ tokens program x, t.2.bits.length ≤ N := by
  rw [tokens_eq program x hw]
  have hv := transition_valid hw program _ (registers_valid (K := K) (Λ := Λ) (σ := σ) x N h)
  intro t ht
  obtain ⟨e, he, ht⟩ := List.mem_flatMap.mp ht
  exact valid_code_bits e N ((transition hw program (registers.restrict x x.1.length)).formulas_valid hv e he) t ht

theorem step_bounded (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) (x : Input)
    (N : ℕ) (hN : 3 ≤ N) (h : RPN.Bounded N x.2) :
    RPN.Bounded (N+tokenBound program x.1.length) (step program x).2 := by
  unfold step
  split
  · exact h.mono (Nat.le_add_right _ _)
  · rename_i hw
    have hw' : 0 < x.1.length := by
      have hx : x.1 ≠ [] := by simpa only [List.isEmpty_iff] using hw
      exact List.length_pos_iff.mpr hx
    have hb := run_bounded (tokens program x) (clear_operands_bounded h) hN (tokens_bits program x hw' N h.refs)
    exact (reverse_operands_bounded hb).mono (Nat.add_le_add_left (tokens_length program x hw') N)

theorem step_exact (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) (x : Input)
    (hw : 0 < x.1.length) :
    step program x =
      let sym := transition hw program (registers.restrict x x.1.length)
      let result := sym.compiled x.2.1.length
      (x.1, x.2.1 ++ List.replicate result.1.length (), result.2, x.2.2.2 ++ result.1.map node) := by
  have he : x.1.isEmpty = false := List.isEmpty_eq_false_iff.mpr (List.length_pos_iff.mp hw)
  simp only [step, he, Bool.false_eq_true, ↓reduceIte, tokens_eq program x hw, run_codes,
    List.append_nil, List.reverse_reverse, Symbolic.compiled, BooleanExpr.compileMany_length]

end InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator

end P2MDyadicModule32

/- Helper module Solutions.RegevBridgeTM2CodeLoop. -/
section P2MDyadicModule33

set_option autoImplicit false

set_option maxHeartbeats 3000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator

open Turing Polynomial

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open RPN

variable {K Λ σ : Type} [DecidableEq K] [Fintype K]
  [DecidableEq Λ] [Fintype Λ] [DecidableEq σ] [Fintype σ]

noncomputable def iterateCode (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) (fuel : List Unit) (x : Input) : Input :=
  fuel.foldl (fun y _ => step program y) x

@[simp] theorem iterateCode_width (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) (fuel : List Unit) (x : Input) :
    (iterateCode program fuel x).1 = x.1 := by
  induction fuel generalizing x with
  | nil => rfl
  | cons u fuel ih => simpa only [iterateCode, List.foldl_cons, step_width] using ih (step program x)

theorem iterateCode_bounded (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) (fuel : List Unit)
    (x : Input) (N : ℕ) (hN : 3 ≤ N) (h : RPN.Bounded N x.2) :
    RPN.Bounded (N+fuel.length*tokenBound program x.1.length) (iterateCode program fuel x).2 := by
  induction fuel generalizing x N with
  | nil => simpa only [iterateCode, List.foldl_nil, List.length_nil, Nat.zero_mul, Nat.add_zero] using h
  | cons u fuel ih =>
    have hs := step_bounded program x N hN h
    have hh := ih (step program x) (N+tokenBound program x.1.length) (by omega) hs
    simpa only [iterateCode, List.foldl_cons, List.length_cons, step_width, Nat.add_mul,
      Nat.one_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh

noncomputable def tokenRate (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) : ℕ :=
  (2*transitionBound program 0+1)*(Fintype.card Λ+1+Fintype.card σ+Fintype.card K*3)

theorem tokenBound_le (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) (width : ℕ) :
    tokenBound program width ≤ tokenRate program*(width+1) := by
  unfold tokenBound tokenRate
  rw [slot_count]
  have h : Fintype.card Λ+1+Fintype.card σ+Fintype.card K*width*3 ≤
      (Fintype.card Λ+1+Fintype.card σ+Fintype.card K*3)*(width+1) := by nlinarith
  have hh := Nat.mul_le_mul_left (2*transitionBound program 0+1) h
  simpa only [Nat.mul_assoc] using hh

noncomputable def loopBound (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) : Polynomial ℕ :=
  2*X+1+20*(X+3+X*C (tokenRate program)*(X+1)+1)^2

theorem iterateCode_partial_bound (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (fuel : List Unit) (x : Input) (pre suf : List Unit) (he : fuel=pre++suf) :
    (enc (iterateCode program pre x)).length ≤ (loopBound program).eval (enc (fuel,x)).length := by
  let L := (enc (fuel,x)).length
  have heL : L = 2*fuel.length+1+2*x.1.length+1+(enc x.2).length := by
    change (encodePair (enc : List Unit → List Bool) (encodePair enc enc) (fuel,x)).length = _
    simp only [encodePair_length, encodedUnit_length]
    omega
  have hw : x.1.length ≤ L := by omega
  have hp : pre.length ≤ L := by have hh := congrArg List.length he; simp only [List.length_append] at hh; omega
  have hs := (bounded_of_encoding x.2).mono (show (enc x.2).length ≤ L+3 by omega)
  have hb := iterateCode_bounded program pre x (L+3) (by omega) hs
  have ht := (tokenBound_le program x.1.length).trans
    (Nat.mul_le_mul_left (tokenRate program) (Nat.add_le_add_right hw 1))
  have hm : pre.length * tokenBound program x.1.length ≤ L*tokenRate program*(L+1) := by
    exact (Nat.mul_le_mul hp ht).trans_eq (Nat.mul_assoc _ _ _).symm
  have hb' := hb.mono (Nat.add_le_add_left hm (L+3))
  have hh := encoding_bound hb'
  have hwidth := iterateCode_width program pre x
  have henc : (enc (iterateCode program pre x)).length = 2*x.1.length+1+(enc (iterateCode program pre x).2).length := by
    change (encodePair (enc : List Unit → List Bool) enc (iterateCode program pre x)).length = _
    rw [encodePair_length, encodedUnit_length, hwidth]
  simp only [loopBound, eval_add, eval_mul, eval_ofNat, eval_X, eval_one, eval_pow, eval_C]
  change _ ≤ 2*L+1+20*(L+3+L*tokenRate program*(L+1)+1)^2
  omega

@[fun_prop] theorem iterateCode_poly (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) :
    Poly (fun x : List Unit × Input => iterateCode program x.1 x.2) := by
  have hs : Poly (fun x : Input × Unit => step program x.1) := by fun_prop
  apply Automatic.Poly.of_program
  exact hs.program.listFold () (loopBound program) (by
    intro fuel x pre suf he
    change (enc (iterateCode program pre x)).length ≤ (loopBound program).eval (enc (fuel,x)).length
    exact iterateCode_partial_bound program fuel x pre suf he)

end InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator

end P2MDyadicModule33

/- Helper module Solutions.RegevBridgeTM2CodeLoopSemantics. -/
section P2MDyadicModule34

set_option autoImplicit false

set_option maxHeartbeats 3000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator

open Turing

open RPN

variable {K Λ σ : Type} [DecidableEq K] [Fintype K]
  [DecidableEq Λ] [Fintype Λ] [DecidableEq σ] [Fintype σ]

noncomputable def view (width : List Unit) (s : RPN.State) : Symbolic K Λ σ width.length :=
  registers.restrict (width,s) width.length

theorem view_rebound (width : List Unit) (s : RPN.State)
    (sym : Symbolic K Λ σ width.length) (start : ℕ) (hr : s.2.1 = (sym.compiled start).2) :
    view width s = sym.rebound start := by
  have hh := CodeFamily.reboundCode_restrict (fun _ : Unit => width.length)
    (fun _ => s.2.1) () sym start hr
  exact hh

noncomputable def innerStep (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (width : List Unit) (s : RPN.State) : RPN.State := (step program (width,s)).2

theorem innerStep_spec (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (width : List Unit) (hw : 0 < width.length) (s : RPN.State) :
    let sym := transition hw program (view width s)
    let result := sym.compiled s.1.length
    (innerStep program width s).1.length = s.1.length+result.1.length ∧
    (innerStep program width s).2.2 = s.2.2 ++ result.1.map node ∧
    view width (innerStep program width s) = sym.rebound s.1.length := by
  have he := step_exact program (width,s) hw
  have hs := congrArg Prod.snd he
  change innerStep program width s = _ at hs
  dsimp only at hs ⊢
  refine ⟨?_, ?_, ?_⟩
  · rw [hs]
    simp only [List.length_append, List.length_replicate, view]
  · rw [hs]
    rfl
  · apply view_rebound
    rw [hs]
    rfl

noncomputable def runState (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (width : List Unit) : ℕ → RPN.State → RPN.State
  | 0, s => s
  | n+1, s => runState program width n (innerStep program width s)

theorem iterateCode_eq_runState (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (fuel : List Unit) (width : List Unit) (s : RPN.State) :
    iterateCode program fuel (width,s) = (width, runState program width fuel.length s) := by
  induction fuel generalizing s with
  | nil => rfl
  | cons u fuel ih =>
    have he : step program (width,s) = (width, innerStep program width s) := by
      apply Prod.ext
      · exact step_width program (width,s)
      · rfl
    change iterateCode program fuel (step program (width,s)) = _
    rw [he, ih]
    rfl

theorem runState_spec (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (width : List Unit) (hw : 0 < width.length) (n : ℕ) (s : RPN.State) :
    let result := compileRun hw program n s.1.length (view width s)
    (runState program width n s).1.length = s.1.length+result.1.length ∧
    (runState program width n s).2.2 = s.2.2 ++ result.1.map node ∧
    view width (runState program width n s) = result.2 := by
  induction n generalizing s with
  | zero => simp [runState, compileRun]
  | succ n ih =>
    obtain ⟨hl, hc, hv⟩ := innerStep_spec program width hw s
    have hh := ih (innerStep program width s)
    dsimp only at hl hc hv hh ⊢
    rw [hl, hv] at hh
    rcases hh with ⟨hl', hc', hv'⟩
    refine ⟨?_, ?_, hv'⟩
    · simpa only [runState, compileRun, List.length_append, Nat.add_assoc] using hl'
    · rw [hc] at hc'
      simpa only [runState, compileRun, List.map_append, List.append_assoc] using hc'

end InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator

end P2MDyadicModule34

/- Helper module Solutions.RegevBridgeTM2ViewCompilation. -/
section P2MDyadicModule35

set_option autoImplicit false

set_option maxHeartbeats 3000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator

open RPN

variable {K Λ σ : Type} [DecidableEq K] [Fintype K]
  [DecidableEq Λ] [Fintype Λ] [DecidableEq σ] [Fintype σ]

theorem compileMany_inputs (start : ℕ) (refs : List ℕ) :
    BooleanExpr.compileMany start (refs.map BooleanExpr.input) = ([],refs) := by
  induction refs with
  | nil => rfl
  | cons i is ih => simpa only [List.map_cons, BooleanExpr.compileMany, BooleanExpr.compile,
      List.length_nil, Nat.add_zero, List.nil_append] using congrArg (fun p : List BooleanOp × List ℕ => (p.1,i::p.2)) ih

theorem view_formulas (width : List Unit) (s : RPN.State) :
    (view (K := K) (Λ := Λ) (σ := σ) width s).formulas =
      (List.ofFn (fun i : Fin (Fintype.card (Slot K Λ σ width.length)) =>
        (s.2.1[i.val]?).getD 0)).map BooleanExpr.input := by
  rw [List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  change ((CodeFamily.reboundCode (fun x : Input => x.1.length) (fun x => x.2.2.1)).restrict
    (width,s) width.length).get ((slotEquiv K Λ σ width.length).symm i) = _
  rw [CodeFamily.reboundCode_get]
  simp only [Equiv.apply_symm_apply, Function.comp_apply]

theorem view_compiled (width : List Unit) (s : RPN.State) (start : ℕ) :
    (view (K := K) (Λ := Λ) (σ := σ) width s).compiled start =
      ([],List.ofFn (fun i : Fin (Fintype.card (Slot K Λ σ width.length)) =>
        (s.2.1[i.val]?).getD 0)) := by
  rw [Symbolic.compiled, view_formulas, compileMany_inputs]

theorem view_output (width : List Unit) (s : RPN.State) (start : ℕ) (i : Slot K Λ σ width.length) :
    (view width s).output start i = (s.2.1[(slotEquiv K Λ σ width.length i).val]?).getD 0 := by
  unfold Symbolic.output
  simp only [view_compiled, List.getElem_ofFn]

end InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator

end P2MDyadicModule35

/- Helper module Solutions.RegevBridgeTM2MachineProgram. -/
section P2MDyadicModule36

set_option autoImplicit false

set_option maxHeartbeats 2500000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean

open Turing

open Integration9_9.TM2OutputLength

variable {K Λ σ : Type} [DecidableEq K] [Fintype K]
  [DecidableEq Λ] [Fintype Λ] [DecidableEq σ] [Fintype σ]

variable {width : ℕ}

def configurationBit (cfg : Configuration K Λ σ) : Slot K Λ σ width → Bool
  | .inl l => decide (l = cfg.l)
  | .inr (.inl v) => decide (v = cfg.var)
  | .inr (.inr (k, i, b)) => decide (b = (cfg.stk k)[i.val]?)

theorem Encodes.get {sym : Symbolic K Λ σ width} {cfg : Configuration K Λ σ}
    {bits : ℕ → Bool} (h : Encodes sym cfg bits) (i : Slot K Λ σ width) :
    (sym.get i).eval bits = configurationBit cfg i := by
  rcases i with l | v | ⟨k, i, b⟩
  · exact h.label l
  · exact h.state v
  · exact h.stack k i b

theorem compileRun_rebound_bounded (hw : 0 < width)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) (ticks start : ℕ)
    (sym : Symbolic K Λ σ width) (h : sym.Bounded 0) :
    (compileRun hw program ticks start sym).2.Bounded 0 := by
  induction ticks generalizing start sym with
  | zero => exact h
  | succ ticks ih => exact ih _ _ ((transition hw program sym).rebound_bounded_zero start)

/-- The compiled classical machine, together with every one-hot output reference. -/
structure MachineProgram (K Λ σ : Type) (width : ℕ) where
  ops : List BooleanOp
  output : Slot K Λ σ width → ℕ

noncomputable def machineProgram (hw : 0 < width)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (input : K) (main : Λ) (initialState : σ) (ticks length : ℕ) : MachineProgram K Λ σ width :=
  let init := initial input main initialState length width
  let first := init.compiled length
  let rest := compileRun hw program ticks (length + first.1.length) (init.rebound length)
  let lastStart := length + first.1.length + rest.1.length
  { ops := first.1 ++ rest.1 ++ (rest.2.compiled lastStart).1
    output := rest.2.output lastStart }

theorem machineProgram_valid (hw : 0 < width)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (input : K) (main : Λ) (initialState : σ) (ticks length : ℕ) :
    BooleanProgram.Valid length (machineProgram hw program input main initialState ticks length).ops ∧
      ∀ i, (machineProgram hw program input main initialState ticks length).output i <
        length + (machineProgram hw program input main initialState ticks length).ops.length := by
  let init := initial input main initialState length width
  have hi : init.Valid length := initial_valid input main initialState length width
  have hp := init.compiled_valid length hi
  have hr := compileRun_valid hw program ticks _ _ (init.rebound_valid length hi)
  constructor
  · apply (BooleanProgram.valid_append _ _ _).2
    constructor
    · exact (BooleanProgram.valid_append _ _ _).2 ⟨hp, hr.1⟩
    · simpa only [List.length_append, Nat.add_assoc] using
        (compileRun hw program ticks _ _).2.compiled_valid _ hr.2
  · intro i
    have hh := (compileRun hw program ticks _ _).2.output_lt _ hr.2 i
    simpa only [machineProgram, List.length_append, Nat.add_assoc, init] using hh

theorem machineProgram_length_le (hw : 0 < width)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (input : K) (main : Λ) (initialState : σ) (ticks length : ℕ) :
    (machineProgram hw program input main initialState ticks length).ops.length ≤
      (1 + ticks * transitionBound program 0) * Fintype.card (Slot K Λ σ width) := by
  let init := initial input main initialState length width
  have hi : init.Bounded 1 := initial_bounded input main initialState length width
  have hp := init.compiled_length_le length 1 hi
  have hm := compileRun_length_le hw program ticks (length + (init.compiled length).1.length) _
    (init.rebound_bounded_zero length)
  have hz := compileRun_rebound_bounded hw program ticks (length + (init.compiled length).1.length) _
    (init.rebound_bounded_zero length)
  let middle := compileRun hw program ticks (length + (init.compiled length).1.length) (init.rebound length)
  have he := middle.2.compiled_length_le
    (length + (init.compiled length).1.length + middle.1.length) 0 hz
  change ((init.compiled length).1 ++ middle.1 ++
    (middle.2.compiled (length + (init.compiled length).1.length + middle.1.length)).1).length ≤ _
  simp only [List.length_append]
  nlinarith

/-- The whole generated straight-line program computes every field of the budgeted machine execution. -/
theorem machineProgram_semantics (hw : 0 < width)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (input : K) (main : Λ) (initialState : σ) (ticks : ℕ)
    (word : List Bool) (bits : ℕ → Bool)
    (hbits : ∀ i, ∀ hi : i < word.length, bits i = word[i])
    (hsize : word.length + programPushBound program * ticks ≤ width) (i : Slot K Λ σ width) :
    BooleanProgram.run word.length (machineProgram hw program input main initialState ticks word.length).ops bits
      ((machineProgram hw program input main initialState ticks word.length).output i) =
      configurationBit ((stickyStep program)^[ticks] (initialConfiguration input main initialState word)) i := by
  let init := initial input main initialState word.length width
  have hi : init.Valid word.length := initial_valid input main initialState word.length width
  have he : Encodes init (initialConfiguration input main initialState word) bits :=
    initial_encodes input main initialState width word bits hbits
  have hp := init.rebound_encodes word.length hi _ bits he
  have hr := compileRun_encodes hw program ticks _ _ _ _
    (init.rebound_valid word.length hi) hp
    ((Nat.add_le_add_right (initial_size_le input main initialState word) _).trans hsize)
  have hv := (compileRun_valid hw program ticks _ _ (init.rebound_valid word.length hi)).2
  let middle := compileRun hw program ticks (word.length + (init.compiled word.length).1.length)
    (init.rebound word.length)
  have ho := middle.2.output_eval _ hv
    (BooleanProgram.run (word.length + (init.compiled word.length).1.length) middle.1
      (BooleanProgram.run word.length (init.compiled word.length).1 bits)) i
  rw [hr.get i] at ho
  simpa only [machineProgram, BooleanProgram.run_append, List.length_append, Nat.add_assoc, init, middle] using ho

end InfoLossLAR.WorstCase.TM2Boolean

end P2MDyadicModule36

/- Helper module Solutions.RegevBridgeTM2CodeGenerate. -/
section P2MDyadicModule37

set_option autoImplicit false

set_option maxHeartbeats 4000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator

open Turing

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open RPN

variable {K Λ σ : Type} [DecidableEq K] [Fintype K]
  [DecidableEq Λ] [Fintype Λ] [DecidableEq σ] [Fintype σ]

/-- Unary input length, stack capacity, and step budget. -/
abbrev Request := List Unit × (List Unit × List Unit)

noncomputable def initialResult (input : K) (main : Λ) (initialState : σ) : Request → List Node × List ℕ :=
  (CodeFamily.initialCode input main initialState (fun x : Request => x.1.length)).compile
    (fun x => x.2.1) Prod.fst

@[fun_prop] theorem initialResult_poly (input : K) (main : Λ) (initialState : σ) :
    Poly (initialResult input main initialState) :=
  CodeFamily.compile_poly _ (CodeFamily.initialCode_poly _ _ _ _ (by fun_prop)) _ _ (by fun_prop) (by fun_prop)

theorem initialResult_eq (input : K) (main : Λ) (initialState : σ) (x : Request) :
    initialResult input main initialState x =
      (((initial input main initialState x.1.length x.2.1.length).compiled x.1.length).1.map node,
        ((initial input main initialState x.1.length x.2.1.length).compiled x.1.length).2) := by
  rw [initialResult, CodeFamily.compile_eq, CodeFamily.initialCode_restrict]

noncomputable def initialInput (input : K) (main : Λ) (initialState : σ) (x : Request) : Input :=
  let result := initialResult input main initialState x
  (x.2.1, x.1 ++ result.1.map (fun _ => ()), result.2, result.1)

@[fun_prop] theorem initialInput_poly (input : K) (main : Λ) (initialState : σ) :
    Poly (initialInput input main initialState) := by
  unfold initialInput
  fun_prop

theorem initialInput_spec (input : K) (main : Λ) (initialState : σ) (x : Request) :
    let sym := initial input main initialState x.1.length x.2.1.length
    let result := sym.compiled x.1.length
    (initialInput input main initialState x).2.1.length = x.1.length+result.1.length ∧
    (initialInput input main initialState x).2.2.2 = result.1.map node ∧
    view x.2.1 (initialInput input main initialState x).2 = sym.rebound x.1.length := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · simp only [initialInput, initialResult_eq, List.length_append, List.length_map]
  · simp only [initialInput, initialResult_eq]
  · apply view_rebound
    simp only [initialInput, initialResult_eq]

noncomputable def generate (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (input : K) (main : Λ) (initialState : σ) (x : Request) : Input :=
  iterateCode program x.2.2 (initialInput input main initialState x)

@[fun_prop] theorem generate_poly (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (input : K) (main : Λ) (initialState : σ) : Poly (generate program input main initialState) := by
  unfold generate
  fun_prop

theorem generate_runState (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (input : K) (main : Λ) (initialState : σ) (x : Request) :
    generate program input main initialState x =
      (x.2.1,runState program x.2.1 x.2.2.length (initialInput input main initialState x).2) := by
  unfold generate
  have he : initialInput input main initialState x =
      (x.2.1,(initialInput input main initialState x).2) := rfl
  rw [he, iterateCode_eq_runState]

theorem generate_spec (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (input : K) (main : Λ) (initialState : σ) (x : Request) (hw : 0 < x.2.1.length) :
    let first := (initial input main initialState x.1.length x.2.1.length).compiled x.1.length
    let result := compileRun hw program x.2.2.length (x.1.length+first.1.length)
      ((initial input main initialState x.1.length x.2.1.length).rebound x.1.length)
    (generate program input main initialState x).2.1.length = x.1.length+first.1.length+result.1.length ∧
    (generate program input main initialState x).2.2.2 = (first.1++result.1).map node ∧
    view x.2.1 (generate program input main initialState x).2 = result.2 := by
  obtain ⟨hl,hc,hv⟩ := initialInput_spec input main initialState x
  have hh := runState_spec program x.2.1 hw x.2.2.length (initialInput input main initialState x).2
  dsimp only at hl hc hv hh ⊢
  rw [hl,hv] at hh
  rw [generate_runState]
  rcases hh with ⟨hl',hc',hv'⟩
  refine ⟨hl',?_,hv'⟩
  rw [hc] at hc'
  simpa only [List.map_append] using hc'

theorem generate_machineProgram (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (input : K) (main : Λ) (initialState : σ) (x : Request) (hw : 0 < x.2.1.length) :
    (generate program input main initialState x).2.2.2 =
      (machineProgram hw program input main initialState x.2.2.length x.1.length).ops.map node ∧
    (generate program input main initialState x).2.1.length =
      x.1.length+(machineProgram hw program input main initialState x.2.2.length x.1.length).ops.length ∧
    ∀ i : Slot K Λ σ x.2.1.length,
      ((generate program input main initialState x).2.2.1[(slotEquiv K Λ σ x.2.1.length i).val]?).getD 0 =
        (machineProgram hw program input main initialState x.2.2.length x.1.length).output i := by
  obtain ⟨hl,hc,hv⟩ := generate_spec program input main initialState x hw
  let first := (initial input main initialState x.1.length x.2.1.length).compiled x.1.length
  let result := compileRun hw program x.2.2.length (x.1.length+first.1.length)
      ((initial input main initialState x.1.length x.2.1.length).rebound x.1.length)
  let lastStart := x.1.length+first.1.length+result.1.length
  have hz : (result.2.compiled lastStart).1 = [] := by
    rw [← hv, view_compiled]
  have ho : (machineProgram hw program input main initialState x.2.2.length x.1.length).ops = first.1++result.1 := by
    change first.1++result.1++(result.2.compiled lastStart).1 = _
    rw [hz, List.append_nil]
  refine ⟨?_, ?_, ?_⟩
  · rw [ho]; exact hc
  · rw [ho, List.length_append]
    simpa only [Nat.add_assoc] using hl
  · intro i
    change _ = result.2.output lastStart i
    rw [← hv, view_output]

end InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator

end P2MDyadicModule37

/- Helper module Solutions.RegevBridgeBooleanNodeSerialization. -/
section P2MDyadicModule38

set_option autoImplicit false

set_option maxHeartbeats 3000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean.RPN

open QAlgorithms.Complexity

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open QMCNumericRuntime

open Integration9_9.TM2PlatformSerialization

def boundedNat (slots : List Unit) (n : ℕ) : Str := lengthToken (slots.take n)

@[fun_prop] theorem boundedNat_poly : Poly (fun x : List Unit × ℕ => boundedNat x.1 x.2) := by
  unfold boundedNat
  fun_prop

theorem boundedNat_eq (slots : List Unit) (n : ℕ) (h : n ≤ slots.length) :
    boundedNat slots n = encNat n := by simp [boundedNat, lengthToken_eq, List.length_take, Nat.min_eq_left h]

def instructionWord (slots : List Unit) (target : ℕ) (v : Node) : Str :=
  if v.1 = 0 then encNat 0 ++ boundedNat slots target
  else if v.1 = 1 then encNat 1 ++ boundedNat slots target
  else if v.1 = 2 then encNat 2 ++ boundedNat slots v.2.1 ++ boundedNat slots target
  else if v.1 = 3 then encNat 3 ++ boundedNat slots v.2.1 ++ boundedNat slots target
  else if v.1 = 4 then encNat 4 ++ boundedNat slots v.2.1 ++ boundedNat slots v.2.2 ++ boundedNat slots target
  else encNat 5 ++ boundedNat slots v.2.1 ++ boundedNat slots v.2.2 ++ boundedNat slots target

@[fun_prop] theorem instructionWord_poly :
    Poly (fun x : List Unit × (ℕ × Node) => instructionWord x.1 x.2.1 x.2.2) := by
  unfold instructionWord
  fun_prop

theorem instructionWord_node {total : ℕ} (slots : List Unit) (op : BooleanOp) (target : Fin total)
    (h : op.Valid target.val) (ht : target.val ≤ slots.length) :
    instructionWord slots target.val (node op) = (op.toGate target).code := by
  cases op with
  | constant b => cases b <;> simp [node, instructionWord, BooleanOp.toGate, BooleanGate.code, boundedNat_eq slots target.val ht]
  | copy a | negate a =>
    have ha : a < target.val := h a (by simp [BooleanOp.sources])
    simp [node, instructionWord, BooleanOp.toGate, BooleanGate.code, ha,
      boundedNat_eq slots target.val ht, boundedNat_eq slots a (ha.le.trans ht)]
  | xor a b | and a b =>
    have ha : a < target.val := h a (by simp [BooleanOp.sources])
    have hb : b < target.val := h b (by simp [BooleanOp.sources])
    simp [node, instructionWord, BooleanOp.toGate, BooleanGate.code, ha, hb,
      boundedNat_eq slots target.val ht, boundedNat_eq slots a (ha.le.trans ht),
      boundedNat_eq slots b (hb.le.trans ht)]

def instructionWords (slots : List Unit) (start : ℕ) (nodes : List Node) : List Str :=
  (List.range nodes.length).map (fun i => instructionWord slots (start+i) ((nodes[i]?).getD (0,0,0)))

@[fun_prop] theorem instructionWords_poly :
    Poly (fun x : List Unit × (ℕ × List Node) => instructionWords x.1 x.2.1 x.2.2) := by
  unfold instructionWords
  apply Automatic.Poly.list_map
  · fun_prop
  · exact Automatic.Poly.comp (f := fun xs : List Node => List.range xs.length)
      (g := fun x : List Unit × (ℕ × List Node) => x.2.2) Automatic.Poly.list_indices (by fun_prop)

theorem instructionWords_mapIdx (slots : List Unit) (start : ℕ) (nodes : List Node) :
    instructionWords slots start nodes = nodes.mapIdx (fun i v => instructionWord slots (start+i) v) := by
  apply List.ext_getElem
  · simp [instructionWords]
  · intro i hi hj
    have hin : i < nodes.length := by simpa only [List.length_mapIdx] using hj
    simp only [instructionWords, List.getElem_map, List.getElem_range, List.getElem_mapIdx,
      List.getElem?_eq_getElem hin, Option.getD_some]

theorem instructionWords_gates {total : ℕ} (slots : List Unit) (start : ℕ) (ops : List BooleanOp)
    (h : start+ops.length ≤ total) (hv : BooleanProgram.Valid start ops)
    (hs : start+ops.length ≤ slots.length) :
    instructionWords slots start (ops.map node) = (BooleanProgram.gates start ops h).map BooleanGate.code := by
  rw [instructionWords_mapIdx]
  induction ops generalizing start with
  | nil => rfl
  | cons op ops ih =>
    simp only [BooleanProgram.Valid] at hv
    simp only [List.length_cons] at h hs
    simp only [List.map_cons, List.mapIdx_cons, BooleanProgram.gates]
    simp only [Nat.add_zero]
    rw [instructionWord_node slots op (⟨start, by omega⟩ : Fin total) hv.1 (by change start ≤ slots.length; omega)]
    congr 1
    have hh := ih (start+1) (by omega) hv.2 (by omega)
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh

end InfoLossLAR.WorstCase.TM2Boolean.RPN

end P2MDyadicModule38

/- Helper module Solutions.RegevBridgeTM2Quantum. -/
section P2MDyadicModule39

set_option autoImplicit false

set_option maxHeartbeats 2500000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean

open Turing QAlgorithms.Complexity

open Integration9_9.TM2OutputLength

variable {K Λ σ : Type} [DecidableEq K] [Fintype K]
  [DecidableEq Λ] [Fintype Λ] [DecidableEq σ] [Fintype σ]

variable {width : ℕ}

/-- The actual word, with zeros on every workspace address. -/
def wordExtension (word : List Bool) (i : ℕ) : Bool := (word[i]?).getD false

theorem wordExtension_before (word : List Bool) (i : ℕ) (h : i < word.length) :
    wordExtension word i = word[i] := by simp only [wordExtension, List.getElem?_eq_getElem h, Option.getD_some]

theorem wordExtension_after (word : List Bool) (i : ℕ) (h : word.length ≤ i) :
    wordExtension word i = false := by simp only [wordExtension, List.getElem?_eq_none h, Option.getD_none]

theorem wordExtension_basis (word : List Bool) (ancillas : ℕ) :
    Fin.append (toBits word) (fun _ : Fin (ancillas + 1) => false) =
      (fun i : Fin (word.length + (ancillas + 1)) => wordExtension word i.val) := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simpa only [Fin.append_left, Fin.coe_castAdd, toBits, List.get_eq_getElem] using
      (wordExtension_before word j.val j.isLt).symm
  · intro j
    simp only [Fin.append_right, Fin.val_natAdd]
    exact (wordExtension_after word _ (Nat.le_add_right _ _)).symm

noncomputable def machineGates (hw : 0 < width)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (input : K) (main : Λ) (initialState : σ) (ticks length : ℕ) :
    List (BooleanGate (length + ((machineProgram hw program input main initialState ticks length).ops.length + 1))) :=
  BooleanProgram.gates length (machineProgram hw program input main initialState ticks length).ops (by omega)

noncomputable def machineCircuit (hw : 0 < width)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (input : K) (main : Λ) (initialState : σ) (ticks length : ℕ) :
    Layered (length + ((machineProgram hw program input main initialState ticks length).ops.length + 1)) :=
  compileReversible (booleanToReversible (machineGates hw program input main initialState ticks length))

noncomputable def machineOutputWire (hw : 0 < width)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (input : K) (main : Λ) (initialState : σ) (ticks length : ℕ) (i : Slot K Λ σ width) :
    Fin (length + ((machineProgram hw program input main initialState ticks length).ops.length + 1)) :=
  ⟨(machineProgram hw program input main initialState ticks length).output i, by
    have := (machineProgram_valid hw program input main initialState ticks length).2 i
    omega⟩

/-- This is the literal Clifford+T circuit on the platform's actual input basis state. -/
theorem machineCircuit_basis (hw : 0 < width)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (input : K) (main : Λ) (initialState : σ) (ticks : ℕ) (word : List Bool) :
    runLayered (machineCircuit hw program input main initialState ticks word.length)
      (basisInput (toBits word)) = computationalBasis (fun j =>
        BooleanProgram.run word.length (machineProgram hw program input main initialState ticks word.length).ops
          (wordExtension word) j.val) := by
  rw [basisInput_eq_computationalBasis, wordExtension_basis]
  exact BooleanProgram.circuit_basis _ _
    (machineProgram_valid hw program input main initialState ticks word.length).1
    (wordExtension word) (fun i hi _ => wordExtension_after word i hi)

/-- Reading any output slot of the compiled basis state recovers the actual budgeted machine field. -/
theorem machineCircuit_output (hw : 0 < width)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (input : K) (main : Λ) (initialState : σ) (ticks : ℕ) (word : List Bool)
    (hsize : word.length + programPushBound program * ticks ≤ width) (i : Slot K Λ σ width) :
    (fun j => BooleanProgram.run word.length
      (machineProgram hw program input main initialState ticks word.length).ops (wordExtension word) j.val)
      (machineOutputWire hw program input main initialState ticks word.length i) =
      configurationBit ((stickyStep program)^[ticks] (initialConfiguration input main initialState word)) i :=
  machineProgram_semantics hw program input main initialState ticks word (wordExtension word)
    (wordExtension_before word) hsize i

end InfoLossLAR.WorstCase.TM2Boolean

end P2MDyadicModule39

/- Helper module Solutions.RegevBridgeTM2CodeDescription. -/
section P2MDyadicModule40

set_option autoImplicit false

set_option maxHeartbeats 3000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator

open Turing QAlgorithms.Complexity

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9.TM2PlatformSerialization

open RPN

variable {K Λ σ : Type} [DecidableEq K] [Fintype K]
  [DecidableEq Λ] [Fintype Λ] [DecidableEq σ] [Fintype σ]

noncomputable def description (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (input : K) (main : Λ) (initialState : σ) (x : Request) (index : ℕ) : Str :=
  let result := generate program input main initialState x
  lengthToken result.2.2.2 ++
    boundedNat result.2.1 ((result.2.2.1[index]?).getD 0) ++
      serializeWords (instructionWords result.2.1 x.1.length result.2.2.2)

@[fun_prop] theorem description_poly (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (input : K) (main : Λ) (initialState : σ) :
    Poly (fun x : Request × ℕ => description program input main initialState x.1 x.2) := by
  unfold description
  fun_prop

theorem description_eq (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (input : K) (main : Λ) (initialState : σ) (x : Request) (hw : 0 < x.2.1.length)
    (i : Slot K Λ σ x.2.1.length) :
    description program input main initialState x (slotEquiv K Λ σ x.2.1.length i).val =
      encNat (machineProgram hw program input main initialState x.2.2.length x.1.length).ops.length ++
      encNat ((machineProgram hw program input main initialState x.2.2.length x.1.length).output i) ++
      encStr ((machineGates hw program input main initialState x.2.2.length x.1.length).map BooleanGate.code) := by
  let g := generate program input main initialState x
  let m := machineProgram hw program input main initialState x.2.2.length x.1.length
  obtain ⟨hops, hslots, hout⟩ := generate_machineProgram program input main initialState x hw
  have hlt := (machineProgram_valid hw program input main initialState x.2.2.length x.1.length).2 i
  have hi : ((g.2.2.1[(slotEquiv K Λ σ x.2.1.length i).val]?).getD 0) ≤ g.2.1.length := by
    change ((generate program input main initialState x).2.2.1[_]?).getD 0 ≤ _
    rw [hout i, hslots]
    exact hlt.le
  unfold description
  dsimp only
  dsimp only [g] at hi
  rw [boundedNat_eq _ _ hi, hout i, lengthToken_eq, hops, List.length_map]
  rw [instructionWords_gates (total := x.1.length+((machineProgram hw program input main initialState x.2.2.length x.1.length).ops.length+1)) _ _ _ (by omega)
    (machineProgram_valid hw program input main initialState x.2.2.length x.1.length).1
    (by rw [hslots])]
  rw [serializeWords_eq]
  rfl

end InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator

end P2MDyadicModule40

/- Helper module Solutions.RegevBridgeTM2PolyCircuit. -/
section P2MDyadicModule41

set_option autoImplicit false

set_option maxHeartbeats 2500000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace InfoLossLAR.WorstCase.TM2Boolean

open Turing StateTransition QAlgorithms.Complexity

open Integration9_9.TM2OutputLength

open OAI.MetricKMedian.Binary

namespace PolyProgramCircuit

variable {f : Str → Str} (P : PolyProgram id id f)

local instance : DecidableEq P.machine.Label := Classical.decEq _

local instance : DecidableEq P.machine.State := Classical.decEq _

noncomputable def capacity (length : ℕ) : ℕ :=
  length + programPushBound P.machine.code * P.time.eval length + 1

theorem capacity_pos (length : ℕ) : 0 < capacity P length := by unfold capacity; omega

noncomputable def compiled (length : ℕ) :
    MachineProgram P.machine.K P.machine.Label P.machine.State (capacity P length) :=
  machineProgram (capacity_pos P length) P.machine.code P.machine.input P.machine.main P.machine.initial
    (P.time.eval length) length

noncomputable def circuit (length : ℕ) : Layered (length + ((compiled P length).ops.length + 1)) :=
  machineCircuit (capacity_pos P length) P.machine.code P.machine.input P.machine.main P.machine.initial
    (P.time.eval length) length

noncomputable def result (word : Str) : Bits (word.length + ((compiled P word.length).ops.length + 1)) :=
  fun j => BooleanProgram.run word.length (compiled P word.length).ops (wordExtension word) j.val

noncomputable def outputWire (length : ℕ) (i : Fin (capacity P length)) (b : Option Bool) :
    Fin (length + ((compiled P length).ops.length + 1)) :=
  machineOutputWire (capacity_pos P length) P.machine.code P.machine.input P.machine.main P.machine.initial
    (P.time.eval length) length (.inr (.inr (P.machine.output, i, b)))

theorem final_configuration (word : Str) :
    (stickyStep P.machine.code)^[P.time.eval word.length]
      (initialConfiguration P.machine.input P.machine.main P.machine.initial word) =
        P.machine.finalCfg (f word) := by
  have hh := P.outputs word
  change EvalsToInTime (TM2.step P.machine.code)
    (initialConfiguration P.machine.input P.machine.main P.machine.initial word)
    (some (P.machine.finalCfg (f word))) (P.time.eval word.length) at hh
  exact sticky_iterate_of_outputs P.machine.code _ _ _ hh rfl

/-- The real fixed-gate circuit computes the machine's complete deterministic basis output. -/
theorem circuit_basis (word : Str) :
    runLayered (circuit P word.length) (basisInput (toBits word)) = computationalBasis (result P word) :=
  machineCircuit_basis _ _ _ _ _ _ word

/-- An actual output wire gives each present/absent symbol of the encoded function output. -/
theorem output_correct (word : Str) (i : Fin (capacity P word.length)) (b : Option Bool) :
    result P word (outputWire P word.length i b) = decide (b = (f word)[i.val]?) := by
  have hh := machineCircuit_output (capacity_pos P word.length) P.machine.code P.machine.input P.machine.main
    P.machine.initial (P.time.eval word.length) word (by unfold capacity; omega)
    (.inr (.inr (P.machine.output, i, b)))
  rw [final_configuration P word] at hh
  simpa only [result, outputWire, compiled, configurationBit, Machine.finalCfg, ↓reduceIte] using hh

/-- A polynomial counting every configuration field at every actual machine step. -/
noncomputable def spacePolynomial : Polynomial ℕ :=
  (1 + P.time * Polynomial.C (transitionBound P.machine.code 0)) *
    (Polynomial.C (Fintype.card P.machine.Label + 1 + Fintype.card P.machine.State) +
      Polynomial.C (3 * Fintype.card P.machine.K) *
        (Polynomial.X + Polynomial.C (programPushBound P.machine.code) * P.time + 1))

theorem spacePolynomial_eval (length : ℕ) :
    (spacePolynomial P).eval length =
      (1 + P.time.eval length * transitionBound P.machine.code 0) *
        Fintype.card (Slot P.machine.K P.machine.Label P.machine.State (capacity P length)) := by
  simp only [spacePolynomial, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_one,
    Polynomial.eval_C, Polynomial.eval_X, slot_count, capacity]
  ring

theorem ancilla_bound (length : ℕ) : (compiled P length).ops.length ≤ (spacePolynomial P).eval length := by
  rw [spacePolynomial_eval]
  exact machineProgram_length_le _ _ _ _ _ _ _

end PolyProgramCircuit

end InfoLossLAR.WorstCase.TM2Boolean

end

end P2MDyadicModule41

/- Helper module Solutions.RegevBridgeTM2PolyUniform. -/
section P2MDyadicModule42

set_option autoImplicit false

set_option maxHeartbeats 4000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit

open Turing StateTransition QAlgorithms.Complexity Polynomial

open Integration9_9.TM2OutputLength Integration9_9.TM2PlatformSerialization

open Integration9_9.TM2PolynomialBudget

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open CodeGenerator

variable {f : Str → Str} (P : PolyProgram id id f)

local instance : DecidableEq P.machine.Label := Classical.decEq _

local instance : DecidableEq P.machine.State := Classical.decEq _

def capacityPolynomial : Polynomial ℕ := X+C (programPushBound P.machine.code)*P.time+1

theorem capacityPolynomial_eval (n : ℕ) : (capacityPolynomial P).eval n = capacity P n := by
  simp only [capacityPolynomial, eval_add, eval_X, eval_mul, eval_C, eval_one, capacity]

def request (xs : Str) : Request :=
  let slots := xs.map (fun _ => ())
  (slots, List.replicate ((capacityPolynomial P).eval slots.length) (), List.replicate (P.time.eval slots.length) ())

@[fun_prop] theorem request_poly : Poly (request P) := by
  unfold request
  fun_prop

theorem request_unary (n : ℕ) : request P (unary n) =
    (List.replicate n (), List.replicate (capacity P n) (), List.replicate (P.time.eval n) ()) := by
  simp only [request, unary, List.map_replicate, List.length_replicate, capacityPolynomial_eval]

def outputIndex (width : ℕ) : ℕ :=
  Fintype.card (Option P.machine.Label)+(Fintype.card P.machine.State+
    ((Fintype.equivFin (Option Bool) (some true)).val+
      (width*Fintype.card (Option Bool))*(Fintype.equivFin P.machine.K P.machine.output).val))

def descriptionGenerator (xs : Str) : Str :=
  CodeGenerator.description P.machine.code P.machine.input P.machine.main P.machine.initial
    (request P xs) (outputIndex P (request P xs).2.1.length)

@[fun_prop] theorem descriptionGenerator_poly : Poly (descriptionGenerator P) := by
  unfold descriptionGenerator outputIndex
  fun_prop

def booleanFamily : BooleanFamily where
  anc n := (compiled P n).ops.length
  gates n := machineGates (capacity_pos P n) P.machine.code P.machine.input P.machine.main P.machine.initial (P.time.eval n) n
  out n := outputWire P n ⟨0,capacity_pos P n⟩ (some true)

def renderedDescription (width ticks length : ℕ) : Str :=
  if hw : 0 < width then
    let m := machineProgram hw P.machine.code P.machine.input P.machine.main P.machine.initial ticks length
    encNat m.ops.length ++ encNat (m.output (.inr (.inr (P.machine.output,⟨0,hw⟩,some true)))) ++
      encStr ((machineGates hw P.machine.code P.machine.input P.machine.main P.machine.initial ticks length).map BooleanGate.code)
  else []

theorem description_request (x : Request) (hw : 0 < x.2.1.length) :
    CodeGenerator.description P.machine.code P.machine.input P.machine.main P.machine.initial
      x (outputIndex P x.2.1.length) = renderedDescription P x.2.1.length x.2.2.length x.1.length := by
  let i : Slot P.machine.K P.machine.Label P.machine.State x.2.1.length :=
    .inr (.inr (P.machine.output,⟨0,hw⟩,some true))
  have hi : (slotEquiv P.machine.K P.machine.Label P.machine.State x.2.1.length i).val = outputIndex P x.2.1.length := by
    rw [slot_stack_index]
    simp only [outputIndex, Nat.mul_zero, Nat.add_zero, i]
  have he := CodeGenerator.description_eq P.machine.code P.machine.input P.machine.main P.machine.initial x hw i
  rw [hi] at he
  simpa only [renderedDescription, dif_pos hw, i] using he

theorem descriptionGenerator_code (n : ℕ) : descriptionGenerator P (unary n) = (booleanFamily P).code n := by
  have hw : 0 < (request P (unary n)).2.1.length := by
    simp only [request_unary, List.length_replicate]
    exact capacity_pos P n
  unfold descriptionGenerator
  rw [description_request P _ hw]
  simp only [request_unary, List.length_replicate]
  simp only [renderedDescription, dif_pos (capacity_pos P n), BooleanFamily.code, booleanFamily,
    compiled, outputWire, machineOutputWire]

theorem booleanFamily_uniform : (booleanFamily P).Uniform :=
  ⟨descriptionGenerator P, polyTime_of_poly (descriptionGenerator_poly P), descriptionGenerator_code P⟩

theorem booleanFamily_polyBounded : (booleanFamily P).PolyBounded := by
  refine ⟨spacePolynomial P, ?_⟩
  intro n
  constructor
  · simpa only [booleanFamily, machineGates, BooleanProgram.gates_length, compiled] using ancilla_bound P n
  · exact ancilla_bound P n

def family : Family := (booleanFamily P).reversible.compile

theorem family_isQPT : IsQPT (family P) :=
  (booleanFamily P).compile_isQPT (booleanFamily_uniform P) (booleanFamily_polyBounded P)

theorem family_output (n : ℕ) : (family P).out n = outputWire P n ⟨0,capacity_pos P n⟩ (some true) := rfl

end InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit

end

end P2MDyadicModule42

/- Helper module Solutions.RegevBridgeTM2PolyAcceptance. -/
section P2MDyadicModule43

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase

open QAlgorithms.Complexity

theorem computationalBasis_event {n : ℕ} (state : Bits n) (event : Bits n → Bool) :
    (∑ y : Bits n, if event y then ‖computationalBasis state y‖^2 else 0 : ℝ) =
      if event state then 1 else 0 := by
  classical
  calc
    _ = ∑ y : Bits n, if y=state then (if event state then (1:ℝ) else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro y hy
      by_cases he : y=state
      · subst y; simp [computationalBasis]
      · simp [computationalBasis,he]
    _ = _ := by simp

namespace TM2Boolean.PolyProgramCircuit

open OAI.MetricKMedian.Binary

noncomputable section

variable {f : Str → Str} (P : PolyProgram id id f)

local instance : DecidableEq P.machine.Label := Classical.decEq _

local instance : DecidableEq P.machine.State := Classical.decEq _

theorem family_basis (word : Str) :
    runLayered ((family P).circ word.length) (basisInput (toBits word)) = computationalBasis (result P word) :=
  circuit_basis P word

theorem family_acceptProb (word : Str) :
    acceptProb (family P) word = if (f word)[0]? = some true then 1 else 0 := by
  unfold acceptProb
  rw [family_basis]
  rw [computationalBasis_event]
  rw [family_output, output_correct]
  cases h : (f word)[0]? with
  | none => simp [h]
  | some b => cases b <;> simp [h]

end

end TM2Boolean.PolyProgramCircuit

end InfoLossLAR.WorstCase

end P2MDyadicModule43

set_option autoImplicit false
open QAlgorithms.Complexity InfoLossLAR.WorstCase
open InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit

theorem solution (f : Str → Str)
    (hf : Nonempty (OAI.MetricKMedian.Binary.PolyProgram id id f)) :
    ∃ E : Family, IsQPT E ∧ ∀ word : Str,
      acceptProb E word = if (f word)[0]? = some true then 1 else 0 := by
  obtain ⟨P⟩ := hf
  exact ⟨family P, family_isQPT P, family_acceptProb P⟩
