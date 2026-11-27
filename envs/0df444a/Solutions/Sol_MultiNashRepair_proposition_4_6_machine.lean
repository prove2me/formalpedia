-- Prove2me | solution 1 for MultiNashRepair.proposition_4_6_machine
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T04:58:37.858842+00:00
-- url     : https://prove2.me/submissions/423a2673-fe3a-43ff-9c54-93a08cafa048

import Mathlib
import Definitions.Def_CFLOutliers_OutputsWithin
import Definitions.Def_MultiNashRepair_IDRH
import Definitions.Def_NashAmplification_Filtering_Encoding
import Definitions.Def_NashAmplification_Filtering_Model
import Definitions.Def_OAILP_Specification
import Definitions.Def_QuantumMaxCutFiniteNumericRuntime
import Theorems.Thm_MultiNashRepair_lemma_5_12
import Theorems.Thm_MultiNashRepair_proposition_4_6_iterations
import Theorems.Thm_OAI_Optimization_LinearProgramming_strongly_polynomial_optimization

-- ===== L22Br =====

namespace MNRBridge
open OAI.MetricKMedian.Binary Turing

abbrev Sym := OnlineCRS.Combine.Sym

def bitS (b : Bool) : Sym := if b then 1 else 0
def decS (s : Sym) : Bool := decide (s = 1)
def hiS (s : Sym) : Bool := decide (2 ≤ s.val)
def loS (s : Sym) : Bool := decide (s.val % 2 = 1)
def symBits (w : List Sym) : List Bool := w.flatMap (fun s => [hiS s, loS s])
def combine (a b : Option Sym) : Sym :=
  ⟨2 * (if a = some 1 then 1 else 0) + (if b = some 1 then 1 else 0), by split_ifs <;> omega⟩

theorem decS_bitS (b : Bool) : decS (bitS b) = b := by cases b <;> decide
theorem combine_bits (s : Sym) : combine (some (bitS (hiS s))) (some (bitS (loS s))) = s := by
  fin_cases s <;> decide

inductive XS | inp | out | tb | ts deriving DecidableEq
inductive Ph | p1 | p2 | p3 | p4 deriving DecidableEq
instance : Fintype XS := ⟨{.inp, .out, .tb, .ts}, by intro x; cases x <;> simp⟩
instance : Fintype Ph := ⟨{.p1, .p2, .p3, .p4}, by intro x; cases x <;> simp⟩

abbrev Aux := Option Sym × Option Sym

variable (B : Machine)

abbrev BK := B.K ⊕ XS
abbrev BL := B.Label ⊕ Ph
abbrev BS := B.State × Aux

abbrev BStmt := TM2.Stmt (fun _ : BK B => Sym) (BL B) (BS B)

def mapStmt : TM2.Stmt (fun _ : B.K => Bool) B.Label B.State → BStmt B
  | .push k f q => .push (.inl k) (fun v => bitS (f v.1)) (mapStmt q)
  | .peek k f q => .peek (.inl k) (fun v o => (f v.1 (o.map decS), v.2)) (mapStmt q)
  | .pop k f q => .pop (.inl k) (fun v o => (f v.1 (o.map decS), v.2)) (mapStmt q)
  | .load a q => .load (fun v => (a v.1, v.2)) (mapStmt q)
  | .branch f q₁ q₂ => .branch (fun v => f v.1) (mapStmt q₁) (mapStmt q₂)
  | .goto f => .goto (fun v => .inl (f v.1))
  | .halt => .goto (fun _ => .inr .p3)

def code : BL B → BStmt B
  | .inl l => mapStmt B (B.code l)
  | .inr .p1 => .pop (.inr .inp) (fun v o => (v.1, (o, v.2.2)))
      (.branch (fun v => v.2.1.isSome)
        (.push (.inr .tb) (fun v => bitS (hiS (v.2.1.getD 0)))
          (.push (.inr .tb) (fun v => bitS (loS (v.2.1.getD 0))) (.goto (fun _ => .inr .p1))))
        (.goto (fun _ => .inr .p2)))
  | .inr .p2 => .pop (.inr .tb) (fun v o => (v.1, (o, v.2.2)))
      (.branch (fun v => v.2.1.isSome)
        (.push (.inl B.input) (fun v => v.2.1.getD 0) (.goto (fun _ => .inr .p2)))
        (.goto (fun _ => .inl B.main)))
  | .inr .p3 => .pop (.inl B.output) (fun v o => (v.1, (o, v.2.2)))
      (.pop (.inl B.output) (fun v o => (v.1, (v.2.1, o)))
        (.branch (fun v => v.2.1.isSome)
          (.push (.inr .ts) (fun v => combine v.2.1 v.2.2) (.goto (fun _ => .inr .p3)))
          (.goto (fun _ => .inr .p4))))
  | .inr .p4 => .pop (.inr .ts) (fun v o => (v.1, (o, v.2.2)))
      (.branch (fun v => v.2.1.isSome)
        (.push (.inr .out) (fun v => v.2.1.getD 0) (.goto (fun _ => .inr .p4)))
        (.load (fun v => (v.1, (none, none))) .halt))

def tm : FinTM2 where
  K := BK B
  k₀ := .inr .inp
  k₁ := .inr .out
  Γ := fun _ => Sym
  Λ := BL B
  main := .inr .p1
  σ := BS B
  initialState := (B.initial, (none, none))
  m := code B

def embS (S : B.K → List Bool) : BK B → List Sym
  | .inl k => (S k).map bitS
  | .inr _ => []

def embCfg (aux : Aux) (c : TM2.Cfg (fun _ : B.K => Bool) B.Label B.State) :
    TM2.Cfg (fun _ : BK B => Sym) (BL B) (BS B) :=
  ⟨some (match c.l with | some l => .inl l | none => .inr .p3), (c.var, aux), embS B c.stk⟩

theorem embS_update (S : B.K → List Bool) (k : B.K) (x : List Bool) :
    embS B (Function.update S k x) = Function.update (embS B S) (.inl k) (x.map bitS) := by
  funext k'
  rcases k' with k' | k'
  · by_cases h : k' = k
    · subst h; simp [embS]
    · simp [embS, Function.update_of_ne h, Function.update_of_ne (show (Sum.inl k' : BK B) ≠ .inl k by
        simpa using h)]
  · simp [embS]

theorem stepAux_map (q : TM2.Stmt (fun _ : B.K => Bool) B.Label B.State) (v : B.State) (aux : Aux)
    (S : B.K → List Bool) :
    TM2.stepAux (mapStmt B q) (v, aux) (embS B S) = embCfg B aux (TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push k f q ih =>
    simp only [mapStmt, TM2.stepAux]
    rw [← ih]; congr 1
    rw [embS_update]; rfl
  | peek k f q ih =>
    simp only [mapStmt, TM2.stepAux]
    rw [← ih]; congr 2
    simp [embS, List.head?_map, Option.map_map, Function.comp_def, decS_bitS]
  | pop k f q ih =>
    simp only [mapStmt, TM2.stepAux]
    rw [← ih]; congr 1
    · simp [embS, List.head?_map, Option.map_map, Function.comp_def, decS_bitS]
    · rw [embS_update]; simp [embS, List.map_tail]
  | load a q ih =>
    simp only [mapStmt, TM2.stepAux]; exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [mapStmt, TM2.stepAux]
    cases f v <;> simp [ih₁, ih₂]
  | goto f => rfl
  | halt => rfl


abbrev BCfg := TM2.Cfg (fun _ : BK B => Sym) (BL B) (BS B)
abbrev bstep : BCfg B → Option (BCfg B) := TM2.step (code B)

theorem runB (aux : Aux) {n : ℕ} {s t : List Bool}
    (h : Trace B.step n (B.initialCfg s) (B.finalCfg t)) :
    Trace (bstep B) n (embCfg B aux (B.initialCfg s)) (embCfg B aux (B.finalCfg t)) := by
  refine Trace.map (embCfg B aux) ?_ h
  intro a b hab
  rcases a with ⟨l, v, S⟩
  cases l with
  | none => simp [Machine.step, TM2.step] at hab
  | some l =>
    simp only [Machine.step, TM2.step, Option.some.injEq] at hab
    subst hab
    show some (TM2.stepAux (mapStmt B (B.code l)) (v, aux) (embS B S)) = _
    rw [stepAux_map]

theorem phase1 (v : B.State) (b : Option Sym) :
    ∀ (w T : List Sym) (S : BK B → List Sym) (a : Option Sym), S (.inr .inp) = w → S (.inr .tb) = T →
    Trace (bstep B) (w.length + 1) ⟨some (.inr .p1), (v, (a, b)), S⟩
      ⟨some (.inr .p2), (v, (none, b)), Function.update (Function.update S (.inr .inp) [])
        (.inr .tb) (((symBits w).map bitS).reverse ++ T)⟩ := by
  intro w
  induction w with
  | nil =>
    intro T S a h1 h2
    refine Trace.cons ?_ (Trace.refl _)
    simp only [bstep, TM2.step, code, TM2.stepAux, h1, List.head?_nil, Option.isSome_none,
      cond_false, Option.some.injEq]
    congr 1
    funext k
    simp only [Function.update_apply, List.tail_nil, symBits, List.flatMap_nil, List.map_nil,
      List.reverse_nil, List.nil_append]
    split_ifs with hk1 hk2 <;> simp_all
  | cons s w ih =>
    intro T S a h1 h2
    let S1 := Function.update (Function.update (Function.update S (.inr .inp) w) (.inr .tb)
      (bitS (hiS s) :: T)) (.inr .tb) (bitS (loS s) :: bitS (hiS s) :: T)
    have h := ih (bitS (loS s) :: bitS (hiS s) :: T) S1 (some s)
      (by simp [S1, Function.update_apply]) (by simp [S1])
    have heq : Function.update (Function.update S1 (.inr .inp) []) (.inr .tb)
        (((symBits w).map bitS).reverse ++ (bitS (loS s) :: bitS (hiS s) :: T)) =
        Function.update (Function.update S (.inr .inp) []) (.inr .tb)
        (((symBits (s :: w)).map bitS).reverse ++ T) := by
      funext k
      simp only [S1, Function.update_apply, symBits, List.flatMap_cons, List.map_append,
        List.reverse_append, List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil,
        List.nil_append, List.append_assoc, List.cons_append, List.singleton_append]
      split_ifs <;> simp_all
    rw [heq] at h
    refine Trace.cons ?_ h
    simp only [bstep, TM2.step, code, TM2.stepAux, h1, List.head?_cons, Option.isSome_some,
      cond_true, Option.getD_some, Option.some.injEq, List.tail_cons]
    congr 1
    funext k
    simp only [S1, Function.update_apply]
    split_ifs <;> simp_all

theorem phase2 (v : B.State) (b : Option Sym) :
    ∀ (U V : List Sym) (S : BK B → List Sym) (a : Option Sym), S (.inr .tb) = U →
    S (.inl B.input) = V →
    Trace (bstep B) (U.length + 1) ⟨some (.inr .p2), (v, (a, b)), S⟩
      ⟨some (.inl B.main), (v, (none, b)), Function.update (Function.update S (.inr .tb) [])
        (.inl B.input) (U.reverse ++ V)⟩ := by
  intro U
  induction U with
  | nil =>
    intro V S a h1 h2
    refine Trace.cons ?_ (Trace.refl _)
    simp only [bstep, TM2.step, code, TM2.stepAux, h1, List.head?_nil, Option.isSome_none,
      cond_false, Option.some.injEq]
    congr 1
    funext k
    simp only [Function.update_apply, List.tail_nil, List.reverse_nil, List.nil_append]
    split_ifs with hk1 hk2 <;> simp_all
  | cons c U ih =>
    intro V S a h1 h2
    let S1 := Function.update (Function.update S (.inr .tb) U) (.inl B.input) (c :: V)
    have h := ih (c :: V) S1 (some c) (by simp [S1]) (by simp [S1])
    have heq : Function.update (Function.update S1 (.inr .tb) []) (.inl B.input) (U.reverse ++ c :: V) =
        Function.update (Function.update S (.inr .tb) []) (.inl B.input) ((c :: U).reverse ++ V) := by
      funext k
      simp only [S1, Function.update_apply, List.reverse_cons, List.append_assoc, List.cons_append,
        List.nil_append]
      split_ifs <;> simp_all
    rw [heq] at h
    refine Trace.cons ?_ h
    simp only [bstep, TM2.step, code, TM2.stepAux, h1, List.head?_cons, Option.isSome_some,
      cond_true, Option.getD_some, Option.some.injEq, List.tail_cons]
    congr 1
    funext k
    simp only [S1, Function.update_apply]
    split_ifs <;> simp_all

theorem phase3 (v : B.State) :
    ∀ (out T : List Sym) (S : BK B → List Sym) (a b : Option Sym),
    S (.inl B.output) = (symBits out).map bitS → S (.inr .ts) = T →
    Trace (bstep B) (out.length + 1) ⟨some (.inr .p3), (v, (a, b)), S⟩
      ⟨some (.inr .p4), (v, (none, none)), Function.update (Function.update S (.inl B.output) [])
        (.inr .ts) (out.reverse ++ T)⟩ := by
  intro out
  induction out with
  | nil =>
    intro T S a b h1 h2
    refine Trace.cons ?_ (Trace.refl _)
    simp only [symBits, List.flatMap_nil, List.map_nil] at h1
    simp only [bstep, TM2.step, code, TM2.stepAux, h1, List.head?_nil, Option.isSome_none,
      cond_false, Option.some.injEq, Function.update_self, List.tail_nil]
    congr 1
    funext k
    simp only [Function.update_apply, List.reverse_nil, List.nil_append]
    split_ifs with hk1 hk2 <;> simp_all
  | cons s out ih =>
    intro T S a b h1 h2
    have h1' : S (.inl B.output) = bitS (hiS s) :: bitS (loS s) :: (symBits out).map bitS := by
      rw [h1]; simp [symBits]
    let S1 := Function.update (Function.update (Function.update S (.inl B.output)
      (bitS (loS s) :: (symBits out).map bitS)) (.inl B.output) ((symBits out).map bitS))
      (.inr .ts) (s :: T)
    have h := ih (s :: T) S1 (some (bitS (hiS s))) (some (bitS (loS s))) (by simp [S1]) (by simp [S1])
    have heq : Function.update (Function.update S1 (.inl B.output) []) (.inr .ts) (out.reverse ++ s :: T) =
        Function.update (Function.update S (.inl B.output) []) (.inr .ts) ((s :: out).reverse ++ T) := by
      funext k
      simp only [S1, Function.update_apply, List.reverse_cons, List.append_assoc, List.cons_append,
        List.nil_append]
      split_ifs <;> simp_all
    rw [heq] at h
    refine Trace.cons ?_ h
    simp only [bstep, TM2.step, code, TM2.stepAux, h1', List.head?_cons, Option.isSome_some,
      cond_true, Option.getD_some, Option.some.injEq, List.tail_cons, Function.update_self]
    congr 1
    funext k
    simp only [S1, Function.update_apply, combine_bits]
    split_ifs <;> simp_all

theorem phase4 (v : B.State) :
    ∀ (U V : List Sym) (S : BK B → List Sym) (a b : Option Sym), S (.inr .ts) = U →
    S (.inr .out) = V →
    Trace (bstep B) (U.length + 1) ⟨some (.inr .p4), (v, (a, b)), S⟩
      ⟨none, (v, (none, none)), Function.update (Function.update S (.inr .ts) [])
        (.inr .out) (U.reverse ++ V)⟩ := by
  intro U
  induction U with
  | nil =>
    intro V S a b h1 h2
    refine Trace.cons ?_ (Trace.refl _)
    simp only [bstep, TM2.step, code, TM2.stepAux, h1, List.head?_nil, Option.isSome_none,
      cond_false, Option.some.injEq]
    congr 1
    funext k
    simp only [Function.update_apply, List.tail_nil, List.reverse_nil, List.nil_append]
    split_ifs with hk1 hk2 <;> simp_all
  | cons c U ih =>
    intro V S a b h1 h2
    let S1 := Function.update (Function.update S (.inr .ts) U) (.inr .out) (c :: V)
    have h := ih (c :: V) S1 (some c) b (by simp [S1]) (by simp [S1])
    have heq : Function.update (Function.update S1 (.inr .ts) []) (.inr .out) (U.reverse ++ c :: V) =
        Function.update (Function.update S (.inr .ts) []) (.inr .out) ((c :: U).reverse ++ V) := by
      funext k
      simp only [S1, Function.update_apply, List.reverse_cons, List.append_assoc, List.cons_append,
        List.nil_append]
      split_ifs <;> simp_all
    rw [heq] at h
    refine Trace.cons ?_ h
    simp only [bstep, TM2.step, code, TM2.stepAux, h1, List.head?_cons, Option.isSome_some,
      cond_true, Option.getD_some, Option.some.injEq, List.tail_cons]
    congr 1
    funext k
    simp only [S1, Function.update_apply]
    split_ifs <;> simp_all

theorem init_eq (w : List Sym) : initList (tm B) w =
    (⟨some (.inr .p1), (B.initial, (none, none)), fun k => if k = .inr .inp then w else []⟩ : BCfg B) :=
  rfl

theorem halt_eq (w : List Sym) : haltList (tm B) w =
    (⟨none, (B.initial, (none, none)), fun k => if k = .inr .out then w else []⟩ : BCfg B) :=
  rfl

theorem run_full {w out : List Sym} {n : ℕ}
    (h : Trace B.step n (B.initialCfg (symBits w)) (B.finalCfg (symBits out))) :
    Trace (bstep B) (w.length + 1 + ((symBits w).length + 1) + n + (out.length + 1) + (out.length + 1))
      (initList (tm B) w) (haltList (tm B) out) := by
  rw [init_eq, halt_eq]
  let S0 : BK B → List Sym := fun k => if k = .inr .inp then w else []
  have h1 := phase1 B B.initial none w [] S0 none (by simp [S0]) (by simp [S0])
  have h2 := phase2 B B.initial none (((symBits w).map bitS).reverse ++ []) []
    (Function.update (Function.update S0 (.inr .inp) []) (.inr .tb) (((symBits w).map bitS).reverse ++ []))
    none (by simp) (by simp [S0, Function.update_apply])
  have e2 : Function.update (Function.update (Function.update (Function.update S0 (.inr .inp) [])
      (.inr .tb) (((symBits w).map bitS).reverse ++ [])) (.inr .tb) []) (.inl B.input)
      ((((symBits w).map bitS).reverse ++ []).reverse ++ []) =
      embS B (fun k => if k = B.input then symBits w else []) := by
    funext k
    rcases k with k | k
    · by_cases hk : k = B.input
      · subst hk; simp [embS]
      · simp [embS, Function.update_apply, hk, S0]
    · cases k <;> simp [embS, Function.update_apply, S0]
  rw [e2] at h2
  have h3 := runB B (none, none) h
  have e3 : (⟨some (.inl B.main), (B.initial, (none, none)),
      embS B (fun k => if k = B.input then symBits w else [])⟩ : BCfg B) =
      embCfg B (none, none) (B.initialCfg (symBits w)) := rfl
  rw [e3] at h2
  have e4 : embCfg B (none, none) (B.finalCfg (symBits out)) =
      (⟨some (.inr .p3), (B.initial, (none, none)),
        embS B (fun k => if k = B.output then symBits out else [])⟩ : BCfg B) := rfl
  rw [e4] at h3
  have h4 := phase3 B B.initial out [] (embS B (fun k => if k = B.output then symBits out else []))
    none none (by simp [embS]) (by simp [embS])
  have h5 := phase4 B B.initial (out.reverse ++ []) []
    (Function.update (Function.update (embS B (fun k => if k = B.output then symBits out else []))
      (.inl B.output) []) (.inr .ts) (out.reverse ++ [])) none none (by simp) (by simp [embS, Function.update_apply])
  have e5 : Function.update (Function.update (Function.update (Function.update
      (embS B (fun k => if k = B.output then symBits out else [])) (.inl B.output) [])
      (.inr .ts) (out.reverse ++ [])) (.inr .ts) []) (.inr .out) ((out.reverse ++ []).reverse ++ []) =
      fun k => if k = .inr .out then out else [] := by
    funext k
    rcases k with k | k
    · by_cases hk : k = B.output
      · subst hk; simp [embS]
      · simp [embS, Function.update_apply, hk]
    · cases k <;> simp [embS, Function.update_apply]
  rw [e5] at h5
  have := (((h1.trans h2).trans h3).trans h4).trans h5
  simpa using this

theorem symBits_length (w : List Sym) : (symBits w).length = 2 * w.length := by
  induction w with
  | nil => rfl
  | cons s w ih => simp [symBits] at ih ⊢; omega

theorem poly_bound (p : Polynomial ℕ) : ∃ c : ℕ, ∀ n : ℕ, p.eval n ≤ c * (n + 2) ^ c := by
  refine ⟨(∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i) + p.natDegree + 1, fun n => ?_⟩
  set C := ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i
  set c := C + p.natDegree + 1
  rw [Polynomial.eval_eq_sum_range]
  have h1 : ∀ i ∈ Finset.range (p.natDegree + 1), p.coeff i * n ^ i ≤ p.coeff i * (n + 2) ^ c := by
    intro i hi
    apply Nat.mul_le_mul_left
    have hi' : i ≤ c := by simp at hi; omega
    calc n ^ i ≤ (n + 2) ^ i := Nat.pow_le_pow_left (by omega) i
      _ ≤ (n + 2) ^ c := Nat.pow_le_pow_right (by omega) hi'
  calc _ ≤ ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * (n + 2) ^ c := Finset.sum_le_sum h1
    _ = C * (n + 2) ^ c := by rw [← Finset.sum_mul]
    _ ≤ c * (n + 2) ^ c := Nat.mul_le_mul_right _ (by omega)

theorem outputsWithin_of_trace (w out : List Sym) (N t : ℕ)
    (h : Trace (bstep B) N (initList (tm B) w) (haltList (tm B) out)) (hN : N ≤ t) :
    CFLOutliers.OutputsWithin ⟨tm B, Equiv.refl Sym, Equiv.refl Sym⟩ w out t := by
  unfold CFLOutliers.OutputsWithin
  refine ⟨⟨⟨N, ?_⟩, hN⟩⟩
  show (flip bind (bstep B))^[N] (some (initList (tm B) (w.map (id : Sym → Sym)))) =
    some (haltList (tm B) (out.map (id : Sym → Sym)))
  have e1 : @List.map Sym ((tm B).Γ (tm B).k₀) id w = w := List.map_id w
  have e2 : @List.map Sym ((tm B).Γ (tm B).k₁) id out = out := List.map_id out
  rw [e1, e2]
  exact h.iterate_eq

theorem bridge {α β : Type} {ea : α → List Sym} {eb : β → List Sym} {f : α → β}
    (P : PolyProgram (fun a => symBits (ea a)) (fun b => symBits (eb b)) f) :
    ∃ (M : TM2ComputableAux Sym Sym) (c : ℕ), ∀ a,
      CFLOutliers.OutputsWithin M (ea a) (eb (f a)) (c * ((ea a).length + 2) ^ c) := by
  let Q : Polynomial ℕ := 3 * Polynomial.X + 4 + P.time.comp (2 * Polynomial.X) +
    2 * P.sizeBound.comp (2 * Polynomial.X)
  obtain ⟨c, hc⟩ := poly_bound Q
  refine ⟨⟨tm P.machine, Equiv.refl Sym, Equiv.refl Sym⟩, c, fun a => ?_⟩
  have hP := P.outputs a
  have tP : Trace P.machine.step hP.steps (P.machine.initialCfg (symBits (ea a)))
      (P.machine.finalCfg (symBits (eb (f a)))) := Trace.of_iterate hP.evals_in_steps
  have hrun := run_full P.machine tP
  have hsteps := hP.steps_le_m
  have hlen := P.length_bound a
  simp only [symBits_length] at hlen hsteps hrun
  have hout : (eb (f a)).length ≤ 2 * (eb (f a)).length := by omega
  refine outputsWithin_of_trace P.machine _ _ _ _ hrun ?_
  refine le_trans ?_ (hc (ea a).length)
  simp only [Q, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X,
    Polynomial.eval_comp]
  omega

end MNRBridge

-- ===== L22A =====

namespace MNRL22
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

@[fun_prop] theorem poly_nat_div : Poly (fun x : ℕ × ℕ => x.1 / x.2) := ⟨PolyProgram.natDiv⟩
@[fun_prop] theorem poly_nat_mod : Poly (fun x : ℕ × ℕ => x.1 % x.2) := ⟨PolyProgram.natMod⟩
@[fun_prop] theorem poly_rat_prod : Poly (List.prod : List ℚ → ℚ) := ⟨PolyProgram.ratProd⟩
@[fun_prop] theorem poly_rat_sum : Poly (List.sum : List ℚ → ℚ) := ⟨PolyProgram.ratSum⟩
@[fun_prop] theorem poly_rat_num : Poly Rat.num := ⟨PolyProgram.ratNum⟩
@[fun_prop] theorem poly_rat_den : Poly Rat.den := ⟨PolyProgram.ratDen⟩
@[fun_prop] theorem poly_int_natAbs : Poly Int.natAbs := ⟨PolyProgram.intAbs⟩
@[fun_prop] theorem poly_list_drop {α : Type} [Coding α] [Inhabited α] :
    Poly (fun x : List α × ℕ => x.1.drop x.2) := ⟨PolyProgram.listDrop enc default⟩

section comp
variable {α : Type} [Coding α]
@[fun_prop] theorem nat_add_comp {f g : α → ℕ} (hf : Poly f) (hg : Poly g) : Poly (fun x => f x + g x) :=
  Poly.comp Poly.nat_add (Poly.pair hf hg)
@[fun_prop] theorem nat_mul_comp {f g : α → ℕ} (hf : Poly f) (hg : Poly g) : Poly (fun x => f x * g x) :=
  Poly.comp Poly.nat_mul (Poly.pair hf hg)
@[fun_prop] theorem nat_div_comp {f g : α → ℕ} (hf : Poly f) (hg : Poly g) : Poly (fun x => f x / g x) :=
  Poly.comp poly_nat_div (Poly.pair hf hg)
@[fun_prop] theorem nat_mod_comp {f g : α → ℕ} (hf : Poly f) (hg : Poly g) : Poly (fun x => f x % g x) :=
  Poly.comp poly_nat_mod (Poly.pair hf hg)
@[fun_prop] theorem rat_add_comp {f g : α → ℚ} (hf : Poly f) (hg : Poly g) : Poly (fun x => f x + g x) :=
  Poly.comp Poly.rat_add (Poly.pair hf hg)
@[fun_prop] theorem rat_mul_comp {f g : α → ℚ} (hf : Poly f) (hg : Poly g) : Poly (fun x => f x * g x) :=
  Poly.comp Poly.rat_mul (Poly.pair hf hg)
@[fun_prop] theorem rat_div_comp {f g : α → ℚ} (hf : Poly f) (hg : Poly g) : Poly (fun x => f x / g x) :=
  Poly.comp Poly.rat_div (Poly.pair hf hg)
@[fun_prop] theorem rat_cast_comp {f : α → ℕ} (hf : Poly f) : Poly (fun x => (f x : ℚ)) :=
  Poly.comp Poly.rat_ofNat hf
@[fun_prop] theorem rat_prod_comp {f : α → List ℚ} (hf : Poly f) : Poly (fun x => (f x).prod) :=
  Poly.comp poly_rat_prod hf
@[fun_prop] theorem rat_sum_comp {f : α → List ℚ} (hf : Poly f) : Poly (fun x => (f x).sum) :=
  Poly.comp poly_rat_sum hf
@[fun_prop] theorem rat_num_comp {f : α → ℚ} (hf : Poly f) : Poly (fun x => (f x).num) :=
  Poly.comp poly_rat_num hf
@[fun_prop] theorem rat_den_comp {f : α → ℚ} (hf : Poly f) : Poly (fun x => (f x).den) :=
  Poly.comp poly_rat_den hf
@[fun_prop] theorem int_natAbs_comp {f : α → ℤ} (hf : Poly f) : Poly (fun x => (f x).natAbs) :=
  Poly.comp poly_int_natAbs hf
@[fun_prop] theorem list_drop_comp {β : Type} [Coding β] [Inhabited β] {f : α → List β} {g : α → ℕ}
    (hf : Poly f) (hg : Poly g) : Poly (fun x => (f x).drop (g x)) :=
  Poly.comp poly_list_drop (Poly.pair hf hg)
@[fun_prop] theorem list_length_comp {β : Type} [Coding β] [Inhabited β] {f : α → List β}
    (hf : Poly f) : Poly (fun x => (f x).length) :=
  Poly.comp Poly.list_length hf
@[fun_prop] theorem list_range_length_comp {β : Type} [Coding β] [Inhabited β] {f : α → List β}
    (hf : Poly f) : Poly (fun x => List.range (f x).length) :=
  Poly.comp (f := fun xs : List β => List.range xs.length) Poly.list_indices hf
theorem poly_filter_lt : Poly (fun x : List ℕ × ℕ => x.1.filter (fun i => decide (i < x.2))) :=
  Poly.list_filter (f := fun (x : List ℕ × ℕ) (i : ℕ) => decide (i < x.2))
    (Poly.nat_lt_comp Poly.snd (Poly.comp Poly.snd Poly.fst)) Poly.fst
@[fun_prop] theorem filter_lt_comp {f : α → List ℕ} {g : α → ℕ} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => (f x).filter (fun i => decide (i < g x))) :=
  Poly.comp poly_filter_lt (Poly.pair hf hg)
end comp

abbrev Ctx := List ℕ × List ℚ

noncomputable def NOf (c : Ctx) : ℕ := c.2.length / c.1.length
noncomputable def rng (c : Ctx) (n : ℕ) : List ℕ := (List.range c.2.length).filter (fun i => decide (i < n))
noncomputable def stride (c : Ctx) (j : ℕ) : ℕ :=
  (((c.1.drop (j + 1)).map (fun n : ℕ => (n : ℚ))).prod).num.natAbs
noncomputable def digit (c : Ctx) (j pos : ℕ) : ℕ := (pos / stride c j) % (c.1[j]?.getD 0)
def prob (y : List (List ℚ)) (j a : ℕ) : ℚ := (y[j]?.getD [])[a]?.getD 0
noncomputable def weight (c : Ctx) (y : List (List ℚ)) (pos : ℕ) : ℚ :=
  ((List.range c.1.length).map (fun j => prob y j (digit c j pos))).prod
noncomputable def payoff (c : Ctx) (y : List (List ℚ)) (r : ℕ) : ℚ :=
  ((rng c (NOf c)).map (fun pos => weight c y pos * (c.2[r * NOf c + pos]?.getD 0))).sum

theorem poly_NOf : Poly (fun c : Ctx => NOf c) := by unfold NOf; fun_prop
theorem poly_rng : Poly (fun x : Ctx × ℕ => rng x.1 x.2) := by unfold rng; fun_prop
theorem poly_digit : Poly (fun x : Ctx × ℕ × ℕ => digit x.1 x.2.1 x.2.2) := by unfold digit stride; fun_prop
theorem poly_prob : Poly (fun x : List (List ℚ) × ℕ × ℕ => prob x.1 x.2.1 x.2.2) := by unfold prob; fun_prop
section comp2
variable {α : Type} [Coding α]
@[fun_prop] theorem NOf_comp {f : α → Ctx} (hf : Poly f) : Poly (fun x => NOf (f x)) := Poly.comp (f := fun c : Ctx => NOf c) poly_NOf hf
@[fun_prop] theorem rng_comp {f : α → Ctx} {g : α → ℕ} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => rng (f x) (g x)) := Poly.comp (f := fun x : Ctx × ℕ => rng x.1 x.2) poly_rng (Poly.pair hf hg)
@[fun_prop] theorem digit_comp {f : α → Ctx} {g h : α → ℕ} (hf : Poly f) (hg : Poly g) (hh : Poly h) :
    Poly (fun x => digit (f x) (g x) (h x)) := Poly.comp (f := fun x : Ctx × ℕ × ℕ => digit x.1 x.2.1 x.2.2) poly_digit (Poly.pair hf (Poly.pair hg hh))
@[fun_prop] theorem prob_comp {f : α → List (List ℚ)} {g h : α → ℕ} (hf : Poly f) (hg : Poly g) (hh : Poly h) :
    Poly (fun x => prob (f x) (g x) (h x)) := Poly.comp (f := fun x : List (List ℚ) × ℕ × ℕ => prob x.1 x.2.1 x.2.2) poly_prob (Poly.pair hf (Poly.pair hg hh))
end comp2

theorem poly_weight : Poly (fun x : Ctx × List (List ℚ) × ℕ => weight x.1 x.2.1 x.2.2) := by
  unfold weight; fun_prop
@[fun_prop] theorem weight_comp {α : Type} [Coding α] {f : α → Ctx} {g : α → List (List ℚ)} {h : α → ℕ}
    (hf : Poly f) (hg : Poly g) (hh : Poly h) :
    Poly (fun x => weight (f x) (g x) (h x)) := Poly.comp (f := fun x : Ctx × List (List ℚ) × ℕ => weight x.1 x.2.1 x.2.2) poly_weight (Poly.pair hf (Poly.pair hg hh))
theorem poly_payoff : Poly (fun x : Ctx × List (List ℚ) × ℕ => payoff x.1 x.2.1 x.2.2) := by
  unfold payoff; fun_prop
@[fun_prop] theorem payoff_comp {α : Type} [Coding α] {f : α → Ctx} {g : α → List (List ℚ)} {h : α → ℕ}
    (hf : Poly f) (hg : Poly g) (hh : Poly h) :
    Poly (fun x => payoff (f x) (g x) (h x)) := Poly.comp (f := fun x : Ctx × List (List ℚ) × ℕ => payoff x.1 x.2.1 x.2.2) poly_payoff (Poly.pair hf (Poly.pair hg hh))

def mixVal (j b a : ℕ) : ℚ :=
  if j = 0 then (if a = b then 1 else 0)
  else (if a = 0 then (j : ℚ) / ((j : ℚ) + 1) else 0) + (if a = b then 1 / ((j : ℚ) + 1) else 0)
noncomputable def mixRow (c : Ctx) (j b : ℕ) : List ℚ := (rng c (c.1[j]?.getD 0)).map (fun a => mixVal j b a)
noncomputable def pureRow (c : Ctx) (j b : ℕ) : List ℚ :=
  (rng c (c.1[j]?.getD 0)).map (fun a => if a = b then (1 : ℚ) else 0)
noncomputable def profAt (c : Ctx) (bs : List ℕ) (r cc : ℕ) : List (List ℚ) :=
  (List.range c.1.length).map (fun j =>
    if j < r then mixRow c j (bs[j]?.getD 0) else if j = r then pureRow c j cc else pureRow c j 0)
noncomputable def vals (c : Ctx) (bs : List ℕ) (r : ℕ) : List ℚ :=
  (rng c (c.1[r]?.getD 0)).map (fun cc => payoff c (profAt c bs r cc) r)

theorem poly_mixRow : Poly (fun x : Ctx × ℕ × ℕ => mixRow x.1 x.2.1 x.2.2) := by
  unfold mixRow mixVal; fun_prop
@[fun_prop] theorem mixRow_comp {α : Type} [Coding α] {f : α → Ctx} {g h : α → ℕ}
    (hf : Poly f) (hg : Poly g) (hh : Poly h) :
    Poly (fun x => mixRow (f x) (g x) (h x)) := Poly.comp (f := fun x : Ctx × ℕ × ℕ => mixRow x.1 x.2.1 x.2.2) poly_mixRow (Poly.pair hf (Poly.pair hg hh))
theorem poly_pureRow : Poly (fun x : Ctx × ℕ × ℕ => pureRow x.1 x.2.1 x.2.2) := by
  unfold pureRow; fun_prop
@[fun_prop] theorem pureRow_comp {α : Type} [Coding α] {f : α → Ctx} {g h : α → ℕ}
    (hf : Poly f) (hg : Poly g) (hh : Poly h) :
    Poly (fun x => pureRow (f x) (g x) (h x)) := Poly.comp (f := fun x : Ctx × ℕ × ℕ => pureRow x.1 x.2.1 x.2.2) poly_pureRow (Poly.pair hf (Poly.pair hg hh))
theorem poly_profAt : Poly (fun x : Ctx × List ℕ × ℕ × ℕ => profAt x.1 x.2.1 x.2.2.1 x.2.2.2) := by
  unfold profAt; fun_prop
@[fun_prop] theorem profAt_comp {α : Type} [Coding α] {f : α → Ctx} {g : α → List ℕ} {h k : α → ℕ}
    (hf : Poly f) (hg : Poly g) (hh : Poly h) (hk : Poly k) :
    Poly (fun x => profAt (f x) (g x) (h x) (k x)) :=
  Poly.comp (f := fun x : Ctx × List ℕ × ℕ × ℕ => profAt x.1 x.2.1 x.2.2.1 x.2.2.2) poly_profAt (Poly.pair hf (Poly.pair hg (Poly.pair hh hk)))

theorem list_all {α β : Type} [Coding α] [Coding β] [Inhabited β] {f : α → β → Bool} {as : α → List β}
    (hf : Poly (fun x : α × β => f x.1 x.2)) (ha : Poly as) : Poly (fun x => (as x).all (f x)) :=
  ⟨(((PolyProgram.identity enc).fanout ha.program).comp (hf.program.listAllWith default)).congr _
    (fun _ => rfl)⟩

theorem poly_vals : Poly (fun x : Ctx × List ℕ × ℕ => vals x.1 x.2.1 x.2.2) := by
  unfold vals; fun_prop

noncomputable def br (c : Ctx) (bs : List ℕ) (r : ℕ) : ℕ :=
  (vals c bs r).findIdx (fun v => (vals c bs r).all (fun v' => decide (v' ≤ v)))

theorem poly_br : Poly (fun x : Ctx × List ℕ × ℕ => br x.1 x.2.1 x.2.2) := by
  unfold br
  refine Poly.list_findIdx (f := fun (x : Ctx × List ℕ × ℕ) (v : ℚ) =>
    (vals x.1 x.2.1 x.2.2).all (fun v' => decide (v' ≤ v))) ?_ poly_vals
  refine list_all (f := fun (p : (Ctx × List ℕ × ℕ) × ℚ) (v' : ℚ) => decide (v' ≤ p.2)) ?_ ?_
  · exact Poly.rat_le_comp (Poly.comp Poly.snd Poly.identity) (Poly.comp Poly.snd Poly.fst)
  · exact Poly.comp (f := fun x : Ctx × List ℕ × ℕ => vals x.1 x.2.1 x.2.2) poly_vals Poly.fst

theorem foldl_pair {γ α β : Type} (op : (γ × β) × α → β) (c : γ) (pre : List α) (b : β) :
    pre.foldl (fun (s : γ × β) a => (s.1, op (s, a))) (c, b) = (c, pre.foldl (fun b a => op ((c, b), a)) b) := by
  induction pre generalizing b with
  | nil => rfl
  | cons a pre ih => simp only [List.foldl_cons]; exact ih _

theorem poly_foldl_ctx {γ α β : Type} [Coding γ] [Coding α] [Coding β] [Inhabited α]
    (op : (γ × β) × α → β) (hop : Poly op) (B : Polynomial ℕ)
    (hB : ∀ (c : γ) (as : List α) (b : β) (pre suf : List α), as = pre ++ suf →
      (enc (c, pre.foldl (fun b a => op ((c, b), a)) b)).length ≤ B.eval (enc (as, (c, b))).length) :
    Poly (fun x : γ × (List α × β) => x.2.1.foldl (fun b a => op ((x.1, b), a)) x.2.2) := by
  let op' : (γ × β) × α → γ × β := fun p => (p.1.1, op p)
  have hop' : Poly op' := Poly.pair (Poly.comp Poly.fst Poly.fst) hop
  have L := PolyProgram.listFold (ea := (enc : α → List Bool)) (eb := (enc : γ × β → List Bool))
    hop'.program default B (by
      intro as b pre suf he
      have h1 := foldl_pair op b.1 pre b.2
      have h2 := hB b.1 as b.2 pre suf he
      simp only [op'] at h1 ⊢
      rw [show (b.1, b.2) = b from rfl] at h1
      rw [h1]; exact h2)
  have hL : Poly (fun x : List α × (γ × β) => x.1.foldl (fun b a => op' (b, a)) x.2) := ⟨L⟩
  have hR : Poly (fun x : γ × (List α × β) =>
      (x.2.1.foldl (fun b a => op' (b, a)) (x.1, x.2.2)).2) :=
    Poly.comp Poly.snd (Poly.comp hL (Poly.pair (Poly.comp Poly.fst Poly.snd)
      (Poly.pair Poly.fst (Poly.comp Poly.snd Poly.snd))))
  have heq : (fun x : γ × (List α × β) => (x.2.1.foldl (fun b a => op' (b, a)) (x.1, x.2.2)).2) =
      (fun x => x.2.1.foldl (fun b a => op ((x.1, b), a)) x.2.2) := by
    funext x
    have := foldl_pair op x.1 x.2.1 x.2.2
    simp only [op'] at this ⊢
    rw [this]
  rw [heq] at hR; exact hR

noncomputable def stepBR (p : (Ctx × List ℕ) × ℕ) : List ℕ := p.1.2 ++ [br p.1.1 p.1.2 p.2]
noncomputable def bsFinal (c : Ctx) : List ℕ :=
  (List.range c.1.length).foldl (fun bs r => stepBR ((c, bs), r)) []

theorem bits_len_le (n : ℕ) : n.bits.length ≤ n := by
  have h := Nat.size_eq_bits_len n
  have h2 : n.size ≤ n := Nat.size_le.2 Nat.lt_two_pow_self
  omega

theorem br_le (c : Ctx) (bs : List ℕ) (r : ℕ) : br c bs r ≤ c.2.length := by
  unfold br
  refine (List.findIdx_le_length).trans ?_
  unfold vals rng
  simp only [List.length_map]
  exact (List.length_filter_le _ _).trans (by simp)

theorem foldl_stepBR (c : Ctx) (pre : List ℕ) (b : List ℕ) :
    ∃ ext : List ℕ, pre.foldl (fun bs r => stepBR ((c, bs), r)) b = b ++ ext ∧ ext.length = pre.length ∧
      ∀ e ∈ ext, e ≤ c.2.length := by
  induction pre generalizing b with
  | nil => exact ⟨[], by simp, rfl, by simp⟩
  | cons a pre ih =>
    obtain ⟨ext, h1, h2, h3⟩ := ih (b ++ [br c b a])
    refine ⟨br c b a :: ext, ?_, by simp [h2], ?_⟩
    · simp only [List.foldl_cons, stepBR] at h1 ⊢; rw [h1]; simp
    · intro e he
      rcases List.mem_cons.mp he with rfl | he
      · exact br_le c b a
      · exact h3 e he

theorem poly_stepBR : Poly stepBR := by
  unfold stepBR
  have := poly_br
  fun_prop

theorem poly_bsFinal : Poly bsFinal := by
  have hF := poly_foldl_ctx (γ := Ctx) (α := ℕ) (β := List ℕ) stepBR poly_stepBR
    (Polynomial.X + Polynomial.X * Polynomial.X) (by
      intro c as b pre suf he
      obtain ⟨ext, h1, h2, h3⟩ := foldl_stepBR c pre b
      rw [h1]
      have hc : c.2.length ≤ (enc c).length := by
        show c.2.length ≤ (encodePair (encodeList Nat.bits) (encodeList Ratio.encode) c).length
        rw [encodePair_length]
        have := EncodedList.length_le Ratio.encode c.2
        omega
      have hext : (encodeList Nat.bits ext).length ≤ ext.length * (2 * (enc c).length + 1) :=
        EncodedList.length_bound Nat.bits ext _ (fun e he => (bits_len_le e).trans ((h3 e he).trans hc))
      have hpre : pre.length ≤ (enc as).length := by
        have := EncodedList.length_le Nat.bits as
        have hl : pre.length ≤ as.length := by rw [he]; simp
        exact hl.trans this
      show (encodePair enc (encodeList Nat.bits) (c, b ++ ext)).length ≤
        Polynomial.eval (encodePair (encodeList Nat.bits) (encodePair enc (encodeList Nat.bits)) (as, (c, b))).length
          (Polynomial.X + Polynomial.X * Polynomial.X)
      simp only [encodePair_length, EncodedList.append, List.length_append, Polynomial.eval_add,
        Polynomial.eval_mul, Polynomial.eval_X]
      set T := 2 * (encodeList Nat.bits as).length + 1 + (2 * (enc c).length + 1 + (encodeList Nat.bits b).length)
      have hT1 : (enc as).length ≤ T := by show (encodeList Nat.bits as).length ≤ T; omega
      have hT2 : 2 * (enc c).length + 1 ≤ T := by omega
      rw [h2] at hext
      have : pre.length * (2 * (enc c).length + 1) ≤ T * T := Nat.mul_le_mul (hpre.trans hT1) hT2
      omega)
  have := Poly.comp hF (Poly.pair Poly.identity (Poly.pair (Poly.comp Poly.list_indices Poly.fst)
    (Automatic.Poly.const (α := Ctx) ([] : List ℕ))))
  exact this

@[fun_prop] theorem bsFinal_comp {α : Type} [Coding α] {f : α → Ctx} (hf : Poly f) :
    Poly (fun x => bsFinal (f x)) := Poly.comp (f := bsFinal) poly_bsFinal hf

theorem poly_flatten {β : Type} [Coding β] [Inhabited β] : Poly (List.flatten : List (List β) → List β) :=
  ⟨PolyProgram.listFlatten enc default⟩
@[fun_prop] theorem flatten_comp {α β : Type} [Coding α] [Coding β] [Inhabited β] {f : α → List (List β)}
    (hf : Poly f) : Poly (fun x => (f x).flatten) := Poly.comp (f := List.flatten) poly_flatten hf

noncomputable def xFinal (c : Ctx) : List (List ℚ) :=
  (List.range c.1.length).map (fun j => mixRow c j ((bsFinal c)[j]?.getD 0))
noncomputable def outItems (c : Ctx) : List (List ℕ) :=
  c.1.map (fun n => [n]) ++ ((xFinal c).flatten).map (fun q => [q.num.natAbs, q.den, 0])
def ctxOf (items : List (List ℕ)) : Ctx :=
  ((items.filter (fun it => decide (it.length = 1))).map (fun it => it.head?.getD 0),
   (items.filter (fun it => !decide (it.length = 1))).map
     (fun it => ((it[0]?.getD 0 : ℕ) : ℚ) / ((it[1]?.getD 0 : ℕ) : ℚ)))
noncomputable def Falg (items : List (List ℕ)) : List (List ℕ) := outItems (ctxOf items)

theorem poly_xFinal : Poly xFinal := by unfold xFinal; fun_prop
theorem poly_outItems : Poly outItems := by
  unfold outItems
  have := poly_xFinal
  fun_prop
theorem poly_ctxOf : Poly ctxOf := by
  unfold ctxOf
  have h1 : Poly (fun items : List (List ℕ) => items.filter (fun it => decide (it.length = 1))) :=
    Poly.list_filter (f := fun (_ : List (List ℕ)) (it : List ℕ) => decide (it.length = 1))
      (by fun_prop) Poly.identity
  have h2 : Poly (fun items : List (List ℕ) => items.filter (fun it => !decide (it.length = 1))) :=
    Poly.list_filter (f := fun (_ : List (List ℕ)) (it : List ℕ) => !decide (it.length = 1))
      (by fun_prop) Poly.identity
  fun_prop
theorem poly_Falg : Poly Falg := Poly.comp (f := outItems) poly_outItems poly_ctxOf

end MNRL22

-- ===== L22B =====

namespace MNRL22
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic MNRBridge
open NashAmplification.Filtering OnlineCRS.Combine

def hIn (s : MNRBridge.Sym) : List Bool :=
  if s = 0 then [true, true, true, false] else if s = 1 then [true, true, true, true]
  else if s = 2 then [true, false] else [true, false, false]

def symOf (h l : Bool) : MNRBridge.Sym := ⟨2 * h.toNat + l.toNat, by cases h <;> cases l <;> decide⟩

theorem symOf_bits (s : MNRBridge.Sym) : symOf (hiS s) (loS s) = s := by
  fin_cases s <;> rfl

def Tin : Transducer where
  Q := Option Bool
  initial := none
  next q b := match q with
    | none => (some b, [])
    | some h => (none, hIn (symOf h b))
  finish _ := []

theorem Tin_run (w : List MNRBridge.Sym) : Tin.run none (symBits w) = w.flatMap hIn := by
  induction w with
  | nil => rfl
  | cons s w ih =>
    show Tin.run none (hiS s :: loS s :: symBits w) = hIn s ++ w.flatMap hIn
    rw [← ih]
    show [] ++ (hIn (symOf (hiS s) (loS s)) ++ Tin.run none (symBits w)) = _
    rw [symOf_bits]; rfl

def escAll (xs : List Bool) : List Bool := xs.flatMap (fun b => [true, b])

theorem escAll_append (xs ys : List Bool) : escAll (xs ++ ys) = escAll xs ++ escAll ys := by
  simp [escAll]

theorem quote_eq (xs : List Bool) : quote xs = escAll xs ++ [false] := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simp [quote, escAll, ih]

theorem bitsMap_hIn (bs : List Bool) : (bs.map bit).flatMap hIn = escAll (escAll bs) := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    cases b <;> simp [bit, hIn, escAll] at ih ⊢ <;> exact ih

theorem encodeList_eq {α : Type} (ea : α → List Bool) (as : List α) :
    encodeList ea as = as.flatMap (fun a => quote (ea a)) := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [encodeList, ih]

theorem encNat_eq (n : ℕ) : encNat n = (Nat.bits n).map bit := by
  simp [encNat, QMCNumericRuntime.encodeNat_eq_bits]

def itemsOf {m : ℕ} (G : Table m) : List (List ℕ) :=
  G.sizes.map (fun n => [n]) ++ G.entries.map (fun r => [r.num, r.den, 0])

theorem encGame_hIn {m : ℕ} (G : Table m) :
    (encGame G).flatMap hIn = (enc (itemsOf G) : List Bool) := by
  show _ = encodeList (encodeList Nat.bits) (itemsOf G)
  simp only [encGame, pack, itemsOf, encodeList_eq, List.flatMap_append, List.flatMap_map,
    List.flatMap_assoc]
  congr 1
  · refine List.flatMap_congr (fun n _ => ?_)
    simp [encNat_eq, bitsMap_hIn, quote_eq, escAll_append, hIn]
    simp [escAll]
  · refine List.flatMap_congr (fun r _ => ?_)
    simp [encRaw, pack, encNat_eq, bitsMap_hIn, quote_eq, escAll_append, hIn]
    simp [escAll]

def Tout : Transducer where
  Q := Bool × Bool × Bool
  initial := (false, false, false)
  next q x := match q with
    | (false, l2, _) => if x then ((true, l2, q.2.2), []) else ((false, l2, false), [true, true])
    | (true, false, p) =>
        if x then ((false, true, false), if p then [true, false] else [])
        else ((false, false, true), if p then [true, false] else [])
    | (true, true, p) => ((false, false, p), [false, x])
  finish _ := []

theorem To1 (l2 p : Bool) : Tout.next (false, l2, p) true = ((true, l2, p), []) := rfl
theorem To2 (l2 p : Bool) : Tout.next (false, l2, p) false = ((false, l2, false), [true, true]) := rfl
theorem To3 (p : Bool) : Tout.next (true, false, p) true =
    ((false, true, false), if p then [true, false] else []) := rfl
theorem To4 (p : Bool) : Tout.next (true, false, p) false =
    ((false, false, true), if p then [true, false] else []) := rfl
theorem To5 (p x : Bool) : Tout.next (true, true, p) x = ((false, false, p), [false, x]) := rfl
theorem ToF (q : Bool × Bool × Bool) : Tout.finish q = [] := rfl

def packItems (items : List (List ℕ)) : List MNRBridge.Sym :=
  items.flatMap (fun it => List.intercalate [2] (it.map encNat) ++ [3])

theorem symBits_encNat (n : ℕ) : symBits (encNat n) = (Nat.bits n).flatMap (fun b => [false, b]) := by
  rw [encNat_eq]
  simp only [symBits, List.flatMap_map]
  refine List.flatMap_congr (fun b _ => ?_)
  cases b <;> rfl

theorem Tout_bits (bs : List Bool) (rest : List Bool) :
    Tout.run (false, false, false) (escAll (escAll bs) ++ rest) =
      bs.flatMap (fun b => [false, b]) ++ Tout.run (false, false, false) rest := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    show Tout.run (false, false, false) (true :: true :: true :: b :: (escAll (escAll bs) ++ rest)) = _
    simp only [Transducer.run, To1, To3, To5, if_false, Bool.false_eq_true, List.nil_append]
    rw [ih]; simp

theorem Tout_seg (p : Bool) (bs : List Bool) (rest : List Bool) :
    Tout.run (false, false, p) (escAll (escAll bs) ++ [true, false] ++ rest) =
      (if p then [true, false] else []) ++ bs.flatMap (fun b => [false, b]) ++
        Tout.run (false, false, true) rest := by
  cases bs with
  | nil =>
    show Tout.run (false, false, p) (true :: false :: rest) = _
    simp only [Transducer.run, To1, To4, List.nil_append, List.flatMap_nil, List.append_nil]
  | cons b bs =>
    show Tout.run (false, false, p) (true :: true :: true :: b :: (escAll (escAll bs) ++ [true, false] ++ rest)) = _
    simp only [Transducer.run, To1, To3, To5, List.nil_append, Bool.false_eq_true, if_false]
    rw [List.append_assoc, Tout_bits]
    have e : Tout.run (false, false, false) (true :: false :: rest) = Tout.run (false, false, true) rest := by
      simp only [Transducer.run, To1, To4, List.nil_append, Bool.false_eq_true, if_false]
    rw [show [true, false] ++ rest = true :: false :: rest from rfl, e]
    simp

theorem symBits_append (a b : List MNRBridge.Sym) : symBits (a ++ b) = symBits a ++ symBits b := by
  simp [symBits]

theorem Tout_segs (it : List ℕ) (p : Bool) (rest : List Bool) :
    Tout.run (false, false, p) (it.flatMap (fun n => escAll (escAll (Nat.bits n)) ++ [true, false]) ++
      false :: rest) =
      (if p && !it.isEmpty then [true, false] else []) ++ symBits (List.intercalate [2] (it.map encNat)) ++
        [true, true] ++ Tout.run (false, false, false) rest := by
  induction it generalizing p with
  | nil =>
    simp only [List.flatMap_nil, List.nil_append, List.isEmpty_nil, Bool.not_true, Bool.and_false,
      Bool.false_eq_true, if_false, List.map_nil, List.intercalate_nil]
    simp only [Transducer.run, To2]; rfl
  | cons n it ih =>
    rw [List.flatMap_cons, List.append_assoc, Tout_seg, ih true]
    cases it with
    | nil => simp [symBits_encNat]; rfl
    | cons n' it' =>
      simp only [List.map_cons, List.intercalate_cons_cons, symBits_append, symBits_encNat]
      simp [symBits, hiS, loS]

theorem Tout_items (items : List (List ℕ)) :
    Tout.run (false, false, false) (enc items : List Bool) = symBits (packItems items) := by
  induction items with
  | nil => rfl
  | cons it items ih =>
    show Tout.run (false, false, false) (encodeList (encodeList Nat.bits) (it :: items)) = _
    have e : encodeList (encodeList Nat.bits) (it :: items) =
        it.flatMap (fun n => escAll (escAll (Nat.bits n)) ++ [true, false]) ++
          false :: encodeList (encodeList Nat.bits) items := by
      rw [EncodedList.cons, quote_eq, encodeList_eq, List.append_assoc]
      congr 1
      simp only [escAll, List.flatMap_assoc]
      refine List.flatMap_congr (fun n _ => ?_)
      simp [quote_eq, escAll, List.flatMap_append, List.flatMap_assoc]
    rw [e, Tout_segs]
    have ih' : Tout.run (false, false, false) (encodeList (encodeList Nat.bits) items) =
        symBits (packItems items) := ih
    rw [ih']
    simp [packItems, symBits_append, symBits, hiS, loS]

end MNRL22

-- ===== L22C =====

namespace MNRL22
open NashAmplification.Filtering

def rankL : List ℕ → List ℕ → ℕ
  | n :: L, d :: ds => d * L.prod + rankL L ds
  | _, _ => 0

theorem foldl_rank (ps : List (ℕ × ℕ)) (z : ℕ) :
    ps.foldl (fun z p => z * p.1 + p.2) z = z * (ps.map Prod.fst).prod + rankL (ps.map Prod.fst) (ps.map Prod.snd) := by
  induction ps generalizing z with
  | nil => simp [rankL]
  | cons p ps ih =>
    simp only [List.foldl_cons, ih, List.map_cons, List.prod_cons, rankL]
    ring

theorem tupleRank_eq {k : ℕ} {n : Fin k → ℕ} (a : Tuple n) :
    tupleRank a = rankL (List.ofFn n) (List.ofFn (fun r => (a r).val)) := by
  unfold tupleRank
  rw [foldl_rank]
  simp [Function.comp_def, List.ofFn_eq_map]

def digitL (L : List ℕ) (j pos : ℕ) : ℕ := (pos / (L.drop (j + 1)).prod) % (L[j]?.getD 0)

theorem rankL_lt : ∀ (L ds : List ℕ), ds.length = L.length → (∀ i (h1 : i < ds.length) (h2 : i < L.length), ds[i] < L[i]) →
    rankL L ds < L.prod
  | [], [], _, _ => by simp [rankL]
  | n :: L, d :: ds, hl, hd => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    have h0 := hd 0 (by simp) (by simp)
    simp only [List.getElem_cons_zero] at h0
    have ih := rankL_lt L ds hl (fun i h1 h2 => hd (i + 1) (by simp; omega) (by simp; omega))
    simp only [rankL, List.prod_cons]
    calc d * L.prod + rankL L ds < d * L.prod + L.prod := by omega
      _ = (d + 1) * L.prod := by ring
      _ ≤ n * L.prod := Nat.mul_le_mul_right _ h0
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

theorem prod_pos_of (L : List ℕ) (hL : ∀ x ∈ L, 0 < x) : 0 < L.prod :=
  List.prod_pos (fun x hx => hL x hx)

theorem digitL_rankL : ∀ (L ds : List ℕ), ds.length = L.length →
    (∀ i (h1 : i < ds.length) (h2 : i < L.length), ds[i] < L[i]) → (∀ x ∈ L, 0 < x) →
    ∀ j (hj : j < ds.length), digitL L j (rankL L ds) = ds[j]
  | [], [], _, _, _, j, hj => by simp at hj
  | n :: L, d :: ds, hl, hd, hpos, j, hj => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    have hd' : ∀ i (h1 : i < ds.length) (h2 : i < L.length), ds[i] < L[i] :=
      fun i h1 h2 => hd (i + 1) (by simp; omega) (by simp; omega)
    have hpos' : ∀ x ∈ L, 0 < x := fun x hx => hpos x (List.mem_cons_of_mem _ hx)
    have hr := rankL_lt L ds hl hd'
    have hP := prod_pos_of L hpos'
    have h0 := hd 0 (by simp) (by simp)
    simp only [List.getElem_cons_zero] at h0
    cases j with
    | zero =>
      simp only [digitL, rankL, List.getElem?_cons_zero, Option.getD_some, List.getElem_cons_zero]
      rw [show (n :: L).drop (0 + 1) = L from rfl, show d * L.prod + rankL L ds = rankL L ds + L.prod * d by ring, Nat.add_mul_div_left _ _ hP,
        Nat.div_eq_of_lt hr, zero_add, Nat.mod_eq_of_lt h0]
    | succ j =>
      have hjL : j < L.length := by simp at hj; omega
      have ih := digitL_rankL L ds hl hd' hpos' j (by simp at hj; omega)
      simp only [List.getElem_cons_succ]
      rw [← ih]
      simp only [digitL, rankL, List.drop_succ_cons, List.getElem?_cons_succ]
      set sP := (L.drop (j + 1)).prod
      have hs : 0 < sP := prod_pos_of _ (fun x hx => hpos' x (List.mem_of_mem_drop hx))
      have hLp : L.prod = sP * (L[j] * (L.take j).prod) := by
        rw [← List.prod_take_mul_prod_drop L (j + 1), List.prod_take_succ L j hjL]
        ring
      rw [List.getElem?_eq_getElem hjL, Option.getD_some, hLp,
        show d * (sP * (L[j] * (L.take j).prod)) + rankL L ds =
          rankL L ds + sP * (d * (L.take j).prod * L[j]) by ring,
        Nat.add_mul_div_left _ _ hs, Nat.add_mul_mod_self_right]
  | [], _ :: _, hl, _, _, _, _ => by simp at hl
  | _ :: _, [], hl, _, _, _, _ => by simp at hl

def valQ (r : RawRat) : ℚ := (r.num : ℚ) / (r.den : ℚ)

theorem ctxOf_itemsOf {m : ℕ} (G : Table m) :
    ctxOf (itemsOf G) = (G.sizes, G.entries.map valQ) := by
  simp only [ctxOf, itemsOf, List.filter_append, List.map_append]
  congr 1
  · simp [List.filter_map, Function.comp_def]
  · simp [List.filter_map, Function.comp_def, valQ]

theorem ofFn_counts {m : ℕ} (G : Table m) : List.ofFn G.counts = G.sizes := by
  apply List.ext_getElem
  · simp [G.sizes_length]
  · intro i h1 h2
    simp [Table.counts, List.getElem?_eq_getElem h2]

theorem stride_eq (c : Ctx) (j : ℕ) : stride c j = (c.1.drop (j + 1)).prod := by
  unfold stride
  rw [← Nat.cast_list_prod, Rat.num_natCast, Int.natAbs_natCast]

theorem digit_eq (c : Ctx) (j pos : ℕ) : digit c j pos = digitL c.1 j pos := by
  simp [digit, digitL, stride_eq]

theorem digit_tupleRank {m : ℕ} (G : Table m) (en : List ℚ) (s : Tuple G.counts) (j : Fin m) :
    digit (G.sizes, en) j (tupleRank s) = (s j).val := by
  rw [digit_eq, tupleRank_eq, ofFn_counts]
  have := digitL_rankL G.sizes (List.ofFn (fun r => (s r).val)) (by simp [G.sizes_length])
    (by
      intro i h1 h2
      simp only [List.getElem_ofFn]
      have := (s ⟨i, by simpa using h1⟩).isLt
      simpa [Table.counts, List.getElem?_eq_getElem h2] using this)
    G.sizes_pos j (by simp)
  simpa using this

theorem range_filter_lt (L n : ℕ) :
    (List.range L).filter (fun i => decide (i < n)) = List.range (min n L) := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [List.range_succ, List.filter_append, ih]
    by_cases h : L < n
    · simp [h, Nat.min_eq_right (show L + 1 ≤ n by omega), Nat.min_eq_right (show L ≤ n by omega),
        List.range_succ]
    · simp [h, Nat.min_eq_left (show n ≤ L by omega), Nat.min_eq_left (show n ≤ L + 1 by omega)]

theorem list_sum_range {M : Type*} [AddCommMonoid M] (f : ℕ → M) (N : ℕ) :
    ((List.range N).map f).sum = ∑ i ∈ Finset.range N, f i := by
  rw [Finset.sum_eq_multiset_sum]; simp [Finset.range_val, Multiset.range]

theorem list_prod_range {M : Type*} [CommMonoid M] (f : ℕ → M) (N : ℕ) :
    ((List.range N).map f).prod = ∏ i ∈ Finset.range N, f i := by
  rw [Finset.prod_eq_multiset_prod]; simp [Finset.range_val, Multiset.range]

theorem tupleRank_lt {m : ℕ} (G : Table m) (s : Tuple G.counts) : tupleRank s < G.sizes.prod := by
  rw [tupleRank_eq, ofFn_counts]
  refine rankL_lt _ _ (by simp [G.sizes_length]) ?_
  intro i h1 h2
  simp only [List.getElem_ofFn]
  have := (s ⟨i, by simpa using h1⟩).isLt
  simpa [Table.counts, List.getElem?_eq_getElem h2] using this

theorem NOf_eq {m : ℕ} (G : Table m) (hm : 1 ≤ m) : NOf (G.sizes, G.entries.map valQ) = G.sizes.prod := by
  simp only [NOf, List.length_map, G.entries_length, G.sizes_length]
  exact Nat.mul_div_cancel_left _ (by omega)

theorem payoff_eq {m : ℕ} (G : Table m) (hm : 1 ≤ m) (y : List (List ℚ)) (r : Fin m) :
    ((payoff (G.sizes, G.entries.map valQ) y r : ℚ) : ℝ) =
      AGT.expectedPayoff G.utility (fun j a => ((prob y j a : ℚ) : ℝ)) r := by
  set c : Ctx := (G.sizes, G.entries.map valQ) with hc
  have hN := NOf_eq G hm
  have hlen : c.2.length = m * G.sizes.prod := by simp [c, G.entries_length]
  have hrng : rng c (NOf c) = List.range G.sizes.prod := by
    unfold rng; rw [range_filter_lt, hN, hlen]
    congr 1; apply Nat.min_eq_left; exact Nat.le_mul_of_pos_left _ (by omega)
  unfold payoff
  rw [hrng, hN, list_sum_range, Rat.cast_sum]
  unfold AGT.expectedPayoff
  symm
  refine Finset.sum_bij (fun s _ => tupleRank s) (fun s _ => Finset.mem_range.2 (tupleRank_lt G s))
    ?_ ?_ ?_
  · intro s _ t _ hst
    funext j
    apply Fin.ext
    rw [← digit_tupleRank G (G.entries.map valQ) s j, ← digit_tupleRank G (G.entries.map valQ) t j, hst]
  · intro b hb
    have hcard : (Finset.range G.sizes.prod).card ≤ (Finset.univ : Finset (Tuple G.counts)).card := by
      rw [Finset.card_range, Finset.card_univ, Fintype.card_pi]
      simp only [Fintype.card_fin]
      rw [← List.prod_ofFn, ofFn_counts]
    obtain ⟨a, ha, hab⟩ := Finset.surj_on_of_inj_on_of_card_le (fun s _ => tupleRank s)
      (fun s _ => Finset.mem_range.2 (tupleRank_lt G s)) (by
        intro s t _ _ hst
        funext j
        apply Fin.ext
        rw [← digit_tupleRank G (G.entries.map valQ) s j, ← digit_tupleRank G (G.entries.map valQ) t j, hst])
      hcard b hb
    exact ⟨a, ha, hab.symm⟩
  · intro s _
    have hw : weight c y (tupleRank s) = ∏ j : Fin m, prob y j (s j) := by
      unfold weight
      rw [show c.1.length = m from G.sizes_length, list_prod_range, ← Fin.prod_univ_eq_prod_range]
      refine Finset.prod_congr rfl (fun j _ => ?_)
      rw [digit_tupleRank]
    have hidx : r.val * G.sizes.prod + tupleRank s < G.entries.length := by
      rw [G.entries_length]
      have h1 := tupleRank_lt G s
      have h2 : r.val + 1 ≤ m := r.isLt
      nlinarith
    have he : c.2[r.val * G.sizes.prod + tupleRank s]?.getD 0 =
        valQ (G.entries[r.val * G.sizes.prod + tupleRank s]) := by
      simp [c, List.getElem?_map, List.getElem?_eq_getElem hidx]
    rw [hw, he]
    simp only [AGT.profileProb, Table.utility, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hidx,
      Option.getD_some, RawRat.value, valQ]
    push_cast
    ring

end MNRL22

-- ===== L22D =====

namespace MNRL22
open NashAmplification.Filtering Finset

variable {m : ℕ} {n : Fin m → ℕ}

theorem pp_update (y : Mixed n) (j : Fin m) (w : Fin (n j) → ℝ) (s : Tuple n) :
    AGT.profileProb (Function.update y j w) s = w (s j) * ∏ k ∈ univ.erase j, y k (s k) := by
  unfold AGT.profileProb
  rw [← Finset.mul_prod_erase univ _ (mem_univ j)]
  simp only [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro k hk
  rw [Function.update_of_ne (ne_of_mem_erase hk)]

theorem sum_pp (y : Mixed n) (hy : AGT.IsMixedProfile y) : ∑ s : Tuple n, AGT.profileProb y s = 1 := by
  unfold AGT.profileProb
  rw [← Fintype.prod_sum]
  exact Finset.prod_eq_one (fun j _ => (hy j).2)

theorem ep_bounds (u : Utility n) (hu : BoundedGame u) (x : Mixed n) (hx : AGT.IsMixedProfile x)
    (i : Fin m) : 0 ≤ AGT.expectedPayoff u x i ∧ AGT.expectedPayoff u x i ≤ 1 := by
  have hp : ∀ s : Tuple n, 0 ≤ AGT.profileProb x s := fun s =>
    Finset.prod_nonneg (fun j _ => (hx j).1 (s j))
  unfold AGT.expectedPayoff
  constructor
  · exact Finset.sum_nonneg (fun s _ => mul_nonneg (hp s) (hu i s).1)
  · calc ∑ s, AGT.profileProb x s * u i s ≤ ∑ s, AGT.profileProb x s * 1 :=
          Finset.sum_le_sum (fun s _ => mul_le_mul_of_nonneg_left (hu i s).2 (hp s))
      _ = 1 := by simp [sum_pp x hx]

theorem update_mixed (x : Mixed n) (hx : AGT.IsMixedProfile x) (j : Fin m) (y : Fin (n j) → ℝ)
    (hy : AGT.IsLottery y) : AGT.IsMixedProfile (Function.update x j y) := by
  intro k
  by_cases hk : k = j
  · subst hk; simpa using hy
  · simpa [Function.update_of_ne hk] using hx k

theorem ep_update (u : Utility n) (Z : Mixed n) (j : Fin m) (w : Fin (n j) → ℝ) (p : Fin m) :
    AGT.expectedPayoff u (Function.update Z j w) p =
      ∑ s : Tuple n, w (s j) * ((∏ k ∈ univ.erase j, Z k (s k)) * u p s) := by
  unfold AGT.expectedPayoff
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [pp_update]; ring

theorem ep_lin (u : Utility n) (Z : Mixed n) (j : Fin m) (v w : Fin (n j) → ℝ) (α β : ℝ) (p : Fin m) :
    AGT.expectedPayoff u (Function.update Z j (fun a => α * v a + β * w a)) p =
      α * AGT.expectedPayoff u (Function.update Z j v) p + β * AGT.expectedPayoff u (Function.update Z j w) p := by
  rw [ep_update, ep_update, ep_update, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  ring

def dlt {k : ℕ} (a : Fin k) : Fin k → ℝ := fun c => if c = a then 1 else 0

theorem dlt_lottery {k : ℕ} (a : Fin k) : AGT.IsLottery (dlt a) := by
  constructor
  · intro c; unfold dlt; split_ifs <;> norm_num
  · simp [dlt]

theorem ep_lottery_le (u : Utility n) (Z : Mixed n) (j : Fin m) (y : Fin (n j) → ℝ) (hy : AGT.IsLottery y)
    (p : Fin m) (B : ℝ) (h : ∀ a, AGT.expectedPayoff u (Function.update Z j (dlt a)) p ≤ B) :
    AGT.expectedPayoff u (Function.update Z j y) p ≤ B := by
  have key : AGT.expectedPayoff u (Function.update Z j y) p =
      ∑ a, y a * AGT.expectedPayoff u (Function.update Z j (dlt a)) p := by
    simp only [ep_update, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    simp only [dlt]
    simp [ite_mul, Finset.sum_ite_eq']
  rw [key]
  calc ∑ a, y a * AGT.expectedPayoff u (Function.update Z j (dlt a)) p ≤ ∑ a, y a * B :=
        Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (h a) (hy.1 a))
    _ = B := by rw [← Finset.sum_mul, hy.2, one_mul]

def d0 {k : ℕ} : Fin k → ℝ := fun a => if a.val = 0 then 1 else 0

def Xr (b : (j : Fin m) → Fin (n j)) (r : ℕ) : Mixed n :=
  fun j a => if j.val < r then ((mixVal j.val (b j).val a.val : ℚ) : ℝ) else d0 a

def mixR (b : (j : Fin m) → Fin (n j)) (j : Fin m) : Fin (n j) → ℝ :=
  fun a => ((mixVal j.val (b j).val a.val : ℚ) : ℝ)

theorem Xr_succ (b : (j : Fin m) → Fin (n j)) (R : Fin m) :
    Xr b (R.val + 1) = Function.update (Xr b R.val) R (mixR b R) := by
  funext j a
  by_cases h : j = R
  · subst h; simp [Xr, mixR]
  · rw [Function.update_of_ne h]
    have : j.val ≠ R.val := fun e => h (Fin.ext e)
    simp only [Xr]
    by_cases h2 : j.val < R.val
    · simp [h2, show j.val < R.val + 1 by omega]
    · simp [h2, show ¬ j.val < R.val + 1 by omega]

theorem Xr_self (b : (j : Fin m) → Fin (n j)) (R : Fin m) :
    Function.update (Xr b R.val) R d0 = Xr b R.val := by
  funext j a
  by_cases h : j = R
  · subst h; simp [Xr]
  · rw [Function.update_of_ne h]

theorem d0_lottery {k : ℕ} (hk : 0 < k) : AGT.IsLottery (d0 : Fin k → ℝ) := by
  constructor
  · intro c; unfold d0; split_ifs <;> norm_num
  · unfold d0
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
    have : (Finset.univ.filter (fun a : Fin k => a.val = 0)) = {⟨0, hk⟩} := by
      ext a; simp [Fin.ext_iff]
    rw [this]; simp

theorem mixR_eq (b : (j : Fin m) → Fin (n j)) (R : Fin m) (hR : 1 ≤ R.val) :
    mixR b R = fun a => ((R.val : ℝ) / (R.val + 1)) * d0 a + (1 / ((R.val : ℝ) + 1)) * dlt (b R) a := by
  funext a
  have hR0 : R.val ≠ 0 := by omega
  simp only [mixR, mixVal, hR0, if_false, d0, dlt, Fin.ext_iff]
  split_ifs <;> push_cast <;> ring

theorem mixR_zero (b : (j : Fin m) → Fin (n j)) (R : Fin m) (hR : R.val = 0) :
    mixR b R = dlt (b R) := by
  funext a
  simp only [mixR, mixVal, hR, if_true, dlt, Fin.ext_iff]
  split_ifs <;> simp

theorem mixR_lottery (b : (j : Fin m) → Fin (n j)) (hn : ∀ j, 0 < n j) (R : Fin m) :
    AGT.IsLottery (mixR b R) := by
  by_cases hR : R.val = 0
  · rw [mixR_zero b R hR]; exact dlt_lottery _
  · rw [mixR_eq b R (by omega)]
    have h1 := d0_lottery (hn R)
    have h2 := dlt_lottery (b R)
    have hr : (0 : ℝ) < R.val + 1 := by positivity
    constructor
    · intro a
      have := h1.1 a; have := h2.1 a
      positivity
    · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, h1.2, h2.2]
      field_simp

theorem Xr_mixed (b : (j : Fin m) → Fin (n j)) (hn : ∀ j, 0 < n j) (r : ℕ) :
    AGT.IsMixedProfile (Xr b r) := by
  intro j
  by_cases h : j.val < r
  · have e : Xr b r j = mixR b j := by funext a; simp [Xr, h, mixR]
    rw [e]; exact mixR_lottery b hn j
  · have e : Xr b r j = d0 := by funext a; simp [Xr, h]
    rw [e]; exact d0_lottery (hn j)

theorem hdrs_inv (u : Utility n) (hu : BoundedGame u) (hn : ∀ j, 0 < n j) (b : (j : Fin m) → Fin (n j))
    (hbr : ∀ (R : Fin m) (cc : Fin (n R)),
      AGT.expectedPayoff u (Function.update (Xr b R.val) R (dlt cc)) R ≤
        AGT.expectedPayoff u (Function.update (Xr b R.val) R (dlt (b R))) R) :
    ∀ r : ℕ, 1 ≤ r → r ≤ m → ∀ p : Fin m, p.val < r → ∀ y : Fin (n p) → ℝ, AGT.IsLottery y →
      AGT.expectedPayoff u (Function.update (Xr b r) p y) p - AGT.expectedPayoff u (Xr b r) p ≤
        ((r : ℝ) - 1) / r := by
  intro r hr1
  induction r, hr1 using Nat.le_induction with
  | base =>
    intro hm p hp y hy
    have hp0 : p.val = 0 := by omega
    have hX : Xr b 1 = Function.update (Xr b 0) p (dlt (b p)) := by
      have := Xr_succ b p
      rw [hp0] at this
      rw [this, mixR_zero b p hp0]
    have hbr' := hbr p
    rw [hp0] at hbr'
    rw [hX, Function.update_idem]
    have := ep_lottery_le u (Xr b 0) p y hy p _ (fun a => hbr' a)
    norm_num
    linarith
  | succ r hr ih =>
    intro hm p hp y hy
    have ih' := ih (by omega)
    obtain ⟨R, hR⟩ : ∃ R : Fin m, R.val = r := ⟨⟨r, by omega⟩, rfl⟩
    subst hR
    have hX : Xr b (R.val + 1) = Function.update (Xr b R.val) R (mixR b R) := Xr_succ b R
    have hmix := mixR_eq b R hr
    have hrpos : (0 : ℝ) < R.val := by exact_mod_cast (show 0 < R.val by omega)
    have hXm := Xr_mixed b hn R.val
    have hXself : Function.update (Xr b R.val) R d0 = Xr b R.val := Xr_self b R
    set α : ℝ := (R.val : ℝ) / (R.val + 1)
    set β : ℝ := 1 / ((R.val : ℝ) + 1)
    have hα0 : 0 ≤ α := by positivity
    have hβ0 : 0 ≤ β := by positivity
    have hfin : ((↑(R.val + 1) : ℝ) - 1) / ↑(R.val + 1) = α := by simp only [α]; push_cast; ring
    rw [hX, hmix, hfin]
    have hZm := update_mixed _ hXm R _ (dlt_lottery (b R))
    by_cases hpR : p = R
    · -- the new player
      subst hpR
      have hEX : AGT.expectedPayoff u (Function.update (Xr b p.val) p
          (fun a => α * d0 a + β * dlt (b p) a)) p =
          α * AGT.expectedPayoff u (Xr b p.val) p +
            β * AGT.expectedPayoff u (Function.update (Xr b p.val) p (dlt (b p))) p := by
        rw [ep_lin, hXself]
      rw [Function.update_idem, hEX]
      have hB := ep_lottery_le u (Xr b p.val) p y hy p _ (fun a => hbr p a)
      have hB1 := (ep_bounds u hu _ hZm p).2
      have hA0 := (ep_bounds u hu _ hXm p).1
      have hαβ : β = 1 - α := by simp only [α, β]; field_simp; ring
      rw [hαβ]
      nlinarith
    · -- an old player
      have hpr : p.val < R.val := by
        have : p.val ≠ R.val := fun e => hpR (Fin.ext e)
        omega
      rw [Function.update_comm (Ne.symm hpR)]
      have h1 : AGT.expectedPayoff u (Function.update (Function.update (Xr b R.val) p y) R
          (fun a => α * d0 a + β * dlt (b R) a)) p =
          α * AGT.expectedPayoff u (Function.update (Xr b R.val) p y) p +
            β * AGT.expectedPayoff u (Function.update (Function.update (Xr b R.val) R (dlt (b R))) p y) p := by
        rw [ep_lin, Function.update_comm hpR, hXself, Function.update_comm hpR]
      have h2 : AGT.expectedPayoff u (Function.update (Xr b R.val) R
          (fun a => α * d0 a + β * dlt (b R) a)) p =
          α * AGT.expectedPayoff u (Xr b R.val) p +
            β * AGT.expectedPayoff u (Function.update (Xr b R.val) R (dlt (b R))) p := by
        rw [ep_lin, hXself]
      rw [h1, h2]
      have hI := ih' p hpr y hy
      have hC1 := (ep_bounds u hu _ (update_mixed _ hZm p y hy) p).2
      have hC0 := (ep_bounds u hu _ hZm p).1
      have hkey : α * (((R.val : ℝ) - 1) / R.val) + β * 1 = α := by
        simp only [α, β]; field_simp; ring
      have e1 : α * AGT.expectedPayoff u (Function.update (Xr b R.val) p y) p -
          α * AGT.expectedPayoff u (Xr b R.val) p ≤ α * (((R.val : ℝ) - 1) / R.val) := by
        rw [← mul_sub]; exact mul_le_mul_of_nonneg_left hI hα0
      have e2 : β * AGT.expectedPayoff u (Function.update (Function.update (Xr b R.val) R (dlt (b R))) p y) p -
          β * AGT.expectedPayoff u (Function.update (Xr b R.val) R (dlt (b R))) p ≤ β * 1 := by
        rw [← mul_sub]; exact mul_le_mul_of_nonneg_left (by linarith) hβ0
      linarith

theorem hdrs (u : Utility n) (hu : BoundedGame u) (hn : ∀ j, 0 < n j) (hm : 1 ≤ m)
    (b : (j : Fin m) → Fin (n j))
    (hbr : ∀ (R : Fin m) (cc : Fin (n R)),
      AGT.expectedPayoff u (Function.update (Xr b R.val) R (dlt cc)) R ≤
        AGT.expectedPayoff u (Function.update (Xr b R.val) R (dlt (b R))) R) :
    DGPNash.WellSupported.IsEpsApproxNash u (Xr b m) (1 - 1 / (m : ℝ)) := by
  refine ⟨Xr_mixed b hn m, fun p y hy => ?_⟩
  have := hdrs_inv u hu hn b hbr m hm le_rfl p p.isLt y hy
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have e : ((m : ℝ) - 1) / m = 1 - 1 / m := by field_simp
  rw [e] at this
  linarith

end MNRL22

-- ===== L22E =====

namespace MNRL22
open NashAmplification.Filtering

theorem foldl_br_prefix (c : Ctx) : ∀ k : ℕ,
    ((List.range k).foldl (fun bs r => stepBR ((c, bs), r)) []).length = k ∧
    ∀ r (h : r < k), ((List.range k).foldl (fun bs r => stepBR ((c, bs), r)) [])[r]? =
      some (br c (((List.range k).foldl (fun bs r => stepBR ((c, bs), r)) []).take r) r) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    obtain ⟨hl, hr⟩ := ih
    rw [List.range_succ, List.foldl_append]
    set A := (List.range k).foldl (fun bs r => stepBR ((c, bs), r)) []
    rw [show List.foldl (fun bs r => stepBR ((c, bs), r)) A [k] = A ++ [br c A k] from rfl]
    refine ⟨by simp [hl], fun r hrk => ?_⟩
    by_cases h : r < k
    · rw [List.getElem?_append_left (by omega), hr r h, List.take_append_of_le_length (by omega)]
    · have hrk' : r = k := by omega
      subst hrk'
      rw [List.getElem?_append_right (by omega), ← hl, List.take_left' rfl]
      simp

theorem rng_eq (c : Ctx) (k : ℕ) (hk : k ≤ c.2.length) : rng c k = List.range k := by
  unfold rng; rw [range_filter_lt, Nat.min_eq_left hk]

theorem br_spec (c : Ctx) (acc : List ℕ) (r : ℕ) (hpos : 0 < c.1[r]?.getD 0)
    (hle : c.1[r]?.getD 0 ≤ c.2.length) :
    br c acc r < c.1[r]?.getD 0 ∧ ∀ cc, cc < c.1[r]?.getD 0 →
      payoff c (profAt c acc r cc) r ≤ payoff c (profAt c acc r (br c acc r)) r := by
  set nr := c.1[r]?.getD 0
  set g : ℕ → ℚ := fun cc => payoff c (profAt c acc r cc) r
  have hV : vals c acc r = (List.range nr).map g := by
    unfold vals; rw [rng_eq c nr hle]
  obtain ⟨i, hi, himax⟩ := Finset.exists_max_image (Finset.range nr) g ⟨0, Finset.mem_range.2 hpos⟩
  have hex : ∃ v ∈ vals c acc r, ((vals c acc r).all (fun v' => decide (v' ≤ v))) = true := by
    refine ⟨g i, ?_, ?_⟩
    · rw [hV]; exact List.mem_map.2 ⟨i, List.mem_range.2 (Finset.mem_range.1 hi), rfl⟩
    · rw [List.all_eq_true, hV]
      intro v hv
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hv
      simpa using himax j (Finset.mem_range.2 (List.mem_range.1 hj))
  have hlt := List.findIdx_lt_length_of_exists hex
  have hP := List.findIdx_getElem (w := hlt)
  unfold br
  have hlen : (vals c acc r).length = nr := by rw [hV]; simp
  refine ⟨by rw [← hlen]; exact hlt, fun cc hcc => ?_⟩
  rw [List.all_eq_true] at hP
  have hmem : g cc ∈ vals c acc r := by
    rw [hV]; exact List.mem_map.2 ⟨cc, List.mem_range.2 hcc, rfl⟩
  have h1 := hP (g cc) hmem
  simp only [decide_eq_true_eq] at h1
  have h2 : (vals c acc r)[(vals c acc r).findIdx (fun v => (vals c acc r).all (fun v' => decide (v' ≤ v)))] =
      g ((vals c acc r).findIdx (fun v => (vals c acc r).all (fun v' => decide (v' ≤ v)))) := by
    simp only [hV, List.getElem_map, List.getElem_range]
  rw [h2] at h1
  exact h1

variable {m : ℕ}

def cG (G : Table m) : Ctx := (G.sizes, G.entries.map valQ)

theorem getD_sizes (G : Table m) (j : Fin m) : (cG G).1[j.val]?.getD 0 = G.counts j := by
  simp [cG, Table.counts]

theorem counts_pos (G : Table m) (j : Fin m) : 0 < G.counts j := by
  have hj : j.val < G.sizes.length := by rw [G.sizes_length]; exact j.isLt
  have := G.sizes_pos _ (List.getElem_mem hj)
  simpa [Table.counts, List.getElem?_eq_getElem hj] using this

theorem counts_le (G : Table m) (hm : 1 ≤ m) (j : Fin m) : G.counts j ≤ (cG G).2.length := by
  have hj : j.val < G.sizes.length := by rw [G.sizes_length]; exact j.isLt
  have h1 : G.counts j ≤ G.sizes.prod := by
    have := List.single_le_prod (l := G.sizes) (fun x hx => G.sizes_pos x hx) _ (List.getElem_mem hj)
    simpa [Table.counts, List.getElem?_eq_getElem hj] using this
  have h2 : G.sizes.prod ≤ (cG G).2.length := by
    simp only [cG, List.length_map, G.entries_length]
    exact Nat.le_mul_of_pos_left _ (by omega)
  omega

theorem bs_len (G : Table m) : (bsFinal (cG G)).length = m := by
  have := (foldl_br_prefix (cG G) (cG G).1.length).1
  unfold bsFinal; rw [this]; simp [cG, G.sizes_length]

theorem bs_get (G : Table m) (r : Fin m) :
    (bsFinal (cG G))[r.val]?.getD 0 = br (cG G) ((bsFinal (cG G)).take r.val) r.val := by
  have := (foldl_br_prefix (cG G) (cG G).1.length).2 r.val (by simp [cG, G.sizes_length])
  unfold bsFinal; rw [this]; rfl

theorem bs_spec (G : Table m) (hm : 1 ≤ m) (r : Fin m) :
    (bsFinal (cG G))[r.val]?.getD 0 < G.counts r ∧ ∀ cc, cc < G.counts r →
      payoff (cG G) (profAt (cG G) ((bsFinal (cG G)).take r.val) r.val cc) r.val ≤
        payoff (cG G) (profAt (cG G) ((bsFinal (cG G)).take r.val) r.val
          ((bsFinal (cG G))[r.val]?.getD 0)) r.val := by
  have h := br_spec (cG G) ((bsFinal (cG G)).take r.val) r.val
    (by rw [getD_sizes]; exact counts_pos G r) (by rw [getD_sizes]; exact counts_le G hm r)
  rw [getD_sizes] at h
  rw [bs_get]
  exact h

noncomputable def bF (G : Table m) (hm : 1 ≤ m) : (j : Fin m) → Fin (G.counts j) :=
  fun j => ⟨(bsFinal (cG G))[j.val]?.getD 0, (bs_spec G hm j).1⟩

theorem prob_rows (rows : ℕ → List ℚ) (k j a : ℕ) (hj : j < k) :
    prob ((List.range k).map rows) j a = (rows j)[a]?.getD 0 := by
  simp [prob, List.getElem?_map, List.getElem?_range hj]

theorem mixRow_get (G : Table m) (hm : 1 ≤ m) (j : Fin m) (b : ℕ) (a : Fin (G.counts j)) :
    (mixRow (cG G) j b)[a.val]?.getD 0 = mixVal j b a := by
  unfold mixRow
  rw [getD_sizes, rng_eq _ _ (counts_le G hm j)]
  simp [List.getElem?_map, List.getElem?_range a.isLt]

theorem pureRow_get (G : Table m) (hm : 1 ≤ m) (j : Fin m) (b : ℕ) (a : Fin (G.counts j)) :
    (pureRow (cG G) j b)[a.val]?.getD 0 = if a.val = b then 1 else 0 := by
  unfold pureRow
  rw [getD_sizes, rng_eq _ _ (counts_le G hm j)]
  simp [List.getElem?_map, List.getElem?_range a.isLt]

theorem prob_profAt (G : Table m) (hm : 1 ≤ m) (r : Fin m) (cc : Fin (G.counts r)) :
    (fun (j : Fin m) (a : Fin (G.counts j)) =>
      ((prob (profAt (cG G) ((bsFinal (cG G)).take r.val) r.val cc.val) j a : ℚ) : ℝ)) =
      Function.update (Xr (bF G hm) r.val) r (dlt cc) := by
  funext j a
  have hjm : j.val < (cG G).1.length := by simp [cG, G.sizes_length]
  unfold profAt
  rw [prob_rows _ _ _ _ hjm]
  by_cases hjr : j = r
  · subst hjr
    simp only [lt_irrefl, if_false, if_true, Function.update_self, dlt]
    rw [pureRow_get G hm]
    simp only [Fin.ext_iff]
    split_ifs <;> simp
  · rw [Function.update_of_ne hjr]
    have hne : j.val ≠ r.val := fun e => hjr (Fin.ext e)
    simp only [Xr, hne, if_false]
    by_cases hlt : j.val < r.val
    · simp only [hlt, if_true]
      rw [mixRow_get G hm]
      simp [bF, List.getElem?_take, hlt]
    · simp only [hlt, if_false]
      rw [pureRow_get G hm]
      simp only [d0]
      split_ifs <;> simp

theorem hbr_G (G : Table m) (hm : 1 ≤ m) (R : Fin m) (cc : Fin (G.counts R)) :
    AGT.expectedPayoff G.utility (Function.update (Xr (bF G hm) R.val) R (dlt cc)) R ≤
      AGT.expectedPayoff G.utility (Function.update (Xr (bF G hm) R.val) R (dlt (bF G hm R))) R := by
  rw [← prob_profAt G hm R cc, ← prob_profAt G hm R (bF G hm R), ← payoff_eq G hm, ← payoff_eq G hm]
  exact_mod_cast (bs_spec G hm R).2 cc.val cc.isLt

def toRaw (q : ℚ) : RawRat := ⟨q.num.natAbs, q.den, q.den_pos⟩

theorem toRaw_value (q : ℚ) (hq : 0 ≤ q) : (toRaw q).value = (q : ℝ) := by
  simp only [toRaw, RawRat.value]
  have : (q.num.natAbs : ℤ) = q.num := Int.natAbs_of_nonneg (Rat.num_nonneg.2 hq)
  have h2 : ((q.num.natAbs : ℕ) : ℝ) = ((q.num : ℤ) : ℝ) := by
    have h3 : (((q.num.natAbs : ℕ) : ℤ) : ℝ) = ((q.num : ℤ) : ℝ) := congrArg (fun z : ℤ => (z : ℝ)) this
    rw [Int.cast_natCast] at h3
    exact h3
  rw [h2, Rat.cast_def]

theorem xFinal_rows (G : Table m) (hm : 1 ≤ m) :
    (xFinal (cG G)).map List.length = G.sizes := by
  apply List.ext_getElem
  · simp [xFinal, cG, G.sizes_length]
  · intro i h1 h2
    have hi : i < m := by rw [← G.sizes_length]; exact h2
    simp only [List.getElem_map, xFinal, List.getElem_range]
    unfold mixRow
    have := getD_sizes G ⟨i, hi⟩
    simp only at this
    rw [this, rng_eq _ _ (counts_le G hm ⟨i, hi⟩)]
    simp [Table.counts, List.getElem?_eq_getElem h2]

theorem flatten_getElem? {α : Type} : ∀ (L : List (List α)) (i a : ℕ) (hi : i < L.length),
    a < L[i].length → L.flatten[((L.take i).map List.length).sum + a]? = L[i][a]?
  | [], i, a, hi, _ => by simp at hi
  | l :: L, 0, a, _, ha => by
    simp only [List.take_zero, List.map_nil, List.sum_nil, zero_add, List.flatten_cons,
      List.getElem_cons_zero] at ha ⊢
    rw [List.getElem?_append_left ha]
  | l :: L, i + 1, a, hi, ha => by
    simp only [List.take_succ_cons, List.map_cons, List.sum_cons, List.flatten_cons,
      List.getElem_cons_succ] at ha ⊢
    rw [show l.length + ((L.take i).map List.length).sum + a =
      l.length + (((L.take i).map List.length).sum + a) by ring,
      List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
    exact flatten_getElem? L i a (by simpa using hi) ha

noncomputable def xOf (G : Table m) (hm : 1 ≤ m) : RawProfile m where
  sizes := G.sizes
  sizes_length := G.sizes_length
  sizes_pos := G.sizes_pos
  entries := (xFinal (cG G)).flatten.map toRaw
  entries_length := by rw [List.length_map, List.length_flatten, xFinal_rows G hm]

theorem mixVal_nonneg (j b a : ℕ) : 0 ≤ mixVal j b a := by
  unfold mixVal
  split_ifs <;> positivity

theorem xOf_on (G : Table m) (hm : 1 ≤ m) : (xOf G hm).on G.counts = Xr (bF G hm) m := by
  funext i a
  have him : i.val < (xFinal (cG G)).length := by simp [xFinal, cG, G.sizes_length]
  have hrow : (xFinal (cG G))[i.val] = mixRow (cG G) i.val ((bsFinal (cG G))[i.val]?.getD 0) := by
    simp [xFinal]
  have hlen : a.val < ((xFinal (cG G))[i.val]).length := by
    have := congrArg (fun L => L[i.val]?) (xFinal_rows G hm)
    simp only [List.getElem?_map, List.getElem?_eq_getElem him, Option.map_some] at this
    have h2 : i.val < G.sizes.length := by rw [G.sizes_length]; exact i.isLt
    rw [List.getElem?_eq_getElem h2] at this
    have h3 := Option.some.inj this
    rw [h3]
    have := a.isLt
    simpa [Table.counts, List.getElem?_eq_getElem h2] using this
  have hidx : (G.sizes.take i.val).sum = (((xFinal (cG G)).take i.val).map List.length).sum := by
    rw [← xFinal_rows G hm, List.map_take]
  have hf := flatten_getElem? (xFinal (cG G)) i.val a.val him hlen
  rw [← hidx] at hf
  have hget : ((xFinal (cG G))[i.val])[a.val]? = some (mixVal i.val (bF G hm i).val a.val) := by
    rw [hrow]
    have := mixRow_get G hm i ((bsFinal (cG G))[i.val]?.getD 0) a
    rw [List.getElem?_eq_getElem (by rw [← hrow]; exact hlen)] at this ⊢
    simp only [Option.getD_some] at this
    rw [this]; rfl
  simp only [RawProfile.on, RawProfile.at, xOf, List.getD_eq_getElem?_getD, List.getElem?_map, hf,
    hget, Option.map_some, Option.getD_some]
  rw [toRaw_value _ (mixVal_nonneg _ _ _)]
  simp [Xr, i.isLt, mixR]

theorem encNat_zero : OnlineCRS.Combine.encNat 0 = [] := rfl

theorem pack_eq (G : Table m) (hm : 1 ≤ m) : packItems (outItems (cG G)) = encProfile (xOf G hm) := by
  simp only [packItems, outItems, encProfile, pack, xOf, cG, List.flatMap_append, List.flatMap_map]
  congr 1
  · refine List.flatMap_congr (fun n _ => ?_)
    simp
  · refine List.flatMap_congr (fun q _ => ?_)
    simp [encRaw, pack, toRaw, encNat_zero, List.intercalate_cons_cons]

theorem bounded_G (G : Table m) : BoundedGame G.utility := by
  intro r a
  simp only [Table.utility]
  set k := r.val * G.sizes.prod + tupleRank a
  have h : ∀ x : RawRat, x ∈ G.entries ∨ x = zeroRat → x.value ∈ Set.Icc (0 : ℝ) 1 := by
    intro x hx
    simp only [RawRat.value, Set.mem_Icc]
    have hd : (0 : ℝ) < x.den := by exact_mod_cast x.den_pos
    constructor
    · positivity
    · rw [div_le_one hd]
      rcases hx with hx | hx
      · exact_mod_cast G.bounded x hx
      · subst hx; simp [zeroRat]
  apply h
  rw [List.getD_eq_getElem?_getD]
  by_cases hk : k < G.entries.length
  · left; rw [List.getElem?_eq_getElem hk]; exact List.getElem_mem hk
  · right; rw [List.getElem?_eq_none (by omega)]; rfl

theorem Falg_itemsOf (G : Table m) : Falg (itemsOf G) = outItems (cG G) := by
  unfold Falg; rw [ctxOf_itemsOf]; rfl

open OAI.MetricKMedian.Binary in
theorem lemma22_main : ∃ (M : Turing.TM2ComputableAux OnlineCRS.Combine.Sym OnlineCRS.Combine.Sym) (c : ℕ),
    ∀ m : ℕ, 1 ≤ m → ∀ G : Table m, ∃ x : RawProfile m, x.sizes = G.sizes ∧
      CFLOutliers.OutputsWithin M (encGame G) (encProfile x) (c * ((encGame G).length + 2) ^ c) ∧
      DGPNash.WellSupported.IsEpsApproxNash G.utility (x.on G.counts) (1 - 1 / (m : ℝ)) := by
  let Pin : PolyProgram (fun a : (Σ k, Table k) => MNRBridge.symBits (encGame a.2))
      (Automatic.enc : List (List ℕ) → List Bool) (fun a => itemsOf a.2) :=
    Tin.program.of_word (fun a => by
      show Tin.run none (MNRBridge.symBits (encGame a.2)) = _
      rw [Tin_run, encGame_hIn])
  let Pcore : PolyProgram (Automatic.enc : List (List ℕ) → List Bool)
      (Automatic.enc : List (List ℕ) → List Bool) Falg := poly_Falg.program
  let Pout : PolyProgram (Automatic.enc : List (List ℕ) → List Bool)
      (fun items => MNRBridge.symBits (packItems items)) id :=
    Tout.program.of_word (fun items => by
      show Tout.run (false, false, false) _ = _
      rw [Tout_items]; rfl)
  obtain ⟨M, c, hM⟩ := MNRBridge.bridge (ea := fun a : (Σ k, Table k) => encGame a.2) (eb := packItems)
    ((Pin.comp Pcore).comp Pout)
  refine ⟨M, c, fun m hm G => ⟨xOf G hm, rfl, ?_, ?_⟩⟩
  · have h := hM ⟨m, G⟩
    have e : (id ∘ (Falg ∘ fun a : (Σ k, Table k) => itemsOf a.2)) ⟨m, G⟩ = outItems (cG G) := by
      show Falg (itemsOf G) = _
      exact Falg_itemsOf G
    rw [e, pack_eq G hm] at h
    exact h
  · rw [xOf_on]
    exact hdrs G.utility (bounded_G G) (counts_pos G) hm (bF G hm) (fun R cc => hbr_G G hm R cc)

end MNRL22

-- ===== Dual43 =====
section Dual43

open NashAmplification.Filtering (Mixed Utility Tuple BoundedGame)
open Finset
open MultiNashRepair

theorem MNR43_swap {m : ℕ} {n : Fin m → ℕ}
    (F : (i : Fin m) → Fin (n i) → (j : Fin m) → Fin (n j) → ℝ) :
    ∑ i, ∑ a, ∑ j, ∑ b, F i a j b = ∑ j, ∑ b, ∑ i, ∑ a, F i a j b := by
  have L : ∑ i, ∑ a, ∑ j, ∑ b, F i a j b =
      ∑ p : (Σ i, Fin (n i)), ∑ q : (Σ j, Fin (n j)), F p.1 p.2 q.1 q.2 := by
    rw [Fintype.sum_sigma]
    refine sum_congr rfl fun i _ => sum_congr rfl fun a _ => ?_
    rw [Fintype.sum_sigma]
  have R : ∑ j, ∑ b, ∑ i, ∑ a, F i a j b =
      ∑ q : (Σ j, Fin (n j)), ∑ p : (Σ i, Fin (n i)), F p.1 p.2 q.1 q.2 := by
    rw [Fintype.sum_sigma]
    refine sum_congr rfl fun i _ => sum_congr rfl fun a _ => ?_
    rw [Fintype.sum_sigma]
  rw [L, R, Finset.sum_comm]

theorem MNR43_weak {m : ℕ} {n : Fin m → ℕ} (u : Utility n) (x : Mixed n) (η : ℝ)
    (w : (i : Fin m) → Fin (n i) → ℝ) (α : ℝ) (hw : DualFeasible u x η w α)
    (z : (j : Fin m) → Fin (n j) → ℝ) (hz : LPFeasible z) :
    dualObj u x w α ≤ lpObj u x η z := by
  obtain ⟨hw0, hw1, hα0, hα⟩ := hw
  obtain ⟨hz0, hz1⟩ := hz
  have hT : ∀ i a, gain u x i a + η * ∑ j, ∑ b, z j b * repl u x j b i a ≤ lpObj u x η z :=
    fun i a => le_ciSup (f := fun p : (Σ i : Fin m, Fin (n i)) =>
      gain u x p.1 p.2 + η * ∑ j, ∑ b, z j b * repl u x j b p.1 p.2)
      (Set.finite_range _).bddAbove ⟨i, a⟩
  -- Σ w (g + η Σ z B) ≤ lpObj
  have h1 : ∑ i, ∑ a, w i a * (gain u x i a + η * ∑ j, ∑ b, z j b * repl u x j b i a) ≤
      lpObj u x η z := by
    calc _ ≤ ∑ i, ∑ a, w i a * lpObj u x η z :=
          sum_le_sum fun i _ => sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hT i a) (hw0 i a)
      _ = lpObj u x η z := by
          rw [show ∑ i, ∑ a, w i a * lpObj u x η z = (∑ i, ∑ a, w i a) * lpObj u x η z by
            rw [Finset.sum_mul]; exact sum_congr rfl fun i _ => (Finset.sum_mul _ _ _).symm,
            hw1, one_mul]
  -- swap
  have h2 : ∑ i, ∑ a, w i a * (gain u x i a + η * ∑ j, ∑ b, z j b * repl u x j b i a) =
      dualObj u x w α + α + ∑ j, ∑ b, z j b * (η * ∑ i, ∑ a, w i a * repl u x j b i a) := by
    unfold dualObj
    simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    have := MNR43_swap (fun i a j b => w i a * (η * (z j b * repl u x j b i a)))
    rw [this]
    have e2 : ∑ j, ∑ b, ∑ i, ∑ a, w i a * (η * (z j b * repl u x j b i a)) =
        ∑ j, ∑ b, ∑ i, ∑ a, z j b * (η * (w i a * repl u x j b i a)) :=
      sum_congr rfl fun j _ => sum_congr rfl fun b _ => sum_congr rfl fun i _ =>
        sum_congr rfl fun a _ => by ring
    rw [e2]; ring
  have h3 : -α ≤ ∑ j, ∑ b, z j b * (η * ∑ i, ∑ a, w i a * repl u x j b i a) := by
    have hA : ∑ j, ∑ b, z j b * (-α) ≤ ∑ j, ∑ b, z j b * (η * ∑ i, ∑ a, w i a * repl u x j b i a) :=
      sum_le_sum fun j _ => sum_le_sum fun b _ =>
        mul_le_mul_of_nonneg_left (by linarith [hα j b]) (hz0 j b)
    have hB : ∑ j, ∑ b, z j b * (-α) = -α * ∑ j, ∑ b, z j b := by
      simp only [Finset.mul_sum]; exact sum_congr rfl fun j _ => sum_congr rfl fun b _ => by ring
    have hC : α * ∑ j, ∑ b, z j b ≤ α * 1 := mul_le_mul_of_nonneg_left hz1 hα0
    linarith
  linarith

theorem MNR43_le_value {m : ℕ} {n : Fin m → ℕ} (u : Utility n) (x : Mixed n) (η : ℝ)
    (w : (i : Fin m) → Fin (n i) → ℝ) (α : ℝ) (hw : DualFeasible u x η w α) :
    dualObj u x w α ≤ lpValue u x η := by
  unfold lpValue
  refine le_csInf ⟨lpObj u x η 0, 0, ⟨fun _ _ => le_rfl, by simp⟩, rfl⟩ ?_
  rintro _ ⟨z, hz, rfl⟩
  exact MNR43_weak u x η w α hw z hz

theorem MNR43_value_eq {m : ℕ} {n : Fin m → ℕ} (u : Utility n) (x : Mixed n) (η : ℝ)
    (w : (i : Fin m) → Fin (n i) → ℝ) (α : ℝ) (hw : DualFeasible u x η w α)
    (z : (j : Fin m) → Fin (n j) → ℝ) (hz : LPFeasible z) (hle : lpObj u x η z ≤ dualObj u x w α) :
    DualOptimal u x η w α := by
  refine ⟨hw, le_antisymm (MNR43_le_value u x η w α hw) ?_⟩
  unfold lpValue
  have hbdd : BddBelow (lpObj u x η '' {z | LPFeasible z}) := by
    refine ⟨dualObj u x w α, ?_⟩
    rintro _ ⟨z', hz', rfl⟩
    exact MNR43_weak u x η w α hw z' hz'
  exact (csInf_le hbdd ⟨z, hz, rfl⟩).trans hle


end Dual43

-- ===== R46A =====

namespace MNRRam
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic MNRL22
open OAI.Optimization.LinearProgramming

/-- RAM state representation: `(pc, data, index, out)` with `out = 0` running, `out = t+1` halted. -/
abbrev RS := ℕ × (List ℚ × (List ℕ × ℕ))

def setL {α : Type} (L : List α) (i : ℕ) (v : α) : List α := L.take i ++ v :: L.drop (i + 1)
def gQ (L : List ℚ) (i : ℕ) : ℚ := L[i]?.getD 0
def gN (L : List ℕ) (i : ℕ) : ℕ := L[i]?.getD 0

def putD (s : RS) (d : ℕ) (x : ℚ) : RS := (s.1 + 1, (setL s.2.1 d x, s.2.2))
def putI (s : RS) (d x : ℕ) : RS := (s.1 + 1, (s.2.1, (setL s.2.2.1 d x, s.2.2.2)))

def execR (i : RAM.Instr) : RS → RS :=
  match i with
  | .const d q => fun s => putD s d q
  | .copy d a => fun s => putD s d (gQ s.2.1 a)
  | .add d a b => fun s => putD s d (gQ s.2.1 a + gQ s.2.1 b)
  | .sub d a b => fun s => putD s d (gQ s.2.1 a - gQ s.2.1 b)
  | .mul d a b => fun s => putD s d (gQ s.2.1 a * gQ s.2.1 b)
  | .div d a b => fun s => putD s d (gQ s.2.1 a / gQ s.2.1 b)
  | .load d a => fun s => putD s d (gQ s.2.1 (gN s.2.2.1 a))
  | .store a d => fun s => putD s (gN s.2.2.1 a) (gQ s.2.1 d)
  | .addrConst d n => fun s => putI s d n
  | .addrCopy d a => fun s => putI s d (gN s.2.2.1 a)
  | .incr d a => fun s => putI s d (gN s.2.2.1 a + 1)
  | .decr d a => fun s => putI s d (gN s.2.2.1 a - 1)
  | .addrLoad d a => fun s => putI s d (gN s.2.2.1 (gN s.2.2.1 a))
  | .addrStore a d => fun s => putI s (gN s.2.2.1 a) (gN s.2.2.1 d)
  | .branchLT a b yes no => fun s => (if gQ s.2.1 a < gQ s.2.1 b then yes else no, s.2)
  | .branchAddrLT a b yes no => fun s => (if gN s.2.2.1 a < gN s.2.2.1 b then yes else no, s.2)
  | .jump t => fun s => (t, s.2)
  | .halt tag => fun s => (s.1, (s.2.1, (s.2.2.1, tag + 1)))

def dispatch : List RAM.Instr → ℕ → RS → RS
  | [], _, s => s
  | i :: p, k, s => if s.1 = k then execR i s else dispatch p (k + 1) s

def stepR (p : RAM.Program) (s : RS) : RS := if s.2.2.2 = 0 then dispatch p 0 s else s

section poly
theorem poly_setL {α : Type} [Coding α] [Inhabited α] :
    Poly (fun x : (List α × ℕ) × α => setL x.1.1 x.1.2 x.2) := by
  unfold setL
  have h1 : Poly (fun x : List α × ℕ => x.1.take x.2) := ⟨PolyProgram.listTake enc default⟩
  have h2 := poly_list_drop (α := α)
  have h3 : Poly (fun x : (List α × ℕ) × α => x.1.1.take x.1.2) := Poly.comp (f := fun x : List α × ℕ => x.1.take x.2) h1 Poly.fst
  have h4 : Poly (fun x : (List α × ℕ) × α => x.1.1.drop (x.1.2 + 1)) := by fun_prop
  fun_prop

@[fun_prop] theorem setL_comp {γ α : Type} [Coding γ] [Coding α] [Inhabited α] {f : γ → List α} {g : γ → ℕ}
    {h : γ → α} (hf : Poly f) (hg : Poly g) (hh : Poly h) : Poly (fun x => setL (f x) (g x) (h x)) :=
  Poly.comp (f := fun x : (List α × ℕ) × α => setL x.1.1 x.1.2 x.2) poly_setL
    (Poly.pair (Poly.pair hf hg) hh)

theorem poly_gQ : Poly (fun x : List ℚ × ℕ => gQ x.1 x.2) := by unfold gQ; fun_prop
@[fun_prop] theorem gQ_comp {γ : Type} [Coding γ] {f : γ → List ℚ} {g : γ → ℕ} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => gQ (f x) (g x)) := Poly.comp (f := fun x : List ℚ × ℕ => gQ x.1 x.2) poly_gQ (Poly.pair hf hg)
theorem poly_gN : Poly (fun x : List ℕ × ℕ => gN x.1 x.2) := by unfold gN; fun_prop
@[fun_prop] theorem gN_comp {γ : Type} [Coding γ] {f : γ → List ℕ} {g : γ → ℕ} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => gN (f x) (g x)) := Poly.comp (f := fun x : List ℕ × ℕ => gN x.1 x.2) poly_gN (Poly.pair hf hg)

theorem poly_execR (i : RAM.Instr) : Poly (execR i) := by
  cases i <;> simp only [execR, putD, putI] <;> fun_prop

theorem poly_dispatch (p : List RAM.Instr) (k : ℕ) : Poly (dispatch p k) := by
  induction p generalizing k with
  | nil => exact Poly.identity
  | cons i p ih =>
    have h1 := poly_execR i
    have h2 := ih (k + 1)
    show Poly (fun s => if s.1 = k then execR i s else dispatch p (k + 1) s)
    fun_prop

theorem poly_stepR (p : RAM.Program) : Poly (stepR p) := by
  have := poly_dispatch p 0
  unfold stepR; fun_prop
end poly

section sim

theorem setL_length {α : Type} (L : List α) (i : ℕ) (v : α) (h : i < L.length) :
    (setL L i v).length = L.length := by
  simp [setL]; omega

theorem gQ_setL (L : List ℚ) (i : ℕ) (v : ℚ) (h : i < L.length) (j : ℕ) :
    gQ (setL L i v) j = Function.update (fun j => gQ L j) i v j := by
  simp only [gQ, setL, Function.update_apply]
  by_cases hji : j = i
  · subst hji; simp [List.getElem?_append_right, Nat.min_eq_left h.le]
  · simp only [hji, if_false]
    rcases Nat.lt_or_ge j i with hlt | hge
    · rw [List.getElem?_append_left (by simp; omega), List.getElem?_take_of_lt hlt]
    · rw [List.getElem?_append_right (by simp; omega)]
      simp only [List.length_take, Nat.min_eq_left h.le]
      have : j - i ≠ 0 := by omega
      obtain ⟨t, ht⟩ : ∃ t, j - i = t + 1 := ⟨j - i - 1, by omega⟩
      rw [ht, List.getElem?_cons_succ, List.getElem?_drop]
      congr 2; omega

theorem gN_setL (L : List ℕ) (i : ℕ) (v : ℕ) (h : i < L.length) (j : ℕ) :
    gN (setL L i v) j = Function.update (fun j => gN L j) i v j := by
  simp only [gN, setL, Function.update_apply]
  by_cases hji : j = i
  · subst hji; simp [List.getElem?_append_right, Nat.min_eq_left h.le]
  · simp only [hji, if_false]
    rcases Nat.lt_or_ge j i with hlt | hge
    · rw [List.getElem?_append_left (by simp; omega), List.getElem?_take_of_lt hlt]
    · rw [List.getElem?_append_right (by simp; omega)]
      simp only [List.length_take, Nat.min_eq_left h.le]
      obtain ⟨t, ht⟩ : ∃ t, j - i = t + 1 := ⟨j - i - 1, by omega⟩
      rw [ht, List.getElem?_cons_succ, List.getElem?_drop]
      congr 2; omega

def absR (s : RS) : RAM.State ℚ :=
  ⟨s.1, fun i => gQ s.2.1 i, fun i => gN s.2.2.1 i, if s.2.2.2 = 0 then none else some (s.2.2.2 - 1)⟩

theorem dispatch_eq (p : List RAM.Instr) (k : ℕ) (s : RS) :
    dispatch p k s = if h : k ≤ s.1 ∧ s.1 - k < p.length then execR (p[s.1 - k]'h.2) s else s := by
  induction p generalizing k with
  | nil => simp [dispatch]
  | cons i p ih =>
    simp only [dispatch]
    by_cases hk : s.1 = k
    · subst hk; simp
    · rw [if_neg hk, ih]
      by_cases h1 : k + 1 ≤ s.1 ∧ s.1 - (k + 1) < p.length
      · have h2 : k ≤ s.1 ∧ s.1 - k < (i :: p).length := by simp; omega
        rw [dif_pos h1, dif_pos h2]
        congr 1
        have : s.1 - k = (s.1 - (k + 1)) + 1 := by omega
        simp [this]
      · have h2 : ¬ (k ≤ s.1 ∧ s.1 - k < (i :: p).length) := by
          intro h; apply h1; simp at h; omega
        rw [dif_neg h1, dif_neg h2]

theorem absR_putD (s : RS) (d : ℕ) (x : ℚ) (h : d < s.2.1.length) :
    absR (putD s d x) = (absR s).putData d x := by
  simp only [absR, putD, RAM.State.putData]
  congr 1
  funext j; exact gQ_setL _ _ _ h j

theorem absR_putI (s : RS) (d x : ℕ) (h : d < s.2.2.1.length) :
    absR (putI s d x) = (absR s).putIndex d x := by
  simp only [absR, putI, RAM.State.putIndex]
  congr 1
  funext j; exact gN_setL _ _ _ h j

def writeOK : RAM.Instr → RS → Prop
  | .const d _, s => d < s.2.1.length
  | .copy d _, s => d < s.2.1.length
  | .add d _ _, s => d < s.2.1.length
  | .sub d _ _, s => d < s.2.1.length
  | .mul d _ _, s => d < s.2.1.length
  | .div d _ _, s => d < s.2.1.length
  | .load d _, s => d < s.2.1.length
  | .store a _, s => gN s.2.2.1 a < s.2.1.length
  | .addrConst d _, s => d < s.2.2.1.length
  | .addrCopy d _, s => d < s.2.2.1.length
  | .incr d _, s => d < s.2.2.1.length
  | .decr d _, s => d < s.2.2.1.length
  | .addrLoad d _, s => d < s.2.2.1.length
  | .addrStore a _, s => gN s.2.2.1 a < s.2.2.1.length
  | _, _ => True

theorem execR_sim (i : RAM.Instr) (s : RS) (s' : RAM.State ℚ) (hw : writeOK i s)
    (hex : RAM.execInstr i (absR s) = some s') : absR (execR i s) = s' := by
  cases i with
  | const d q => simp only [RAM.execInstr, Option.some.injEq] at hex; subst hex; exact absR_putD _ _ _ hw
  | copy d a => simp only [RAM.execInstr, Option.some.injEq] at hex; subst hex; exact absR_putD _ _ _ hw
  | add d a b => simp only [RAM.execInstr, Option.some.injEq] at hex; subst hex; exact absR_putD _ _ _ hw
  | sub d a b => simp only [RAM.execInstr, Option.some.injEq] at hex; subst hex; exact absR_putD _ _ _ hw
  | mul d a b => simp only [RAM.execInstr, Option.some.injEq] at hex; subst hex; exact absR_putD _ _ _ hw
  | div d a b =>
    simp only [RAM.execInstr] at hex
    split_ifs at hex with h0
    simp only [Option.some.injEq] at hex; subst hex; exact absR_putD _ _ _ hw
  | load d a => simp only [RAM.execInstr, Option.some.injEq] at hex; subst hex; exact absR_putD _ _ _ hw
  | store a d => simp only [RAM.execInstr, Option.some.injEq] at hex; subst hex; exact absR_putD _ _ _ hw
  | addrConst d n => simp only [RAM.execInstr, Option.some.injEq] at hex; subst hex; exact absR_putI _ _ _ hw
  | addrCopy d a => simp only [RAM.execInstr, Option.some.injEq] at hex; subst hex; exact absR_putI _ _ _ hw
  | incr d a => simp only [RAM.execInstr, Option.some.injEq] at hex; subst hex; exact absR_putI _ _ _ hw
  | decr d a => simp only [RAM.execInstr, Option.some.injEq] at hex; subst hex; exact absR_putI _ _ _ hw
  | addrLoad d a => simp only [RAM.execInstr, Option.some.injEq] at hex; subst hex; exact absR_putI _ _ _ hw
  | addrStore a d => simp only [RAM.execInstr, Option.some.injEq] at hex; subst hex; exact absR_putI _ _ _ hw
  | branchLT a b y n => simp only [RAM.execInstr, Option.some.injEq] at hex; subst hex; rfl
  | branchAddrLT a b y n => simp only [RAM.execInstr, Option.some.injEq] at hex; subst hex; rfl
  | jump t => simp only [RAM.execInstr, Option.some.injEq] at hex; subst hex; rfl
  | halt tag =>
    simp only [RAM.execInstr, Option.some.injEq] at hex; subst hex
    simp [absR, execR]

theorem stepR_sim (p : RAM.Program) (s : RS) (s' : RAM.State ℚ)
    (hstep : RAM.step p (absR s) = some s')
    (hw : ∀ i, p[s.1]? = some i → writeOK i s) : absR (stepR p s) = s' := by
  unfold RAM.step at hstep
  have hout : s.2.2.2 = 0 := by
    by_contra hne
    simp [absR, hne] at hstep
  have hout' : (absR s).output = none := by simp [absR, hout]
  rw [hout'] at hstep
  cases hp : p[(absR s).pc]? with
  | none => rw [hp] at hstep; simp at hstep
  | some i =>
    rw [hp] at hstep
    simp only at hstep
    have hpc : (absR s).pc = s.1 := rfl
    rw [hpc] at hp
    have hlt : s.1 < p.length := (List.getElem?_eq_some_iff.1 hp).1
    unfold stepR
    rw [if_pos hout, dispatch_eq, dif_pos ⟨Nat.zero_le _, by simpa using hlt⟩]
    have hi : p[s.1 - 0]'(by simpa using hlt) = i := by
      simp only [Nat.sub_zero]; exact (List.getElem?_eq_some_iff.1 hp).2
    rw [hi]
    exact execR_sim i s s' (hw i hp) hstep

end sim

end MNRRam

-- ===== R46B =====

namespace MNRRam
open OAI.Optimization.LinearProgramming

def instrMax : RAM.Instr → ℕ
  | .const d _ => d
  | .copy d a => d + a
  | .add d a b => d + a + b
  | .sub d a b => d + a + b
  | .mul d a b => d + a + b
  | .div d a b => d + a + b
  | .load d a => d + a
  | .store a d => a + d
  | .addrConst d n => d + n
  | .addrCopy d a => d + a
  | .incr d a => d + a
  | .decr d a => d + a
  | .addrLoad d a => d + a
  | .addrStore a d => a + d
  | .branchLT a b y n => a + b + y + n
  | .branchAddrLT a b y n => a + b + y + n
  | .jump t => t
  | .halt tag => tag

def maxC (p : RAM.Program) : ℕ := (p.map instrMax).sum

theorem instrMax_le (p : RAM.Program) (i : RAM.Instr) (h : i ∈ p) : instrMax i ≤ maxC p := by
  unfold maxC
  exact List.le_sum_of_mem (List.mem_map.2 ⟨i, h, rfl⟩)

/-- index registers stay bounded along a run -/
theorem index_step (p : RAM.Program) (s s' : RAM.State ℚ) (V : ℕ) (hV : ∀ j, s.index j ≤ V)
    (hc : maxC p ≤ V) (h : RAM.step p s = some s') : ∀ j, s'.index j ≤ V + 1 := by
  unfold RAM.step at h
  cases ho : s.output with
  | some _ => rw [ho] at h; simp at h
  | none =>
    rw [ho] at h
    cases hp : p[s.pc]? with
    | none => rw [hp] at h; simp at h
    | some i =>
      rw [hp] at h
      have hi : i ∈ p := List.mem_of_getElem? hp
      have him := instrMax_le p i hi
      intro j
      cases i <;> simp only [RAM.execInstr, instrMax] at h him <;>
        (try split_ifs at h) <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
        simp only [RAM.State.putData, RAM.State.putIndex, Function.update_apply] <;>
        (try split_ifs) <;>
        (first | (have := hV j; omega) | omega | exact le_trans (hV _) (by omega) |
          exact Nat.add_le_add_right (hV _) 1 | exact le_trans (Nat.sub_le _ _) (le_trans (hV _) (by omega)))

/-! ### the LP input -/

abbrev LPIn := (ℕ × ℕ) × List ℚ

def goodIn (x : LPIn) : Prop := 0 < x.1.1 ∧ 0 < x.1.2 ∧ x.2.length = x.1.1 * x.1.2 + x.1.1 + x.1.2

def Aof (x : LPIn) : Matrix (Fin x.1.1) (Fin x.1.2) ℚ := fun i j => x.2.getD (i.val * x.1.2 + j.val) 0
def bof (x : LPIn) : Fin x.1.1 → ℚ := fun i => x.2.getD (x.1.1 * x.1.2 + i.val) 0
def oof (x : LPIn) : Fin x.1.2 → ℚ := fun j => x.2.getD (x.1.1 * x.1.2 + x.1.1 + j.val) 0

def inpOf (x : LPIn) : List ℚ := lpInput (Aof x) (bof x) ++ List.ofFn (oof x)

theorem ofFn_seg (L : List ℚ) (off n : ℕ) (h : off + n ≤ L.length) :
    List.ofFn (fun k : Fin n => L.getD (off + k.val) 0) = (L.drop off).take n := by
  apply List.ext_getElem
  · simp; omega
  · intro i h1 h2
    simp only [List.getElem_ofFn, List.getElem_take, List.getElem_drop, List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_getElem (by simp at h1; omega)]; rfl

theorem inpOf_eq (x : LPIn) (hx : goodIn x) : inpOf x = x.2 := by
  obtain ⟨hm, hd, hl⟩ := hx
  set m := x.1.1
  set d := x.1.2
  have hA : (List.ofFn fun i => List.ofFn (Aof x i)).flatten =
      List.ofFn (fun k : Fin (m * d) => x.2.getD (0 + k.val) 0) := by
    rw [List.ofFn_mul (f := fun k : Fin (m * d) => x.2.getD (0 + k.val) 0)]
    congr 1
    congr 1
    funext i
    congr 1
    funext j
    simp [Aof, m, d]
  have hB : List.ofFn (bof x) = List.ofFn (fun k : Fin m => x.2.getD (m * d + k.val) 0) := rfl
  have hO : List.ofFn (oof x) = List.ofFn (fun k : Fin d => x.2.getD (m * d + m + k.val) 0) := rfl
  simp only [inpOf, lpInput]
  rw [hA, hB, hO, ofFn_seg _ _ _ (by omega), ofFn_seg _ _ _ (by omega), ofFn_seg _ _ _ (by omega)]
  simp only [List.drop_zero]
  conv_rhs => rw [← List.take_append_drop (m * d) x.2]
  rw [List.append_assoc]
  congr 1
  conv_rhs => rw [← List.take_append_drop m (x.2.drop (m * d))]
  congr 1
  rw [List.drop_drop, List.take_of_length_le (by simp; omega)]

/-! ### the platform solver -/

theorem spo : StronglyPolynomialOptimization := strongly_polynomial_optimization

noncomputable def oP : RAM.Program := Classical.choose spo
noncomputable def oc : ℕ := Classical.choose (Classical.choose_spec spo)
noncomputable def oe : ℕ := Classical.choose (Classical.choose_spec (Classical.choose_spec spo))
noncomputable def obC : ℕ :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec spo)))
noncomputable def obE : ℕ :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec spo))))

theorem o_spec : ∀ (m d : ℕ), 0 < m → 0 < d →
    ∀ (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (obj : Fin d → ℚ),
    ∃ (k : ℕ) (t : Fin (k + 1) → RAM.State ℚ),
      RAM.Trace oP (RAM.start [m, d] (lpInput A b ++ List.ofFn obj)) k t ∧ k ≤ RAM.polyBound oc oe (m + d) ∧
      (∀ i, RAM.scalarBound (RAM.polyBound obC obE (RAM.totalBits (lpInput A b ++ List.ofFn obj))) (t i)) ∧
      OptimizationOutput A b obj (t (Fin.last k)) :=
  Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec spo))))

/-! ### padded start and the run invariant -/

def powList (L : List ℚ) : ℕ → List ℚ
  | 0 => [0]
  | k + 1 => (powList L k).flatMap (fun _ => 0 :: L.map (fun _ => 0))

theorem flatMap_len_const {α β : Type} (l : List α) (f : α → List β) (c : ℕ) (h : ∀ a, (f a).length = c) :
    (l.flatMap f).length = l.length * c := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, h, ih]; ring

theorem powList_length (L : List ℚ) (k : ℕ) : (powList L k).length = (L.length + 1) ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [powList]
    rw [flatMap_len_const _ _ (L.length + 1) (fun _ => by simp), ih, pow_succ]

noncomputable def C0 : ℕ := oc + maxC oP + 2

noncomputable def padQ (L : List ℚ) : List ℚ := L.map (fun _ => 0) ++ (List.range C0).flatMap (fun _ => powList L oe)
noncomputable def padN (L : List ℚ) : List ℕ := (padQ L).map (fun _ => 0)

theorem padQ_length (L : List ℚ) : (padQ L).length = L.length + C0 * (L.length + 1) ^ oe := by
  unfold padQ
  rw [List.length_append, flatMap_len_const _ _ ((L.length + 1) ^ oe) (fun _ => powList_length L oe)]
  simp

theorem powList_zero (L : List ℚ) (k : ℕ) : ∀ q ∈ powList L k, q = 0 := by
  induction k with
  | zero => simp [powList]
  | succ k ih =>
    intro q hq
    simp only [powList, List.mem_flatMap, List.mem_cons, List.mem_map] at hq
    obtain ⟨_, _, hq⟩ := hq
    rcases hq with rfl | ⟨_, _, rfl⟩ <;> rfl

theorem padQ_zero (L : List ℚ) : ∀ q ∈ padQ L, q = 0 := by
  intro q hq
  simp only [padQ, List.mem_append, List.mem_map, List.mem_flatMap] at hq
  rcases hq with ⟨_, _, rfl⟩ | ⟨_, _, hq⟩
  · rfl
  · exact powList_zero L oe q hq

noncomputable def rep0 (x : LPIn) : RS := (0, (x.2 ++ padQ x.2, ([x.1.1, x.1.2] ++ padN x.2, 0)))

theorem absR_rep0 (x : LPIn) : absR (rep0 x) = RAM.start [x.1.1, x.1.2] x.2 := by
  simp only [absR, rep0, RAM.start]
  congr 1
  · funext j
    simp only [gQ]
    by_cases hj : j < x.2.length
    · rw [List.getElem?_append_left hj]
    · rw [List.getElem?_append_right (by omega), List.getElem?_eq_none (l := x.2) (by omega)]
      cases h : (padQ x.2)[j - x.2.length]? with
      | none => rfl
      | some q => simp [padQ_zero x.2 q (List.mem_of_getElem? h)]
  · funext j
    simp only [gN]
    by_cases hj : j < 2
    · rw [List.getElem?_append_left (by simpa using hj)]
    · rw [List.getElem?_append_right (by simp; omega),
        List.getElem?_eq_none (l := [x.1.1, x.1.2]) (by simp; omega)]
      cases h : (padN x.2)[j - 2]? with
      | none => rfl
      | some q =>
        simp only [padN, List.getElem?_map] at h
        cases h' : (padQ x.2)[j - 2]? <;> simp_all


noncomputable def iterR (s : RS) (i : ℕ) : RS := (stepR oP)^[i] s

theorem execR_len (i : RAM.Instr) (s : RS) (hw : writeOK i s) :
    (execR i s).2.1.length = s.2.1.length ∧ (execR i s).2.2.1.length = s.2.2.1.length := by
  cases i <;> simp only [execR, putD, putI, writeOK] at hw ⊢ <;>
    (first | exact ⟨setL_length _ _ _ hw, rfl⟩ | exact ⟨rfl, setL_length _ _ _ hw⟩ |
      exact setL_length _ _ _ hw | simp [setL_length _ _ _ hw] | simp)

theorem stepR_len (p : RAM.Program) (s : RS) (hw : ∀ i, p[s.1]? = some i → writeOK i s) :
    (stepR p s).2.1.length = s.2.1.length ∧ (stepR p s).2.2.1.length = s.2.2.1.length := by
  unfold stepR
  split_ifs with h
  · rw [dispatch_eq]
    split_ifs with h2
    · apply execR_len
      apply hw
      simp only [Nat.sub_zero] at h2 ⊢
      exact List.getElem?_eq_some_iff.2 ⟨h2.2, rfl⟩
    · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

noncomputable def Kc (x : LPIn) : ℕ := RAM.polyBound oc oe (x.1.1 + x.1.2)
noncomputable def M0 (x : LPIn) : ℕ := max (max x.1.1 x.1.2) (maxC oP)
noncomputable def Dl (x : LPIn) : ℕ := x.2.length + (padQ x.2).length
noncomputable def Il (x : LPIn) : ℕ := 2 + (padN x.2).length

theorem inpOf_eq' (x : LPIn) (hx : goodIn x) : lpInput (Aof x) (bof x) ++ List.ofFn (oof x) = x.2 :=
  inpOf_eq x hx

theorem bound_D (x : LPIn) (hx : goodIn x) : M0 x + Kc x < Dl x ∧ M0 x + Kc x < Il x ∧ maxC oP < Dl x ∧
    maxC oP < Il x := by
  obtain ⟨hm, hd, hl⟩ := hx
  have hmd : x.1.1 + x.1.2 ≤ x.2.length := by rw [hl]; nlinarith
  have hP : 1 ≤ (x.2.length + 1) ^ oe := Nat.one_le_pow _ _ (by omega)
  have hK : Kc x ≤ oc * (x.2.length + 1) ^ oe := by
    unfold Kc RAM.polyBound
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
  set P := (x.2.length + 1) ^ oe with hPdef
  have hpad : (padQ x.2).length = x.2.length + (oc * P + (maxC oP + 2) * P) := by
    rw [padQ_length]; simp only [C0]; ring
  have hpadN : (padN x.2).length = (padQ x.2).length := by simp [padN]
  have hM : M0 x ≤ x.2.length + maxC oP := by unfold M0; omega
  have e2 : maxC oP + 2 ≤ (maxC oP + 2) * P := Nat.le_mul_of_pos_right _ hP
  unfold Dl Il
  rw [hpadN, hpad]
  generalize oc * P = Q1 at *
  generalize (maxC oP + 2) * P = Q2 at *
  omega


noncomputable def kOf (x : LPIn) (hx : goodIn x) : ℕ :=
  Classical.choose (o_spec x.1.1 x.1.2 hx.1 hx.2.1 (Aof x) (bof x) (oof x))
noncomputable def tOf (x : LPIn) (hx : goodIn x) : Fin (kOf x hx + 1) → RAM.State ℚ :=
  Classical.choose (Classical.choose_spec (o_spec x.1.1 x.1.2 hx.1 hx.2.1 (Aof x) (bof x) (oof x)))
theorem tOf_spec (x : LPIn) (hx : goodIn x) :
    RAM.Trace oP (RAM.start [x.1.1, x.1.2] (lpInput (Aof x) (bof x) ++ List.ofFn (oof x))) (kOf x hx) (tOf x hx) ∧
      kOf x hx ≤ RAM.polyBound oc oe (x.1.1 + x.1.2) ∧
      (∀ i, RAM.scalarBound (RAM.polyBound obC obE (RAM.totalBits (lpInput (Aof x) (bof x) ++ List.ofFn (oof x))))
        (tOf x hx i)) ∧
      OptimizationOutput (Aof x) (bof x) (oof x) (tOf x hx (Fin.last (kOf x hx))) :=
  Classical.choose_spec (Classical.choose_spec (o_spec x.1.1 x.1.2 hx.1 hx.2.1 (Aof x) (bof x) (oof x)))

theorem writeOK_of (s : RS) (i0 : RAM.Instr) (hi : i0 ∈ oP) (V : ℕ) (hV : ∀ j, gN s.2.2.1 j ≤ V)
    (hD : V < s.2.1.length) (hI : V < s.2.2.1.length) (hcD : maxC oP < s.2.1.length)
    (hcI : maxC oP < s.2.2.1.length) : writeOK i0 s := by
  have him := instrMax_le oP i0 hi
  cases i0 <;> simp only [writeOK, instrMax] at him ⊢ <;>
    first | omega | trivial | exact lt_of_le_of_lt (hV _) hD | exact lt_of_le_of_lt (hV _) hI

theorem run_inv (x : LPIn) (hx : goodIn x) : ∀ i (hi : i ≤ kOf x hx),
    absR (iterR (rep0 x) i) = tOf x hx ⟨i, by omega⟩ ∧ (iterR (rep0 x) i).2.1.length = Dl x ∧
      (iterR (rep0 x) i).2.2.1.length = Il x ∧ ∀ j, (tOf x hx ⟨i, by omega⟩).index j ≤ M0 x + i := by
  obtain ⟨⟨htr0, htrs⟩, hk, -, -⟩ := tOf_spec x hx
  have hB := bound_D x hx
  have hKk : kOf x hx ≤ Kc x := hk
  intro i
  induction i with
  | zero =>
    intro _
    have e0 : (⟨0, by omega⟩ : Fin (kOf x hx + 1)) = 0 := rfl
    refine ⟨?_, ?_, ?_, ?_⟩
    · show absR (rep0 x) = _
      rw [absR_rep0, e0, htr0, inpOf_eq' x hx]
    · simp [iterR, rep0, Dl]
    · simp [iterR, rep0, Il]; omega
    · intro j
      rw [e0, htr0]
      simp only [RAM.start]
      have : M0 x ≥ max x.1.1 x.1.2 := le_max_left _ _
      rcases j with _ | _ | j <;> simp <;> omega
  | succ i ih =>
    intro hi
    obtain ⟨h1, h2, h3, h4⟩ := ih (by omega)
    set s := iterR (rep0 x) i
    have hstep : RAM.step oP (absR s) = some (tOf x hx ⟨i + 1, by omega⟩) := by
      rw [h1]; exact htrs ⟨i, by omega⟩
    have hV : ∀ j, gN s.2.2.1 j ≤ M0 x + i := fun j => by
      have := h4 j
      rw [← h1] at this
      exact this
    have hw : ∀ i0, oP[s.1]? = some i0 → writeOK i0 s := fun i0 hi0 =>
      writeOK_of s i0 (List.mem_of_getElem? hi0) (M0 x + i) hV (by rw [h2]; omega) (by rw [h3]; omega)
        (by rw [h2]; exact hB.2.2.1) (by rw [h3]; exact hB.2.2.2)
    have hit : iterR (rep0 x) (i + 1) = stepR oP s := Function.iterate_succ_apply' _ _ _
    have hlen := stepR_len oP s hw
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hit]; exact stepR_sim oP s _ hstep hw
    · rw [hit, hlen.1, h2]
    · rw [hit, hlen.2, h3]
    · intro j
      have hc : maxC oP ≤ M0 x + i := le_trans (le_max_right _ _) (Nat.le_add_right _ _)
      have := index_step oP (absR s) _ (M0 x + i) (by rw [h1]; exact h4) hc hstep j
      omega


/-- program counter and output tag stay bounded -/
theorem pcout_step (s s' : RAM.State ℚ) (hpc : s.pc ≤ maxC oP + oP.length)
    (hout : ∀ t, s.output = some t → t ≤ maxC oP) (h : RAM.step oP s = some s') :
    s'.pc ≤ maxC oP + oP.length ∧ ∀ t, s'.output = some t → t ≤ maxC oP := by
  unfold RAM.step at h
  cases ho : s.output with
  | some _ => rw [ho] at h; simp at h
  | none =>
    rw [ho] at h
    cases hp : oP[s.pc]? with
    | none => rw [hp] at h; simp at h
    | some i =>
      rw [hp] at h
      have hi : i ∈ oP := List.mem_of_getElem? hp
      have him := instrMax_le oP i hi
      have hlt : s.pc < oP.length := (List.getElem?_eq_some_iff.1 hp).1
      cases i <;> simp only [RAM.execInstr, instrMax] at h him <;>
        (try split_ifs at h) <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
        simp only [RAM.State.putData, RAM.State.putIndex, ho, reduceCtorEq, false_implies, implies_true,
          and_true, Option.some.injEq] <;>
        (try split_ifs) <;> (try omega) <;> (try (intro t ht; omega)) <;>
        (try exact ⟨hpc, fun t ht => ht ▸ him⟩)


theorem bits_len_log2 (n : ℕ) : n.bits.length ≤ n.log2 + 2 := by
  have h : n ≤ 2 ^ (n.log2 + 1) := (Nat.lt_log2_self).le
  have := OAI.MetricKMedian.Binary.NatBinary.length_le_height h
  omega

theorem log2_le_bits (n : ℕ) : n.log2 ≤ n.bits.length := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · rw [Nat.size_eq_bits_len]
    have := (Nat.log2_lt (Nat.pos_iff_ne_zero.1 h)).2 (Nat.lt_size_self n)
    omega

open OAI.MetricKMedian.Binary in
theorem ratEnc_le (q : ℚ) : (Ratio.encode q).length ≤ 13 + 2 * RAM.ratBits q := by
  rw [Ratio.encode_length]
  unfold RAM.ratBits
  have h1 := bits_len_log2 q.num.natAbs
  have h2 := bits_len_log2 q.den
  omega

open OAI.MetricKMedian.Binary in
theorem ratBits_le_enc (q : ℚ) : RAM.ratBits q ≤ (Ratio.encode q).length := by
  rw [Ratio.encode_length]
  unfold RAM.ratBits
  have h1 := log2_le_bits q.num.natAbs
  have h2 := log2_le_bits q.den
  omega

open OAI.MetricKMedian.Binary in
theorem totalBits_le (L : List ℚ) : RAM.totalBits L ≤ (encodeList Ratio.encode L).length := by
  induction L with
  | nil => simp [RAM.totalBits, encodeList]
  | cons q L ih =>
    simp only [RAM.totalBits, List.map_cons, List.sum_cons] at ih ⊢
    rw [EncodedList.cons_length]
    have := ratBits_le_enc q
    omega

end MNRRam
-- ===== R46C =====

namespace MNRRam
open OAI.Optimization.LinearProgramming
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

theorem pc_inv (x : LPIn) (hx : goodIn x) : ∀ i (hi : i ≤ kOf x hx),
    (tOf x hx ⟨i, by omega⟩).pc ≤ maxC oP + oP.length ∧
      ∀ t, (tOf x hx ⟨i, by omega⟩).output = some t → t ≤ maxC oP := by
  obtain ⟨⟨htr0, htrs⟩, -, -, -⟩ := tOf_spec x hx
  intro i
  induction i with
  | zero =>
    intro _
    have e0 : (⟨0, by omega⟩ : Fin (kOf x hx + 1)) = 0 := rfl
    rw [e0, htr0]; simp [RAM.start]
  | succ i ih =>
    intro hi
    obtain ⟨h1, h2⟩ := ih (by omega)
    exact pcout_step _ _ h1 h2 (htrs ⟨i, by omega⟩)

theorem last_halted (x : LPIn) (hx : goodIn x) : ∃ t, (tOf x hx (Fin.last _)).output = some t := by
  obtain ⟨-, -, -, hout⟩ := tOf_spec x hx
  rcases hout with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> exact ⟨_, h⟩

theorem not_halted (x : LPIn) (hx : goodIn x) (i : ℕ) (hi : i < kOf x hx) :
    (tOf x hx ⟨i, by omega⟩).output = none := by
  obtain ⟨⟨-, htrs⟩, -, -, -⟩ := tOf_spec x hx
  have h := htrs ⟨i, hi⟩
  unfold RAM.step at h
  cases ho : (tOf x hx (Fin.castSucc ⟨i, hi⟩)).output with
  | none => exact ho
  | some _ => rw [ho] at h; simp at h

abbrev LS := ℕ × (LPIn × RS)

def validLS (a : LS) : Prop :=
  ∃ hx : goodIn a.2.1, ∃ i, i ≤ kOf a.2.1 hx ∧ a.1 = Kc a.2.1 - i ∧ a.2.2 = iterR (rep0 a.2.1) i

abbrev VS := {a : LS // validLS a}

theorem out_iff (x : LPIn) (hx : goodIn x) (i : ℕ) (hi : i ≤ kOf x hx) :
    (iterR (rep0 x) i).2.2.2 ≠ 0 ↔ i = kOf x hx := by
  have hab := (run_inv x hx i hi).1
  have hout : (absR (iterR (rep0 x) i)).output =
      (if (iterR (rep0 x) i).2.2.2 = 0 then none else some ((iterR (rep0 x) i).2.2.2 - 1)) := rfl
  constructor
  · intro hne
    by_contra hik
    have := not_halted x hx i (by omega)
    rw [← hab, hout, if_neg hne] at this
    simp at this
  · intro hik
    subst hik
    obtain ⟨t, ht⟩ := last_halted x hx
    intro h0
    have e : (⟨kOf x hx, by omega⟩ : Fin (kOf x hx + 1)) = Fin.last _ := rfl
    rw [e] at hab
    rw [← hab, hout, if_pos h0] at ht
    simp at ht

noncomputable def body0 (a : LS) : RS ⊕ LS :=
  if a.1 = 0 ∨ a.2.2.2.2.2 ≠ 0 then .inl a.2.2 else .inr (a.1 - 1, (a.2.1, stepR oP a.2.2))

theorem valid_next (a : VS) (h : ¬ (a.1.1 = 0 ∨ a.1.2.2.2.2.2 ≠ 0)) :
    validLS (a.1.1 - 1, (a.1.2.1, stepR oP a.1.2.2)) := by
  obtain ⟨hx, i, hi, hc, hr⟩ := a.2
  push_neg at h
  have hik : i ≠ kOf a.1.2.1 hx := by
    intro e
    have := (out_iff a.1.2.1 hx i hi).2 e
    rw [← hr] at this
    exact this h.2
  refine ⟨hx, i + 1, (show i + 1 ≤ kOf a.1.2.1 hx by omega), ?_, ?_⟩
  · show a.1.1 - 1 = Kc a.1.2.1 - (i + 1)
    omega
  · simp only; rw [hr]; exact (Function.iterate_succ_apply' _ _ _).symm

noncomputable def body (a : VS) : RS ⊕ VS :=
  if h : a.1.1 = 0 ∨ a.1.2.2.2.2.2 ≠ 0 then .inl a.1.2.2
  else .inr ⟨(a.1.1 - 1, (a.1.2.1, stepR oP a.1.2.2)), valid_next a h⟩

noncomputable def gfin (a : VS) : RS := iterR (rep0 a.1.2.1) (kOf a.1.2.1 a.2.fst)

noncomputable def eVS : VS → List Bool := fun a => (enc a.1 : List Bool)

theorem poly_body0 : Poly (fun a : LS => decide (a.1 = 0 ∨ a.2.2.2.2.2 ≠ 0)) := by
  have h : (fun a : LS => decide (a.1 = 0 ∨ a.2.2.2.2.2 ≠ 0)) =
      (fun a : LS => decide (a.1 = 0) || !decide (a.2.2.2.2.2 = 0)) := by
    funext a; by_cases h1 : a.1 = 0 <;> by_cases h2 : a.2.2.2.2.2 = 0 <;> simp [h1, h2]
  rw [h]; fun_prop

noncomputable def bodyP0 : PolyProgram (enc : LS → List Bool) (encodeLoop (enc : LS → List Bool) (enc : RS → List Bool)) body0 := by
  have hc := poly_body0
  have hs := poly_stepR oP
  have hstep : Poly (fun a : LS => (a.1 - 1, (a.2.1, stepR oP a.2.2))) := by fun_prop
  have hfin : Poly (fun a : LS => a.2.2) := by fun_prop
  exact (PolyProgram.ite hc.program
    (hstep.program.comp (PolyProgram.injectRight (enc : LS → List Bool) (enc : RS → List Bool)))
    (hfin.program.comp (PolyProgram.injectLeft (enc : LS → List Bool) (enc : RS → List Bool)))).congr _
    (fun a => by unfold body0; split_ifs <;> simp_all)

noncomputable def bodyP : PolyProgram eVS (encodeLoop eVS (enc : RS → List Bool)) body :=
  bodyP0.recode Subtype.val (fun _ => rfl) (fun a => by
    unfold body body0
    split_ifs <;> rfl)

theorem x2_le (x : LPIn) : x.2.length ≤ (enc x : List Bool).length ∧
    RAM.totalBits x.2 ≤ (enc x : List Bool).length := by
  show _ ≤ (encodePair (encodePair Nat.bits Nat.bits) (encodeList Ratio.encode) x).length ∧
    _ ≤ (encodePair (encodePair Nat.bits Nat.bits) (encodeList Ratio.encode) x).length
  rw [encodePair_length]
  have h1 := EncodedList.length_le Ratio.encode x.2
  have h2 := totalBits_le x.2
  constructor <;> omega

theorem data_bits (x : LPIn) (hx : goodIn x) (i : ℕ) (hi : i ≤ kOf x hx) :
    ∀ q ∈ (iterR (rep0 x) i).2.1, RAM.ratBits q ≤ RAM.polyBound obC obE (RAM.totalBits x.2) := by
  intro q hq
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hq
  have hab := (run_inv x hx i hi).1
  obtain ⟨-, -, hsb, -⟩ := tOf_spec x hx
  have := hsb ⟨i, by omega⟩ j
  rw [inpOf_eq' x hx, ← hab] at this
  simpa [absR, gQ, List.getElem?_eq_getElem hj] using this

theorem idx_le (x : LPIn) (hx : goodIn x) (i : ℕ) (hi : i ≤ kOf x hx) :
    ∀ v ∈ (iterR (rep0 x) i).2.2.1, v ≤ M0 x + Kc x := by
  intro v hv
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hv
  obtain ⟨hab, -, -, hix⟩ := run_inv x hx i hi
  have hk : kOf x hx ≤ Kc x := (tOf_spec x hx).2.1
  have := hix j
  rw [← hab] at this
  simp only [absR, gN, List.getElem?_eq_getElem hj, Option.getD_some] at this
  omega

theorem pc_out_le (x : LPIn) (hx : goodIn x) (i : ℕ) (hi : i ≤ kOf x hx) :
    (iterR (rep0 x) i).1 ≤ maxC oP + oP.length ∧ (iterR (rep0 x) i).2.2.2 ≤ maxC oP + 1 := by
  obtain ⟨hab, -, -, -⟩ := run_inv x hx i hi
  obtain ⟨hpc, hout⟩ := pc_inv x hx i hi
  rw [← hab] at hpc hout
  refine ⟨hpc, ?_⟩
  by_cases h0 : (iterR (rep0 x) i).2.2.2 = 0
  · omega
  · have := hout ((iterR (rep0 x) i).2.2.2 - 1) (by simp [absR, h0])
    omega

noncomputable def SzP : Polynomial ℕ :=
  let X : Polynomial ℕ := Polynomial.X
  let KP : Polynomial ℕ := Polynomial.C oc * (X + 1) ^ oe
  let BqP : Polynomial ℕ := Polynomial.C obC * (X + 1) ^ obE
  let DlP : Polynomial ℕ := 2 * X + Polynomial.C C0 * (X + 1) ^ oe
  let IlP : Polynomial ℕ := 2 + X + Polynomial.C C0 * (X + 1) ^ oe
  2 * KP + 1 + 2 * X + 1 + (2 * Polynomial.C (maxC oP + oP.length) + 1 +
    (2 * (DlP * (2 * (13 + 2 * BqP) + 1)) + 1 +
      (2 * (IlP * (2 * (X + Polynomial.C (maxC oP) + KP) + 1)) + 1 + Polynomial.C (maxC oP + 1))))

theorem size_valid (x : LPIn) (hx : goodIn x) (i : ℕ) (hi : i ≤ kOf x hx) :
    (enc ((Kc x - i, (x, iterR (rep0 x) i)) : LS) : List Bool).length ≤ SzP.eval (enc x : List Bool).length := by
  set N := (enc x : List Bool).length
  set rs := iterR (rep0 x) i
  obtain ⟨hx2, htb⟩ := x2_le x
  obtain ⟨-, hlD, hlI, -⟩ := run_inv x hx i hi
  obtain ⟨hpc, hout⟩ := pc_out_le x hx i hi
  have hdb := data_bits x hx i hi
  have hib := idx_le x hx i hi
  have hP1 : (x.2.length + 1) ^ oe ≤ (N + 1) ^ oe := Nat.pow_le_pow_left (by omega) _
  have hK : Kc x ≤ oc * (N + 1) ^ oe := by
    unfold Kc RAM.polyBound
    have : x.1.1 + x.1.2 ≤ x.2.length := by obtain ⟨hm, hd, hl⟩ := hx; rw [hl]; nlinarith
    exact Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left (by omega) _).trans hP1)
  have hBq : RAM.polyBound obC obE (RAM.totalBits x.2) ≤ obC * (N + 1) ^ obE :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
  have hDl : Dl x ≤ 2 * N + C0 * (N + 1) ^ oe := by
    unfold Dl; rw [padQ_length]
    have := Nat.mul_le_mul_left C0 hP1
    omega
  have hIl : Il x ≤ 2 + N + C0 * (N + 1) ^ oe := by
    unfold Il; rw [show (padN x.2).length = (padQ x.2).length by simp [padN], padQ_length]
    have := Nat.mul_le_mul_left C0 hP1
    omega
  have hM0 : M0 x ≤ N + maxC oP := by
    unfold M0
    have : x.1.1 + x.1.2 ≤ x.2.length := by obtain ⟨hm, hd, hl⟩ := hx; rw [hl]; nlinarith
    omega
  -- data list encoding
  have hdata : (encodeList Ratio.encode rs.2.1).length ≤
      (2 * N + C0 * (N + 1) ^ oe) * (2 * (13 + 2 * (obC * (N + 1) ^ obE)) + 1) := by
    have := EncodedList.length_bound Ratio.encode rs.2.1 (13 + 2 * (obC * (N + 1) ^ obE)) (fun q hq => by
      have := ratEnc_le q; have := hdb q hq; omega)
    rw [hlD] at this
    exact this.trans (Nat.mul_le_mul_right _ hDl)
  have hidx : (encodeList Nat.bits rs.2.2.1).length ≤
      (2 + N + C0 * (N + 1) ^ oe) * (2 * (N + maxC oP + oc * (N + 1) ^ oe) + 1) := by
    have := EncodedList.length_bound Nat.bits rs.2.2.1 (N + maxC oP + oc * (N + 1) ^ oe) (fun v hv => by
      have := MNRL22.bits_len_le v; have := hib v hv; omega)
    rw [hlI] at this
    exact this.trans (Nat.mul_le_mul_right _ hIl)
  have hcnt : (Kc x - i).bits.length ≤ oc * (N + 1) ^ oe := (MNRL22.bits_len_le _).trans (by omega)
  have hpcb : rs.1.bits.length ≤ maxC oP + oP.length := (MNRL22.bits_len_le _).trans hpc
  have houtb : rs.2.2.2.bits.length ≤ maxC oP + 1 := (MNRL22.bits_len_le _).trans hout
  show (encodePair Nat.bits (encodePair (enc : LPIn → List Bool)
    (encodePair Nat.bits (encodePair (encodeList Ratio.encode) (encodePair (encodeList Nat.bits) Nat.bits))))
    (Kc x - i, (x, rs))).length ≤ _
  simp only [encodePair_length]
  simp only [SzP, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_ofNat, Polynomial.eval_one]
  generalize (N + 1) ^ oe = P1 at *
  generalize (N + 1) ^ obE = P2 at *
  generalize oc * P1 = Q1 at *
  generalize C0 * P1 = Q2 at *
  generalize obC * P2 = Q3 at *
  generalize (2 * N + Q2) * (2 * (13 + 2 * Q3) + 1) = Q4 at *
  generalize (2 + N + Q2) * (2 * (N + maxC oP + Q1) + 1) = Q5 at *
  omega

theorem run_bounded (x : LPIn) (hx : goodIn x) : ∀ j i (a : VS), i + j = kOf x hx →
    a.1 = (Kc x - i, (x, iterR (rep0 x) i)) →
    BoundedRun eVS body (SzP.eval (enc x : List Bool).length) (j + 1) a (gfin a) := by
  have hk : kOf x hx ≤ Kc x := (tOf_spec x hx).2.1
  intro j
  induction j with
  | zero =>
    rintro i ⟨⟨cnt, x', rs⟩, hv⟩ hij ha
    simp only [Prod.mk.injEq] at ha
    obtain ⟨hc, hx', hr⟩ := ha
    subst hx' hc hr
    have hik : i = kOf x' hx := by omega
    have hsz : (eVS ⟨(Kc x' - i, (x', iterR (rep0 x') i)), hv⟩).length ≤ SzP.eval (enc x' : List Bool).length :=
      size_valid x' hx i (by omega)
    refine BoundedRun.stop hsz ?_
    have hout : (iterR (rep0 x') i).2.2.2 ≠ 0 := (out_iff x' hx i (by omega)).2 hik
    unfold body
    rw [dif_pos (Or.inr hout)]
    congr 1
    unfold gfin
    exact congrArg (iterR (rep0 x')) hik
  | succ j ih =>
    rintro i ⟨⟨cnt, x', rs⟩, hv⟩ hij ha
    simp only [Prod.mk.injEq] at ha
    obtain ⟨hc, hx', hr⟩ := ha
    subst hx' hc hr
    have hsz : (eVS ⟨(Kc x' - i, (x', iterR (rep0 x') i)), hv⟩).length ≤ SzP.eval (enc x' : List Bool).length :=
      size_valid x' hx i (by omega)
    have hne : ¬ ((Kc x' - i) = 0 ∨ (iterR (rep0 x') i).2.2.2 ≠ 0) := by
      push_neg
      refine ⟨by omega, ?_⟩
      by_contra h
      have := (out_iff x' hx i (by omega)).1 h
      omega
    have hb : body ⟨(Kc x' - i, (x', iterR (rep0 x') i)), hv⟩ =
        .inr ⟨(Kc x' - i - 1, (x', stepR oP (iterR (rep0 x') i))), valid_next ⟨(Kc x' - i, (x', iterR (rep0 x') i)), hv⟩ hne⟩ := by
      unfold body; rw [dif_neg hne]
    refine BoundedRun.step hsz hb ?_
    have e1 : (⟨(Kc x' - i - 1, (x', stepR oP (iterR (rep0 x') i))), valid_next ⟨(Kc x' - i, (x', iterR (rep0 x') i)), hv⟩ hne⟩ : VS).1 =
        (Kc x' - (i + 1), (x', iterR (rep0 x') (i + 1))) := by
      simp only [Prod.mk.injEq, true_and]
      exact ⟨by omega, (Function.iterate_succ_apply' _ _ _).symm⟩
    exact ih (i + 1) _ (by omega) e1

theorem bounded_mono {α β : Type} {ea : α → List Bool} {f : α → β ⊕ α} {S S' n : ℕ} {a : α} {b : β}
    (h : BoundedRun ea f S n a b) (hS : S ≤ S') : BoundedRun ea f S' n a b := by
  induction h with
  | stop h1 h2 => exact BoundedRun.stop (h1.trans hS) h2
  | step h1 h2 _ ih => exact BoundedRun.step (h1.trans hS) h2 ih

theorem encx_le (a : VS) : (enc a.1.2.1 : List Bool).length ≤ (eVS a).length := by
  show _ ≤ (encodePair Nat.bits (encodePair (enc : LPIn → List Bool) (enc : RS → List Bool)) a.1).length
  simp only [encodePair_length]; omega

noncomputable def iterP : Polynomial ℕ := Polynomial.C oc * (Polynomial.X + 1) ^ oe + 1

noncomputable def lpRunP : PolyProgram eVS (enc : RS → List Bool) gfin :=
  bodyP.loop gfin iterP SzP (fun a => by
    obtain ⟨hx, i, hi, hc, hr⟩ := a.2
    have hk : kOf a.1.2.1 hx ≤ Kc a.1.2.1 := (tOf_spec a.1.2.1 hx).2.1
    refine ⟨kOf a.1.2.1 hx - i + 1, ?_, ?_⟩
    · have h1 := encx_le a
      have h2 := (x2_le a.1.2.1).1
      have hK : Kc a.1.2.1 ≤ oc * ((eVS a).length + 1) ^ oe := by
        unfold Kc RAM.polyBound
        have : a.1.2.1.1.1 + a.1.2.1.1.2 ≤ a.1.2.1.2.length := by
          obtain ⟨hm, hd, hl⟩ := hx; rw [hl]; nlinarith
        exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
      simp only [iterP, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
        Polynomial.eval_X, Polynomial.eval_one]
      omega
    · have := run_bounded a.1.2.1 hx (kOf a.1.2.1 hx - i) i a (by omega) (by
        rw [← hr, ← hc])
      exact bounded_mono this (polynomial_eval_mono _ (encx_le a)))

theorem poly_natpow (e : ℕ) : Poly (fun n : ℕ => n ^ e) := by
  induction e with
  | zero => simp only [pow_zero]; exact Automatic.Poly.const 1
  | succ e ih =>
    have : (fun n : ℕ => n ^ (e + 1)) = fun n => n ^ e * n := by funext n; ring
    rw [this]
    exact MNRL22.nat_mul_comp ih Poly.identity

theorem poly_powList (k : ℕ) : Poly (fun L : List ℚ => powList L k) := by
  induction k with
  | zero => exact Automatic.Poly.const [0]
  | succ k ih =>
    show Poly (fun L : List ℚ => (powList L k).flatMap (fun _ => 0 :: L.map (fun _ => 0)))
    exact Poly.list_flatMap (f := fun (L : List ℚ) (_ : ℚ) => 0 :: L.map (fun _ => 0)) (by fun_prop) ih

theorem poly_padQ : Poly padQ := by
  have h := poly_powList oe
  unfold padQ
  have h2 : Poly (fun L : List ℚ => (List.range C0).flatMap (fun _ => powList L oe)) :=
    Poly.list_flatMap (f := fun (L : List ℚ) (_ : ℕ) => powList L oe)
      (Poly.comp (f := fun L : List ℚ => powList L oe) h Poly.fst) (Automatic.Poly.const _)
  fun_prop

theorem poly_start : Poly (fun x : LPIn => ((Kc x, (x, rep0 x)) : LS)) := by
  have hp := poly_natpow oe
  have hq := poly_padQ
  have hK : Poly (fun x : LPIn => Kc x) := by
    unfold Kc RAM.polyBound
    exact MNRL22.nat_mul_comp (Automatic.Poly.const _)
      (Poly.comp (f := fun n : ℕ => n ^ oe) hp (by fun_prop))
  have hr : Poly (fun x : LPIn => rep0 x) := by
    unfold rep0 padN
    have : Poly (fun x : LPIn => padQ x.2) := Poly.comp (f := padQ) hq Poly.snd
    fun_prop
  fun_prop

abbrev GI := {x : LPIn // goodIn x}
noncomputable def eGI : GI → List Bool := fun x => (enc x.1 : List Bool)

noncomputable def startV (x : GI) : VS :=
  ⟨(Kc x.1, (x.1, rep0 x.1)), ⟨x.2, 0, Nat.zero_le _, by simp, rfl⟩⟩

noncomputable def startP : PolyProgram eGI eVS startV :=
  poly_start.program.recode Subtype.val (fun _ => rfl) (fun _ => rfl)

noncomputable def lpSolveP : PolyProgram eGI (enc : RS → List Bool) (fun x => gfin (startV x)) :=
  startP.comp lpRunP

theorem lpSolve_spec (x : GI) :
    OptimizationOutput (Aof x.1) (bof x.1) (oof x.1) (absR (gfin (startV x))) := by
  have h := (tOf_spec x.1 x.2).2.2.2
  have hk := (run_inv x.1 x.2 (kOf x.1 x.2) le_rfl).1
  have e : gfin (startV x) = iterR (rep0 x.1) (kOf x.1 x.2) := rfl
  rw [e, hk]
  exact h

end MNRRam

-- ===== R46D =====

namespace MNRLP
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic MNRL22 MNRRam

noncomputable def nOf (c : Ctx) (j : ℕ) : ℕ := c.1[j]?.getD 0
noncomputable def pairs (c : Ctx) : List (ℕ × ℕ) :=
  (List.range c.1.length).flatMap (fun j => (rng c (nOf c j)).map (fun b => (j, b)))
noncomputable def pureQ (c : Ctx) (x : List (List ℚ)) (i a : ℕ) : ℚ := payoff c (setL x i (pureRow c i a)) i
noncomputable def gainQ (c : Ctx) (x : List (List ℚ)) (i a : ℕ) : ℚ := pureQ c x i a - payoff c x i
noncomputable def replQ (c : Ctx) (x : List (List ℚ)) (j b i a : ℕ) : ℚ :=
  gainQ c (setL x j (pureRow c j b)) i a - gainQ c x i a

theorem poly_nOf : Poly (fun x : Ctx × ℕ => nOf x.1 x.2) := by unfold nOf; fun_prop
@[fun_prop] theorem nOf_comp {α : Type} [Coding α] {f : α → Ctx} {g : α → ℕ} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => nOf (f x) (g x)) := Poly.comp (f := fun x : Ctx × ℕ => nOf x.1 x.2) poly_nOf (Poly.pair hf hg)
attribute [irreducible] nOf
theorem poly_pairs : Poly pairs := by
  unfold pairs
  refine Poly.list_flatMap (f := fun (c : Ctx) (j : ℕ) => (rng c (nOf c j)).map (fun b => (j, b))) ?_ (by fun_prop)
  fun_prop
attribute [irreducible] pairs
@[fun_prop] theorem pairs_comp {α : Type} [Coding α] {f : α → Ctx} (hf : Poly f) :
    Poly (fun x => pairs (f x)) := Poly.comp (f := pairs) poly_pairs hf

theorem poly_gainQ : Poly (fun y : (Ctx × List (List ℚ)) × (ℕ × ℕ) => gainQ y.1.1 y.1.2 y.2.1 y.2.2) := by
  unfold gainQ pureQ; fun_prop
attribute [irreducible] gainQ
@[fun_prop] theorem gainQ_comp {α : Type} [Coding α] {f : α → Ctx} {g : α → List (List ℚ)} {h k : α → ℕ}
    (hf : Poly f) (hg : Poly g) (hh : Poly h) (hk : Poly k) : Poly (fun x => gainQ (f x) (g x) (h x) (k x)) :=
  Poly.comp (f := fun y : (Ctx × List (List ℚ)) × (ℕ × ℕ) => gainQ y.1.1 y.1.2 y.2.1 y.2.2) poly_gainQ
    (Poly.pair (Poly.pair hf hg) (Poly.pair hh hk))
theorem poly_replQ : Poly (fun y : (Ctx × List (List ℚ)) × ((ℕ × ℕ) × (ℕ × ℕ)) =>
    replQ y.1.1 y.1.2 y.2.1.1 y.2.1.2 y.2.2.1 y.2.2.2) := by
  unfold replQ; fun_prop
attribute [irreducible] replQ
@[fun_prop] theorem replQ_comp {α : Type} [Coding α] {f : α → Ctx} {g : α → List (List ℚ)} {h1 h2 h3 h4 : α → ℕ}
    (hf : Poly f) (hg : Poly g) (h1p : Poly h1) (h2p : Poly h2) (h3p : Poly h3) (h4p : Poly h4) :
    Poly (fun x => replQ (f x) (g x) (h1 x) (h2 x) (h3 x) (h4 x)) :=
  Poly.comp (f := fun y : (Ctx × List (List ℚ)) × ((ℕ × ℕ) × (ℕ × ℕ)) =>
    replQ y.1.1 y.1.2 y.2.1.1 y.2.1.2 y.2.2.1 y.2.2.2) poly_replQ
    (Poly.pair (Poly.pair hf hg) (Poly.pair (Poly.pair h1p h2p) (Poly.pair h3p h4p)))

noncomputable def rowP (c : Ctx) (x : List (List ℚ)) (η : ℚ) (p : ℕ × ℕ) : List ℚ :=
  (pairs c).map (fun q => η * replQ c x q.1 q.2 p.1 p.2) ++ [-1]
noncomputable def rowZ (c : Ctx) (q : ℕ × ℕ) : List ℚ :=
  (pairs c).map (fun q' => if q'.1 = q.1 then (if q'.2 = q.2 then (-1 : ℚ) else 0) else 0) ++ [0]
noncomputable def rowS (c : Ctx) : List ℚ := (pairs c).map (fun _ => (1 : ℚ)) ++ [0]

theorem poly_rowP (η : ℚ) : Poly (fun z : (Ctx × List (List ℚ)) × (ℕ × ℕ) => rowP z.1.1 z.1.2 η z.2) := by
  unfold rowP
  have : Poly (fun z : (Ctx × List (List ℚ)) × (ℕ × ℕ) => (pairs z.1.1).map
      (fun q => η * replQ z.1.1 z.1.2 q.1 q.2 z.2.1 z.2.2)) :=
    Poly.list_map (f := fun (z : (Ctx × List (List ℚ)) × (ℕ × ℕ)) (q : ℕ × ℕ) =>
      η * replQ z.1.1 z.1.2 q.1 q.2 z.2.1 z.2.2) (by fun_prop) (by fun_prop)
  fun_prop
theorem poly_rowZ : Poly (fun z : Ctx × (ℕ × ℕ) => rowZ z.1 z.2) := by
  unfold rowZ
  have : Poly (fun z : Ctx × (ℕ × ℕ) => (pairs z.1).map
      (fun q' => if q'.1 = z.2.1 then (if q'.2 = z.2.2 then (-1 : ℚ) else 0) else 0)) :=
    Poly.list_map (f := fun (z : Ctx × (ℕ × ℕ)) (q' : ℕ × ℕ) =>
      if q'.1 = z.2.1 then (if q'.2 = z.2.2 then (-1 : ℚ) else 0) else 0) (by fun_prop) (by fun_prop)
  fun_prop
attribute [irreducible] rowP rowZ

noncomputable def lpFlat (c : Ctx) (x : List (List ℚ)) (η : ℚ) : List ℚ :=
  ((pairs c).map (rowP c x η) ++ (pairs c).map (rowZ c) ++ [rowS c]).flatten ++
    ((pairs c).map (fun p => -gainQ c x p.1 p.2) ++ (pairs c).map (fun _ => (0 : ℚ)) ++ [1]) ++
    ((pairs c).map (fun _ => (0 : ℚ)) ++ [-1])
noncomputable def lpIn (c : Ctx) (x : List (List ℚ)) (η : ℚ) : LPIn :=
  ((2 * (pairs c).length + 1, (pairs c).length + 1), lpFlat c x η)

theorem poly_lpIn (η : ℚ) : Poly (fun y : Ctx × List (List ℚ) => lpIn y.1 y.2 η) := by
  have h1 : Poly (fun y : Ctx × List (List ℚ) => (pairs y.1).map (rowP y.1 y.2 η)) :=
    Poly.list_map (f := fun (y : Ctx × List (List ℚ)) (p : ℕ × ℕ) => rowP y.1 y.2 η p)
      (Poly.comp (f := fun z : (Ctx × List (List ℚ)) × (ℕ × ℕ) => rowP z.1.1 z.1.2 η z.2) (poly_rowP η)
        Poly.identity) (by fun_prop)
  have h2 : Poly (fun y : Ctx × List (List ℚ) => (pairs y.1).map (rowZ y.1)) :=
    Poly.list_map (f := fun (y : Ctx × List (List ℚ)) (p : ℕ × ℕ) => rowZ y.1 p)
      (Poly.comp (f := fun z : Ctx × (ℕ × ℕ) => rowZ z.1 z.2)
        (g := fun z : (Ctx × List (List ℚ)) × (ℕ × ℕ) => (z.1.1, z.2)) poly_rowZ (by fun_prop)) (by fun_prop)
  have h3 : Poly (fun y : Ctx × List (List ℚ) => (pairs y.1).map (fun p => -gainQ y.1 y.2 p.1 p.2)) :=
    Poly.list_map (f := fun (y : Ctx × List (List ℚ)) (p : ℕ × ℕ) => -gainQ y.1 y.2 p.1 p.2)
      (Poly.comp (f := fun q : ℚ => -q) Poly.rat_neg
        (gainQ_comp (f := fun z : (Ctx × List (List ℚ)) × (ℕ × ℕ) => z.1.1)
          (g := fun z : (Ctx × List (List ℚ)) × (ℕ × ℕ) => z.1.2)
          (h := fun z : (Ctx × List (List ℚ)) × (ℕ × ℕ) => z.2.1)
          (k := fun z : (Ctx × List (List ℚ)) × (ℕ × ℕ) => z.2.2)
          (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop))) (by fun_prop)
  unfold lpIn lpFlat rowS
  fun_prop

/-! ### structure of the LP input -/

theorem rowP_len (c : Ctx) (x : List (List ℚ)) (η : ℚ) (p : ℕ × ℕ) : (rowP c x η p).length = (pairs c).length + 1 := by
  unfold rowP; simp
theorem rowZ_len (c : Ctx) (q : ℕ × ℕ) : (rowZ c q).length = (pairs c).length + 1 := by
  unfold rowZ; simp
theorem rowS_len (c : Ctx) : (rowS c).length = (pairs c).length + 1 := by
  unfold rowS; simp

theorem flatten_const {α : Type} (L : List (List α)) (d : ℕ) (hL : ∀ l ∈ L, l.length = d) (r q : ℕ)
    (hr : r < L.length) (hq : q < d) : L.flatten[r * d + q]? = (L[r])[q]? := by
  induction L generalizing r with
  | nil => simp at hr
  | cons l L ih =>
    have hl : l.length = d := hL l (List.mem_cons_self)
    cases r with
    | zero =>
      simp only [zero_mul, zero_add, List.flatten_cons, List.getElem_cons_zero]
      rw [List.getElem?_append_left (by omega)]
    | succ r =>
      simp only [List.flatten_cons, List.getElem_cons_succ]
      rw [List.getElem?_append_right (by rw [hl]; nlinarith)]
      rw [show (r + 1) * d + q - l.length = r * d + q by rw [hl]; ring_nf; omega]
      exact ih (fun l' hl' => hL l' (List.mem_cons_of_mem _ hl')) r (by simpa using hr)

theorem lpIn_good (c : Ctx) (x : List (List ℚ)) (η : ℚ) : goodIn (lpIn c x η) := by
  refine ⟨by simp [lpIn], by simp [lpIn], ?_⟩
  simp only [lpIn, lpFlat, List.length_append, List.length_flatten, List.length_map, List.length_cons,
    List.length_nil]
  have h1 : ((pairs c).map (rowP c x η) ++ (pairs c).map (rowZ c) ++ [rowS c]).map List.length =
      List.replicate (2 * (pairs c).length + 1) ((pairs c).length + 1) := by
    apply List.eq_replicate_iff.2
    refine ⟨by simp; ring, fun l hl => ?_⟩
    simp only [List.map_append, List.mem_append, List.mem_map, List.mem_singleton, List.map_cons,
      List.map_nil] at hl
    rcases hl with (⟨l', ⟨p, _, rfl⟩, rfl⟩ | ⟨l', ⟨p, _, rfl⟩, rfl⟩) | rfl
    · exact rowP_len c x η p
    · exact rowZ_len c p
    · exact rowS_len c
  rw [show (List.map List.length ((pairs c).map (rowP c x η) ++ (pairs c).map (rowZ c) ++ [rowS c])) =
    ((pairs c).map (rowP c x η) ++ (pairs c).map (rowZ c) ++ [rowS c]).map List.length from rfl, h1,
    List.sum_replicate, smul_eq_mul]
  ring

section entries
variable (c : Ctx) (x : List (List ℚ)) (η : ℚ)

noncomputable def NPc : ℕ := (pairs c).length
noncomputable def pr (q : ℕ) : ℕ × ℕ := (pairs c).getD q (0, 0)

noncomputable def lpRows : List (List ℚ) := (pairs c).map (rowP c x η) ++ (pairs c).map (rowZ c) ++ [rowS c]

theorem lpRows_len : (lpRows c x η).length = 2 * NPc c + 1 := by simp [lpRows, NPc]; ring

theorem lpRows_get (r : ℕ) (hr : r < 2 * NPc c + 1) :
    (lpRows c x η)[r]?.getD [] =
      if r < NPc c then rowP c x η (pr c r) else if r < 2 * NPc c then rowZ c (pr c (r - NPc c)) else rowS c := by
  unfold lpRows NPc pr at *
  by_cases h1 : r < (pairs c).length
  · rw [if_pos h1, List.getElem?_append_left (by simp; omega), List.getElem?_append_left (by simp; omega)]
    simp [List.getElem?_map, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]
  · rw [if_neg h1]
    by_cases h2 : r < 2 * (pairs c).length
    · rw [if_pos h2, List.getElem?_append_left (by simp; omega), List.getElem?_append_right (by simp; omega)]
      simp only [List.length_map, List.getElem?_map, List.getD_eq_getElem?_getD]
      rw [List.getElem?_eq_getElem (by omega)]; rfl
    · rw [if_neg h2, List.getElem?_append_right (by simp; omega)]
      have : r - ((pairs c).map (rowP c x η) ++ (pairs c).map (rowZ c)).length = 0 := by simp; omega
      rw [this]; rfl

theorem A_entry (r q : ℕ) (hr : r < 2 * NPc c + 1) (hq : q < NPc c + 1) :
    (lpIn c x η).2.getD (r * (NPc c + 1) + q) 0 = ((lpRows c x η)[r]?.getD [])[q]?.getD 0 := by
  have hlen : ∀ l ∈ lpRows c x η, l.length = NPc c + 1 := by
    intro l hl
    simp only [lpRows, List.mem_append, List.mem_map, List.mem_singleton] at hl
    rcases hl with (⟨p, _, rfl⟩ | ⟨p, _, rfl⟩) | rfl
    · exact rowP_len c x η p
    · exact rowZ_len c p
    · exact rowS_len c
  have hf := flatten_const (lpRows c x η) (NPc c + 1) hlen r q (by rw [lpRows_len]; exact hr) hq
  have hrows : (lpRows c x η).flatten.length = (2 * NPc c + 1) * (NPc c + 1) := by
    rw [List.length_flatten, show (lpRows c x η).map List.length =
      List.replicate (2 * NPc c + 1) (NPc c + 1) from List.eq_replicate_iff.2
        ⟨by simp [lpRows_len], fun l hl => by
          obtain ⟨l', hl', rfl⟩ := List.mem_map.1 hl; exact hlen l' hl'⟩, List.sum_replicate, smul_eq_mul]
  have hidx : r * (NPc c + 1) + q < (lpRows c x η).flatten.length := by
    rw [hrows]; nlinarith
  obtain ⟨T, hT⟩ : ∃ T, lpFlat c x η = (lpRows c x η).flatten ++ T :=
    ⟨_, by unfold lpFlat lpRows; rw [List.append_assoc]⟩
  show (lpFlat c x η).getD (r * (NPc c + 1) + q) 0 = _
  have hr' : r < (lpRows c x η).length := by rw [lpRows_len]; exact hr
  rw [hT, List.getD_eq_getElem?_getD, List.getElem?_append_left hidx, hf, List.getElem?_eq_getElem hr']
  rfl

noncomputable def bvec : List ℚ := (pairs c).map (fun p => -gainQ c x p.1 p.2) ++ (pairs c).map (fun _ => (0 : ℚ)) ++ [1]
noncomputable def ovec : List ℚ := (pairs c).map (fun _ => (0 : ℚ)) ++ [-1]

theorem flat_eq : lpFlat c x η = (lpRows c x η).flatten ++ bvec c x ++ ovec c := by
  unfold lpFlat lpRows bvec ovec; rfl

theorem flatten_len : (lpRows c x η).flatten.length = (2 * NPc c + 1) * (NPc c + 1) := by
  rw [List.length_flatten, show (lpRows c x η).map List.length =
    List.replicate (2 * NPc c + 1) (NPc c + 1) from List.eq_replicate_iff.2
      ⟨by simp [lpRows_len], fun l hl => by
        obtain ⟨l', hl', rfl⟩ := List.mem_map.1 hl
        simp only [lpRows, List.mem_append, List.mem_map, List.mem_singleton] at hl'
        rcases hl' with (⟨p, _, rfl⟩ | ⟨p, _, rfl⟩) | rfl
        · exact rowP_len c x η p
        · exact rowZ_len c p
        · exact rowS_len c⟩, List.sum_replicate, smul_eq_mul]

theorem bvec_len : (bvec c x).length = 2 * NPc c + 1 := by simp [bvec, NPc]; ring

theorem b_entry (r : ℕ) (hr : r < 2 * NPc c + 1) :
    (lpIn c x η).2.getD ((2 * NPc c + 1) * (NPc c + 1) + r) 0 = (bvec c x).getD r 0 := by
  show (lpFlat c x η).getD _ 0 = _
  rw [flat_eq, List.append_assoc, List.getD_eq_getElem?_getD, List.getElem?_append_right
    (by rw [flatten_len]; omega), flatten_len, Nat.add_sub_cancel_left]
  rw [List.getElem?_append_left (by rw [bvec_len]; exact hr), ← List.getD_eq_getElem?_getD]

theorem o_entry (q : ℕ) :
    (lpIn c x η).2.getD ((2 * NPc c + 1) * (NPc c + 1) + (2 * NPc c + 1) + q) 0 = (ovec c).getD q 0 := by
  show (lpFlat c x η).getD _ 0 = _
  rw [flat_eq, List.getD_eq_getElem?_getD, List.getElem?_append_right
    (by rw [List.length_append, flatten_len, bvec_len]; omega)]
  rw [List.length_append, flatten_len, bvec_len, Nat.add_sub_cancel_left, ← List.getD_eq_getElem?_getD]

theorem rowP_get (p : ℕ × ℕ) (q : ℕ) (hq : q < NPc c + 1) :
    (rowP c x η p)[q]?.getD 0 = if q < NPc c then η * replQ c x (pr c q).1 (pr c q).2 p.1 p.2 else -1 := by
  unfold rowP
  split_ifs with h
  · rw [List.getElem?_append_left (by simp [NPc] at h ⊢; exact h)]
    simp [List.getElem?_map, pr, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show q < (pairs c).length from h)]
  · rw [List.getElem?_append_right (by simp [NPc] at h ⊢; omega)]
    simp [NPc] at h hq ⊢; rw [show q - (pairs c).length = 0 by omega]; rfl

theorem rowZ_get (q0 : ℕ × ℕ) (q : ℕ) (hq : q < NPc c + 1) :
    (rowZ c q0)[q]?.getD 0 = if q < NPc c then (if (pr c q).1 = q0.1 then (if (pr c q).2 = q0.2 then -1 else 0) else 0) else 0 := by
  unfold rowZ
  by_cases h : q < NPc c
  · rw [if_pos h, List.getElem?_append_left (by simp [NPc] at h ⊢; exact h)]
    simp only [List.getElem?_map, List.getElem?_eq_getElem (show q < (pairs c).length from h), Option.map_some,
      Option.getD_some, pr, List.getD_eq_getElem?_getD]
  · rw [if_neg h, List.getElem?_append_right (by simp [NPc] at h ⊢; omega)]
    simp [NPc] at h hq ⊢

theorem rowS_get (q : ℕ) (hq : q < NPc c + 1) :
    (rowS c)[q]?.getD 0 = if q < NPc c then 1 else 0 := by
  unfold rowS
  split_ifs with h
  · rw [List.getElem?_append_left (by simp [NPc] at h ⊢; exact h)]
    simp [List.getElem?_replicate, show q < (pairs c).length from h]
  · rw [List.getElem?_append_right (by simp [NPc] at h ⊢; omega)]
    simp [NPc] at h hq ⊢

end entries

section vals
variable (c : Ctx) (x : List (List ℚ)) (η : ℚ)

theorem pairs_nodup : (pairs c).Nodup := by
  unfold pairs
  rw [List.nodup_flatMap]
  refine ⟨fun j _ => ?_, ?_⟩
  · exact (List.nodup_range.filter _).map (fun a b h => by simpa using h)
  · apply List.Pairwise.imp_of_mem _ List.nodup_range
    intro j1 j2 _ _ hne
    simp only [Function.onFun, List.disjoint_left, List.mem_map]
    rintro _ ⟨b1, _, rfl⟩ ⟨b2, _, h⟩
    simp at h; exact hne h.1.symm

theorem pr_inj (q q0 : ℕ) (hq : q < NPc c) (hq0 : q0 < NPc c) (h : pr c q = pr c q0) : q = q0 := by
  unfold pr NPc at *
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq,
    List.getElem?_eq_getElem hq0] at h
  simp only [Option.getD_some] at h
  exact (List.Nodup.getElem_inj_iff (pairs_nodup c)).1 h

theorem A_val (r q : ℕ) (hr : r < 2 * NPc c + 1) (hq : q < NPc c + 1) :
    Aof (lpIn c x η) ⟨r, by simpa [lpIn, NPc] using hr⟩ ⟨q, by simpa [lpIn, NPc] using hq⟩ =
      if r < NPc c then (if q < NPc c then η * replQ c x (pr c q).1 (pr c q).2 (pr c r).1 (pr c r).2 else -1)
      else if r < 2 * NPc c then (if q < NPc c then (if q = r - NPc c then -1 else 0) else 0)
      else (if q < NPc c then 1 else 0) := by
  show (lpIn c x η).2.getD (r * ((pairs c).length + 1) + q) 0 = _
  rw [show (pairs c).length = NPc c from rfl, A_entry c x η r q hr hq, lpRows_get c x η r hr]
  by_cases h1 : r < NPc c
  · rw [if_pos h1, if_pos h1, rowP_get c x η _ q hq]
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : r < 2 * NPc c
    · rw [if_pos h2, if_pos h2, rowZ_get c _ q hq]
      by_cases h4 : q < NPc c
      · rw [if_pos h4, if_pos h4]
        by_cases hq' : q = r - NPc c
        · subst hq'; simp
        · rw [if_neg hq']
          by_cases e : (pr c q).1 = (pr c (r - NPc c)).1 ∧ (pr c q).2 = (pr c (r - NPc c)).2
          · exact absurd (pr_inj c q (r - NPc c) h4 (by omega) (Prod.ext e.1 e.2)) hq'
          · rcases not_and_or.1 e with e | e <;> simp [e]
      · rw [if_neg h4, if_neg h4]
    · rw [if_neg h2, if_neg h2, rowS_get c q hq]

theorem b_val (r : ℕ) (hr : r < 2 * NPc c + 1) :
    bof (lpIn c x η) ⟨r, by simpa [lpIn, NPc] using hr⟩ =
      if r < NPc c then -gainQ c x (pr c r).1 (pr c r).2 else if r < 2 * NPc c then 0 else 1 := by
  show (lpIn c x η).2.getD ((2 * (pairs c).length + 1) * ((pairs c).length + 1) + r) 0 = _
  rw [show (pairs c).length = NPc c from rfl, b_entry c x η r hr]
  have hN : NPc c = (pairs c).length := rfl
  unfold bvec
  rw [List.getD_eq_getElem?_getD]
  by_cases h1 : r < NPc c
  · rw [if_pos h1, List.getElem?_append_left (by simp [NPc] at h1 ⊢; omega),
      List.getElem?_append_left (by simp [NPc] at h1 ⊢; omega)]
    simp [List.getElem?_map, pr, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (show r < (pairs c).length from h1)]
  · rw [if_neg h1]
    by_cases h2 : r < 2 * NPc c
    · rw [if_pos h2, List.getElem?_append_left (by simp [NPc] at h2 ⊢; omega),
        List.getElem?_append_right (by simp [NPc] at h1 ⊢; omega)]
      simp [List.getElem?_replicate]; split_ifs <;> rfl
    · rw [if_neg h2, List.getElem?_append_right (by simp [NPc] at h2 ⊢; omega)]
      simp [NPc] at h2 hr ⊢
      rw [show r - ((pairs c).length + (pairs c).length) = 0 by omega]; rfl

theorem o_val (q : ℕ) (hq : q < NPc c + 1) :
    oof (lpIn c x η) ⟨q, by simpa [lpIn, NPc] using hq⟩ = if q < NPc c then 0 else -1 := by
  show (lpIn c x η).2.getD ((2 * (pairs c).length + 1) * ((pairs c).length + 1) +
    (2 * (pairs c).length + 1) + q) 0 = _
  rw [show (pairs c).length = NPc c from rfl, o_entry c x η q]
  have hN : NPc c = (pairs c).length := rfl
  unfold ovec
  rw [List.getD_eq_getElem?_getD]
  by_cases h1 : q < NPc c
  · rw [if_pos h1, List.getElem?_append_left (by simp [NPc] at h1 ⊢; omega)]
    simp [List.getElem?_replicate]; split_ifs <;> rfl
  · rw [if_neg h1, List.getElem?_append_right (by simp [NPc] at h1 ⊢; omega)]
    simp [NPc] at h1 hq ⊢
    rw [show q - (pairs c).length = 0 by omega]; rfl

noncomputable def Avn (r q : ℕ) : ℚ :=
  if r < NPc c then (if q < NPc c then η * replQ c x (pr c q).1 (pr c q).2 (pr c r).1 (pr c r).2 else -1)
  else if r < 2 * NPc c then (if q < NPc c then (if q = r - NPc c then -1 else 0) else 0)
  else (if q < NPc c then 1 else 0)
noncomputable def bvn (r : ℕ) : ℚ :=
  if r < NPc c then -gainQ c x (pr c r).1 (pr c r).2 else if r < 2 * NPc c then 0 else 1
noncomputable def ovn (q : ℕ) : ℚ := if q < NPc c then 0 else -1

open Matrix in
theorem mulVec_eq (v : Fin (lpIn c x η).1.2 → ℚ) (f : ℕ → ℚ) (hv : ∀ j, v j = f j.val)
    (i : Fin (lpIn c x η).1.1) :
    (Aof (lpIn c x η) *ᵥ v) i = ∑ q ∈ Finset.range (NPc c + 1), Avn c x η i.val q * f q := by
  simp only [Matrix.mulVec, dotProduct]
  have hi : i.val < 2 * NPc c + 1 := i.isLt
  rw [show NPc c + 1 = (lpIn c x η).1.2 from rfl, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [hv j]
  have hj : j.val < NPc c + 1 := j.isLt
  have := A_val c x η i.val j.val hi hj
  simp only [Fin.eta] at this
  rw [this]; rfl

open Matrix in
theorem tmulVec_eq (y : Fin (lpIn c x η).1.1 → ℚ) (f : ℕ → ℚ) (hy : ∀ j, y j = f j.val)
    (q : Fin (lpIn c x η).1.2) :
    ((Aof (lpIn c x η)).transpose *ᵥ y) q = ∑ r ∈ Finset.range (2 * NPc c + 1), Avn c x η r q.val * f r := by
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  have hq : q.val < NPc c + 1 := q.isLt
  rw [show 2 * NPc c + 1 = (lpIn c x η).1.1 from rfl, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [hy j]
  have hj : j.val < 2 * NPc c + 1 := j.isLt
  have := A_val c x η j.val q.val hj hq
  simp only [Fin.eta] at this
  rw [this]; rfl

theorem row_lt (f : ℕ → ℚ) (r : ℕ) (hr : r < NPc c) :
    ∑ q ∈ Finset.range (NPc c + 1), Avn c x η r q * f q =
      ∑ q ∈ Finset.range (NPc c), η * replQ c x (pr c q).1 (pr c q).2 (pr c r).1 (pr c r).2 * f q - f (NPc c) := by
  rw [Finset.sum_range_succ]
  simp only [Avn, if_pos hr, lt_irrefl, if_false]
  rw [Finset.sum_congr rfl (fun q hq => by rw [if_pos (Finset.mem_range.1 hq)])]
  ring

theorem row_mid (f : ℕ → ℚ) (r : ℕ) (hr1 : NPc c ≤ r) (hr2 : r < 2 * NPc c) :
    ∑ q ∈ Finset.range (NPc c + 1), Avn c x η r q * f q = -f (r - NPc c) := by
  rw [Finset.sum_range_succ]
  simp only [Avn, if_neg (show ¬ r < NPc c by omega), if_pos hr2, lt_irrefl, if_false, zero_mul, add_zero]
  rw [Finset.sum_congr rfl (fun q hq => by rw [if_pos (Finset.mem_range.1 hq)])]
  rw [Finset.sum_eq_single (r - NPc c)]
  · simp
  · intro q _ hq; simp [hq]
  · intro h; exact absurd (Finset.mem_range.2 (by omega)) h

theorem row_last (f : ℕ → ℚ) :
    ∑ q ∈ Finset.range (NPc c + 1), Avn c x η (2 * NPc c) q * f q = ∑ q ∈ Finset.range (NPc c), f q := by
  rw [Finset.sum_range_succ]
  by_cases h0 : NPc c = 0
  · simp [h0, Avn]
  simp only [Avn, if_neg (show ¬ 2 * NPc c < NPc c by omega), lt_irrefl, if_false, zero_mul, add_zero]
  exact Finset.sum_congr rfl (fun q hq => by rw [if_pos (Finset.mem_range.1 hq)]; ring)

theorem col_lt (g : ℕ → ℚ) (q : ℕ) (hq : q < NPc c) :
    ∑ r ∈ Finset.range (2 * NPc c + 1), Avn c x η r q * g r =
      ∑ r ∈ Finset.range (NPc c), η * replQ c x (pr c q).1 (pr c q).2 (pr c r).1 (pr c r).2 * g r -
        g (NPc c + q) + g (2 * NPc c) := by
  rw [Finset.sum_range_succ, show 2 * NPc c = NPc c + NPc c by ring, Finset.sum_range_add]
  have e1 : ∀ r ∈ Finset.range (NPc c), Avn c x η r q * g r =
      η * replQ c x (pr c q).1 (pr c q).2 (pr c r).1 (pr c r).2 * g r := by
    intro r hr; have := Finset.mem_range.1 hr; simp [Avn, this, hq]
  have e2 : ∀ k ∈ Finset.range (NPc c), Avn c x η (NPc c + k) q * g (NPc c + k) =
      if q = k then -g (NPc c + q) else 0 := by
    intro k hk
    have := Finset.mem_range.1 hk
    simp only [Avn, if_neg (show ¬ NPc c + k < NPc c by omega),
      if_pos (show NPc c + k < 2 * NPc c by omega), if_pos hq, show NPc c + k - NPc c = k by omega]
    split_ifs with h <;> simp [h]
  have e3 : Avn c x η (NPc c + NPc c) q * g (NPc c + NPc c) = g (NPc c + NPc c) := by
    simp [Avn, hq, show ¬ NPc c + NPc c < NPc c by omega, show ¬ NPc c + NPc c < 2 * NPc c by omega]
  rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, Finset.sum_ite_eq, if_pos (Finset.mem_range.2 hq), e3]
  ring

theorem col_last (g : ℕ → ℚ) :
    ∑ r ∈ Finset.range (2 * NPc c + 1), Avn c x η r (NPc c) * g r = -∑ r ∈ Finset.range (NPc c), g r := by
  rw [Finset.sum_range_succ, show 2 * NPc c = NPc c + NPc c by ring, Finset.sum_range_add]
  have e1 : ∀ r ∈ Finset.range (NPc c), Avn c x η r (NPc c) * g r = -g r := by
    intro r hr; have := Finset.mem_range.1 hr; simp [Avn, this]
  have e2 : ∀ k ∈ Finset.range (NPc c), Avn c x η (NPc c + k) (NPc c) * g (NPc c + k) = 0 := by
    intro k hk; have := Finset.mem_range.1 hk
    simp [Avn, show ¬ NPc c + k < NPc c by omega, show NPc c + k < 2 * NPc c by omega]
  have e3 : Avn c x η (NPc c + NPc c) (NPc c) * g (NPc c + NPc c) = 0 := by
    simp [Avn, show ¬ NPc c + NPc c < NPc c by omega, show ¬ NPc c + NPc c < 2 * NPc c by omega]
  rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, e3, Finset.sum_neg_distrib]
  simp

open Matrix in
theorem dot_b (y : Fin (lpIn c x η).1.1 → ℚ) (f : ℕ → ℚ) (hy : ∀ j, y j = f j.val) :
    bof (lpIn c x η) ⬝ᵥ y = ∑ r ∈ Finset.range (NPc c), (-gainQ c x (pr c r).1 (pr c r).2) * f r + f (2 * NPc c) := by
  simp only [dotProduct]
  rw [show (∑ i : Fin (lpIn c x η).1.1, bof (lpIn c x η) i * y i) =
      ∑ r ∈ Finset.range (2 * NPc c + 1), bvn c x r * f r from by
    rw [show 2 * NPc c + 1 = (lpIn c x η).1.1 from rfl, ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hy j]
    have := b_val c x η j.val j.isLt
    simp only [Fin.eta] at this
    rw [this]; rfl]
  rw [Finset.sum_range_succ, show 2 * NPc c = NPc c + NPc c by ring, Finset.sum_range_add]
  have e1 : ∀ r ∈ Finset.range (NPc c), bvn c x r * f r = (-gainQ c x (pr c r).1 (pr c r).2) * f r := by
    intro r hr; have := Finset.mem_range.1 hr; simp [bvn, this]
  have e2 : ∀ k ∈ Finset.range (NPc c), bvn c x (NPc c + k) * f (NPc c + k) = 0 := by
    intro k hk; have := Finset.mem_range.1 hk
    simp [bvn, show ¬ NPc c + k < NPc c by omega, show NPc c + k < 2 * NPc c by omega]
  have e3 : bvn c x (NPc c + NPc c) * f (NPc c + NPc c) = f (NPc c + NPc c) := by
    simp [bvn, show ¬ NPc c + NPc c < NPc c by omega, show ¬ NPc c + NPc c < 2 * NPc c by omega]
  rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, e3]
  simp

open Matrix in
theorem dot_o (v : Fin (lpIn c x η).1.2 → ℚ) (f : ℕ → ℚ) (hv : ∀ j, v j = f j.val) :
    oof (lpIn c x η) ⬝ᵥ v = -f (NPc c) := by
  simp only [dotProduct]
  rw [show (∑ i : Fin (lpIn c x η).1.2, oof (lpIn c x η) i * v i) =
      ∑ q ∈ Finset.range (NPc c + 1), ovn c q * f q from by
    rw [show NPc c + 1 = (lpIn c x η).1.2 from rfl, ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hv j]
    have := o_val c x η j.val j.isLt
    simp only [Fin.eta] at this
    rw [this]; rfl]
  rw [Finset.sum_range_succ]
  rw [Finset.sum_eq_zero (fun q hq => by have := Finset.mem_range.1 hq; simp [ovn, this])]
  simp [ovn]

open Matrix in
theorem cert (s : OAI.Optimization.LinearProgramming.RAM.State ℚ) (hN : 0 < NPc c)
    (hs : OAI.Optimization.LinearProgramming.OptimizationOutput (Aof (lpIn c x η)) (bof (lpIn c x η))
      (oof (lpIn c x η)) s) :
    let N := NPc c
    s.output = some 1 ∧
    (∀ p < N, gainQ c x (pr c p).1 (pr c p).2 +
      ∑ q ∈ Finset.range N, η * replQ c x (pr c q).1 (pr c q).2 (pr c p).1 (pr c p).2 * s.data q ≤ s.data N) ∧
    (∀ q < N, 0 ≤ s.data q) ∧ ∑ q ∈ Finset.range N, s.data q ≤ 1 ∧
    (∀ p < N, 0 ≤ s.data (N + 1 + p)) ∧ 0 ≤ s.data (N + 1 + 2 * N) ∧
    (∀ q < N, 0 ≤ s.data (N + 1 + 2 * N) +
      ∑ p ∈ Finset.range N, η * replQ c x (pr c q).1 (pr c q).2 (pr c p).1 (pr c p).2 * s.data (N + 1 + p)) ∧
    ∑ p ∈ Finset.range N, s.data (N + 1 + p) = 1 ∧
    ∑ p ∈ Finset.range N, s.data (N + 1 + p) * gainQ c x (pr c p).1 (pr c p).2 - s.data (N + 1 + 2 * N) =
      s.data N := by
  intro N
  have hD : (lpIn c x η).1.2 = N + 1 := rfl
  have hM : (lpIn c x η).1.1 = 2 * N + 1 := rfl
  rcases hs with ⟨_, hcert⟩ | ⟨hout, hfeas, hy0, hdual, hcx, hby, -⟩ | ⟨_, hfeas, hray, hcv⟩
  · -- infeasibility certificate impossible
    exfalso
    obtain ⟨hy0, hAy, hby, -⟩ := hcert
    set yv := OAI.Optimization.LinearProgramming.readVector s 0 (lpIn c x η).1.1
    have hcol := congrFun hAy ⟨N, by rw [hD]; omega⟩
    rw [tmulVec_eq c x η yv (fun r => s.data (0 + r)) (fun j => rfl)] at hcol
    simp only [Pi.zero_apply] at hcol
    rw [col_last] at hcol
    have hz : ∀ r ∈ Finset.range N, s.data (0 + r) = 0 := by
      have hnn : ∀ r ∈ Finset.range N, 0 ≤ s.data (0 + r) := fun r hr =>
        hy0 ⟨r, by rw [hM]; have := Finset.mem_range.1 hr; omega⟩
      exact (Finset.sum_eq_zero_iff_of_nonneg hnn).1 (by linarith)
    rw [dot_b c x η yv (fun r => s.data (0 + r)) (fun j => rfl)] at hby
    rw [Finset.sum_eq_zero (fun r hr => by rw [hz r hr, mul_zero])] at hby
    have := hy0 ⟨2 * N, by rw [hM]; omega⟩
    change 0 ≤ s.data (0 + 2 * N) at this
    linarith
  · set xv := OAI.Optimization.LinearProgramming.readVector s 0 (lpIn c x η).1.2
    set yv := OAI.Optimization.LinearProgramming.readVector s (lpIn c x η).1.2 (lpIn c x η).1.1
    have hxv : ∀ j, xv j = (fun q => s.data q) j.val := fun j => by simp [xv, OAI.Optimization.LinearProgramming.readVector]
    have hyv : ∀ j, yv j = (fun r => s.data (N + 1 + r)) j.val := fun j => rfl
    have hrow : ∀ (r : ℕ) (hr : r < 2 * N + 1), ∑ q ∈ Finset.range (NPc c + 1), Avn c x η r q * s.data q ≤
        bvn c x r := by
      intro r hr
      have h := hfeas ⟨r, by rw [hM]; exact hr⟩
      rw [mulVec_eq c x η xv (fun q => s.data q) hxv] at h
      have hb := b_val c x η r hr
      simp only [Fin.val_mk] at h
      rw [show bof (lpIn c x η) ⟨r, _⟩ = bvn c x r from hb] at h
      exact h
    have hcol : ∀ (q : ℕ) (hq : q < N + 1), ∑ r ∈ Finset.range (2 * NPc c + 1), Avn c x η r q * s.data (N + 1 + r) =
        ovn c q := by
      intro q hq
      have h := congrFun hdual ⟨q, by rw [hD]; exact hq⟩
      rw [tmulVec_eq c x η yv (fun r => s.data (N + 1 + r)) hyv] at h
      simp only [Fin.val_mk] at h
      rw [h]
      exact o_val c x η q hq
    refine ⟨hout, fun p hp => ?_, fun q hq => ?_, ?_, fun p hp => ?_, ?_, fun q hq => ?_, ?_, ?_⟩
    · have h := hrow p (by omega)
      rw [row_lt c x η (fun q => s.data q) p hp] at h
      simp only [bvn, if_pos (show p < NPc c from hp)] at h
      simp only [show NPc c = N from rfl] at h
      linarith
    · have h := hrow (N + q) (by omega)
      rw [row_mid c x η _ (N + q) (by omega) (by omega)] at h
      simp only [bvn, if_neg (show ¬ N + q < NPc c by omega), if_pos (show N + q < 2 * NPc c by omega),
        show N + q - NPc c = q by omega] at h
      linarith
    · have h := hrow (2 * N) (by omega)
      rw [row_last] at h
      simp only [bvn, if_neg (show ¬ 2 * N < NPc c by omega), if_neg (show ¬ 2 * N < 2 * NPc c by omega)] at h
      exact h
    · exact hy0 ⟨p, by rw [hM]; omega⟩
    · exact hy0 ⟨2 * N, by rw [hM]; omega⟩
    · have h := hcol q (by omega)
      rw [col_lt c x η (fun r => s.data (N + 1 + r)) q hq] at h
      simp only [ovn, if_pos (show q < NPc c from hq)] at h
      simp only [show NPc c = N from rfl] at h
      have hmu : 0 ≤ s.data (N + 1 + (N + q)) := hy0 ⟨N + q, by rw [hM]; omega⟩
      have e : N + 1 + (NPc c + q) = N + 1 + (N + q) := rfl
      rw [e] at h
      linarith
    · have h := hcol N (by omega)
      rw [col_last] at h
      simp only [ovn, show NPc c = N from rfl, lt_irrefl, if_false] at h
      linarith
    · have h1 := hcx
      rw [dot_o c x η xv (fun q => s.data q) hxv] at h1
      have h2 := hby
      rw [dot_b c x η yv (fun r => s.data (N + 1 + r)) hyv] at h2
      have e : ∑ r ∈ Finset.range (NPc c), (-gainQ c x (pr c r).1 (pr c r).2) * s.data (N + 1 + r) =
          -∑ p ∈ Finset.range N, s.data (N + 1 + p) * gainQ c x (pr c p).1 (pr c p).2 := by
        rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl (fun r _ => by ring)
      rw [e] at h2
      linarith
  · -- unboundedness impossible
    exfalso
    set v := OAI.Optimization.LinearProgramming.readVector s (lpIn c x η).1.2 (lpIn c x η).1.2
    rw [dot_o c x η v (fun q => s.data ((lpIn c x η).1.2 + q)) (fun j => rfl)] at hcv
    have hrow : ∀ i, (Aof (lpIn c x η) *ᵥ v) i ≤ 0 := fun i => hray i
    have hnn : ∀ q < N, 0 ≤ s.data ((lpIn c x η).1.2 + q) := by
      intro q hq
      have := hrow ⟨N + q, by rw [hM]; omega⟩
      rw [mulVec_eq c x η v (fun q => s.data ((lpIn c x η).1.2 + q)) (fun j => rfl)] at this
      simp only [Fin.val_mk] at this
      rw [row_mid c x η _ (N + q) (by omega) (by omega)] at this
      simp only [show N + q - NPc c = q by omega] at this
      linarith
    have hsum := hrow ⟨2 * N, by rw [hM]; omega⟩
    rw [mulVec_eq c x η v (fun q => s.data ((lpIn c x η).1.2 + q)) (fun j => rfl), row_last] at hsum
    have hz : ∀ q ∈ Finset.range N, s.data ((lpIn c x η).1.2 + q) = 0 := by
      have hnn' : ∀ q ∈ Finset.range N, 0 ≤ s.data ((lpIn c x η).1.2 + q) := fun q hq =>
        hnn q (Finset.mem_range.1 hq)
      have := Finset.sum_nonneg hnn'
      exact (Finset.sum_eq_zero_iff_of_nonneg hnn').1 (by linarith)
    have hp := hrow ⟨0, by rw [hM]; omega⟩
    rw [mulVec_eq c x η v (fun q => s.data ((lpIn c x η).1.2 + q)) (fun j => rfl), row_lt c x η _ 0 hN] at hp
    rw [Finset.sum_eq_zero (fun q hq => by rw [hz q hq, mul_zero])] at hp
    linarith

end vals

end MNRLP

-- ===== R46E =====

namespace MNRLP
open NashAmplification.Filtering MNRL22 MNRRam MultiNashRepair

theorem prob_setL (x : List (List ℚ)) (i : ℕ) (v : List ℚ) (hi : i < x.length) (j a : ℕ) :
    prob (setL x i v) j a = if j = i then v[a]?.getD 0 else prob x j a := by
  unfold prob setL
  by_cases hji : j = i
  · subst hji; simp [List.getElem?_append_right, Nat.min_eq_left hi.le]
  · rw [if_neg hji]
    rcases Nat.lt_or_ge j i with hlt | hge
    · rw [List.getElem?_append_left (by simp; omega), List.getElem?_take_of_lt hlt]
    · rw [List.getElem?_append_right (by simp; omega)]
      simp only [List.length_take, Nat.min_eq_left hi.le]
      obtain ⟨t, ht⟩ : ∃ t, j - i = t + 1 := ⟨j - i - 1, by omega⟩
      rw [ht, List.getElem?_cons_succ, List.getElem?_drop, show i + 1 + t = j by omega]

theorem setL_len (x : List (List ℚ)) (i : ℕ) (v : List ℚ) (hi : i < x.length) : (setL x i v).length = x.length :=
  setL_length x i v hi

variable {m : ℕ}

noncomputable def Xof (G : Table m) (x : List (List ℚ)) : Mixed G.counts := fun j a => (prob x j a : ℝ)

theorem setL_pure_real (G : Table m) (hm : 1 ≤ m) (x : List (List ℚ)) (hxl : x.length = m)
    (j : Fin m) (b : Fin (G.counts j)) :
    (fun (j' : Fin m) (a' : Fin (G.counts j')) => ((prob (setL x j.val (pureRow (cG G) j.val b.val)) j' a' : ℚ) : ℝ)) =
      Function.update (Xof G x) j (ePure b) := by
  funext j' a'
  rw [prob_setL x j.val _ (by omega)]
  by_cases h : j' = j
  · subst h
    simp only [if_true, Function.update_self, ePure, DGPNash.WellSupported.pureStrategy]
    rw [pureRow_get G hm j' b.val a']
    simp only [Fin.ext_iff]; split_ifs <;> simp
  · rw [if_neg (fun e => h (Fin.ext e)), Function.update_of_ne h]; rfl

theorem gainQ_eq (G : Table m) (hm : 1 ≤ m) (x : List (List ℚ)) (hxl : x.length = m)
    (i : Fin m) (a : Fin (G.counts i)) :
    ((gainQ (cG G) x i.val a.val : ℚ) : ℝ) = gain G.utility (Xof G x) i a := by
  unfold gainQ pureQ gain DGPNash.NashMap.purePayoff
  push_cast
  have e1 := payoff_eq G hm (setL x i.val (pureRow (cG G) i.val a.val)) i
  have e2 := payoff_eq G hm x i
  rw [show (G.sizes, G.entries.map valQ) = cG G from rfl] at e1 e2
  rw [e1, e2, setL_pure_real G hm x hxl i a]
  rfl

theorem replQ_eq (G : Table m) (hm : 1 ≤ m) (x : List (List ℚ)) (hxl : x.length = m)
    (j : Fin m) (b : Fin (G.counts j)) (i : Fin m) (a : Fin (G.counts i)) :
    ((replQ (cG G) x j.val b.val i.val a.val : ℚ) : ℝ) = repl G.utility (Xof G x) j b i a := by
  unfold replQ repl
  push_cast
  rw [gainQ_eq G hm _ (by rw [setL_len _ _ _ (by omega), hxl]) i a, gainQ_eq G hm x hxl i a]
  congr 2
  funext j' a'
  have := congrFun (congrFun (setL_pure_real G hm x hxl j b) j') a'
  exact this

theorem sum_blocks {M : Type*} [AddCommMonoid M] (H : ℕ → M) : ∀ L : List ℕ,
    ∑ q ∈ Finset.range L.sum, H q =
      ∑ j ∈ Finset.range L.length, ∑ b ∈ Finset.range (L.getD j 0), H ((L.take j).sum + b)
  | [] => by simp
  | l :: L => by
    rw [List.sum_cons, Finset.sum_range_add, List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_zero, List.take_zero, List.sum_nil, zero_add, List.getD_cons_succ,
      List.take_succ_cons, List.sum_cons]
    rw [add_comm]
    congr 1
    rw [sum_blocks (fun k => H (l + k)) L]
    refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun b _ => ?_))
    rw [Nat.add_assoc]

noncomputable def off (G : Table m) (j : ℕ) : ℕ := (G.sizes.take j).sum

theorem pairs_eq (G : Table m) (hm : 1 ≤ m) :
    pairs (cG G) = (List.range m).flatMap (fun j => (List.range (G.sizes.getD j 0)).map (fun b => (j, b))) := by
  unfold pairs
  have hl : (cG G).1.length = m := by simp [cG, G.sizes_length]
  rw [hl]
  refine List.flatMap_congr (fun j hj => ?_)
  have hj' : j < m := List.mem_range.1 hj
  have hn : nOf (cG G) j = G.sizes.getD j 0 := by unfold nOf; simp [cG, List.getD_eq_getElem?_getD]
  rw [hn, rng_eq _ _ (by
    have := counts_le G hm ⟨j, hj'⟩
    simpa [Table.counts] using this)]

theorem NPc_eq (G : Table m) (hm : 1 ≤ m) : NPc (cG G) = G.sizes.sum := by
  unfold NPc
  rw [pairs_eq G hm, List.length_flatMap]
  simp only [List.length_map, List.length_range]
  apply congrArg List.sum
  apply List.ext_getElem
  · simp [G.sizes_length]
  · intro i h1 h2
    have h1' : i < m := by simpa using h1
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

theorem pr_off (G : Table m) (hm : 1 ≤ m) (j : Fin m) (b : ℕ) (hb : b < G.counts j) :
    pr (cG G) (off G j.val + b) = (j.val, b) ∧ off G j.val + b < NPc (cG G) := by
  set L := (List.range m).map (fun j => (List.range (G.sizes.getD j 0)).map (fun b => (j, b))) with hL
  have hpe : pairs (cG G) = L.flatten := by rw [pairs_eq G hm, List.flatMap_def]
  have hjL : j.val < L.length := by simp [L]
  have hbL : b < (L[j.val]'hjL).length := by simpa [L, Table.counts] using hb
  have htake : ((L.take j.val).map List.length).sum = off G j.val := by
    unfold off
    congr 1
    apply List.ext_getElem
    · simp [L, G.sizes_length]
    · intro i h1 h2
      simp only [List.length_map, List.length_take] at h1
      simp [L, List.getElem_take, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (show i < G.sizes.length by rw [G.sizes_length]; omega)]
  have hf := flatten_getElem? L j.val b hjL hbL
  rw [htake, ← hpe] at hf
  have hget : (L[j.val]'hjL)[b]? = some (j.val, b) := by
    have hb' : b < G.sizes[j.val]?.getD 0 := by simpa [L] using hbL
    simp [L, List.getElem?_range hb']
  rw [hget] at hf
  refine ⟨?_, ?_⟩
  · unfold pr; rw [List.getD_eq_getElem?_getD, hf]; rfl
  · unfold NPc; exact (List.getElem?_eq_some_iff.1 hf).1

theorem sum_pairs (G : Table m) (hm : 1 ≤ m) (H : ℕ → ℝ) :
    ∑ q ∈ Finset.range (NPc (cG G)), H q = ∑ j : Fin m, ∑ b : Fin (G.counts j), H (off G j.val + b.val) := by
  rw [NPc_eq G hm, sum_blocks H G.sizes, G.sizes_length, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [show G.sizes.getD j.val 0 = G.counts j from rfl, ← Fin.sum_univ_eq_sum_range]
  rfl

theorem NPc_pos (G : Table m) (hm : 1 ≤ m) : 0 < NPc (cG G) := by
  rw [NPc_eq G hm]
  have h0 : 0 < G.sizes.length := by rw [G.sizes_length]; omega
  have := G.sizes_pos _ (List.getElem_mem h0)
  have h1 : G.sizes[0] ≤ G.sizes.sum := List.le_sum_of_mem (List.getElem_mem h0)
  omega

theorem lp_link (G : Table m) (hm : 1 ≤ m) (x : List (List ℚ)) (hxl : x.length = m) (η : ℚ)
    (s : OAI.Optimization.LinearProgramming.RAM.State ℚ)
    (hs : OAI.Optimization.LinearProgramming.OptimizationOutput (Aof (lpIn (cG G) x η)) (bof (lpIn (cG G) x η))
      (oof (lpIn (cG G) x η)) s) :
    LPOptimal G.utility (Xof G x) η (fun j b => (s.data (off G j.val + b.val) : ℝ)) ∧
    DualOptimal G.utility (Xof G x) η (fun i a => (s.data (NPc (cG G) + 1 + (off G i.val + a.val)) : ℝ))
      (s.data (NPc (cG G) + 1 + 2 * NPc (cG G)) : ℝ) ∧
    lpValue G.utility (Xof G x) η = (s.data (NPc (cG G)) : ℝ) := by
  obtain ⟨-, hF1, hF2, hF3, hD1, hDa, hD2, hD3, hV⟩ := cert (cG G) x η s (NPc_pos G hm) hs
  have hsumQ : ∀ (H : ℕ → ℚ), ((∑ q ∈ Finset.range (NPc (cG G)), H q : ℚ) : ℝ) =
      ∑ j : Fin m, ∑ b : Fin (G.counts j), ((H (off G j.val + b.val) : ℚ) : ℝ) := by
    intro H; rw [Rat.cast_sum]; exact sum_pairs G hm (fun q => ((H q : ℚ) : ℝ))
  have hpr : ∀ (j : Fin m) (b : Fin (G.counts j)), pr (cG G) (off G j.val + b.val) = (j.val, b.val) :=
    fun j b => (pr_off G hm j b.val b.isLt).1
  have hlt : ∀ (j : Fin m) (b : Fin (G.counts j)), off G j.val + b.val < NPc (cG G) :=
    fun j b => (pr_off G hm j b.val b.isLt).2
  have hLPF : LPFeasible (fun (j : Fin m) (b : Fin (G.counts j)) => (s.data (off G j.val + b.val) : ℝ)) := by
    refine ⟨fun j b => by beta_reduce; exact_mod_cast hF2 _ (hlt j b), ?_⟩
    have := hsumQ (fun q => s.data q)
    have h3 : ((∑ q ∈ Finset.range (NPc (cG G)), s.data q : ℚ) : ℝ) ≤ 1 := by exact_mod_cast hF3
    rw [this] at h3; exact h3
  have hrep : ∀ (j : Fin m) (b : Fin (G.counts j)) (f : ℕ → ℚ),
      ((∑ p ∈ Finset.range (NPc (cG G)), η * replQ (cG G) x j.val b.val (pr (cG G) p).1 (pr (cG G) p).2 * f p : ℚ) : ℝ) =
        (η : ℝ) * ∑ i : Fin m, ∑ a : Fin (G.counts i), ((f (off G i.val + a.val) : ℚ) : ℝ) *
          repl G.utility (Xof G x) j b i a := by
    intro j b f
    rw [hsumQ, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [hpr i a]
    push_cast
    rw [replQ_eq G hm x hxl j b i a]
    ring
  have hDF : DualFeasible G.utility (Xof G x) η
      (fun (i : Fin m) (a : Fin (G.counts i)) => (s.data (NPc (cG G) + 1 + (off G i.val + a.val)) : ℝ))
      (s.data (NPc (cG G) + 1 + 2 * NPc (cG G)) : ℝ) := by
    refine ⟨fun i a => by beta_reduce; exact_mod_cast hD1 _ (hlt i a), ?_, by exact_mod_cast hDa, fun j b => ?_⟩
    · have := hsumQ (fun p => s.data (NPc (cG G) + 1 + p))
      have h3 : ((∑ p ∈ Finset.range (NPc (cG G)), s.data (NPc (cG G) + 1 + p) : ℚ) : ℝ) = 1 := by
        exact_mod_cast hD3
      rw [this] at h3; exact h3
    · have h2 := hD2 _ (hlt j b)
      rw [hpr j b] at h2
      have h2' : ((s.data (NPc (cG G) + 1 + 2 * NPc (cG G)) + ∑ p ∈ Finset.range (NPc (cG G)),
          η * replQ (cG G) x j.val b.val (pr (cG G) p).1 (pr (cG G) p).2 * s.data (NPc (cG G) + 1 + p) : ℚ) : ℝ) ≥ 0 := by
        exact_mod_cast h2
      rw [Rat.cast_add, hrep j b (fun p => s.data (NPc (cG G) + 1 + p))] at h2'
      exact h2'
  have hdual : dualObj G.utility (Xof G x)
      (fun (i : Fin m) (a : Fin (G.counts i)) => (s.data (NPc (cG G) + 1 + (off G i.val + a.val)) : ℝ))
      (s.data (NPc (cG G) + 1 + 2 * NPc (cG G)) : ℝ) = (s.data (NPc (cG G)) : ℝ) := by
    unfold dualObj
    have hv : ((∑ p ∈ Finset.range (NPc (cG G)), s.data (NPc (cG G) + 1 + p) * gainQ (cG G) x (pr (cG G) p).1 (pr (cG G) p).2 -
        s.data (NPc (cG G) + 1 + 2 * NPc (cG G)) : ℚ) : ℝ) = (s.data (NPc (cG G)) : ℝ) := by exact_mod_cast hV
    rw [Rat.cast_sub, hsumQ] at hv
    rw [← hv]
    congr 1
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun a _ => ?_))
    rw [hpr i a]; push_cast; rw [gainQ_eq G hm x hxl i a]
  have hobj : lpObj G.utility (Xof G x) η (fun (j : Fin m) (b : Fin (G.counts j)) => (s.data (off G j.val + b.val) : ℝ)) ≤
      (s.data (NPc (cG G)) : ℝ) := by
    unfold lpObj
    haveI : Nonempty ((i : Fin m) × Fin (G.counts i)) := ⟨⟨⟨0, by omega⟩, ⟨0, counts_pos G _⟩⟩⟩
    refine ciSup_le (fun p => ?_)
    have h1 := hF1 _ (hlt p.1 p.2)
    rw [hpr p.1 p.2] at h1
    have h1' : ((gainQ (cG G) x p.1.val p.2.val + ∑ q ∈ Finset.range (NPc (cG G)),
        η * replQ (cG G) x (pr (cG G) q).1 (pr (cG G) q).2 p.1.val p.2.val * s.data q : ℚ) : ℝ) ≤
        (s.data (NPc (cG G)) : ℝ) := by exact_mod_cast h1
    rw [Rat.cast_add, gainQ_eq G hm x hxl, hsumQ] at h1'
    refine le_trans (le_of_eq ?_) h1'
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [hpr j b]; push_cast; rw [replQ_eq G hm x hxl j b p.1 p.2]; ring
  have hDO := MNR43_value_eq G.utility (Xof G x) η _ _ hDF _ hLPF (by rw [hdual]; exact hobj)
  have hval : lpValue G.utility (Xof G x) η = (s.data (NPc (cG G)) : ℝ) := by rw [← hDO.2, hdual]
  refine ⟨⟨hLPF, le_antisymm (hobj.trans hval.symm.le) ?_⟩, hDO, hval⟩
  unfold lpValue
  have hbdd : BddBelow (lpObj G.utility (Xof G x) η '' {z | LPFeasible z}) := by
    refine ⟨dualObj G.utility (Xof G x)
      (fun (i : Fin m) (a : Fin (G.counts i)) => (s.data (NPc (cG G) + 1 + (off G i.val + a.val)) : ℝ))
      (s.data (NPc (cG G) + 1 + 2 * NPc (cG G)) : ℝ), ?_⟩
    rintro _ ⟨z', hz', rfl⟩
    exact MNR43_weak G.utility (Xof G x) η _ _ hDF z' hz'
  exact csInf_le hbdd ⟨_, hLPF, rfl⟩

end MNRLP

-- ===== R46F =====

namespace MNRAlg
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic MNRL22 MNRRam MNRLP

/-- exact maximum of a list of rationals (0 for the empty list) -/
noncomputable def maxL (L : List ℚ) : ℚ := L[L.findIdx (fun v => L.all (fun v' => decide (v' ≤ v)))]?.getD 0

theorem poly_maxL : Poly maxL := by
  unfold maxL
  have hf : Poly (fun L : List ℚ => L.findIdx (fun v => L.all (fun v' => decide (v' ≤ v)))) := by
    refine Poly.list_findIdx (f := fun (L : List ℚ) (v : ℚ) => L.all (fun v' => decide (v' ≤ v))) ?_ Poly.identity
    refine MNRL22.list_all (f := fun (p : List ℚ × ℚ) (v' : ℚ) => decide (v' ≤ p.2)) ?_ ?_
    · exact Poly.rat_le_comp (Poly.comp Poly.snd Poly.identity) (Poly.comp Poly.snd Poly.fst)
    · exact Poly.fst
  fun_prop
attribute [irreducible] maxL
@[fun_prop] theorem maxL_comp {α : Type} [Coding α] {f : α → List ℚ} (hf : Poly f) :
    Poly (fun x => maxL (f x)) := Poly.comp (f := maxL) poly_maxL hf

theorem maxL_spec (L : List ℚ) (hL : L ≠ []) : maxL L ∈ L ∧ ∀ v ∈ L, v ≤ maxL L := by
  unfold maxL
  obtain ⟨v0, hv0, hmax⟩ := L.toFinset.exists_max_image id (by simpa using hL)
  have hex : ∃ v ∈ L, (L.all (fun v' => decide (v' ≤ v))) = true := by
    refine ⟨v0, List.mem_toFinset.1 hv0, ?_⟩
    rw [List.all_eq_true]
    intro v hv; simpa using hmax v (List.mem_toFinset.2 hv)
  have hlt := List.findIdx_lt_length_of_exists hex
  have hP := List.findIdx_getElem (w := hlt)
  rw [List.getElem?_eq_getElem hlt, Option.getD_some]
  refine ⟨List.getElem_mem hlt, fun v hv => ?_⟩
  rw [List.all_eq_true] at hP
  simpa using hP v hv

noncomputable def lpRes (η : ℚ) (y : Ctx × List (List ℚ)) : RS :=
  gfin (startV ⟨lpIn y.1 y.2 η, lpIn_good y.1 y.2 η⟩)

noncomputable def lpResP (η : ℚ) : PolyProgram (enc : Ctx × List (List ℚ) → List Bool) (enc : RS → List Bool) (lpRes η) :=
  ((poly_lpIn η).program.recode (ea' := (enc : Ctx × List (List ℚ) → List Bool)) (eb' := eGI)
    (f' := fun y => (⟨lpIn y.1 y.2 η, lpIn_good y.1 y.2 η⟩ : GI)) id (fun _ => rfl) (fun _ => rfl)).comp lpSolveP

theorem poly_lpRes (η : ℚ) : Poly (lpRes η) := ⟨lpResP η⟩
attribute [irreducible] lpRes
@[fun_prop] theorem lpRes_comp (η : ℚ) {α : Type} [Coding α] {f : α → Ctx × List (List ℚ)} (hf : Poly f) :
    Poly (fun x => lpRes η (f x)) := Poly.comp (f := lpRes η) (poly_lpRes η) hf

theorem lpRes_spec (η : ℚ) (c : Ctx) (x : List (List ℚ)) :
    OAI.Optimization.LinearProgramming.OptimizationOutput (Aof (lpIn c x η)) (bof (lpIn c x η))
      (oof (lpIn c x η)) (absR (lpRes η (c, x))) := by
  unfold lpRes
  exact lpSolve_spec ⟨lpIn c x η, lpIn_good c x η⟩

theorem poly_take' {α : Type} [Coding α] [Inhabited α] :
    Poly (fun x : List α × ℕ => x.1.take x.2) := ⟨PolyProgram.listTake enc default⟩
@[fun_prop] theorem take_comp' {γ β : Type} [Coding γ] [Coding β] [Inhabited β] {f : γ → List β}
    {g : γ → ℕ} (hf : Poly f) (hg : Poly g) : Poly (fun x => (f x).take (g x)) :=
  Poly.comp poly_take' (Poly.pair hf hg)

/-- the rational constants of the algorithm -/
structure KQ where
  σ : ℚ
  η : ℚ
  d : ℚ
  c : ℚ
  t : ℚ
  rho : ℚ
  beta : ℚ
  nu : ℚ
  R0 : ℚ
  G0 : ℚ
  Q : ℚ

variable (K : KQ)

noncomputable def regQ (c : Ctx) (x : List (List ℚ)) (i : ℕ) : ℚ :=
  maxL ((rng c (nOf c i)).map (fun a => gainQ c x i a))
theorem poly_regQ : Poly (fun y : (Ctx × List (List ℚ)) × ℕ => regQ y.1.1 y.1.2 y.2) := by
  unfold regQ
  have : Poly (fun y : (Ctx × List (List ℚ)) × ℕ => (rng y.1.1 (nOf y.1.1 y.2)).map (fun a => gainQ y.1.1 y.1.2 y.2 a)) :=
    Poly.list_map (f := fun (y : (Ctx × List (List ℚ)) × ℕ) (a : ℕ) => gainQ y.1.1 y.1.2 y.2 a) (by fun_prop) (by fun_prop)
  fun_prop
attribute [irreducible] regQ
@[fun_prop] theorem regQ_comp {α : Type} [Coding α] {f : α → Ctx} {g : α → List (List ℚ)} {h : α → ℕ}
    (hf : Poly f) (hg : Poly g) (hh : Poly h) : Poly (fun x => regQ (f x) (g x) (h x)) :=
  Poly.comp (f := fun y : (Ctx × List (List ℚ)) × ℕ => regQ y.1.1 y.1.2 y.2) poly_regQ (Poly.pair (Poly.pair hf hg) hh)

noncomputable def RegQ (c : Ctx) (x : List (List ℚ)) : ℚ := maxL ((List.range c.1.length).map (fun i => regQ c x i))
theorem poly_RegQ : Poly (fun y : Ctx × List (List ℚ) => RegQ y.1 y.2) := by unfold RegQ; fun_prop
attribute [irreducible] RegQ
@[fun_prop] theorem RegQ_comp {α : Type} [Coding α] {f : α → Ctx} {g : α → List (List ℚ)}
    (hf : Poly f) (hg : Poly g) : Poly (fun x => RegQ (f x) (g x)) :=
  Poly.comp (f := fun y : Ctx × List (List ℚ) => RegQ y.1 y.2) poly_RegQ (Poly.pair hf hg)

noncomputable def scQ (c : Ctx) (x : List (List ℚ)) : ℚ := (c.1.length : ℚ) * (1 - RegQ c x)
noncomputable def SuQ (H : ℚ) : ℚ := 1 + H + K.R0 * (1 + H) / (1 + K.Q * H)
noncomputable def muQ (c : Ctx) (x : List (List ℚ)) (H : ℚ) : ℚ := SuQ K H - scQ c x - K.d
noncomputable def offQ (c : Ctx) (j : ℕ) : ℕ := (((c.1.take j).map (fun n : ℕ => (n : ℚ))).sum).num.natAbs

theorem poly_scQ : Poly (fun y : Ctx × List (List ℚ) => scQ y.1 y.2) := by unfold scQ; fun_prop
theorem poly_muQ : Poly (fun y : (Ctx × List (List ℚ)) × ℚ => muQ K y.1.1 y.1.2 y.2) := by
  unfold muQ SuQ scQ; fun_prop
theorem poly_offQ : Poly (fun y : Ctx × ℕ => offQ y.1 y.2) := by unfold offQ; fun_prop
attribute [irreducible] scQ muQ offQ
@[fun_prop] theorem scQ_comp {α : Type} [Coding α] {f : α → Ctx} {g : α → List (List ℚ)}
    (hf : Poly f) (hg : Poly g) : Poly (fun x => scQ (f x) (g x)) :=
  Poly.comp (f := fun y : Ctx × List (List ℚ) => scQ y.1 y.2) poly_scQ (Poly.pair hf hg)
@[fun_prop] theorem muQ_comp {α : Type} [Coding α] {f : α → Ctx} {g : α → List (List ℚ)} {h : α → ℚ}
    (hf : Poly f) (hg : Poly g) (hh : Poly h) : Poly (fun x => muQ K (f x) (g x) (h x)) :=
  Poly.comp (f := fun y : (Ctx × List (List ℚ)) × ℚ => muQ K y.1.1 y.1.2 y.2) (poly_muQ K) (Poly.pair (Poly.pair hf hg) hh)
@[fun_prop] theorem offQ_comp {α : Type} [Coding α] {f : α → Ctx} {g : α → ℕ}
    (hf : Poly f) (hg : Poly g) : Poly (fun x => offQ (f x) (g x)) :=
  Poly.comp (f := fun y : Ctx × ℕ => offQ y.1 y.2) poly_offQ (Poly.pair hf hg)

/-! ### descent -/

noncomputable def ZQ (c : Ctx) (D : List ℚ) (j : ℕ) : ℚ :=
  ((rng c (nOf c j)).map (fun b => gQ D (offQ c j + b))).sum
theorem poly_ZQ : Poly (fun y : (Ctx × List ℚ) × ℕ => ZQ y.1.1 y.1.2 y.2) := by
  unfold ZQ
  have : Poly (fun y : (Ctx × List ℚ) × ℕ => (rng y.1.1 (nOf y.1.1 y.2)).map (fun b => gQ y.1.2 (offQ y.1.1 y.2 + b))) :=
    Poly.list_map (f := fun (y : (Ctx × List ℚ) × ℕ) (b : ℕ) => gQ y.1.2 (offQ y.1.1 y.2 + b)) (by fun_prop) (by fun_prop)
  fun_prop
attribute [irreducible] ZQ
@[fun_prop] theorem ZQ_comp {α : Type} [Coding α] {f : α → Ctx} {g : α → List ℚ} {h : α → ℕ}
    (hf : Poly f) (hg : Poly g) (hh : Poly h) : Poly (fun x => ZQ (f x) (g x) (h x)) :=
  Poly.comp (f := fun y : (Ctx × List ℚ) × ℕ => ZQ y.1.1 y.1.2 y.2) poly_ZQ (Poly.pair (Poly.pair hf hg) hh)

noncomputable def descRow (c : Ctx) (x : List (List ℚ)) (D : List ℚ) (j : ℕ) : List ℚ :=
  (rng c (nOf c j)).map (fun b => (1 - K.η * ZQ c D j) * prob x j b + K.η * gQ D (offQ c j + b))
theorem poly_descRow : Poly (fun y : ((Ctx × List (List ℚ)) × List ℚ) × ℕ => descRow K y.1.1.1 y.1.1.2 y.1.2 y.2) := by
  unfold descRow
  exact Poly.list_map (f := fun (y : ((Ctx × List (List ℚ)) × List ℚ) × ℕ) (b : ℕ) =>
    (1 - K.η * ZQ y.1.1.1 y.1.2 y.2) * prob y.1.1.2 y.2 b + K.η * gQ y.1.2 (offQ y.1.1.1 y.2 + b)) (by fun_prop) (by fun_prop)
attribute [irreducible] descRow
@[fun_prop] theorem descRow_comp {α : Type} [Coding α] {f : α → Ctx} {g : α → List (List ℚ)} {h : α → List ℚ}
    {k : α → ℕ} (hf : Poly f) (hg : Poly g) (hh : Poly h) (hk : Poly k) :
    Poly (fun x => descRow K (f x) (g x) (h x) (k x)) :=
  Poly.comp (f := fun y : ((Ctx × List (List ℚ)) × List ℚ) × ℕ => descRow K y.1.1.1 y.1.1.2 y.1.2 y.2) (poly_descRow K)
    (Poly.pair (Poly.pair (Poly.pair hf hg) hh) hk)

noncomputable def PdQ (c : Ctx) (D : List ℚ) : ℚ := ((List.range c.1.length).map (fun j => 1 - K.η * ZQ c D j)).prod
theorem poly_PdQ : Poly (fun y : Ctx × List ℚ => PdQ K y.1 y.2) := by unfold PdQ; fun_prop
attribute [irreducible] PdQ
@[fun_prop] theorem PdQ_comp {α : Type} [Coding α] {f : α → Ctx} {g : α → List ℚ}
    (hf : Poly f) (hg : Poly g) : Poly (fun x => PdQ K (f x) (g x)) :=
  Poly.comp (f := fun y : Ctx × List ℚ => PdQ K y.1 y.2) (poly_PdQ K) (Poly.pair hf hg)

/-! ### repair: weights -/

noncomputable def lamQ (c : Ctx) (D : List ℚ) (i : ℕ) : ℚ :=
  ((rng c (nOf c i)).map (fun a => gQ D (NPc c + 1 + (offQ c i + a)))).sum
theorem poly_lamQ : Poly (fun y : (Ctx × List ℚ) × ℕ => lamQ y.1.1 y.1.2 y.2) := by
  unfold lamQ
  have h0 : Poly (fun c : Ctx => NPc c) := by unfold NPc; fun_prop
  have : Poly (fun y : (Ctx × List ℚ) × ℕ => (rng y.1.1 (nOf y.1.1 y.2)).map
      (fun a => gQ y.1.2 (NPc y.1.1 + 1 + (offQ y.1.1 y.2 + a)))) :=
    Poly.list_map (f := fun (y : (Ctx × List ℚ) × ℕ) (a : ℕ) => gQ y.1.2 (NPc y.1.1 + 1 + (offQ y.1.1 y.2 + a)))
      (by fun_prop) (by fun_prop)
  fun_prop
attribute [irreducible] lamQ
@[fun_prop] theorem lamQ_comp {α : Type} [Coding α] {f : α → Ctx} {g : α → List ℚ} {h : α → ℕ}
    (hf : Poly f) (hg : Poly g) (hh : Poly h) : Poly (fun x => lamQ (f x) (g x) (h x)) :=
  Poly.comp (f := fun y : (Ctx × List ℚ) × ℕ => lamQ y.1.1 y.1.2 y.2) poly_lamQ (Poly.pair (Poly.pair hf hg) hh)

/-- the repair context `(c, x, D, h, H)` -/
abbrev RC := Ctx × (List (List ℚ) × (List ℚ × (List ℚ × ℚ)))

section rep
variable (R : RC)

noncomputable def bdevRow (i : ℕ) : List ℚ :=
  if 0 < lamQ R.1 R.2.2.1 i then
    (rng R.1 (nOf R.1 i)).map (fun a => gQ R.2.2.1 (NPc R.1 + 1 + (offQ R.1 i + a)) / lamQ R.1 R.2.2.1 i)
  else (rng R.1 (nOf R.1 i)).map (fun a => if a = 0 then (1 : ℚ) else 0)
noncomputable def rVQ (i : ℕ) : ℚ := (R.1.1.length : ℚ) * gQ R.2.2.2.1 i - R.2.2.2.2
noncomputable def tauR : ℚ := ((List.range R.1.1.length).map (fun i => lamQ R.1 R.2.2.1 i * rVQ R i)).sum
noncomputable def gamQ (i : ℕ) : ℚ := lamQ R.1 R.2.2.1 i * (K.G0 - K.Q * rVQ R i) / (K.G0 - K.Q * tauR R)
noncomputable def DshQ (H : ℚ) : ℚ := K.beta * (K.G0 + K.Q * H)
noncomputable def delQ (i : ℕ) : ℚ := DshQ K R.2.2.2.2 / (R.1.1.length : ℚ) - K.beta * gamQ K R i - K.nu * gQ R.2.2.2.1 i
noncomputable def yRow (i : ℕ) : List ℚ :=
  (rng R.1 (nOf R.1 i)).map (fun a => (1 - K.t * gamQ K R i) * prob R.2.1 i a + K.t * gamQ K R i * gQ (bdevRow R i) a)
noncomputable def revP (i : ℕ) : ℚ :=
  delQ K R i / (1 - (((List.range R.1.1.length).filter (fun j => decide (j < i))).map (delQ K R)).sum)
end rep

theorem poly_bdevRow : Poly (fun y : RC × ℕ => bdevRow y.1 y.2) := by
  unfold bdevRow
  have h0 : Poly (fun c : Ctx => NPc c) := by unfold NPc; fun_prop
  have h1 : Poly (fun y : RC × ℕ => (rng y.1.1 (nOf y.1.1 y.2)).map
      (fun a => gQ y.1.2.2.1 (NPc y.1.1 + 1 + (offQ y.1.1 y.2 + a)) / lamQ y.1.1 y.1.2.2.1 y.2)) :=
    Poly.list_map (f := fun (y : RC × ℕ) (a : ℕ) =>
      gQ y.1.2.2.1 (NPc y.1.1 + 1 + (offQ y.1.1 y.2 + a)) / lamQ y.1.1 y.1.2.2.1 y.2) (by fun_prop) (by fun_prop)
  have h2 : Poly (fun y : RC × ℕ => (rng y.1.1 (nOf y.1.1 y.2)).map (fun a => if a = 0 then (1 : ℚ) else 0)) :=
    Poly.list_map (f := fun (_ : RC × ℕ) (a : ℕ) => if a = 0 then (1 : ℚ) else 0) (by fun_prop) (by fun_prop)
  fun_prop
attribute [irreducible] bdevRow
@[fun_prop] theorem bdevRow_comp {α : Type} [Coding α] {f : α → RC} {g : α → ℕ} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => bdevRow (f x) (g x)) := Poly.comp (f := fun y : RC × ℕ => bdevRow y.1 y.2) poly_bdevRow (Poly.pair hf hg)

theorem poly_rVQ : Poly (fun y : RC × ℕ => rVQ y.1 y.2) := by unfold rVQ; fun_prop
attribute [irreducible] rVQ
@[fun_prop] theorem rVQ_comp {α : Type} [Coding α] {f : α → RC} {g : α → ℕ} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => rVQ (f x) (g x)) := Poly.comp (f := fun y : RC × ℕ => rVQ y.1 y.2) poly_rVQ (Poly.pair hf hg)
theorem poly_tauR : Poly tauR := by unfold tauR; fun_prop
attribute [irreducible] tauR
@[fun_prop] theorem tauR_comp {α : Type} [Coding α] {f : α → RC} (hf : Poly f) : Poly (fun x => tauR (f x)) :=
  Poly.comp (f := tauR) poly_tauR hf
theorem poly_gamQ : Poly (fun y : RC × ℕ => gamQ K y.1 y.2) := by unfold gamQ; fun_prop
attribute [irreducible] gamQ
@[fun_prop] theorem gamQ_comp {α : Type} [Coding α] {f : α → RC} {g : α → ℕ} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => gamQ K (f x) (g x)) := Poly.comp (f := fun y : RC × ℕ => gamQ K y.1 y.2) (poly_gamQ K) (Poly.pair hf hg)
theorem poly_delQ : Poly (fun y : RC × ℕ => delQ K y.1 y.2) := by unfold delQ DshQ; fun_prop
attribute [irreducible] delQ
@[fun_prop] theorem delQ_comp {α : Type} [Coding α] {f : α → RC} {g : α → ℕ} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => delQ K (f x) (g x)) := Poly.comp (f := fun y : RC × ℕ => delQ K y.1 y.2) (poly_delQ K) (Poly.pair hf hg)
theorem poly_yRow : Poly (fun y : RC × ℕ => yRow K y.1 y.2) := by
  unfold yRow
  exact Poly.list_map (f := fun (y : RC × ℕ) (a : ℕ) =>
    (1 - K.t * gamQ K y.1 y.2) * prob y.1.2.1 y.2 a + K.t * gamQ K y.1 y.2 * gQ (bdevRow y.1 y.2) a) (by fun_prop) (by fun_prop)
attribute [irreducible] yRow
@[fun_prop] theorem yRow_comp {α : Type} [Coding α] {f : α → RC} {g : α → ℕ} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => yRow K (f x) (g x)) := Poly.comp (f := fun y : RC × ℕ => yRow K y.1 y.2) (poly_yRow K) (Poly.pair hf hg)
theorem poly_revP : Poly (fun y : RC × ℕ => revP K y.1 y.2) := by
  unfold revP
  have : Poly (fun y : RC × ℕ => (((List.range y.1.1.1.length).filter (fun j => decide (j < y.2))).map (delQ K y.1)).sum) := by
    have h1 : Poly (fun y : RC × ℕ => ((List.range y.1.1.1.length).filter (fun j => decide (j < y.2))).map (delQ K y.1)) := by
      exact Poly.list_map (f := fun (y : RC × ℕ) (j : ℕ) => delQ K y.1 j) (by fun_prop) (by fun_prop)
    fun_prop
  fun_prop
attribute [irreducible] revP
@[fun_prop] theorem revP_comp {α : Type} [Coding α] {f : α → RC} {g : α → ℕ} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => revP K (f x) (g x)) := Poly.comp (f := fun y : RC × ℕ => revP K y.1 y.2) (poly_revP K) (Poly.pair hf hg)

/-! ### generic append-fold and argmax -/

theorem poly_appFold {γ : Type} [Coding γ] (f : (γ × List ℕ) × ℕ → ℕ) (hf : Poly f)
    (hb : ∀ g bs k, f ((g, bs), k) ≤ (enc g).length) :
    Poly (fun x : γ × List ℕ => x.2.foldl (fun bs k => bs ++ [f ((x.1, bs), k)]) []) := by
  have hop : Poly (fun p : (γ × List ℕ) × ℕ => p.1.2 ++ [f p]) := by fun_prop
  have hext : ∀ (g : γ) (pre b : List ℕ), ∃ ext : List ℕ,
      pre.foldl (fun bs k => (fun p : (γ × List ℕ) × ℕ => p.1.2 ++ [f p]) ((g, bs), k)) b = b ++ ext ∧
      ext.length = pre.length ∧ ∀ e ∈ ext, e ≤ (enc g).length := by
    intro g pre
    induction pre with
    | nil => intro b; exact ⟨[], by simp, rfl, by simp⟩
    | cons a pre ih =>
      intro b
      obtain ⟨ext, h1, h2, h3⟩ := ih (b ++ [f ((g, b), a)])
      refine ⟨f ((g, b), a) :: ext, ?_, by simp [h2], ?_⟩
      · simp only [List.foldl_cons] at h1 ⊢; rw [h1]; simp
      · intro e he
        rcases List.mem_cons.mp he with rfl | he
        · exact hb _ _ _
        · exact h3 e he
  have hF := poly_foldl_ctx (γ := γ) (α := ℕ) (β := List ℕ) (fun p => p.1.2 ++ [f p]) hop
    (Polynomial.X + Polynomial.X * Polynomial.X) (by
      intro g as b pre suf he
      obtain ⟨ext, h1, h2, h3⟩ := hext g pre b
      rw [h1]
      have hx : (encodeList Nat.bits ext).length ≤ ext.length * (2 * (enc g).length + 1) :=
        EncodedList.length_bound Nat.bits ext _ (fun e he => (bits_len_le e).trans (h3 e he))
      have hpre : pre.length ≤ (enc as).length := by
        have := EncodedList.length_le Nat.bits as
        have hl : pre.length ≤ as.length := by rw [he]; simp
        exact hl.trans this
      show (encodePair enc (encodeList Nat.bits) (g, b ++ ext)).length ≤
        Polynomial.eval (encodePair (encodeList Nat.bits) (encodePair enc (encodeList Nat.bits)) (as, (g, b))).length
          (Polynomial.X + Polynomial.X * Polynomial.X)
      simp only [encodePair_length, EncodedList.append, List.length_append, Polynomial.eval_add,
        Polynomial.eval_mul, Polynomial.eval_X]
      set T := 2 * (encodeList Nat.bits as).length + 1 + (2 * (enc g).length + 1 + (encodeList Nat.bits b).length)
      have hT1 : (enc as).length ≤ T := by show (encodeList Nat.bits as).length ≤ T; omega
      have hT2 : 2 * (enc g).length + 1 ≤ T := by omega
      rw [h2] at hx
      have : pre.length * (2 * (enc g).length + 1) ≤ T * T := Nat.mul_le_mul (hpre.trans hT1) hT2
      omega)
  exact Poly.comp hF (Poly.pair Poly.fst (Poly.pair Poly.snd (Automatic.Poly.const (α := γ × List ℕ) ([] : List ℕ))))

noncomputable def argI (L : List ℚ) : ℕ := L.findIdx (fun v => L.all (fun v' => decide (v' ≤ v)))
theorem poly_argI : Poly argI := by
  unfold argI
  refine Poly.list_findIdx (f := fun (L : List ℚ) (v : ℚ) => L.all (fun v' => decide (v' ≤ v))) ?_ Poly.identity
  refine MNRL22.list_all (f := fun (p : List ℚ × ℚ) (v' : ℚ) => decide (v' ≤ p.2)) ?_ ?_
  · exact Poly.rat_le_comp (Poly.comp Poly.snd Poly.identity) (Poly.comp Poly.snd Poly.fst)
  · exact Poly.fst
theorem argI_le (L : List ℚ) : argI L ≤ L.length := by unfold argI; exact List.findIdx_le_length
theorem argI_spec (L : List ℚ) (hL : L ≠ []) : ∃ h : argI L < L.length, ∀ v ∈ L, v ≤ L[argI L] := by
  unfold argI
  obtain ⟨v0, hv0, hmax⟩ := L.toFinset.exists_max_image id (by simpa using hL)
  have hex : ∃ v ∈ L, (L.all (fun v' => decide (v' ≤ v))) = true := by
    refine ⟨v0, List.mem_toFinset.1 hv0, ?_⟩
    rw [List.all_eq_true]
    intro v hv; simpa using hmax v (List.mem_toFinset.2 hv)
  have hlt := List.findIdx_lt_length_of_exists hex
  have hP := List.findIdx_getElem (w := hlt)
  refine ⟨hlt, fun v hv => ?_⟩
  rw [List.all_eq_true] at hP
  simpa using hP v hv
attribute [irreducible] argI
@[fun_prop] theorem argI_comp {α : Type} [Coding α] {f : α → List ℚ} (hf : Poly f) :
    Poly (fun x => argI (f x)) := Poly.comp (f := argI) poly_argI hf

theorem ctx_len (c : Ctx) : c.2.length ≤ (enc c).length := by
  show c.2.length ≤ (encodePair (encodeList Nat.bits) (encodeList Ratio.encode) c).length
  rw [encodePair_length]
  have := EncodedList.length_le Ratio.encode c.2
  omega
theorem pair_len_fst {α β : Type} [Coding α] [Coding β] (p : α × β) : (enc p.1).length ≤ (enc p).length := by
  show (enc p.1).length ≤ (encodePair enc enc p).length
  rw [encodePair_length]; omega
theorem rng_len (c : Ctx) (n : ℕ) : (rng c n).length ≤ c.2.length := by
  unfold rng; exact (List.length_filter_le _ _).trans (by simp)

/-! ### the reverse sweep -/
section rev
variable (R : RC)

noncomputable def revRowA (j a : ℕ) : List ℚ :=
  (rng R.1 (nOf R.1 j)).map (fun b => (1 - revP K R j) * gQ (yRow K R j) b + revP K R j * (if b = a then 1 else 0))
noncomputable def profR (bs : List ℕ) (i : ℕ) : List (List ℚ) :=
  (List.range R.1.1.length).map (fun j =>
    if j < i then yRow K R j else revRowA K R j (bs[R.1.1.length - 1 - j]?.getD 0))
noncomputable def revBR (bs : List ℕ) (i : ℕ) : ℕ :=
  argI ((rng R.1 (nOf R.1 i)).map (fun a => pureQ R.1 (profR K R bs i) i a))
noncomputable def arevL : List ℕ :=
  (List.range R.1.1.length).foldl (fun bs k => bs ++ [revBR K R bs (R.1.1.length - 1 - k)]) []
end rev

theorem poly_revRowA : Poly (fun y : RC × ℕ × ℕ => revRowA K y.1 y.2.1 y.2.2) := by
  unfold revRowA
  exact Poly.list_map (f := fun (y : RC × ℕ × ℕ) (b : ℕ) =>
    (1 - revP K y.1 y.2.1) * gQ (yRow K y.1 y.2.1) b + revP K y.1 y.2.1 * (if b = y.2.2 then 1 else 0))
    (by fun_prop) (by fun_prop)
attribute [irreducible] revRowA
@[fun_prop] theorem revRowA_comp {α : Type} [Coding α] {f : α → RC} {g h : α → ℕ} (hf : Poly f) (hg : Poly g) (hh : Poly h) :
    Poly (fun x => revRowA K (f x) (g x) (h x)) :=
  Poly.comp (f := fun y : RC × ℕ × ℕ => revRowA K y.1 y.2.1 y.2.2) (poly_revRowA K) (Poly.pair hf (Poly.pair hg hh))
theorem poly_profR : Poly (fun y : RC × List ℕ × ℕ => profR K y.1 y.2.1 y.2.2) := by
  unfold profR
  exact Poly.list_map (f := fun (y : RC × List ℕ × ℕ) (j : ℕ) =>
    if j < y.2.2 then yRow K y.1 j else revRowA K y.1 j (y.2.1[y.1.1.1.length - 1 - j]?.getD 0))
    (by fun_prop) (by fun_prop)
attribute [irreducible] profR
@[fun_prop] theorem profR_comp {α : Type} [Coding α] {f : α → RC} {g : α → List ℕ} {h : α → ℕ} (hf : Poly f) (hg : Poly g) (hh : Poly h) :
    Poly (fun x => profR K (f x) (g x) (h x)) :=
  Poly.comp (f := fun y : RC × List ℕ × ℕ => profR K y.1 y.2.1 y.2.2) (poly_profR K) (Poly.pair hf (Poly.pair hg hh))
theorem poly_revBR : Poly (fun y : RC × List ℕ × ℕ => revBR K y.1 y.2.1 y.2.2) := by
  unfold revBR pureQ
  have : Poly (fun y : RC × List ℕ × ℕ => (rng y.1.1 (nOf y.1.1 y.2.2)).map (fun a =>
      payoff y.1.1 (setL (profR K y.1 y.2.1 y.2.2) y.2.2 (pureRow y.1.1 y.2.2 a)) y.2.2)) :=
    Poly.list_map (f := fun (y : RC × List ℕ × ℕ) (a : ℕ) =>
      payoff y.1.1 (setL (profR K y.1 y.2.1 y.2.2) y.2.2 (pureRow y.1.1 y.2.2 a)) y.2.2)
      (by fun_prop) (by fun_prop)
  fun_prop
theorem revBR_le (R : RC) (bs : List ℕ) (i : ℕ) : revBR K R bs i ≤ (enc R).length := by
  unfold revBR
  refine (argI_le _).trans ?_
  rw [List.length_map]
  exact (rng_len _ _).trans ((ctx_len _).trans (pair_len_fst R))
attribute [irreducible] revBR
theorem poly_arevL : Poly (arevL K) := by
  have h := poly_appFold (γ := RC) (fun p => revBR K p.1.1 p.1.2 (p.1.1.1.1.length - 1 - p.2))
    (by have := poly_revBR K; fun_prop) (fun g bs k => revBR_le K g bs _)
  have := Poly.comp h (Poly.pair Poly.identity (Poly.comp Poly.list_indices (Poly.comp Poly.fst Poly.fst)))
  unfold arevL; exact this
attribute [irreducible] arevL
@[fun_prop] theorem arevL_comp {α : Type} [Coding α] {f : α → RC} (hf : Poly f) :
    Poly (fun x => arevL K (f x)) := Poly.comp (f := arevL K) (poly_arevL K) hf

/-! ### the forward sweep -/
abbrev RA := RC × List ℕ

section fwd
variable (A : RA)
noncomputable def xtRow (j : ℕ) : List ℚ := revRowA K A.1 j (A.2[A.1.1.1.length - 1 - j]?.getD 0)
noncomputable def xtL : List (List ℚ) := (List.range A.1.1.1.length).map (xtRow K A)
noncomputable def CrawQ (R : RC) : ℚ := K.rho * ((List.range R.1.1.length).map (fun i => 1 - K.t * gamQ K R i)).prod
noncomputable def eQ (i : ℕ) : ℚ :=
  if (CrawQ K A.1 * scQ A.1.1 A.1.2.1 + DshQ K A.1.2.2.2.2) / (A.1.1.1.length : ℚ) - (1 - regQ A.1.1 (xtL K A) i) ≤ 0 then 0
  else (CrawQ K A.1 * scQ A.1.1 A.1.2.1 + DshQ K A.1.2.2.2.2) / (A.1.1.1.length : ℚ) - (1 - regQ A.1.1 (xtL K A) i)
noncomputable def fwdP (i : ℕ) : ℚ :=
  eQ K A i / (1 + (((List.range A.1.1.1.length).filter (fun j => decide (j < i + 1))).map (eQ K A)).sum)
noncomputable def fwdRowA (j a : ℕ) : List ℚ :=
  (rng A.1.1 (nOf A.1.1 j)).map (fun b => (1 - fwdP K A j) * gQ (xtRow K A j) b + fwdP K A j * (if b = a then 1 else 0))
noncomputable def profF (bs : List ℕ) (i : ℕ) : List (List ℚ) :=
  (List.range A.1.1.1.length).map (fun j => if j < i then fwdRowA K A j (bs[j]?.getD 0) else xtRow K A j)
noncomputable def fwdBR (bs : List ℕ) (i : ℕ) : ℕ :=
  argI ((rng A.1.1 (nOf A.1.1 i)).map (fun a => pureQ A.1.1 (profF K A bs i) i a))
noncomputable def acorL : List ℕ :=
  (List.range A.1.1.1.length).foldl (fun bs k => bs ++ [fwdBR K A bs k]) []
end fwd

theorem poly_xtRow : Poly (fun y : RA × ℕ => xtRow K y.1 y.2) := by unfold xtRow; fun_prop
attribute [irreducible] xtRow
@[fun_prop] theorem xtRow_comp {α : Type} [Coding α] {f : α → RA} {g : α → ℕ} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => xtRow K (f x) (g x)) := Poly.comp (f := fun y : RA × ℕ => xtRow K y.1 y.2) (poly_xtRow K) (Poly.pair hf hg)
theorem poly_xtL : Poly (xtL K) := by
  unfold xtL
  exact Poly.list_map (f := fun (y : RA) (j : ℕ) => xtRow K y j) (by fun_prop) (by fun_prop)
attribute [irreducible] xtL
@[fun_prop] theorem xtL_comp {α : Type} [Coding α] {f : α → RA} (hf : Poly f) :
    Poly (fun x => xtL K (f x)) := Poly.comp (f := xtL K) (poly_xtL K) hf
theorem poly_CrawQ : Poly (CrawQ K) := by
  unfold CrawQ
  have : Poly (fun R : RC => (List.range R.1.1.length).map (fun i => 1 - K.t * gamQ K R i)) :=
    Poly.list_map (f := fun (R : RC) (i : ℕ) => 1 - K.t * gamQ K R i) (by fun_prop) (by fun_prop)
  fun_prop
attribute [irreducible] CrawQ
@[fun_prop] theorem CrawQ_comp {α : Type} [Coding α] {f : α → RC} (hf : Poly f) :
    Poly (fun x => CrawQ K (f x)) := Poly.comp (f := CrawQ K) (poly_CrawQ K) hf
theorem poly_eQ : Poly (fun y : RA × ℕ => eQ K y.1 y.2) := by unfold eQ DshQ; fun_prop
attribute [irreducible] eQ
@[fun_prop] theorem eQ_comp {α : Type} [Coding α] {f : α → RA} {g : α → ℕ} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => eQ K (f x) (g x)) := Poly.comp (f := fun y : RA × ℕ => eQ K y.1 y.2) (poly_eQ K) (Poly.pair hf hg)
theorem poly_fwdP : Poly (fun y : RA × ℕ => fwdP K y.1 y.2) := by
  unfold fwdP
  have : Poly (fun y : RA × ℕ => ((List.range y.1.1.1.1.length).filter (fun j => decide (j < y.2 + 1))).map (eQ K y.1)) :=
    Poly.list_map (f := fun (y : RA × ℕ) (j : ℕ) => eQ K y.1 j) (by fun_prop) (by fun_prop)
  fun_prop
attribute [irreducible] fwdP
@[fun_prop] theorem fwdP_comp {α : Type} [Coding α] {f : α → RA} {g : α → ℕ} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => fwdP K (f x) (g x)) := Poly.comp (f := fun y : RA × ℕ => fwdP K y.1 y.2) (poly_fwdP K) (Poly.pair hf hg)
theorem poly_fwdRowA : Poly (fun y : RA × ℕ × ℕ => fwdRowA K y.1 y.2.1 y.2.2) := by
  unfold fwdRowA
  exact Poly.list_map (f := fun (y : RA × ℕ × ℕ) (b : ℕ) =>
    (1 - fwdP K y.1 y.2.1) * gQ (xtRow K y.1 y.2.1) b + fwdP K y.1 y.2.1 * (if b = y.2.2 then 1 else 0))
    (by fun_prop) (by fun_prop)
attribute [irreducible] fwdRowA
@[fun_prop] theorem fwdRowA_comp {α : Type} [Coding α] {f : α → RA} {g h : α → ℕ} (hf : Poly f) (hg : Poly g) (hh : Poly h) :
    Poly (fun x => fwdRowA K (f x) (g x) (h x)) :=
  Poly.comp (f := fun y : RA × ℕ × ℕ => fwdRowA K y.1 y.2.1 y.2.2) (poly_fwdRowA K) (Poly.pair hf (Poly.pair hg hh))
theorem poly_profF : Poly (fun y : RA × List ℕ × ℕ => profF K y.1 y.2.1 y.2.2) := by
  unfold profF
  exact Poly.list_map (f := fun (y : RA × List ℕ × ℕ) (j : ℕ) =>
    if j < y.2.2 then fwdRowA K y.1 j (y.2.1[j]?.getD 0) else xtRow K y.1 j)
    (by fun_prop) (by fun_prop)
attribute [irreducible] profF
@[fun_prop] theorem profF_comp {α : Type} [Coding α] {f : α → RA} {g : α → List ℕ} {h : α → ℕ} (hf : Poly f) (hg : Poly g) (hh : Poly h) :
    Poly (fun x => profF K (f x) (g x) (h x)) :=
  Poly.comp (f := fun y : RA × List ℕ × ℕ => profF K y.1 y.2.1 y.2.2) (poly_profF K) (Poly.pair hf (Poly.pair hg hh))
theorem poly_fwdBR : Poly (fun y : RA × List ℕ × ℕ => fwdBR K y.1 y.2.1 y.2.2) := by
  unfold fwdBR pureQ
  have : Poly (fun y : RA × List ℕ × ℕ => (rng y.1.1.1 (nOf y.1.1.1 y.2.2)).map (fun a =>
      payoff y.1.1.1 (setL (profF K y.1 y.2.1 y.2.2) y.2.2 (pureRow y.1.1.1 y.2.2 a)) y.2.2)) :=
    Poly.list_map (f := fun (y : RA × List ℕ × ℕ) (a : ℕ) =>
      payoff y.1.1.1 (setL (profF K y.1 y.2.1 y.2.2) y.2.2 (pureRow y.1.1.1 y.2.2 a)) y.2.2)
      (by fun_prop) (by fun_prop)
  fun_prop
theorem fwdBR_le (A : RA) (bs : List ℕ) (i : ℕ) : fwdBR K A bs i ≤ (enc A).length := by
  unfold fwdBR
  refine (argI_le _).trans ?_
  rw [List.length_map]
  exact (rng_len _ _).trans ((ctx_len _).trans ((pair_len_fst A.1).trans (pair_len_fst A)))
attribute [irreducible] fwdBR
theorem poly_acorL : Poly (acorL K) := by
  have h := poly_appFold (γ := RA) (fun p => fwdBR K p.1.1 p.1.2 p.2)
    (by have := poly_fwdBR K; fun_prop) (fun g bs k => fwdBR_le K g bs _)
  have := Poly.comp h (Poly.pair Poly.identity (Poly.comp Poly.list_indices (Poly.comp Poly.fst (Poly.comp Poly.fst Poly.fst))))
  unfold acorL; exact this
attribute [irreducible] acorL
@[fun_prop] theorem acorL_comp {α : Type} [Coding α] {f : α → RA} (hf : Poly f) :
    Poly (fun x => acorL K (f x)) := Poly.comp (f := acorL K) (poly_acorL K) hf

/-! ### one iteration of Algorithm 1 -/
/-- algorithm state `(c, x, h, H)` -/
abbrev ST := Ctx × (List (List ℚ) × (List ℚ × ℚ))

theorem poly_NPc' : Poly (fun c : Ctx => NPc c) := by unfold NPc; fun_prop
@[fun_prop] theorem NPc_comp' {α : Type} [Coding α] {f : α → Ctx} (hf : Poly f) :
    Poly (fun x => NPc (f x)) := Poly.comp (f := fun c : Ctx => NPc c) poly_NPc' hf

section it
variable (S : ST)
noncomputable def DQ : List ℚ := (lpRes K.η (S.1, S.2.1)).2.1
noncomputable def RofS : RC := (S.1, (S.2.1, (DQ K S, (S.2.2.1, S.2.2.2))))
noncomputable def AofS : RA := (RofS K S, arevL K (RofS K S))
noncomputable def repST : ST :=
  (S.1, ((List.range S.1.1.length).map (fun j => fwdRowA K (AofS K S) j ((acorL K (AofS K S))[j]?.getD 0)),
    ((List.range S.1.1.length).map (fun i => K.c * (gQ S.2.2.1 i + K.t * gamQ K (RofS K S) i)),
      K.c * (S.2.2.2 + K.t))))
noncomputable def descST : ST :=
  (S.1, ((List.range S.1.1.length).map (descRow K S.1 S.2.1 (DQ K S)),
    (S.2.2.1.map (fun v => PdQ K S.1 (DQ K S) * v), PdQ K S.1 (DQ K S) * S.2.2.2)))
noncomputable def iterQ : ST :=
  if K.σ ≤ scQ S.1 S.2.1 then S
  else if gQ (DQ K S) (NPc S.1) ≤ RegQ S.1 S.2.1 - K.η * muQ K S.1 S.2.1 S.2.2.2 / (S.1.1.length : ℚ) then descST K S
  else repST K S
end it

theorem poly_DQ : Poly (DQ K) := by unfold DQ; fun_prop
attribute [irreducible] DQ
@[fun_prop] theorem DQ_comp {α : Type} [Coding α] {f : α → ST} (hf : Poly f) :
    Poly (fun x => DQ K (f x)) := Poly.comp (f := DQ K) (poly_DQ K) hf
theorem poly_RofS : Poly (RofS K) := by unfold RofS; fun_prop
attribute [irreducible] RofS
@[fun_prop] theorem RofS_comp {α : Type} [Coding α] {f : α → ST} (hf : Poly f) :
    Poly (fun x => RofS K (f x)) := Poly.comp (f := RofS K) (poly_RofS K) hf
theorem poly_AofS : Poly (AofS K) := by unfold AofS; fun_prop
attribute [irreducible] AofS
@[fun_prop] theorem AofS_comp {α : Type} [Coding α] {f : α → ST} (hf : Poly f) :
    Poly (fun x => AofS K (f x)) := Poly.comp (f := AofS K) (poly_AofS K) hf
theorem poly_repST : Poly (repST K) := by
  unfold repST
  have h1 : Poly (fun S : ST => (List.range S.1.1.length).map (fun j => fwdRowA K (AofS K S) j ((acorL K (AofS K S))[j]?.getD 0))) :=
    Poly.list_map (f := fun (S : ST) (j : ℕ) => fwdRowA K (AofS K S) j ((acorL K (AofS K S))[j]?.getD 0)) (by fun_prop) (by fun_prop)
  have h2 : Poly (fun S : ST => (List.range S.1.1.length).map (fun i => K.c * (gQ S.2.2.1 i + K.t * gamQ K (RofS K S) i))) :=
    Poly.list_map (f := fun (S : ST) (i : ℕ) => K.c * (gQ S.2.2.1 i + K.t * gamQ K (RofS K S) i)) (by fun_prop) (by fun_prop)
  fun_prop
theorem poly_descST : Poly (descST K) := by
  unfold descST
  have h1 : Poly (fun S : ST => (List.range S.1.1.length).map (descRow K S.1 S.2.1 (DQ K S))) :=
    Poly.list_map (f := fun (S : ST) (j : ℕ) => descRow K S.1 S.2.1 (DQ K S) j) (by fun_prop) (by fun_prop)
  have h2 : Poly (fun S : ST => S.2.2.1.map (fun v => PdQ K S.1 (DQ K S) * v)) :=
    Poly.list_map (f := fun (S : ST) (v : ℚ) => PdQ K S.1 (DQ K S) * v) (by fun_prop) (by fun_prop)
  fun_prop
theorem poly_iterQ : Poly (iterQ K) := by
  have := poly_repST K; have := poly_descST K
  unfold iterQ; fun_prop
attribute [irreducible] repST descST iterQ

end MNRAlg

-- ===== R46G =====

namespace MNRAlg
open NashAmplification.Filtering MNRL22 MNRRam MNRLP MultiNashRepair

variable {σ : ℚ} (ctrl : Controls σ)

/-- the rational constants of Algorithm 1 for the controls `ctrl` -/
def uQ : ℚ := ctrl.u
noncomputable def KofC : KQ where
  σ := σ
  η := ctrl.η
  d := ctrl.d
  c := 1 - ctrl.u + ctrl.u ^ 2 / 2 - ctrl.u ^ 3
  t := ctrl.f0 * ctrl.u
  rho := 1 - (1 - ctrl.f0) * ctrl.u + (1 - ctrl.f0) ^ 2 * ctrl.u ^ 2 / 2
  beta := (1 - ctrl.u + ctrl.u ^ 2 / 2 - ctrl.u ^ 3) * (ctrl.f0 * ctrl.u) * (1 + (ctrl.u - ctrl.u ^ 2))
  nu := (1 - ctrl.u + ctrl.u ^ 2 / 2 - ctrl.u ^ 3) * (ctrl.u - ctrl.u ^ 2)
  R0 := (1 - (1 - (1 - ctrl.f0) * ctrl.u + (1 - ctrl.f0) ^ 2 * ctrl.u ^ 2 / 2)) /
    ((1 - ctrl.u + ctrl.u ^ 2 / 2 - ctrl.u ^ 3) * (ctrl.f0 * ctrl.u) * (1 + (ctrl.u - ctrl.u ^ 2)))
  G0 := 1 + (1 - (1 - (1 - ctrl.f0) * ctrl.u + (1 - ctrl.f0) ^ 2 * ctrl.u ^ 2 / 2)) /
    ((1 - ctrl.u + ctrl.u ^ 2 / 2 - ctrl.u ^ 3) * (ctrl.f0 * ctrl.u) * (1 + (ctrl.u - ctrl.u ^ 2)))
  Q := ((1 - ctrl.u + ctrl.u ^ 2 / 2 - ctrl.u ^ 3) * (ctrl.u - ctrl.u ^ 2)) /
    ((1 - ctrl.u + ctrl.u ^ 2 / 2 - ctrl.u ^ 3) * (ctrl.f0 * ctrl.u) * (1 + (ctrl.u - ctrl.u ^ 2)))

theorem K_c : ((KofC ctrl).c : ℝ) = ctrl.knobs.c := by
  simp [KofC, Knobs.c, Controls.knobs]
theorem K_t : ((KofC ctrl).t : ℝ) = ctrl.knobs.t := by
  simp [KofC, Knobs.t, Controls.knobs]
theorem K_rho : ((KofC ctrl).rho : ℝ) = ctrl.knobs.rho := by
  simp [KofC, Knobs.rho, Controls.knobs]
theorem K_beta : ((KofC ctrl).beta : ℝ) = ctrl.knobs.beta := by
  simp [KofC, Knobs.beta, Knobs.c, Knobs.t, Knobs.u0, Controls.knobs]
theorem K_nu : ((KofC ctrl).nu : ℝ) = ctrl.knobs.nu := by
  simp [KofC, Knobs.nu, Knobs.c, Knobs.u0, Controls.knobs]
theorem K_R0 : ((KofC ctrl).R0 : ℝ) = ctrl.knobs.R0 := by
  simp [KofC, Knobs.R0, Knobs.rho, Knobs.beta, Knobs.c, Knobs.t, Knobs.u0, Controls.knobs]
theorem K_G0 : ((KofC ctrl).G0 : ℝ) = ctrl.knobs.G0 := by
  simp [KofC, Knobs.G0, Knobs.R0, Knobs.rho, Knobs.beta, Knobs.c, Knobs.t, Knobs.u0, Controls.knobs]
theorem K_Q : ((KofC ctrl).Q : ℝ) = ctrl.knobs.Q := by
  simp [KofC, Knobs.Q, Knobs.nu, Knobs.beta, Knobs.c, Knobs.t, Knobs.u0, Controls.knobs]
theorem K_eta : ((KofC ctrl).η : ℝ) = (ctrl.η : ℝ) := rfl
theorem K_d : ((KofC ctrl).d : ℝ) = (ctrl.d : ℝ) := rfl
theorem K_sigma : ((KofC ctrl).σ : ℝ) = (σ : ℝ) := rfl

theorem K_Su (H : ℚ) : ((SuQ (KofC ctrl) H : ℚ) : ℝ) = ctrl.knobs.Su H := by
  unfold SuQ Knobs.Su Knobs.Cu; push_cast; rw [K_R0, K_Q]
theorem K_Dsh (H : ℚ) : ((DshQ (KofC ctrl) H : ℚ) : ℝ) = ctrl.knobs.Dsh H := by
  unfold DshQ Knobs.Dsh; push_cast; rw [K_beta, K_G0, K_Q]

/-! ### list/finset bridges -/

theorem sumQ_fin (n : ℕ) (f : ℕ → ℚ) : ((((List.range n).map f).sum : ℚ) : ℝ) = ∑ a : Fin n, (f a : ℝ) := by
  rw [list_sum_range, Rat.cast_sum, Fin.sum_univ_eq_sum_range (fun a => (f a : ℝ))]
theorem prodQ_fin (n : ℕ) (f : ℕ → ℚ) : ((((List.range n).map f).prod : ℚ) : ℝ) = ∏ a : Fin n, (f a : ℝ) := by
  rw [list_prod_range, Rat.cast_prod, Fin.prod_univ_eq_prod_range (fun a => (f a : ℝ))]

theorem maxL_fin (n : ℕ) (hn : 0 < n) (f : ℕ → ℚ) :
    ((maxL ((List.range n).map f) : ℚ) : ℝ) = ⨆ a : Fin n, (f a : ℝ) := by
  have hne : (List.range n).map f ≠ [] := by simp; omega
  obtain ⟨hmem, hle⟩ := maxL_spec _ hne
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  apply le_antisymm
  · obtain ⟨a, ha, he⟩ := List.mem_map.1 hmem
    rw [← he]
    exact le_ciSup (f := fun b : Fin n => ((f b : ℚ) : ℝ)) (Finite.bddAbove_range _) (⟨a, List.mem_range.1 ha⟩ : Fin n)
  · refine ciSup_le (fun a => ?_)
    exact_mod_cast hle _ (List.mem_map.2 ⟨a, List.mem_range.2 a.isLt, rfl⟩)

theorem fsum_filter_lt (n : ℕ) (f : ℕ → ℚ) (i : Fin n) :
    (((((List.range n).filter (fun j => decide (j < i.val))).map f).sum : ℚ) : ℝ) =
      ∑ j ∈ Finset.univ.filter (· < i), (f j : ℝ) := by
  rw [range_filter_lt, show min i.val n = i.val from min_eq_left i.isLt.le, list_sum_range, Rat.cast_sum]
  rw [Finset.sum_filter]
  have e : ∀ a : Fin n, (if a < i then (f a : ℝ) else 0) = (fun j => if j < i.val then (f j : ℝ) else 0) a.val :=
    fun a => if_congr Fin.lt_iff_val_lt_val rfl rfl
  rw [Finset.sum_congr rfl (fun a _ => e a), Fin.sum_univ_eq_sum_range (fun j => if j < i.val then (f j : ℝ) else 0) n]
  rw [← Finset.sum_range_add_sum_Ico _ i.isLt.le]
  rw [Finset.sum_congr rfl (fun j hj => if_pos (Finset.mem_range.1 hj))]
  rw [Finset.sum_eq_zero (fun j hj => if_neg (by have := (Finset.mem_Ico.1 hj).1; omega)), add_zero]
theorem fsum_filter_le (n : ℕ) (f : ℕ → ℚ) (i : Fin n) :
    (((((List.range n).filter (fun j => decide (j < i.val + 1))).map f).sum : ℚ) : ℝ) =
      ∑ j ∈ Finset.univ.filter (· ≤ i), (f j : ℝ) := by
  rw [range_filter_lt, show min (i.val + 1) n = i.val + 1 from min_eq_left i.isLt, list_sum_range, Rat.cast_sum]
  rw [Finset.sum_filter]
  have e : ∀ a : Fin n, (if a ≤ i then (f a : ℝ) else 0) = (fun j => if j ≤ i.val then (f j : ℝ) else 0) a.val :=
    fun a => if_congr Fin.le_iff_val_le_val rfl rfl
  rw [Finset.sum_congr rfl (fun a _ => e a), Fin.sum_univ_eq_sum_range (fun j => if j ≤ i.val then (f j : ℝ) else 0) n]
  rw [← Finset.sum_range_add_sum_Ico _ (show i.val + 1 ≤ n from i.isLt)]
  rw [Finset.sum_congr rfl (fun j hj => if_pos (by have := Finset.mem_range.1 hj; omega))]
  rw [Finset.sum_eq_zero (fun j hj => if_neg (by have := (Finset.mem_Ico.1 hj).1; omega)), add_zero]

theorem appFold_spec (F : List ℕ → ℕ → ℕ) : ∀ n : ℕ,
    ((List.range n).foldl (fun bs k => bs ++ [F bs k]) []).length = n ∧
    ∀ k < n, ((List.range n).foldl (fun bs k => bs ++ [F bs k]) [])[k]?.getD 0 =
      F (((List.range n).foldl (fun bs k => bs ++ [F bs k]) []).take k) k
  | 0 => by simp
  | n + 1 => by
    obtain ⟨hl, hk⟩ := appFold_spec F n
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    set r := (List.range n).foldl (fun bs k => bs ++ [F bs k]) [] with hr
    refine ⟨by simp [hl], fun k hk' => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk' with hlt | heq
    · rw [List.getElem?_append_left (by omega), List.take_append_of_le_length (by omega)]
      exact hk k hlt
    · subst heq
      rw [List.getElem?_append_right (by omega), List.take_append_of_le_length (by omega)]
      simp only [hl, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
      rw [show List.take k r = r from by rw [← hl, List.take_length]]

/-! ### the game context -/
section G
variable {m : ℕ} (G : Table m) (hm : 1 ≤ m)

theorem len_G : (cG G).1.length = m := by simp [cG, G.sizes_length]
theorem nOf_G (j : Fin m) : nOf (cG G) j.val = G.counts j := by unfold nOf; exact getD_sizes G j
include hm in
theorem rng_G (j : Fin m) : rng (cG G) (nOf (cG G) j.val) = List.range (G.counts j) := by
  rw [nOf_G]; exact rng_eq _ _ (counts_le G hm j)
theorem offQ_G (j : ℕ) : offQ (cG G) j = off G j := by
  unfold offQ off
  rw [show ((cG G).1.take j).map (fun n : ℕ => (n : ℚ)) = (G.sizes.take j).map (fun n : ℕ => (n : ℚ)) from rfl,
    ← Nat.cast_list_sum, Rat.num_natCast, Int.natAbs_natCast]
include hm in
theorem regQ_eq (x : List (List ℚ)) (hxl : x.length = m) (i : Fin m) :
    (regQ (cG G) x i.val : ℝ) = regret G.utility (Xof G x) i := by
  unfold regQ regret
  rw [rng_G G hm i, maxL_fin _ (counts_pos G i)]
  congr 1; funext a; exact gainQ_eq G hm x hxl i a
include hm in
theorem RegQ_eq (x : List (List ℚ)) (hxl : x.length = m) :
    (RegQ (cG G) x : ℝ) = Reg G.utility (Xof G x) := by
  unfold RegQ Reg
  rw [len_G, maxL_fin _ hm]
  congr 1; funext i; exact regQ_eq G hm x hxl i
include hm in
theorem scQ_eq (x : List (List ℚ)) (hxl : x.length = m) :
    (scQ (cG G) x : ℝ) = scaled G.utility (Xof G x) := by
  unfold scQ scaled q
  push_cast
  rw [len_G, RegQ_eq G hm x hxl]

include hm in
theorem row_get (j : Fin m) (f : ℕ → ℚ) (a : Fin (G.counts j)) :
    ((rng (cG G) (nOf (cG G) j.val)).map f)[a.val]?.getD 0 = f a.val := by
  rw [rng_G G hm j]; simp [List.getElem?_map, List.getElem?_range a.isLt]

theorem gQ_map_mul (L : List ℚ) (P : ℚ) (i : ℕ) : gQ (L.map (fun v => P * v)) i = P * gQ L i := by
  unfold gQ
  rcases lt_or_ge i L.length with h | h
  · simp [List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getElem?_eq_none h, List.getElem?_eq_none (by simpa using h : (L.map (fun v => P * v)).length ≤ i)]

theorem gQ_range (k : ℕ) (f : ℕ → ℚ) (i : ℕ) (hi : i < k) : gQ ((List.range k).map f) i = f i := by
  unfold gQ; simp [List.getElem?_map, List.getElem?_range hi]

theorem sum_pure (j : Fin m) (z : Fin (G.counts j) → ℝ) (a : Fin (G.counts j)) :
    (∑ b, z b • (ePure (n := G.counts) (j := j) b)) a = z a := by
  simp [Finset.sum_apply, DGPNash.WellSupported.pureStrategy]

include hm in
theorem ZQ_eq (D : List ℚ) (j : Fin m) :
    (ZQ (cG G) D j.val : ℝ) = ∑ b : Fin (G.counts j), (gQ D (off G j.val + b.val) : ℝ) := by
  unfold ZQ
  rw [rng_G G hm j, sumQ_fin, offQ_G]

include hm in
theorem PdQ_eq (D : List ℚ) :
    (PdQ (KofC ctrl) (cG G) D : ℝ) = descentFactor (ctrl.η : ℝ) (fun (j : Fin m) (b : Fin (G.counts j)) => (gQ D (off G j.val + b.val) : ℝ)) := by
  unfold PdQ descentFactor
  rw [len_G, prodQ_fin]
  refine Finset.prod_congr rfl (fun j _ => ?_)
  push_cast; rw [ZQ_eq G hm]; rfl

include hm in
theorem descRow_eq (x : List (List ℚ)) (hxl : x.length = m) (D : List ℚ) :
    Xof G ((List.range (cG G).1.length).map (descRow (KofC ctrl) (cG G) x D)) =
      descentProfile (Xof G x) (ctrl.η : ℝ) (fun j b => (gQ D (off G j.val + b.val) : ℝ)) := by
  funext j a
  unfold Xof descentProfile
  rw [len_G, prob_rows _ _ _ _ j.isLt]
  unfold descRow
  rw [row_get G hm j]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [sum_pure G j]
  push_cast
  rw [ZQ_eq G hm, offQ_G]
  rfl

include hm in
theorem lp_at (x : List (List ℚ)) (hxl : x.length = m) (S : ST) (hS : S = (cG G, (x, S.2.2))) :
    LPOptimal G.utility (Xof G x) (ctrl.η : ℝ) (fun j b => (gQ (DQ (KofC ctrl) S) (off G j.val + b.val) : ℝ)) ∧
    DualOptimal G.utility (Xof G x) (ctrl.η : ℝ)
      (fun i a => (gQ (DQ (KofC ctrl) S) (NPc (cG G) + 1 + (off G i.val + a.val)) : ℝ))
      (gQ (DQ (KofC ctrl) S) (NPc (cG G) + 1 + 2 * NPc (cG G)) : ℝ) ∧
    lpValue G.utility (Xof G x) (ctrl.η : ℝ) = (gQ (DQ (KofC ctrl) S) (NPc (cG G)) : ℝ) := by
  have := lp_link G hm x hxl (KofC ctrl).η (absR (lpRes (KofC ctrl).η (cG G, x))) (lpRes_spec _ _ _)
  rw [hS]; unfold DQ
  exact this

include hm in
theorem muQ_eq (x : List (List ℚ)) (hxl : x.length = m) (H : ℚ) :
    (muQ (KofC ctrl) (cG G) x H : ℝ) = ctrl.mu (scaled G.utility (Xof G x)) H := by
  unfold muQ Controls.mu
  push_cast
  rw [K_Su, scQ_eq G hm x hxl]; rfl

include hm in
theorem passes_iff (x : List (List ℚ)) (hxl : x.length = m) (h : List ℚ) (H : ℚ) (s : State G.counts)
    (hx : s.x = Xof G x) (hH : s.H = H) :
    Passes ctrl G.utility s ↔ gQ (DQ (KofC ctrl) (cG G, (x, (h, H)))) (NPc (cG G)) ≤
      RegQ (cG G) x - (KofC ctrl).η * muQ (KofC ctrl) (cG G) x H / ((cG G).1.length : ℚ) := by
  unfold Passes LPPasses
  rw [hx, hH, (lp_at ctrl G hm x hxl (cG G, (x, (h, H))) rfl).2.2, ← Rat.cast_le (K := ℝ)]
  push_cast
  rw [RegQ_eq G hm x hxl, muQ_eq ctrl G hm x hxl, len_G]; rfl

include hm in
theorem desc_ok (x : List (List ℚ)) (hxl : x.length = m) (h : List ℚ) (H : ℚ) (s : State G.counts)
    (hx : s.x = Xof G x) (hh : s.h = fun i => (gQ h i.val : ℝ)) (hH : s.H = H) (hpass : Passes ctrl G.utility s) :
    ∃ s', DescentStep ctrl G.utility s s' ∧
      (descST (KofC ctrl) (cG G, (x, (h, H)))).1 = cG G ∧
      (descST (KofC ctrl) (cG G, (x, (h, H)))).2.1.length = m ∧
      s'.x = Xof G (descST (KofC ctrl) (cG G, (x, (h, H)))).2.1 ∧
      s'.h = (fun i => (gQ (descST (KofC ctrl) (cG G, (x, (h, H)))).2.2.1 i.val : ℝ)) ∧
      s'.H = (descST (KofC ctrl) (cG G, (x, (h, H)))).2.2.2 := by
  set D := DQ (KofC ctrl) (cG G, (x, (h, H))) with hD
  have hlp := lp_at ctrl G hm x hxl (cG G, (x, (h, H))) rfl
  refine ⟨descentState (ctrl.η : ℝ) s (fun j b => (gQ D (off G j.val + b.val) : ℝ)), ⟨hpass, _, ?_, fun j b => ⟨_, rfl⟩, rfl⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hx]; exact hlp.1
  · unfold descST; rfl
  · unfold descST; simp [len_G]
  · unfold descST descentState; dsimp only
    rw [hx, ← descRow_eq ctrl G hm x hxl D]
  · unfold descST descentState; dsimp only
    funext i
    rw [hh, gQ_map_mul, ← PdQ_eq ctrl G hm D]
    simp [Pi.smul_apply, hD]
  · unfold descST descentState; dsimp only
    rw [hH, ← PdQ_eq ctrl G hm D]; push_cast; rfl

/-! ### the repair quantities -/
noncomputable def wOf (D : List ℚ) : (i : Fin m) → Fin (G.counts i) → ℝ :=
  fun i a => (gQ D (NPc (cG G) + 1 + (off G i.val + a.val)) : ℝ)
noncomputable def sOf (x : List (List ℚ)) (h : List ℚ) (H : ℚ) (gens : List (Gen G.counts)) : State G.counts :=
  ⟨Xof G x, fun i => (gQ h i.val : ℝ), H, gens⟩

section rep
variable (x : List (List ℚ)) (D h : List ℚ) (H : ℚ) (gens : List (Gen G.counts))

include hm in
theorem lamQ_eq (i : Fin m) : (lamQ (cG G) D i.val : ℝ) = lam (wOf G D) i := by
  unfold lamQ lam wOf
  rw [rng_G G hm i, sumQ_fin, offQ_G]

include hm in
theorem bdev_eq (i : Fin m) (a : Fin (G.counts i)) :
    (gQ (bdevRow (cG G, (x, (D, (h, H)))) i.val) a.val : ℝ) = bdev (wOf G D) i a := by
  unfold bdevRow bdev gQ
  dsimp only
  have hl : (0 < lamQ (cG G) D i.val) ↔ 0 < lam (wOf G D) i := by
    rw [← lamQ_eq G hm D i]; exact_mod_cast Iff.rfl
  by_cases hp : 0 < lamQ (cG G) D i.val
  · rw [if_pos hp, if_pos (hl.1 hp), row_get G hm i]
    push_cast; rw [lamQ_eq G hm D i, offQ_G]; rfl
  · rw [if_neg hp, if_neg (fun h' => hp (hl.2 h')), row_get G hm i]
    split_ifs <;> simp

theorem rVQ_eq (i : Fin m) :
    (rVQ (cG G, (x, (D, (h, H)))) i.val : ℝ) = rV (sOf G x h H gens) i := by
  unfold rVQ rV sOf; push_cast; rw [len_G]

include hm in
theorem tauR_eq :
    (tauR (cG G, (x, (D, (h, H)))) : ℝ) = rTau (sOf G x h H gens) (wOf G D) := by
  unfold tauR rTau
  rw [len_G, sumQ_fin]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  push_cast; rw [lamQ_eq G hm D i, rVQ_eq G x D h H gens i]

include hm in
theorem gamQ_eq (i : Fin m) :
    (gamQ (KofC ctrl) (cG G, (x, (D, (h, H)))) i.val : ℝ) = rGamma ctrl.knobs (sOf G x h H gens) (wOf G D) i := by
  unfold gamQ rGamma
  push_cast
  rw [lamQ_eq G hm D i, rVQ_eq G x D h H gens i, tauR_eq G hm x D h H gens, K_G0, K_Q]

include hm in
theorem delQ_eq (i : Fin m) :
    (delQ (KofC ctrl) (cG G, (x, (D, (h, H)))) i.val : ℝ) = rDelta ctrl.knobs (sOf G x h H gens) (wOf G D) i := by
  unfold delQ rDelta
  push_cast
  rw [K_Dsh, gamQ_eq ctrl G hm x D h H gens i, K_beta, K_nu, len_G]; rfl

include hm in
theorem yRow_eq (i : Fin m) (a : Fin (G.counts i)) :
    (gQ (yRow (KofC ctrl) (cG G, (x, (D, (h, H)))) i.val) a.val : ℝ) =
      rY ctrl.knobs (sOf G x h H gens) (wOf G D) i a := by
  unfold yRow rY actY
  rw [gQ, row_get G hm i]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  push_cast
  rw [gamQ_eq ctrl G hm x D h H gens i, bdev_eq G hm x D h H i a, K_t]; rfl

include hm in
theorem revP_eq (i : Fin m) :
    (revP (KofC ctrl) (cG G, (x, (D, (h, H)))) i.val : ℝ) = revProb (rDelta ctrl.knobs (sOf G x h H gens) (wOf G D)) i := by
  unfold revP revProb
  rw [Rat.cast_div, Rat.cast_sub, Rat.cast_one, delQ_eq ctrl G hm x D h H gens i]
  congr 2
  dsimp only
  rw [len_G, fsum_filter_lt]
  exact Finset.sum_congr rfl (fun j _ => delQ_eq ctrl G hm x D h H gens j)

include hm in
theorem revRowA_eq (ar : (i : Fin m) → Fin (G.counts i)) (j : Fin m) (a : Fin (G.counts j)) :
    (gQ (revRowA (KofC ctrl) (cG G, (x, (D, (h, H)))) j.val (ar j).val) a.val : ℝ) =
      revSweep (rY ctrl.knobs (sOf G x h H gens) (wOf G D)) (rDelta ctrl.knobs (sOf G x h H gens) (wOf G D)) ar j a := by
  unfold revRowA revSweep
  rw [gQ, row_get G hm j]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, ePure, DGPNash.WellSupported.pureStrategy]
  push_cast
  rw [revP_eq ctrl G hm x D h H gens j, yRow_eq ctrl G hm x D h H gens j a]
  congr 2
  by_cases e : a = ar j
  · subst e; simp
  · rw [if_neg e, if_neg (fun e' => e (Fin.ext e'))]; simp

end rep

include hm in
theorem pureQ_eq (P : List (List ℚ)) (hPl : P.length = m) (i : Fin m) (a : Fin (G.counts i)) :
    ((pureQ (cG G) P i.val a.val : ℚ) : ℝ) = DGPNash.NashMap.purePayoff G.utility (Xof G P) i a := by
  unfold pureQ DGPNash.NashMap.purePayoff
  have e1 := payoff_eq G hm (setL P i.val (pureRow (cG G) i.val a.val)) i
  rw [show (G.sizes, G.entries.map valQ) = cG G from rfl] at e1
  rw [e1, setL_pure_real G hm P hPl i a]
  rfl

omit hm in
theorem purePayoff_congr (P P' : Mixed G.counts) (i : Fin m) (hP : ∀ j, j ≠ i → P j = P' j) (a : Fin (G.counts i)) :
    DGPNash.NashMap.purePayoff G.utility P i a = DGPNash.NashMap.purePayoff G.utility P' i a := by
  unfold DGPNash.NashMap.purePayoff
  congr 1
  funext j
  by_cases e : j = i
  · subst e; simp
  · rw [Function.update_of_ne e, Function.update_of_ne e, hP j e]

include hm in
theorem argmax_spec (P : List (List ℚ)) (i : Fin m) :
    ∃ hlt : argI ((rng (cG G) (nOf (cG G) i.val)).map (fun a => pureQ (cG G) P i.val a)) < G.counts i,
      ∀ a : Fin (G.counts i), pureQ (cG G) P i.val a.val ≤
        pureQ (cG G) P i.val (argI ((rng (cG G) (nOf (cG G) i.val)).map (fun a => pureQ (cG G) P i.val a))) := by
  rw [rng_G G hm i]
  have hne : (List.range (G.counts i)).map (fun a => pureQ (cG G) P i.val a) ≠ [] := by
    simp; exact (counts_pos G i).ne'
  obtain ⟨hlt, hmax⟩ := argI_spec _ hne
  rw [List.length_map, List.length_range] at hlt
  refine ⟨hlt, fun a => ?_⟩
  have := hmax _ (List.mem_map.2 ⟨a.val, List.mem_range.2 a.isLt, rfl⟩)
  simpa using this

/-! ### the reverse sweep -/
section rev2
variable (x : List (List ℚ)) (D h : List ℚ) (H : ℚ) (gens : List (Gen G.counts))

theorem arevL_spec : (arevL (KofC ctrl) (cG G, (x, (D, (h, H))))).length = m ∧
    ∀ k < m, (arevL (KofC ctrl) (cG G, (x, (D, (h, H)))))[k]?.getD 0 =
      revBR (KofC ctrl) (cG G, (x, (D, (h, H)))) ((arevL (KofC ctrl) (cG G, (x, (D, (h, H))))).take k) (m - 1 - k) := by
  have hL : (cG G, (x, (D, (h, H)))).1.1.length = m := len_G G
  unfold arevL
  rw [hL]
  exact appFold_spec (fun bs k => revBR (KofC ctrl) (cG G, (x, (D, (h, H)))) bs (m - 1 - k)) m

theorem arev_val (i : Fin m) : (arevL (KofC ctrl) (cG G, (x, (D, (h, H)))))[m - 1 - i.val]?.getD 0 =
    revBR (KofC ctrl) (cG G, (x, (D, (h, H)))) ((arevL (KofC ctrl) (cG G, (x, (D, (h, H))))).take (m - 1 - i.val)) i.val := by
  rw [(arevL_spec ctrl G x D h H).2 _ (by omega)]
  congr 1; omega

include hm in
theorem revBR_lt (bs : List ℕ) (i : Fin m) : revBR (KofC ctrl) (cG G, (x, (D, (h, H)))) bs i.val < G.counts i := by
  unfold revBR; exact (argmax_spec G hm _ i).1

noncomputable def arevF : (i : Fin m) → Fin (G.counts i) := fun i =>
  ⟨(arevL (KofC ctrl) (cG G, (x, (D, (h, H)))))[m - 1 - i.val]?.getD 0, by
    rw [arev_val ctrl G x D h H i]; exact revBR_lt ctrl G hm x D h H _ i⟩

theorem profR_len (bs : List ℕ) (i : ℕ) : (profR (KofC ctrl) (cG G, (x, (D, (h, H)))) bs i).length = m := by
  unfold profR; simp [len_G]

theorem profR_rows (i : Fin m) (j : Fin m) (hji : j ≠ i) :
    Xof G (profR (KofC ctrl) (cG G, (x, (D, (h, H))))
      ((arevL (KofC ctrl) (cG G, (x, (D, (h, H))))).take (m - 1 - i.val)) i.val) j =
    (if j < i then rY ctrl.knobs (sOf G x h H gens) (wOf G D) j
      else revSweep (rY ctrl.knobs (sOf G x h H gens) (wOf G D)) (rDelta ctrl.knobs (sOf G x h H gens) (wOf G D))
        (arevF ctrl G hm x D h H) j) := by
  have hL : (cG G, (x, (D, (h, H)))).1.1.length = m := len_G G
  funext a
  unfold Xof profR
  rw [hL, prob_rows _ _ _ _ j.isLt]
  by_cases hlt : j < i
  · rw [if_pos (Fin.lt_iff_val_lt_val.1 hlt), if_pos hlt]
    exact yRow_eq ctrl G hm x D h H gens j a
  · rw [if_neg (fun e => hlt (Fin.lt_iff_val_lt_val.2 e)), if_neg hlt]
    have hgt : i.val < j.val := by
      rcases lt_or_gt_of_ne (fun e : i.val = j.val => hji (Fin.ext e).symm) with h1 | h1
      · exact h1
      · exact absurd (Fin.lt_iff_val_lt_val.2 h1) hlt
    rw [List.getElem?_take_of_lt (by omega)]
    exact revRowA_eq ctrl G hm x D h H gens (arevF ctrl G hm x D h H) j a

include hm in
theorem isRevBR : IsRevBR G.utility (rY ctrl.knobs (sOf G x h H gens) (wOf G D))
    (rDelta ctrl.knobs (sOf G x h H gens) (wOf G D)) (arevF ctrl G hm x D h H) := by
  intro i a
  set bs := (arevL (KofC ctrl) (cG G, (x, (D, (h, H))))).take (m - 1 - i.val)
  set P := profR (KofC ctrl) (cG G, (x, (D, (h, H)))) bs i.val
  have hP : ∀ j, j ≠ i → (fun j => if j < i then rY ctrl.knobs (sOf G x h H gens) (wOf G D) j
      else revSweep (rY ctrl.knobs (sOf G x h H gens) (wOf G D)) (rDelta ctrl.knobs (sOf G x h H gens) (wOf G D))
        (arevF ctrl G hm x D h H) j) j = Xof G P j :=
    fun j hj => (profR_rows ctrl G hm x D h H gens i j hj).symm
  rw [purePayoff_congr G _ _ i hP a, purePayoff_congr G _ _ i hP (arevF ctrl G hm x D h H i)]
  rw [← pureQ_eq G hm P (profR_len ctrl G x D h H bs i.val) i a,
    ← pureQ_eq G hm P (profR_len ctrl G x D h H bs i.val) i (arevF ctrl G hm x D h H i)]
  have hv : (arevF ctrl G hm x D h H i).val = revBR (KofC ctrl) (cG G, (x, (D, (h, H)))) bs i.val :=
    arev_val ctrl G x D h H i
  rw [hv]
  unfold revBR
  exact_mod_cast (argmax_spec G hm P i).2 a

/-! ### the forward sweep -/
theorem xtL_len : (xtL (KofC ctrl) ((cG G, (x, (D, (h, H)))), arevL (KofC ctrl) (cG G, (x, (D, (h, H)))))).length = m := by
  unfold xtL; simp [len_G]

include hm in
theorem xtRow_eq (j : Fin m) (a : Fin (G.counts j)) :
    (gQ (xtRow (KofC ctrl) ((cG G, (x, (D, (h, H)))), arevL (KofC ctrl) (cG G, (x, (D, (h, H))))) j.val) a.val : ℝ) =
      rXt ctrl.knobs (sOf G x h H gens) (wOf G D) (arevF ctrl G hm x D h H) j a := by
  have hL : (cG G, (x, (D, (h, H)))).1.1.length = m := len_G G
  unfold xtRow
  dsimp only
  rw [hL]
  exact revRowA_eq ctrl G hm x D h H gens (arevF ctrl G hm x D h H) j a

include hm in
theorem xtL_eq :
    Xof G (xtL (KofC ctrl) ((cG G, (x, (D, (h, H)))), arevL (KofC ctrl) (cG G, (x, (D, (h, H)))))) =
      rXt ctrl.knobs (sOf G x h H gens) (wOf G D) (arevF ctrl G hm x D h H) := by
  funext j a
  unfold Xof
  rw [show xtL (KofC ctrl) ((cG G, (x, (D, (h, H)))), arevL (KofC ctrl) (cG G, (x, (D, (h, H))))) =
    (List.range m).map (xtRow (KofC ctrl) ((cG G, (x, (D, (h, H)))), arevL (KofC ctrl) (cG G, (x, (D, (h, H)))))) by
      unfold xtL; rw [show (cG G, (x, (D, (h, H)))).1.1.length = m from len_G G]]
  rw [prob_rows _ _ _ _ j.isLt]
  exact xtRow_eq ctrl G hm x D h H gens j a

include hm in
theorem CrawQ_eq : (CrawQ (KofC ctrl) (cG G, (x, (D, (h, H)))) : ℝ) = rCraw ctrl.knobs (sOf G x h H gens) (wOf G D) := by
  unfold CrawQ rCraw
  rw [Rat.cast_mul, K_rho, len_G, prodQ_fin]
  congr 1
  refine Finset.prod_congr rfl (fun i _ => ?_)
  push_cast; rw [K_t, gamQ_eq ctrl G hm x D h H gens i]

include hm in
theorem eQ_eq (hxl : x.length = m) (i : Fin m) :
    (eQ (KofC ctrl) ((cG G, (x, (D, (h, H)))), arevL (KofC ctrl) (cG G, (x, (D, (h, H))))) i.val : ℝ) =
      rE ctrl.knobs G.utility (sOf G x h H gens) (wOf G D) (arevF ctrl G hm x D h H) i := by
  unfold eQ rE corrDef qi
  dsimp only
  have e1 : (((CrawQ (KofC ctrl) (cG G, (x, (D, (h, H)))) * scQ (cG G) x + DshQ (KofC ctrl) H) / ((cG G).1.length : ℚ) -
      (1 - regQ (cG G) (xtL (KofC ctrl) ((cG G, (x, (D, (h, H)))), arevL (KofC ctrl) (cG G, (x, (D, (h, H)))))) i.val) : ℚ) : ℝ) =
      (rCraw ctrl.knobs (sOf G x h H gens) (wOf G D) * scaled G.utility (sOf G x h H gens).x + ctrl.knobs.Dsh (sOf G x h H gens).H) / m -
        (1 - regret G.utility (rXt ctrl.knobs (sOf G x h H gens) (wOf G D) (arevF ctrl G hm x D h H)) i) := by
    push_cast
    rw [CrawQ_eq ctrl G hm x D h H gens, scQ_eq G hm x hxl, K_Dsh, len_G,
      regQ_eq G hm _ (xtL_len ctrl G x D h H) i, xtL_eq ctrl G hm x D h H gens]
    rfl
  rw [← e1]
  generalize ((CrawQ (KofC ctrl) (cG G, (x, (D, (h, H)))) * scQ (cG G) x + DshQ (KofC ctrl) H) / ((cG G).1.length : ℚ) -
      (1 - regQ (cG G) (xtL (KofC ctrl) ((cG G, (x, (D, (h, H)))), arevL (KofC ctrl) (cG G, (x, (D, (h, H)))))) i.val) : ℚ) = v
  split_ifs with hc
  · have : (v : ℝ) ≤ 0 := by exact_mod_cast hc
    push_cast; exact (max_eq_left this).symm
  · have : ¬ (v : ℝ) ≤ 0 := by exact_mod_cast hc
    exact (max_eq_right (le_of_lt (not_le.1 this))).symm

noncomputable abbrev AQ : RA := ((cG G, (x, (D, (h, H)))), arevL (KofC ctrl) (cG G, (x, (D, (h, H)))))

theorem AQ_len : (AQ ctrl G x D h H).1.1.1.length = m := len_G G

include hm in
theorem fwdP_eq (hxl : x.length = m) (i : Fin m) :
    (fwdP (KofC ctrl) (AQ ctrl G x D h H) i.val : ℝ) =
      fwdProb (rE ctrl.knobs G.utility (sOf G x h H gens) (wOf G D) (arevF ctrl G hm x D h H)) i := by
  unfold fwdP fwdProb
  rw [Rat.cast_div, Rat.cast_add, Rat.cast_one, eQ_eq ctrl G hm x D h H gens hxl i, AQ_len, fsum_filter_le]
  congr 2
  exact Finset.sum_congr rfl (fun j _ => eQ_eq ctrl G hm x D h H gens hxl j)

include hm in
theorem fwdRowA_eq (hxl : x.length = m) (ac : (i : Fin m) → Fin (G.counts i)) (j : Fin m) (a : Fin (G.counts j)) :
    (gQ (fwdRowA (KofC ctrl) (AQ ctrl G x D h H) j.val (ac j).val) a.val : ℝ) =
      fwdSweep (rXt ctrl.knobs (sOf G x h H gens) (wOf G D) (arevF ctrl G hm x D h H))
        (rE ctrl.knobs G.utility (sOf G x h H gens) (wOf G D) (arevF ctrl G hm x D h H)) ac j a := by
  unfold fwdRowA fwdSweep
  rw [gQ, row_get G hm j]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, ePure, DGPNash.WellSupported.pureStrategy]
  push_cast
  rw [fwdP_eq ctrl G hm x D h H gens hxl j, xtRow_eq ctrl G hm x D h H gens j a]
  congr 2
  by_cases e : a = ac j
  · subst e; simp
  · rw [if_neg e, if_neg (fun e' => e (Fin.ext e'))]; simp

theorem acorL_spec : (acorL (KofC ctrl) (AQ ctrl G x D h H)).length = m ∧
    ∀ k < m, (acorL (KofC ctrl) (AQ ctrl G x D h H))[k]?.getD 0 =
      fwdBR (KofC ctrl) (AQ ctrl G x D h H) ((acorL (KofC ctrl) (AQ ctrl G x D h H)).take k) k := by
  unfold acorL
  rw [AQ_len]
  exact appFold_spec (fun bs k => fwdBR (KofC ctrl) (AQ ctrl G x D h H) bs k) m

include hm in
theorem fwdBR_lt (bs : List ℕ) (i : Fin m) : fwdBR (KofC ctrl) (AQ ctrl G x D h H) bs i.val < G.counts i := by
  unfold fwdBR; exact (argmax_spec G hm _ i).1

noncomputable def acorF : (i : Fin m) → Fin (G.counts i) := fun i =>
  ⟨(acorL (KofC ctrl) (AQ ctrl G x D h H))[i.val]?.getD 0, by
    rw [(acorL_spec ctrl G x D h H).2 _ i.isLt]; exact fwdBR_lt ctrl G hm x D h H _ i⟩

theorem profF_len (bs : List ℕ) (i : ℕ) : (profF (KofC ctrl) (AQ ctrl G x D h H) bs i).length = m := by
  unfold profF; simp [len_G]

theorem profF_rows (hxl : x.length = m) (i : Fin m) (j : Fin m) (hji : j ≠ i) :
    Xof G (profF (KofC ctrl) (AQ ctrl G x D h H) ((acorL (KofC ctrl) (AQ ctrl G x D h H)).take i.val) i.val) j =
    (if j < i then fwdSweep (rXt ctrl.knobs (sOf G x h H gens) (wOf G D) (arevF ctrl G hm x D h H))
        (rE ctrl.knobs G.utility (sOf G x h H gens) (wOf G D) (arevF ctrl G hm x D h H)) (acorF ctrl G hm x D h H) j
      else rXt ctrl.knobs (sOf G x h H gens) (wOf G D) (arevF ctrl G hm x D h H) j) := by
  funext a
  unfold Xof profF
  rw [AQ_len, prob_rows _ _ _ _ j.isLt]
  by_cases hlt : j < i
  · rw [if_pos (Fin.lt_iff_val_lt_val.1 hlt), if_pos hlt]
    rw [List.getElem?_take_of_lt (Fin.lt_iff_val_lt_val.1 hlt)]
    exact fwdRowA_eq ctrl G hm x D h H gens hxl (acorF ctrl G hm x D h H) j a
  · rw [if_neg (fun e => hlt (Fin.lt_iff_val_lt_val.2 e)), if_neg hlt]
    exact xtRow_eq ctrl G hm x D h H gens j a

include hm in
theorem isFwdBR (hxl : x.length = m) :
    IsFwdBR G.utility (rXt ctrl.knobs (sOf G x h H gens) (wOf G D) (arevF ctrl G hm x D h H))
      (rE ctrl.knobs G.utility (sOf G x h H gens) (wOf G D) (arevF ctrl G hm x D h H)) (acorF ctrl G hm x D h H) := by
  intro i a
  set bs := (acorL (KofC ctrl) (AQ ctrl G x D h H)).take i.val
  set P := profF (KofC ctrl) (AQ ctrl G x D h H) bs i.val
  have hP : ∀ j, j ≠ i → (fun j => if j < i then fwdSweep (rXt ctrl.knobs (sOf G x h H gens) (wOf G D) (arevF ctrl G hm x D h H))
        (rE ctrl.knobs G.utility (sOf G x h H gens) (wOf G D) (arevF ctrl G hm x D h H)) (acorF ctrl G hm x D h H) j
      else rXt ctrl.knobs (sOf G x h H gens) (wOf G D) (arevF ctrl G hm x D h H) j) j = Xof G P j :=
    fun j hj => (profF_rows ctrl G hm x D h H gens hxl i j hj).symm
  rw [purePayoff_congr G _ _ i hP a, purePayoff_congr G _ _ i hP (acorF ctrl G hm x D h H i)]
  rw [← pureQ_eq G hm P (profF_len ctrl G x D h H bs i.val) i a,
    ← pureQ_eq G hm P (profF_len ctrl G x D h H bs i.val) i (acorF ctrl G hm x D h H i)]
  have hv : (acorF ctrl G hm x D h H i).val = fwdBR (KofC ctrl) (AQ ctrl G x D h H) bs i.val :=
    (acorL_spec ctrl G x D h H).2 _ i.isLt
  rw [hv]
  unfold fwdBR
  exact_mod_cast (argmax_spec G hm P i).2 a

end rev2

/-! ### the repair step -/
include hm in
theorem rep_ok (x : List (List ℚ)) (hxl : x.length = m) (h : List ℚ) (H : ℚ) (s : State G.counts)
    (hx : s.x = Xof G x) (hh : s.h = fun i => (gQ h i.val : ℝ)) (hH : s.H = H) (hpass : ¬ Passes ctrl G.utility s) :
    ∃ s', RepairStep ctrl G.utility s s' ∧
      (repST (KofC ctrl) (cG G, (x, (h, H)))).1 = cG G ∧
      (repST (KofC ctrl) (cG G, (x, (h, H)))).2.1.length = m ∧
      s'.x = Xof G (repST (KofC ctrl) (cG G, (x, (h, H)))).2.1 ∧
      s'.h = (fun i => (gQ (repST (KofC ctrl) (cG G, (x, (h, H)))).2.2.1 i.val : ℝ)) ∧
      s'.H = (repST (KofC ctrl) (cG G, (x, (h, H)))).2.2.2 := by
  set D := DQ (KofC ctrl) (cG G, (x, (h, H))) with hD
  have hlp := lp_at ctrl G hm x hxl (cG G, (x, (h, H))) rfl
  obtain ⟨sx, sh, sH, sg⟩ := s
  simp only at hx hh hH
  subst hx hh hH
  have hs : (⟨Xof G x, fun i => (gQ h i.val : ℝ), (H : ℝ), sg⟩ : State G.counts) = sOf G x h H sg := rfl
  rw [hs] at hpass ⊢
  have hA : AofS (KofC ctrl) (cG G, (x, (h, H))) = AQ ctrl G x D h H := by unfold AofS RofS; rfl
  have hR : RofS (KofC ctrl) (cG G, (x, (h, H))) = (cG G, (x, (D, (h, H)))) := by unfold RofS; rfl
  refine ⟨repairState ctrl.knobs G.utility (sOf G x h H sg) (wOf G D) (arevF ctrl G hm x D h H) (acorF ctrl G hm x D h H),
    ⟨hpass, wOf G D, _, arevF ctrl G hm x D h H, acorF ctrl G hm x D h H, hlp.2.1, fun i a => ⟨_, rfl⟩,
      isRevBR ctrl G hm x D h H sg, isFwdBR ctrl G hm x D h H sg hxl, rfl⟩, ?_, ?_, ?_, ?_, ?_⟩
  · unfold repST; rfl
  · unfold repST; simp [len_G]
  · unfold repST repairState
    dsimp only
    rw [hA, len_G]
    funext j a
    unfold Xof
    rw [prob_rows _ _ _ _ j.isLt]
    exact (fwdRowA_eq ctrl G hm x D h H sg hxl (acorF ctrl G hm x D h H) j a).symm
  · unfold repST repairState
    dsimp only
    rw [hR, len_G]
    funext i
    rw [gQ_range _ _ _ i.isLt]
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    push_cast
    rw [K_c, K_t, gamQ_eq ctrl G hm x D h H sg i]; rfl
  · unfold repST repairState
    dsimp only
    push_cast; rw [K_c, K_t]; rfl

/-! ### one iteration -/
include hm in
theorem iter_ok (x : List (List ℚ)) (hxl : x.length = m) (h : List ℚ) (H : ℚ) (s : State G.counts)
    (hx : s.x = Xof G x) (hh : s.h = fun i => (gQ h i.val : ℝ)) (hH : s.H = H) :
    (Terminal σ G.utility s → iterQ (KofC ctrl) (cG G, (x, (h, H))) = (cG G, (x, (h, H)))) ∧
    (¬ Terminal σ G.utility s → ∃ s', Step ctrl G.utility s s' ∧
      (iterQ (KofC ctrl) (cG G, (x, (h, H)))).1 = cG G ∧
      (iterQ (KofC ctrl) (cG G, (x, (h, H)))).2.1.length = m ∧
      s'.x = Xof G (iterQ (KofC ctrl) (cG G, (x, (h, H)))).2.1 ∧
      s'.h = (fun i => (gQ (iterQ (KofC ctrl) (cG G, (x, (h, H)))).2.2.1 i.val : ℝ)) ∧
      s'.H = (iterQ (KofC ctrl) (cG G, (x, (h, H)))).2.2.2) := by
  have hterm : Terminal σ G.utility s ↔ (KofC ctrl).σ ≤ scQ (cG G) x := by
    unfold Terminal
    rw [hx, ← scQ_eq G hm x hxl, ← K_sigma ctrl]
    exact Rat.cast_le
  constructor
  · intro ht
    unfold iterQ; rw [if_pos (hterm.1 ht)]
  · intro ht
    have e1 : iterQ (KofC ctrl) (cG G, (x, (h, H))) =
        if gQ (DQ (KofC ctrl) (cG G, (x, (h, H)))) (NPc (cG G)) ≤
          RegQ (cG G) x - (KofC ctrl).η * muQ (KofC ctrl) (cG G) x H / ((cG G).1.length : ℚ)
        then descST (KofC ctrl) (cG G, (x, (h, H))) else repST (KofC ctrl) (cG G, (x, (h, H))) := by
      unfold iterQ; rw [if_neg (fun h' => ht (hterm.2 h'))]
    rw [e1]
    by_cases hp : Passes ctrl G.utility s
    · rw [if_pos ((passes_iff ctrl G hm x hxl h H s hx hH).1 hp)]
      obtain ⟨s', hst, r⟩ := desc_ok ctrl G hm x hxl h H s hx hh hH hp
      exact ⟨s', ⟨ht, Or.inl hst⟩, r⟩
    · rw [if_neg (fun h' => hp ((passes_iff ctrl G hm x hxl h H s hx hH).2 h'))]
      obtain ⟨s', hst, r⟩ := rep_ok ctrl G hm x hxl h H s hx hh hH hp
      exact ⟨s', ⟨ht, Or.inr hst⟩, r⟩

/-! ### row shapes -/
include hm in
theorem shape_range (g : ℕ → ℕ → ℚ) :
    ((List.range m).map (fun j => (rng (cG G) (nOf (cG G) j)).map (g j))).map List.length = G.sizes := by
  apply List.ext_getElem
  · simp [G.sizes_length]
  · intro i h1 h2
    have hi : i < m := by rw [← G.sizes_length]; exact h2
    simp only [List.getElem_map, List.getElem_range, List.length_map]
    rw [rng_G G hm ⟨i, hi⟩]
    simp [Table.counts, List.getElem?_eq_getElem h2]

include hm in
theorem iter_shape (x : List (List ℚ)) (h : List ℚ) (H : ℚ) (hsh : x.map List.length = G.sizes) :
    (iterQ (KofC ctrl) (cG G, (x, (h, H)))).2.1.map List.length = G.sizes := by
  unfold iterQ
  split_ifs
  · exact hsh
  · unfold descST; dsimp only; rw [len_G]; unfold descRow
    exact shape_range G hm _
  · unfold repST; dsimp only; rw [len_G]; unfold fwdRowA
    rw [show (AofS (KofC ctrl) (cG G, (x, (h, H)))).1.1 = cG G by unfold AofS RofS; rfl]
    exact shape_range G hm _

/-! ### runs -/
include hm in
theorem run_ok (x0 : List (List ℚ)) (hxl0 : x0.length = m) (s0 : State G.counts) (hinit : Init G.utility s0)
    (hx0 : s0.x = Xof G x0) : ∀ N : ℕ, ∃ (k : ℕ) (s : State G.counts) (x : List (List ℚ)) (h : List ℚ) (H : ℚ),
      (iterQ (KofC ctrl))^[N] (cG G, (x0, ([], 0))) = (cG G, (x, (h, H))) ∧ x.length = m ∧
      Reach ctrl G.utility k s ∧ s.x = Xof G x ∧ s.h = (fun i => (gQ h i.val : ℝ)) ∧ s.H = H ∧
      (Terminal σ G.utility s ∨ k = N)
  | 0 => by
    refine ⟨0, s0, x0, [], 0, rfl, hxl0, Reach.init hinit, hx0, ?_, ?_, Or.inr rfl⟩
    · rw [hinit.2.2.2.1]; funext i; simp [gQ]
    · rw [hinit.2.2.2.2.1]; simp
  | N + 1 => by
    obtain ⟨k, s, x, h, H, hS, hxl, hr, hx, hh, hH, ht⟩ := run_ok x0 hxl0 s0 hinit hx0 N
    rw [Function.iterate_succ_apply', hS]
    have hio := iter_ok ctrl G hm x hxl h H s hx hh hH
    by_cases hT : Terminal σ G.utility s
    · rw [hio.1 hT]
      exact ⟨k, s, x, h, H, rfl, hxl, hr, hx, hh, hH, Or.inl hT⟩
    · have hk : k = N := ht.resolve_left hT
      obtain ⟨s', hst, e1, e2, e3, e4, e5⟩ := hio.2 hT
      generalize iterQ (KofC ctrl) (cG G, (x, (h, H))) = T at e1 e2 e3 e4 e5 ⊢
      obtain ⟨c', x', h', H'⟩ := T
      simp only at e1 e2 e3 e4 e5; subst e1
      exact ⟨k + 1, s', x', h', H', rfl, e2, Reach.step hr hst, e3, e4, e5, Or.inr (by omega)⟩

end G

end MNRAlg

-- ===== R46H =====

namespace MNRAlg
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open NashAmplification.Filtering MNRL22 MNRRam MNRLP MultiNashRepair

theorem poly_iterate {α : Type} [Coding α] {f : α → α} (hf : Poly f) : ∀ n : ℕ, Poly (f^[n])
  | 0 => by rw [Function.iterate_zero]; exact Poly.identity
  | n + 1 => by
    rw [Function.iterate_succ']
    exact Poly.comp (f := f) hf (poly_iterate hf n)

/-- the rows output by the algorithm -/
noncomputable def finRows (K : KQ) (N m0 : ℕ) (c : Ctx) : List (List ℚ) :=
  if c.1.length < m0 then xFinal c else ((iterQ K)^[N] (c, (xFinal c, ([], 0)))).2.1

theorem poly_finRows (K : KQ) (N m0 : ℕ) : Poly (finRows K N m0) := by
  have hI : Poly ((iterQ K)^[N]) := poly_iterate (poly_iterQ K) N
  have hS : Poly (fun c : Ctx => (c, (xFinal c, (([] : List ℚ), (0 : ℚ))))) := by
    have := poly_xFinal; fun_prop
  have h1 : Poly (fun c : Ctx => ((iterQ K)^[N] (c, (xFinal c, ([], 0))))) := Poly.comp hI hS
  have h2 : Poly (fun c : Ctx => ((iterQ K)^[N] (c, (xFinal c, ([], 0)))).2.1) :=
    Poly.comp Poly.fst (Poly.comp Poly.snd h1)
  unfold finRows
  have := poly_xFinal
  fun_prop

noncomputable def outItems2 (K : KQ) (N m0 : ℕ) (c : Ctx) : List (List ℕ) :=
  c.1.map (fun n => [n]) ++ ((finRows K N m0 c).flatten).map (fun q => [q.num.natAbs, q.den, 0])
noncomputable def Falg2 (K : KQ) (N m0 : ℕ) (items : List (List ℕ)) : List (List ℕ) :=
  outItems2 K N m0 (ctxOf items)

theorem poly_Falg2 (K : KQ) (N m0 : ℕ) : Poly (Falg2 K N m0) := by
  have h := poly_finRows K N m0
  have h2 : Poly (outItems2 K N m0) := by unfold outItems2; fun_prop
  exact Poly.comp (f := outItems2 K N m0) h2 poly_ctxOf

theorem Falg2_itemsOf {m : ℕ} (K : KQ) (N m0 : ℕ) (G : Table m) :
    Falg2 K N m0 (itemsOf G) = outItems2 K N m0 (cG G) := by
  unfold Falg2; rw [ctxOf_itemsOf]; rfl

section G
variable {m : ℕ} (G : Table m) (hm : 1 ≤ m)

noncomputable def rawOf (rows : List (List ℚ)) (hsh : rows.map List.length = G.sizes) : RawProfile m where
  sizes := G.sizes
  sizes_length := G.sizes_length
  sizes_pos := G.sizes_pos
  entries := rows.flatten.map toRaw
  entries_length := by rw [List.length_map, List.length_flatten, hsh]

theorem rawOf_on (rows : List (List ℚ)) (hsh : rows.map List.length = G.sizes)
    (hnn : ∀ (j : Fin m) (a : Fin (G.counts j)), 0 ≤ prob rows j a) :
    (rawOf G rows hsh).on G.counts = Xof G rows := by
  funext i a
  have hrl : rows.length = m := by rw [← List.length_map (f := List.length), hsh, G.sizes_length]
  have him : i.val < rows.length := by rw [hrl]; exact i.isLt
  have hlen : a.val < (rows[i.val]).length := by
    have := congrArg (fun L => L[i.val]?) hsh
    simp only [List.getElem?_map, List.getElem?_eq_getElem him, Option.map_some] at this
    have h2 : i.val < G.sizes.length := by rw [G.sizes_length]; exact i.isLt
    rw [List.getElem?_eq_getElem h2] at this
    have h3 := Option.some.inj this
    rw [h3]
    have := a.isLt
    simpa [Table.counts, List.getElem?_eq_getElem h2] using this
  have hidx : (G.sizes.take i.val).sum = ((rows.take i.val).map List.length).sum := by
    rw [← hsh, List.map_take]
  have hf := flatten_getElem? rows i.val a.val him hlen
  rw [← hidx] at hf
  have hget : (rows[i.val])[a.val]? = some (prob rows i.val a.val) := by
    unfold prob
    rw [List.getElem?_eq_getElem him, Option.getD_some, List.getElem?_eq_getElem hlen, Option.getD_some]
  simp only [RawProfile.on, RawProfile.at, rawOf, List.getD_eq_getElem?_getD, List.getElem?_map, hf,
    hget, Option.map_some, Option.getD_some]
  rw [toRaw_value _ (hnn i a)]
  rfl

theorem pack_eq2 (K : KQ) (N m0 : ℕ) (hsh : (finRows K N m0 (cG G)).map List.length = G.sizes) :
    packItems (outItems2 K N m0 (cG G)) = encProfile (rawOf G (finRows K N m0 (cG G)) hsh) := by
  simp only [packItems, outItems2, encProfile, pack, rawOf, cG, List.flatMap_append, List.flatMap_map]
  congr 1
  · refine List.flatMap_congr (fun n _ => ?_)
    simp
  · refine List.flatMap_congr (fun q _ => ?_)
    simp [encRaw, pack, toRaw, encNat_zero, List.intercalate_cons_cons]

include hm in
theorem xFinal_Xof : Xof G (xFinal (cG G)) = Xr (bF G hm) m := by
  funext j a
  unfold Xof xFinal
  rw [len_G, prob_rows _ _ _ _ j.isLt, mixRow_get G hm j]
  simp [Xr, j.isLt, bF]

include hm in
theorem scaled_ge (x : Mixed G.counts) (hx : DGPNash.WellSupported.IsEpsApproxNash G.utility x (1 - 1 / (m : ℝ))) :
    1 ≤ scaled G.utility x := by
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have hR : Reg G.utility x ≤ 1 - 1 / (m : ℝ) := by
    refine ciSup_le (fun i => ?_)
    haveI : Nonempty (Fin (G.counts i)) := ⟨⟨0, counts_pos G i⟩⟩
    refine ciSup_le (fun a => ?_)
    unfold gain DGPNash.NashMap.purePayoff
    have := hx.2 i (fun k => if k = a then 1 else 0) (dlt_lottery a)
    linarith
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  unfold scaled q
  have : (m : ℝ) * (1 / m) = 1 := by field_simp
  nlinarith

theorem iterQ_fst (K : KQ) (S : ST) : (iterQ K S).1 = S.1 := by
  unfold iterQ; split_ifs
  · rfl
  · unfold descST; rfl
  · unfold repST; rfl

include hm in
theorem iterate_shape {σ : ℚ} (ctrl : Controls σ) (x : List (List ℚ)) (hsh : x.map List.length = G.sizes) (h : List ℚ) (H : ℚ) :
    ∀ N : ℕ, ∃ x' h' H', (iterQ (KofC ctrl))^[N] (cG G, (x, (h, H))) = (cG G, (x', (h', H'))) ∧
      x'.map List.length = G.sizes
  | 0 => ⟨x, h, H, rfl, hsh⟩
  | N + 1 => by
    obtain ⟨x', h', H', e, hs⟩ := iterate_shape ctrl x hsh h H N
    rw [Function.iterate_succ_apply', e]
    have hf := iterQ_fst (KofC ctrl) (cG G, (x', (h', H')))
    have hsh' := iter_shape ctrl G hm x' h' H' hs
    generalize iterQ (KofC ctrl) (cG G, (x', (h', H'))) = T at hf hsh' ⊢
    obtain ⟨c', x'', h'', H''⟩ := T
    simp only at hf hsh'; subst hf
    exact ⟨x'', h'', H'', rfl, hsh'⟩

include hm in
theorem sem_ok {σ : ℚ} (ctrl : Controls σ) (N0 : ℕ)
    (hN0 : ∀ (k : ℕ) (s : State G.counts), ctrl.m0 ≤ m → Reach ctrl G.utility k s → k ≤ N0) :
    (∀ (j : Fin m) (a : Fin (G.counts j)), 0 ≤ prob (finRows (KofC ctrl) (N0 + 1) ctrl.m0 (cG G)) j a) ∧
      IDRHOutput ctrl G.utility (Xof G (finRows (KofC ctrl) (N0 + 1) ctrl.m0 (cG G))) := by
  have hd := hdrs G.utility (bounded_G G) (counts_pos G) hm (bF G hm) (fun R cc => hbr_G G hm R cc)
  rw [← xFinal_Xof G hm] at hd
  by_cases hlt : m < ctrl.m0
  · have e : finRows (KofC ctrl) (N0 + 1) ctrl.m0 (cG G) = xFinal (cG G) := by
      unfold finRows; rw [len_G, if_pos hlt]
    rw [e]
    refine ⟨fun j a => ?_, Or.inl ⟨hlt, hd.1, fun i a => ⟨_, rfl⟩, scaled_ge G hm _ hd⟩⟩
    have := (hd.1 j).1 a
    unfold Xof at this; exact_mod_cast this
  · have hge : ctrl.m0 ≤ m := by omega
    have hxl0 : (xFinal (cG G)).length = m := by simp [xFinal, len_G]
    let s0 : State G.counts := ⟨Xof G (xFinal (cG G)), 0, 0, []⟩
    have hinit : Init G.utility s0 := ⟨hd.1, fun i a => ⟨_, rfl⟩, scaled_ge G hm _ hd, rfl, rfl, rfl⟩
    obtain ⟨k, s, x, h, H, heq, hxl, hr, hx, hh, hH, ht⟩ :=
      run_ok ctrl G hm (xFinal (cG G)) hxl0 s0 hinit rfl (N0 + 1)
    have hk := hN0 k s hge hr
    have hT : Terminal σ G.utility s := ht.resolve_right (by omega)
    have e : finRows (KofC ctrl) (N0 + 1) ctrl.m0 (cG G) = x := by
      unfold finRows; rw [len_G, if_neg hlt, heq]
    rw [e]
    have hmix : AGT.IsMixedProfile s.x := (lemma_5_12 ctrl hge (counts_pos G) G.utility (bounded_G G) hr).1.1
    refine ⟨fun j a => ?_, Or.inr ⟨hge, k, s, hr, hT, hx⟩⟩
    have := (hmix j).1 a
    rw [hx] at this
    unfold Xof at this; exact_mod_cast this

end G

open OAI.MetricKMedian.Binary in
theorem machine_main (σ : ℚ) (hσ1 : 1 < σ) (hσ2 : (σ : ℝ) < sigmaStar) (ctrl : Controls σ) :
    ∃ (M : Turing.TM2ComputableAux OnlineCRS.Combine.Sym OnlineCRS.Combine.Sym) (c : ℕ), ∀ m : ℕ, 1 ≤ m → ∀ G : Table m,
      ∃ x : RawProfile m, x.sizes = G.sizes ∧
        CFLOutliers.OutputsWithin M (encGame G) (encProfile x) (c * ((encGame G).length + 2) ^ c) ∧
        IDRHOutput ctrl G.utility (x.on G.counts) := by
  obtain ⟨N0, hN0⟩ := proposition_4_6_iterations σ hσ1 hσ2 ctrl
  let Pin : PolyProgram (fun a : (Σ k, Table k) => MNRBridge.symBits (encGame a.2))
      (Automatic.enc : List (List ℕ) → List Bool) (fun a => itemsOf a.2) :=
    Tin.program.of_word (fun a => by
      show Tin.run none (MNRBridge.symBits (encGame a.2)) = _
      rw [Tin_run, encGame_hIn])
  let Pcore : PolyProgram (Automatic.enc : List (List ℕ) → List Bool)
      (Automatic.enc : List (List ℕ) → List Bool) (Falg2 (KofC ctrl) (N0 + 1) ctrl.m0) :=
    (poly_Falg2 (KofC ctrl) (N0 + 1) ctrl.m0).program
  let Pout : PolyProgram (Automatic.enc : List (List ℕ) → List Bool)
      (fun items => MNRBridge.symBits (packItems items)) id :=
    Tout.program.of_word (fun items => by
      show Tout.run (false, false, false) _ = _
      rw [Tout_items]; rfl)
  obtain ⟨M, c, hM⟩ := MNRBridge.bridge (ea := fun a : (Σ k, Table k) => encGame a.2) (eb := packItems)
    ((Pin.comp Pcore).comp Pout)
  refine ⟨M, c, fun m hm G => ?_⟩
  have hsh : (finRows (KofC ctrl) (N0 + 1) ctrl.m0 (cG G)).map List.length = G.sizes := by
    unfold finRows; rw [len_G]; split_ifs
    · exact xFinal_rows G hm
    · obtain ⟨x', h', H', e, hs⟩ := iterate_shape G hm ctrl (xFinal (cG G)) (xFinal_rows G hm) [] 0 (N0 + 1)
      rw [e]; exact hs
  obtain ⟨hnn, hout⟩ := sem_ok G hm ctrl N0
    (fun k s hge hr => hN0 m G.counts G.utility hge (counts_pos G) (bounded_G G) k s hr)
  refine ⟨rawOf G _ hsh, rfl, ?_, ?_⟩
  · have h := hM ⟨m, G⟩
    have e : (id ∘ (Falg2 (KofC ctrl) (N0 + 1) ctrl.m0 ∘ fun a : (Σ k, Table k) => itemsOf a.2)) ⟨m, G⟩ =
        outItems2 (KofC ctrl) (N0 + 1) ctrl.m0 (cG G) := by
      show Falg2 _ _ _ (itemsOf G) = _
      exact Falg2_itemsOf _ _ _ G
    rw [e, pack_eq2 G (KofC ctrl) (N0 + 1) ctrl.m0 hsh] at h
    exact h
  · rw [rawOf_on G _ hsh hnn]
    exact hout

end MNRAlg

open OnlineCRS.Combine (Sym)
open NashAmplification.Filtering (Table RawProfile encGame encProfile)
open MultiNashRepair

theorem solution (σ : ℚ) (hσ1 : 1 < σ) (hσ2 : (σ : ℝ) < sigmaStar)
    (ctrl : Controls σ) :
    ∃ (M : Turing.TM2ComputableAux Sym Sym) (c : ℕ), ∀ m : ℕ, 1 ≤ m → ∀ G : Table m,
      ∃ x : RawProfile m, x.sizes = G.sizes ∧
        CFLOutliers.OutputsWithin M (encGame G) (encProfile x) (c * ((encGame G).length + 2) ^ c) ∧
        IDRHOutput ctrl G.utility (x.on G.counts) :=
  MNRAlg.machine_main σ hσ1 hσ2 ctrl
