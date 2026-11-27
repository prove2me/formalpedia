-- Prove2me | solution 1 for MultiNashRepair.lemma_2_2
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T03:08:26.120802+00:00
-- url     : https://prove2.me/submissions/00a5a0ad-8f0d-4436-aa5c-a6bd70a6fc01

import Mathlib
import Definitions.Def_QuantumMaxCutFiniteNumericRuntime
import Definitions.Def_CFLOutliers_OutputsWithin
import Definitions.Def_NashAmplification_Filtering_Encoding
import Definitions.Def_DGPNash_WellSupported_Equilibria


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

open OnlineCRS.Combine (Sym)
open NashAmplification.Filtering (Table RawProfile encGame encProfile)

theorem solution :
    ∃ (M : Turing.TM2ComputableAux Sym Sym) (c : ℕ),
      ∀ m : ℕ, 1 ≤ m → ∀ G : Table m,
        ∃ x : RawProfile m, x.sizes = G.sizes ∧
          CFLOutliers.OutputsWithin M (encGame G) (encProfile x) (c * ((encGame G).length + 2) ^ c) ∧
          DGPNash.WellSupported.IsEpsApproxNash G.utility (x.on G.counts)
            (1 - 1 / (m : ℝ)) :=
  MNRL22.lemma22_main
