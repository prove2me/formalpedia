-- Prove2me | solution 1 for MultiNashRepair.lemma_2_1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T03:47:55.460441+00:00
-- url     : https://prove2.me/submissions/ee7821c2-3fe6-4f2f-877c-33bd54650492

import Mathlib
import Definitions.Def_QuantumMaxCutFiniteNumericRuntime
import Definitions.Def_CFLOutliers_OutputsWithin
import Definitions.Def_NashAmplification_Filtering_Encoding
import Definitions.Def_DGPNash_WellSupported_Equilibria
import Definitions.Def_MultiNashRepair_PolyANE


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


namespace MNRCombo
open OAI.MetricKMedian.Binary Turing MNRBridge

inductive XC | inp | out | bak | t1 | t2 | t3 deriving DecidableEq
instance : Fintype XC := ⟨{.inp, .out, .bak, .t1, .t2, .t3}, by intro x; cases x <;> simp⟩
inductive PC | a1 | a2 | a3 | a4 | a5 | a6 | a7 | a8 | a9 | a10 | a11 deriving DecidableEq
instance : Fintype PC := ⟨{.a1, .a2, .a3, .a4, .a5, .a6, .a7, .a8, .a9, .a10, .a11}, by
  intro x; cases x <;> simp⟩

variable (M : TM2ComputableAux Sym Sym) (B1 B2 : Machine)

abbrev CK := M.tm.K ⊕ (B1.K ⊕ (B2.K ⊕ XC))
abbrev CΓ : CK M B1 B2 → Type
  | .inl k => M.tm.Γ k
  | .inr _ => Sym
abbrev CL := M.tm.Λ ⊕ (B1.Label ⊕ (B2.Label ⊕ PC))
abbrev CS := M.tm.σ × (B1.State × (B2.State × Aux))

abbrev CStmt := TM2.Stmt (CΓ M B1 B2) (CL M B1 B2) (CS M B1 B2)
abbrev CCfg := TM2.Cfg (CΓ M B1 B2) (CL M B1 B2) (CS M B1 B2)

abbrev sk (x : XC) : CK M B1 B2 := .inr (.inr (.inr x))
abbrev pl (p : PC) : CL M B1 B2 := .inr (.inr (.inr p))

def mapM : TM2.Stmt M.tm.Γ M.tm.Λ M.tm.σ → CStmt M B1 B2
  | .push k f q => .push (.inl k) (fun v => f v.1) (mapM q)
  | .peek k f q => .peek (.inl k) (fun v o => (f v.1 o, v.2)) (mapM q)
  | .pop k f q => .pop (.inl k) (fun v o => (f v.1 o, v.2)) (mapM q)
  | .load a q => .load (fun v => (a v.1, v.2)) (mapM q)
  | .branch f q₁ q₂ => .branch (fun v => f v.1) (mapM q₁) (mapM q₂)
  | .goto f => .goto (fun v => .inl (f v.1))
  | .halt => .goto (fun _ => pl M B1 B2 .a6)

def mapB1 : TM2.Stmt (fun _ : B1.K => Bool) B1.Label B1.State → CStmt M B1 B2
  | .push k f q => .push (.inr (.inl k)) (fun v => bitS (f v.2.1)) (mapB1 q)
  | .peek k f q => .peek (.inr (.inl k)) (fun v o => (v.1, (f v.2.1 (o.map decS), v.2.2))) (mapB1 q)
  | .pop k f q => .pop (.inr (.inl k)) (fun v o => (v.1, (f v.2.1 (o.map decS), v.2.2))) (mapB1 q)
  | .load a q => .load (fun v => (v.1, (a v.2.1, v.2.2))) (mapB1 q)
  | .branch f q₁ q₂ => .branch (fun v => f v.2.1) (mapB1 q₁) (mapB1 q₂)
  | .goto f => .goto (fun v => .inr (.inl (f v.2.1)))
  | .halt => .goto (fun _ => pl M B1 B2 .a4)

def mapB2 : TM2.Stmt (fun _ : B2.K => Bool) B2.Label B2.State → CStmt M B1 B2
  | .push k f q => .push (.inr (.inr (.inl k))) (fun v => bitS (f v.2.2.1)) (mapB2 q)
  | .peek k f q => .peek (.inr (.inr (.inl k))) (fun v o => (v.1, (v.2.1, (f v.2.2.1 (o.map decS), v.2.2.2)))) (mapB2 q)
  | .pop k f q => .pop (.inr (.inr (.inl k))) (fun v o => (v.1, (v.2.1, (f v.2.2.1 (o.map decS), v.2.2.2)))) (mapB2 q)
  | .load a q => .load (fun v => (v.1, (v.2.1, (a v.2.2.1, v.2.2.2)))) (mapB2 q)
  | .branch f q₁ q₂ => .branch (fun v => f v.2.2.1) (mapB2 q₁) (mapB2 q₂)
  | .goto f => .goto (fun v => .inr (.inr (.inl (f v.2.2.1))))
  | .halt => .goto (fun _ => pl M B1 B2 .a10)

def setA (v : CS M B1 B2) (o : Option Sym) : CS M B1 B2 := (v.1, (v.2.1, (v.2.2.1, (o, v.2.2.2.2))))
def setB (v : CS M B1 B2) (o : Option Sym) : CS M B1 B2 := (v.1, (v.2.1, (v.2.2.1, (v.2.2.2.1, o))))
def getA (v : CS M B1 B2) : Option Sym := v.2.2.2.1
def getB (v : CS M B1 B2) : Option Sym := v.2.2.2.2

def code : CL M B1 B2 → CStmt M B1 B2
  | .inl l => mapM M B1 B2 (M.tm.m l)
  | .inr (.inl l) => mapB1 M B1 B2 (B1.code l)
  | .inr (.inr (.inl l)) => mapB2 M B1 B2 (B2.code l)
  | .inr (.inr (.inr .a1)) => .pop (sk M B1 B2 .inp) (setA M B1 B2)
      (.branch (fun v => (getA M B1 B2 v).isSome)
        (.push (sk M B1 B2 .t1) (fun v => (getA M B1 B2 v).getD 0)
          (.push (sk M B1 B2 .t2) (fun v => bitS (hiS ((getA M B1 B2 v).getD 0)))
            (.push (sk M B1 B2 .t2) (fun v => bitS (loS ((getA M B1 B2 v).getD 0)))
              (.goto (fun _ => pl M B1 B2 .a1)))))
        (.goto (fun _ => pl M B1 B2 .a2)))
  | .inr (.inr (.inr .a2)) => .pop (sk M B1 B2 .t1) (setA M B1 B2)
      (.branch (fun v => (getA M B1 B2 v).isSome)
        (.push (sk M B1 B2 .bak) (fun v => (getA M B1 B2 v).getD 0) (.goto (fun _ => pl M B1 B2 .a2)))
        (.goto (fun _ => pl M B1 B2 .a3)))
  | .inr (.inr (.inr .a3)) => .pop (sk M B1 B2 .t2) (setA M B1 B2)
      (.branch (fun v => (getA M B1 B2 v).isSome)
        (.push (.inr (.inl B1.input)) (fun v => (getA M B1 B2 v).getD 0) (.goto (fun _ => pl M B1 B2 .a3)))
        (.goto (fun _ => .inr (.inl B1.main))))
  | .inr (.inr (.inr .a4)) => .pop (.inr (.inl B1.output)) (setA M B1 B2)
      (.pop (.inr (.inl B1.output)) (setB M B1 B2)
        (.branch (fun v => (getA M B1 B2 v).isSome)
          (.push (sk M B1 B2 .t3) (fun v => combine (getA M B1 B2 v) (getB M B1 B2 v))
            (.goto (fun _ => pl M B1 B2 .a4)))
          (.goto (fun _ => pl M B1 B2 .a5))))
  | .inr (.inr (.inr .a5)) => .pop (sk M B1 B2 .t3) (setA M B1 B2)
      (.branch (fun v => (getA M B1 B2 v).isSome)
        (.push (.inl M.tm.k₀) (fun v => M.inputAlphabet.symm ((getA M B1 B2 v).getD 0))
          (.goto (fun _ => pl M B1 B2 .a5)))
        (.goto (fun _ => .inl M.tm.main)))
  | .inr (.inr (.inr .a6)) => .pop (.inl M.tm.k₁) (fun v o => setA M B1 B2 v (o.map M.outputAlphabet))
      (.branch (fun v => (getA M B1 B2 v).isSome)
        (.push (sk M B1 B2 .t1) (fun v => (getA M B1 B2 v).getD 0) (.goto (fun _ => pl M B1 B2 .a6)))
        (.goto (fun _ => pl M B1 B2 .a7)))
  | .inr (.inr (.inr .a7)) => .pop (sk M B1 B2 .bak) (setA M B1 B2)
      (.branch (fun v => (getA M B1 B2 v).isSome)
        (.push (sk M B1 B2 .t3) (fun v => (getA M B1 B2 v).getD 0) (.goto (fun _ => pl M B1 B2 .a7)))
        (.goto (fun _ => pl M B1 B2 .a8)))
  | .inr (.inr (.inr .a8)) => .pop (sk M B1 B2 .t1) (setA M B1 B2)
      (.branch (fun v => (getA M B1 B2 v).isSome)
        (.push (.inr (.inr (.inl B2.input))) (fun v => bitS (loS ((getA M B1 B2 v).getD 0)))
          (.push (.inr (.inr (.inl B2.input))) (fun v => bitS (hiS ((getA M B1 B2 v).getD 0)))
            (.goto (fun _ => pl M B1 B2 .a8))))
        (.goto (fun _ => pl M B1 B2 .a9)))
  | .inr (.inr (.inr .a9)) => .pop (sk M B1 B2 .t3) (setA M B1 B2)
      (.branch (fun v => (getA M B1 B2 v).isSome)
        (.push (.inr (.inr (.inl B2.input))) (fun v => bitS (loS ((getA M B1 B2 v).getD 0)))
          (.push (.inr (.inr (.inl B2.input))) (fun v => bitS (hiS ((getA M B1 B2 v).getD 0)))
            (.goto (fun _ => pl M B1 B2 .a9))))
        (.goto (fun _ => .inr (.inr (.inl B2.main)))))
  | .inr (.inr (.inr .a10)) => .pop (.inr (.inr (.inl B2.output))) (setA M B1 B2)
      (.pop (.inr (.inr (.inl B2.output))) (setB M B1 B2)
        (.branch (fun v => (getA M B1 B2 v).isSome)
          (.push (sk M B1 B2 .t1) (fun v => combine (getA M B1 B2 v) (getB M B1 B2 v))
            (.goto (fun _ => pl M B1 B2 .a10)))
          (.goto (fun _ => pl M B1 B2 .a11))))
  | .inr (.inr (.inr .a11)) => .pop (sk M B1 B2 .t1) (setA M B1 B2)
      (.branch (fun v => (getA M B1 B2 v).isSome)
        (.push (sk M B1 B2 .out) (fun v => (getA M B1 B2 v).getD 0) (.goto (fun _ => pl M B1 B2 .a11)))
        (.load (fun v => setB M B1 B2 (setA M B1 B2 v none) none) .halt))

instance : Fintype (CΓ M B1 B2 (sk M B1 B2 .inp)) := inferInstanceAs (Fintype Sym)

def ctm : FinTM2 where
  K := CK M B1 B2
  kDecidableEq := inferInstance
  kFin := @instFintypeSum _ _ M.tm.kFin inferInstance
  k₀ := sk M B1 B2 .inp
  k₁ := sk M B1 B2 .out
  Γ := CΓ M B1 B2
  Λ := CL M B1 B2
  main := pl M B1 B2 .a1
  ΛFin := @instFintypeSum _ _ M.tm.ΛFin inferInstance
  σ := CS M B1 B2
  initialState := (M.tm.initialState, (B1.initial, (B2.initial, (none, none))))
  σFin := @instFintypeProd _ _ M.tm.σFin inferInstance
  Γk₀Fin := inferInstanceAs (Fintype Sym)
  m := code M B1 B2

abbrev cstep : CCfg M B1 B2 → Option (CCfg M B1 B2) := TM2.step (code M B1 B2)

/-! ### embedding of `M` -/

def embM (R : (k : CK M B1 B2) → List (CΓ M B1 B2 k)) (S : (k : M.tm.K) → List (M.tm.Γ k)) :
    (k : CK M B1 B2) → List (CΓ M B1 B2 k)
  | .inl k => S k
  | .inr k => R (.inr k)

def embCfgM (R : (k : CK M B1 B2) → List (CΓ M B1 B2 k)) (w : B1.State × (B2.State × Aux))
    (c : TM2.Cfg M.tm.Γ M.tm.Λ M.tm.σ) : CCfg M B1 B2 :=
  ⟨some (match c.l with | some l => .inl l | none => pl M B1 B2 .a6), (c.var, w), embM M B1 B2 R c.stk⟩

theorem embM_update (R : (k : CK M B1 B2) → List (CΓ M B1 B2 k)) (S : (k : M.tm.K) → List (M.tm.Γ k))
    (k : M.tm.K) (x : List (M.tm.Γ k)) :
    embM M B1 B2 R (Function.update S k x) = Function.update (embM M B1 B2 R S) (.inl k) x := by
  rw [Function.eq_update_iff]
  refine ⟨by show Function.update S k x k = x; exact Function.update_self k x S, fun y hy => ?_⟩
  rcases y with k' | k'
  · have h : k' ≠ k := fun e => hy (by rw [e])
    show Function.update S k x k' = S k'
    exact Function.update_of_ne h x S
  · rfl

theorem stepAux_mapM (R : (k : CK M B1 B2) → List (CΓ M B1 B2 k)) (w : B1.State × (B2.State × Aux))
    (q : TM2.Stmt M.tm.Γ M.tm.Λ M.tm.σ) (v : M.tm.σ) (S : (k : M.tm.K) → List (M.tm.Γ k)) :
    TM2.stepAux (mapM M B1 B2 q) (v, w) (embM M B1 B2 R S) = embCfgM M B1 B2 R w (TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push k f q ih =>
    simp only [mapM, TM2.stepAux]
    rw [← ih]; congr 1
    exact (embM_update M B1 B2 R S k (f v :: S k)).symm
  | peek k f q ih =>
    simp only [mapM, TM2.stepAux]; exact ih _ _
  | pop k f q ih =>
    simp only [mapM, TM2.stepAux]
    rw [← ih]; congr 1
    exact (embM_update M B1 B2 R S k (S k).tail).symm
  | load a q ih =>
    simp only [mapM, TM2.stepAux]; exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [mapM, TM2.stepAux]
    cases f v <;> simp [ih₁, ih₂]
  | goto f => rfl
  | halt => rfl

theorem runM (R : (k : CK M B1 B2) → List (CΓ M B1 B2 k)) (w : B1.State × (B2.State × Aux))
    {n : ℕ} {a b : TM2.Cfg M.tm.Γ M.tm.Λ M.tm.σ} (h : Trace (TM2.step M.tm.m) n a b) :
    Trace (cstep M B1 B2) n (embCfgM M B1 B2 R w a) (embCfgM M B1 B2 R w b) := by
  refine Trace.map (embCfgM M B1 B2 R w) ?_ h
  intro a b hab
  rcases a with ⟨l, v, S⟩
  cases l with
  | none => simp [TM2.step] at hab
  | some l =>
    simp only [TM2.step, Option.some.injEq] at hab
    subst hab
    show some (TM2.stepAux (mapM M B1 B2 (M.tm.m l)) (v, w) (embM M B1 B2 R S)) = _
    rw [stepAux_mapM]

/-! ### embedding of `B1` -/

def embB1 (R : (k : CK M B1 B2) → List (CΓ M B1 B2 k)) (S : B1.K → List Bool) :
    (k : CK M B1 B2) → List (CΓ M B1 B2 k)
  | .inl k => R (.inl k)
  | .inr (.inl k) => (S k).map bitS
  | .inr (.inr k) => R (.inr (.inr k))

def embCfgB1 (R : (k : CK M B1 B2) → List (CΓ M B1 B2 k)) (vM : M.tm.σ) (w2 : B2.State × Aux)
    (c : TM2.Cfg (fun _ : B1.K => Bool) B1.Label B1.State) : CCfg M B1 B2 :=
  ⟨some (match c.l with | some l => .inr (.inl l) | none => pl M B1 B2 .a4), (vM, (c.var, w2)),
    embB1 M B1 B2 R c.stk⟩

theorem embB1_update (R : (k : CK M B1 B2) → List (CΓ M B1 B2 k)) (S : B1.K → List Bool)
    (k : B1.K) (x : List Bool) :
    embB1 M B1 B2 R (Function.update S k x) = Function.update (embB1 M B1 B2 R S) (.inr (.inl k)) (x.map bitS) := by
  rw [Function.eq_update_iff]
  refine ⟨by show (Function.update S k x k).map bitS = _; rw [Function.update_self], fun y hy => ?_⟩
  rcases y with k' | (k' | k')
  · rfl
  · have h : k' ≠ k := fun e => hy (by rw [e])
    show (Function.update S k x k').map bitS = (S k').map bitS
    rw [Function.update_of_ne h]
  · rfl

theorem stepAux_mapB1 (R : (k : CK M B1 B2) → List (CΓ M B1 B2 k)) (vM : M.tm.σ) (w2 : B2.State × Aux)
    (q : TM2.Stmt (fun _ : B1.K => Bool) B1.Label B1.State) (v : B1.State) (S : B1.K → List Bool) :
    TM2.stepAux (mapB1 M B1 B2 q) (vM, (v, w2)) (embB1 M B1 B2 R S) =
      embCfgB1 M B1 B2 R vM w2 (TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push k f q ih =>
    simp only [mapB1, TM2.stepAux]
    rw [← ih]; congr 1
    exact (embB1_update M B1 B2 R S k (f v :: S k)).symm
  | peek k f q ih =>
    have hh : Option.map decS (embB1 M B1 B2 R S (Sum.inr (Sum.inl k))).head? = (S k).head? := by
      simp [embB1, List.head?_map, Option.map_map, Function.comp_def, decS_bitS]
    simp only [mapB1, TM2.stepAux, hh]
    exact ih _ _
  | pop k f q ih =>
    have hh : Option.map decS (embB1 M B1 B2 R S (Sum.inr (Sum.inl k))).head? = (S k).head? := by
      simp [embB1, List.head?_map, Option.map_map, Function.comp_def, decS_bitS]
    simp only [mapB1, TM2.stepAux, hh]
    rw [← ih]; congr 1
    rw [embB1_update]; congr 1; simp [embB1, List.map_tail]
  | load a q ih =>
    simp only [mapB1, TM2.stepAux]; exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [mapB1, TM2.stepAux]
    cases f v <;> simp [ih₁, ih₂]
  | goto f => rfl
  | halt => rfl

theorem runB1 (R : (k : CK M B1 B2) → List (CΓ M B1 B2 k)) (vM : M.tm.σ) (w2 : B2.State × Aux)
    {n : ℕ} {a b : TM2.Cfg (fun _ : B1.K => Bool) B1.Label B1.State} (h : Trace B1.step n a b) :
    Trace (cstep M B1 B2) n (embCfgB1 M B1 B2 R vM w2 a) (embCfgB1 M B1 B2 R vM w2 b) := by
  refine Trace.map (embCfgB1 M B1 B2 R vM w2) ?_ h
  intro a b hab
  rcases a with ⟨l, v, S⟩
  cases l with
  | none => simp [Machine.step, TM2.step] at hab
  | some l =>
    simp only [Machine.step, TM2.step, Option.some.injEq] at hab
    subst hab
    show some (TM2.stepAux (mapB1 M B1 B2 (B1.code l)) (vM, (v, w2)) (embB1 M B1 B2 R S)) = _
    rw [stepAux_mapB1]

/-! ### embedding of `B2` -/

def embB2 (R : (k : CK M B1 B2) → List (CΓ M B1 B2 k)) (S : B2.K → List Bool) :
    (k : CK M B1 B2) → List (CΓ M B1 B2 k)
  | .inl k => R (.inl k)
  | .inr (.inl k) => R (.inr (.inl k))
  | .inr (.inr (.inl k)) => (S k).map bitS
  | .inr (.inr (.inr k)) => R (.inr (.inr (.inr k)))

def embCfgB2 (R : (k : CK M B1 B2) → List (CΓ M B1 B2 k)) (vM : M.tm.σ) (v1 : B1.State) (a : Aux)
    (c : TM2.Cfg (fun _ : B2.K => Bool) B2.Label B2.State) : CCfg M B1 B2 :=
  ⟨some (match c.l with | some l => .inr (.inr (.inl l)) | none => pl M B1 B2 .a10), (vM, (v1, (c.var, a))),
    embB2 M B1 B2 R c.stk⟩

theorem embB2_update (R : (k : CK M B1 B2) → List (CΓ M B1 B2 k)) (S : B2.K → List Bool)
    (k : B2.K) (x : List Bool) :
    embB2 M B1 B2 R (Function.update S k x) =
      Function.update (embB2 M B1 B2 R S) (.inr (.inr (.inl k))) (x.map bitS) := by
  rw [Function.eq_update_iff]
  refine ⟨by show (Function.update S k x k).map bitS = _; rw [Function.update_self], fun y hy => ?_⟩
  rcases y with k' | (k' | (k' | k'))
  · rfl
  · rfl
  · have h : k' ≠ k := fun e => hy (by rw [e])
    show (Function.update S k x k').map bitS = (S k').map bitS
    rw [Function.update_of_ne h]
  · rfl

theorem stepAux_mapB2 (R : (k : CK M B1 B2) → List (CΓ M B1 B2 k)) (vM : M.tm.σ) (v1 : B1.State) (a : Aux)
    (q : TM2.Stmt (fun _ : B2.K => Bool) B2.Label B2.State) (v : B2.State) (S : B2.K → List Bool) :
    TM2.stepAux (mapB2 M B1 B2 q) (vM, (v1, (v, a))) (embB2 M B1 B2 R S) =
      embCfgB2 M B1 B2 R vM v1 a (TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push k f q ih =>
    simp only [mapB2, TM2.stepAux]
    rw [← ih]; congr 1
    exact (embB2_update M B1 B2 R S k (f v :: S k)).symm
  | peek k f q ih =>
    have hh : Option.map decS (embB2 M B1 B2 R S (Sum.inr (Sum.inr (Sum.inl k)))).head? = (S k).head? := by
      simp [embB2, List.head?_map, Option.map_map, Function.comp_def, decS_bitS]
    simp only [mapB2, TM2.stepAux, hh]
    exact ih _ _
  | pop k f q ih =>
    have hh : Option.map decS (embB2 M B1 B2 R S (Sum.inr (Sum.inr (Sum.inl k)))).head? = (S k).head? := by
      simp [embB2, List.head?_map, Option.map_map, Function.comp_def, decS_bitS]
    simp only [mapB2, TM2.stepAux, hh]
    rw [← ih]; congr 1
    rw [embB2_update]; congr 1; simp [embB2, List.map_tail]
  | load a q ih =>
    simp only [mapB2, TM2.stepAux]; exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [mapB2, TM2.stepAux]
    cases f v <;> simp [ih₁, ih₂]
  | goto f => rfl
  | halt => rfl

theorem runB2 (R : (k : CK M B1 B2) → List (CΓ M B1 B2 k)) (vM : M.tm.σ) (v1 : B1.State) (a : Aux)
    {n : ℕ} {c d : TM2.Cfg (fun _ : B2.K => Bool) B2.Label B2.State} (h : Trace B2.step n c d) :
    Trace (cstep M B1 B2) n (embCfgB2 M B1 B2 R vM v1 a c) (embCfgB2 M B1 B2 R vM v1 a d) := by
  refine Trace.map (embCfgB2 M B1 B2 R vM v1 a) ?_ h
  intro c d hcd
  rcases c with ⟨l, v, S⟩
  cases l with
  | none => simp [Machine.step, TM2.step] at hcd
  | some l =>
    simp only [Machine.step, TM2.step, Option.some.injEq] at hcd
    subst hcd
    show some (TM2.stepAux (mapB2 M B1 B2 (B2.code l)) (vM, (v1, (v, a))) (embB2 M B1 B2 R S)) = _
    rw [stepAux_mapB2]

/-! ### the full stack state -/

def full (SM : (k : M.tm.K) → List (M.tm.Γ k)) (S1 : B1.K → List Bool) (S2 : B2.K → List Bool)
    (X : XC → List Sym) : (k : CK M B1 B2) → List (CΓ M B1 B2 k)
  | .inl k => SM k
  | .inr (.inl k) => (S1 k).map bitS
  | .inr (.inr (.inl k)) => (S2 k).map bitS
  | .inr (.inr (.inr x)) => X x

variable {M B1 B2}

theorem full_updX (SM : (k : M.tm.K) → List (M.tm.Γ k)) (S1 : B1.K → List Bool) (S2 : B2.K → List Bool)
    (X : XC → List Sym) (x : XC) (v : List Sym) :
    Function.update (full M B1 B2 SM S1 S2 X) (sk M B1 B2 x) v = full M B1 B2 SM S1 S2 (Function.update X x v) := by
  symm
  rw [Function.eq_update_iff]
  refine ⟨by show Function.update X x v x = v; simp, fun y hy => ?_⟩
  rcases y with k' | (k' | (k' | k'))
  · rfl
  · rfl
  · rfl
  · have h : k' ≠ x := fun e => hy (by rw [e])
    show Function.update X x v k' = X k'
    rw [Function.update_of_ne h]

theorem full_upd1 (SM : (k : M.tm.K) → List (M.tm.Γ k)) (S1 : B1.K → List Bool) (S2 : B2.K → List Bool)
    (X : XC → List Sym) (k : B1.K) (l : List Bool) :
    Function.update (full M B1 B2 SM S1 S2 X) (.inr (.inl k)) (l.map bitS) =
      full M B1 B2 SM (Function.update S1 k l) S2 X := by
  symm
  rw [Function.eq_update_iff]
  refine ⟨by show (Function.update S1 k l k).map bitS = _; simp, fun y hy => ?_⟩
  rcases y with k' | (k' | (k' | k'))
  · rfl
  · have h : k' ≠ k := fun e => hy (by rw [e])
    show (Function.update S1 k l k').map bitS = (S1 k').map bitS
    rw [Function.update_of_ne h]
  · rfl
  · rfl

theorem full_upd2 (SM : (k : M.tm.K) → List (M.tm.Γ k)) (S1 : B1.K → List Bool) (S2 : B2.K → List Bool)
    (X : XC → List Sym) (k : B2.K) (l : List Bool) :
    Function.update (full M B1 B2 SM S1 S2 X) (.inr (.inr (.inl k))) (l.map bitS) =
      full M B1 B2 SM S1 (Function.update S2 k l) X := by
  symm
  rw [Function.eq_update_iff]
  refine ⟨by show (Function.update S2 k l k).map bitS = _; simp, fun y hy => ?_⟩
  rcases y with k' | (k' | (k' | k'))
  · rfl
  · rfl
  · have h : k' ≠ k := fun e => hy (by rw [e])
    show (Function.update S2 k l k').map bitS = (S2 k').map bitS
    rw [Function.update_of_ne h]
  · rfl

theorem full_updM (SM : (k : M.tm.K) → List (M.tm.Γ k)) (S1 : B1.K → List Bool) (S2 : B2.K → List Bool)
    (X : XC → List Sym) (k : M.tm.K) (l : List (M.tm.Γ k)) :
    Function.update (full M B1 B2 SM S1 S2 X) (.inl k) l = full M B1 B2 (Function.update SM k l) S1 S2 X := by
  symm
  rw [Function.eq_update_iff]
  refine ⟨by show Function.update SM k l k = l; simp, fun y hy => ?_⟩
  rcases y with k' | (k' | (k' | k'))
  · have h : k' ≠ k := fun e => hy (by rw [e])
    show Function.update SM k l k' = SM k'
    rw [Function.update_of_ne h]
  · rfl
  · rfl
  · rfl

abbrev CV := CS M B1 B2

theorem ph_a1 (SM : (k : M.tm.K) → List (M.tm.Γ k)) (S1 : B1.K → List Bool) (S2 : B2.K → List Bool)
    (vM : M.tm.σ) (v1 : B1.State) (v2 : B2.State) (b : Option Sym) :
    ∀ (w T1 T2 : List Sym) (X : XC → List Sym) (a : Option Sym), X .inp = w → X .t1 = T1 → X .t2 = T2 →
    Trace (cstep M B1 B2) (w.length + 1)
      ⟨some (pl M B1 B2 .a1), (vM, (v1, (v2, (a, b)))), full M B1 B2 SM S1 S2 X⟩
      ⟨some (pl M B1 B2 .a2), (vM, (v1, (v2, (none, b)))), full M B1 B2 SM S1 S2
        (Function.update (Function.update (Function.update X .inp []) .t1 (w.reverse ++ T1)) .t2
          (((symBits w).map bitS).reverse ++ T2))⟩ := by
  intro w
  induction w with
  | nil =>
    intro T1 T2 X a h1 h2 h3
    refine Trace.cons ?_ (Trace.refl _)
    simp only [cstep, TM2.step, code, TM2.stepAux, full, h1, List.head?_nil, setA, getA,
      Option.isSome_none, cond_false, Option.some.injEq, List.tail_nil, full_updX]
    congr 2
    funext k
    simp only [Function.update_apply, List.reverse_nil, List.nil_append, symBits, List.flatMap_nil,
      List.map_nil]
    split_ifs <;> simp_all
  | cons s w ih =>
    intro T1 T2 X a h1 h2 h3
    let X1 := Function.update (Function.update (Function.update X .inp w) .t1 (s :: T1)) .t2
      (bitS (loS s) :: bitS (hiS s) :: T2)
    have h := ih (s :: T1) (bitS (loS s) :: bitS (hiS s) :: T2) X1 (some s)
      (by simp [X1, Function.update_apply]) (by simp [X1, Function.update_apply])
      (by simp [X1])
    have heq : Function.update (Function.update (Function.update X1 .inp []) .t1 (w.reverse ++ s :: T1)) .t2
        (((symBits w).map bitS).reverse ++ (bitS (loS s) :: bitS (hiS s) :: T2)) =
        Function.update (Function.update (Function.update X .inp []) .t1 ((s :: w).reverse ++ T1)) .t2
        (((symBits (s :: w)).map bitS).reverse ++ T2) := by
      funext k
      simp only [X1, Function.update_apply, symBits, List.flatMap_cons, List.map_append,
        List.reverse_append, List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil,
        List.nil_append, List.append_assoc, List.cons_append, List.singleton_append]
      split_ifs <;> simp_all
    rw [heq] at h
    refine Trace.cons ?_ h
    simp only [cstep, TM2.step, code, TM2.stepAux, full, h1, List.head?_cons, setA, getA,
      Option.isSome_some, cond_true, Option.getD_some, Option.some.injEq, List.tail_cons, full_updX]
    congr 2
    funext k
    simp only [X1, Function.update_apply, h2, h3]
    split_ifs <;> simp_all

variable (SM : (k : M.tm.K) → List (M.tm.Γ k)) (S1 : B1.K → List Bool) (S2 : B2.K → List Bool)
    (vM : M.tm.σ) (v1 : B1.State) (v2 : B2.State)

theorem ph_a2 (b : Option Sym) :
    ∀ (U V : List Sym) (X : XC → List Sym) (a : Option Sym), X .t1 = U → X .bak = V →
    Trace (cstep M B1 B2) (U.length + 1)
      ⟨some (pl M B1 B2 .a2), (vM, (v1, (v2, (a, b)))), full M B1 B2 SM S1 S2 X⟩
      ⟨some (pl M B1 B2 .a3), (vM, (v1, (v2, (none, b)))), full M B1 B2 SM S1 S2
        (Function.update (Function.update X .t1 []) .bak (U.reverse ++ V))⟩ := by
  intro U
  induction U with
  | nil =>
    intro V X a h1 h2
    refine Trace.cons ?_ (Trace.refl _)
    simp only [cstep, TM2.step, code, TM2.stepAux, full, h1, List.head?_nil, setA, getA,
      Option.isSome_none, cond_false, Option.some.injEq, List.tail_nil, full_updX]
    congr 2
    funext k
    simp only [Function.update_apply, List.reverse_nil, List.nil_append]
    split_ifs <;> simp_all
  | cons c U ih =>
    intro V X a h1 h2
    let X1 := Function.update (Function.update X .t1 U) .bak (c :: V)
    have h := ih (c :: V) X1 (some c) (by simp [X1]) (by simp [X1])
    have heq : Function.update (Function.update X1 .t1 []) .bak (U.reverse ++ c :: V) =
        Function.update (Function.update X .t1 []) .bak ((c :: U).reverse ++ V) := by
      funext k
      simp only [X1, Function.update_apply, List.reverse_cons, List.append_assoc, List.cons_append,
        List.nil_append]
      split_ifs <;> simp_all
    rw [heq] at h
    refine Trace.cons ?_ h
    simp only [cstep, TM2.step, code, TM2.stepAux, full, h1, List.head?_cons, setA, getA,
      Option.isSome_some, cond_true, Option.getD_some, Option.some.injEq, List.tail_cons, full_updX]
    congr 2
    funext k
    simp only [X1, Function.update_apply, h2]
    split_ifs <;> simp_all

theorem ph_a7 (b : Option Sym) :
    ∀ (U V : List Sym) (X : XC → List Sym) (a : Option Sym), X .bak = U → X .t3 = V →
    Trace (cstep M B1 B2) (U.length + 1)
      ⟨some (pl M B1 B2 .a7), (vM, (v1, (v2, (a, b)))), full M B1 B2 SM S1 S2 X⟩
      ⟨some (pl M B1 B2 .a8), (vM, (v1, (v2, (none, b)))), full M B1 B2 SM S1 S2
        (Function.update (Function.update X .bak []) .t3 (U.reverse ++ V))⟩ := by
  intro U
  induction U with
  | nil =>
    intro V X a h1 h2
    refine Trace.cons ?_ (Trace.refl _)
    simp only [cstep, TM2.step, code, TM2.stepAux, full, h1, List.head?_nil, setA, getA,
      Option.isSome_none, cond_false, Option.some.injEq, List.tail_nil, full_updX]
    congr 2
    funext k
    simp only [Function.update_apply, List.reverse_nil, List.nil_append]
    split_ifs <;> simp_all
  | cons c U ih =>
    intro V X a h1 h2
    let X1 := Function.update (Function.update X .bak U) .t3 (c :: V)
    have h := ih (c :: V) X1 (some c) (by simp [X1]) (by simp [X1])
    have heq : Function.update (Function.update X1 .bak []) .t3 (U.reverse ++ c :: V) =
        Function.update (Function.update X .bak []) .t3 ((c :: U).reverse ++ V) := by
      funext k
      simp only [X1, Function.update_apply, List.reverse_cons, List.append_assoc, List.cons_append,
        List.nil_append]
      split_ifs <;> simp_all
    rw [heq] at h
    refine Trace.cons ?_ h
    simp only [cstep, TM2.step, code, TM2.stepAux, full, h1, List.head?_cons, setA, getA,
      Option.isSome_some, cond_true, Option.getD_some, Option.some.injEq, List.tail_cons, full_updX]
    congr 2
    funext k
    simp only [X1, Function.update_apply, h2]
    split_ifs <;> simp_all

theorem full_apply1 (SM : (k : M.tm.K) → List (M.tm.Γ k)) (S1 : B1.K → List Bool) (S2 : B2.K → List Bool)
    (X : XC → List Sym) (k : B1.K) : full M B1 B2 SM S1 S2 X (.inr (.inl k)) = (S1 k).map bitS := rfl
theorem full_apply2 (SM : (k : M.tm.K) → List (M.tm.Γ k)) (S1 : B1.K → List Bool) (S2 : B2.K → List Bool)
    (X : XC → List Sym) (k : B2.K) : full M B1 B2 SM S1 S2 X (.inr (.inr (.inl k))) = (S2 k).map bitS := rfl
theorem full_applyX (SM : (k : M.tm.K) → List (M.tm.Γ k)) (S1 : B1.K → List Bool) (S2 : B2.K → List Bool)
    (X : XC → List Sym) (x : XC) : full M B1 B2 SM S1 S2 X (sk M B1 B2 x) = X x := rfl
theorem full_applyM (SM : (k : M.tm.K) → List (M.tm.Γ k)) (S1 : B1.K → List Bool) (S2 : B2.K → List Bool)
    (X : XC → List Sym) (k : M.tm.K) : full M B1 B2 SM S1 S2 X (.inl k) = SM k := rfl

theorem full_push1 (SM : (k : M.tm.K) → List (M.tm.Γ k)) (S1 : B1.K → List Bool) (S2 : B2.K → List Bool)
    (X : XC → List Sym) (k : B1.K) (u : Bool) :
    Function.update (full M B1 B2 SM S1 S2 X) (.inr (.inl k)) (bitS u :: List.map bitS (S1 k)) =
      full M B1 B2 SM (Function.update S1 k (u :: S1 k)) S2 X :=
  full_upd1 SM S1 S2 X k (u :: S1 k)

theorem full_pop1 (SM : (k : M.tm.K) → List (M.tm.Γ k)) (S1 : B1.K → List Bool) (S2 : B2.K → List Bool)
    (X : XC → List Sym) (k : B1.K) :
    Function.update (full M B1 B2 SM S1 S2 X) (.inr (.inl k)) (List.map bitS (S1 k)).tail =
      full M B1 B2 SM (Function.update S1 k (S1 k).tail) S2 X := by
  rw [← List.map_tail]; exact full_upd1 SM S1 S2 X k _

theorem full_push2 (SM : (k : M.tm.K) → List (M.tm.Γ k)) (S1 : B1.K → List Bool) (S2 : B2.K → List Bool)
    (X : XC → List Sym) (k : B2.K) (u : Bool) :
    Function.update (full M B1 B2 SM S1 S2 X) (.inr (.inr (.inl k))) (bitS u :: List.map bitS (S2 k)) =
      full M B1 B2 SM S1 (Function.update S2 k (u :: S2 k)) X :=
  full_upd2 SM S1 S2 X k (u :: S2 k)

theorem full_pop2 (SM : (k : M.tm.K) → List (M.tm.Γ k)) (S1 : B1.K → List Bool) (S2 : B2.K → List Bool)
    (X : XC → List Sym) (k : B2.K) :
    Function.update (full M B1 B2 SM S1 S2 X) (.inr (.inr (.inl k))) (List.map bitS (S2 k)).tail =
      full M B1 B2 SM S1 (Function.update S2 k (S2 k).tail) X := by
  rw [← List.map_tail]; exact full_upd2 SM S1 S2 X k _

theorem ph_a3 (b : Option Sym) (SM : (k : M.tm.K) → List (M.tm.Γ k)) (S2 : B2.K → List Bool) (vM : M.tm.σ)
    (v1 : B1.State) (v2 : B2.State) :
    ∀ (U V : List Bool) (S1 : B1.K → List Bool) (X : XC → List Sym) (a : Option Sym),
    X .t2 = U.map bitS → S1 B1.input = V →
    Trace (cstep M B1 B2) (U.length + 1)
      ⟨some (pl M B1 B2 .a3), (vM, (v1, (v2, (a, b)))), full M B1 B2 SM S1 S2 X⟩
      ⟨some (.inr (.inl B1.main)), (vM, (v1, (v2, (none, b)))), full M B1 B2 SM
        (Function.update S1 B1.input (U.reverse ++ V)) S2 (Function.update X .t2 [])⟩ := by
  intro U
  induction U with
  | nil =>
    intro V S1 X a h1 h2
    refine Trace.cons ?_ (Trace.refl _)
    simp only [List.map_nil] at h1
    simp only [cstep, TM2.step, code, TM2.stepAux, full, h1, List.head?_nil, setA, getA,
      Option.isSome_none, cond_false, Option.some.injEq, List.tail_nil, full_updX]
    rw [List.reverse_nil, List.nil_append, ← h2, Function.update_eq_self]
  | cons u U ih =>
    intro V S1 X a h1 h2
    have h := ih (u :: V) (Function.update S1 B1.input (u :: V)) (Function.update X .t2 (U.map bitS))
      (some (bitS u)) (by simp) (by simp)
    rw [Function.update_idem, Function.update_idem,
      show U.reverse ++ u :: V = (u :: U).reverse ++ V by simp] at h
    refine Trace.cons ?_ h
    simp only [List.map_cons] at h1
    simp only [cstep, TM2.step, code, TM2.stepAux, full, h1, List.head?_cons, setA, getA,
      Option.isSome_some, cond_true, Option.getD_some, Option.some.injEq, List.tail_cons, full_updX]
    rw [← h2, full_push1]

theorem ph_a5 (b : Option Sym) (S1 : B1.K → List Bool) (S2 : B2.K → List Bool) (vM : M.tm.σ)
    (v1 : B1.State) (v2 : B2.State) :
    ∀ (U : List Sym) (SM : (k : M.tm.K) → List (M.tm.Γ k)) (X : XC → List Sym) (a : Option Sym),
    X .t3 = U →
    Trace (cstep M B1 B2) (U.length + 1)
      ⟨some (pl M B1 B2 .a5), (vM, (v1, (v2, (a, b)))), full M B1 B2 SM S1 S2 X⟩
      ⟨some (.inl M.tm.main), (vM, (v1, (v2, (none, b)))), full M B1 B2
        (Function.update SM M.tm.k₀ ((U.map M.inputAlphabet.symm).reverse ++ SM M.tm.k₀)) S1 S2
        (Function.update X .t3 [])⟩ := by
  intro U
  induction U with
  | nil =>
    intro SM X a h1
    refine Trace.cons ?_ (Trace.refl _)
    simp only [cstep, TM2.step, code, TM2.stepAux, full, h1, List.head?_nil, setA, getA,
      Option.isSome_none, cond_false, Option.some.injEq, List.tail_nil, full_updX]
    simp
  | cons u U ih =>
    intro SM X a h1
    have h := ih (Function.update SM M.tm.k₀ (M.inputAlphabet.symm u :: SM M.tm.k₀))
      (Function.update X .t3 U) (some u) (by simp)
    rw [Function.update_idem, Function.update_idem, Function.update_self] at h
    rw [show (List.map M.inputAlphabet.symm U).reverse ++ M.inputAlphabet.symm u :: SM M.tm.k₀ =
      (List.map M.inputAlphabet.symm (u :: U)).reverse ++ SM M.tm.k₀ by simp] at h
    refine Trace.cons ?_ h
    simp only [cstep, TM2.step, code, TM2.stepAux, full, h1, List.head?_cons, setA, getA,
      Option.isSome_some, cond_true, Option.getD_some, Option.some.injEq, List.tail_cons, full_updX]
    rw [full_updM]

theorem ph_a4 (SM : (k : M.tm.K) → List (M.tm.Γ k)) (S2 : B2.K → List Bool) (vM : M.tm.σ)
    (v1 : B1.State) (v2 : B2.State) :
    ∀ (out T : List Sym) (S1 : B1.K → List Bool) (X : XC → List Sym) (a b : Option Sym),
    S1 B1.output = symBits out → X .t3 = T →
    Trace (cstep M B1 B2) (out.length + 1)
      ⟨some (pl M B1 B2 .a4), (vM, (v1, (v2, (a, b)))), full M B1 B2 SM S1 S2 X⟩
      ⟨some (pl M B1 B2 .a5), (vM, (v1, (v2, (none, none)))), full M B1 B2 SM
        (Function.update S1 B1.output []) S2 (Function.update X .t3 (out.reverse ++ T))⟩ := by
  intro out
  induction out with
  | nil =>
    intro T S1 X a b h1 h2
    refine Trace.cons ?_ (Trace.refl _)
    simp only [symBits, List.flatMap_nil] at h1
    simp only [cstep, TM2.step, code, TM2.stepAux, setA, getA, setB, getB, Option.some.injEq, full_apply1]
    rw [full_pop1]
    simp only [full_apply1, Function.update_self, h1, List.tail_nil, List.map_nil, List.head?_nil,
      Option.isSome_none, cond_false, List.reverse_nil, List.nil_append]
    rw [show ([] : List Sym) = ([] : List Bool).map bitS from rfl, full_upd1, Function.update_idem,
      ← h2, Function.update_eq_self]
  | cons s out ih =>
    intro T S1 X a b h1 h2
    have h1' : S1 B1.output = hiS s :: loS s :: symBits out := by rw [h1]; simp [symBits]
    have h := ih (s :: T) (Function.update S1 B1.output (symBits out)) (Function.update X .t3 (s :: T))
      (some (bitS (hiS s))) (some (bitS (loS s))) (by simp) (by simp)
    rw [Function.update_idem, Function.update_idem,
      show out.reverse ++ s :: T = (s :: out).reverse ++ T by simp] at h
    refine Trace.cons ?_ h
    simp only [cstep, TM2.step, code, TM2.stepAux, setA, getA, setB, getB, Option.some.injEq, full_apply1]
    rw [full_pop1]
    simp only [full_apply1, Function.update_self, h1', List.tail_cons, List.map_cons, List.head?_cons,
      Option.isSome_some, cond_true, combine_bits]
    rw [full_upd1, Function.update_idem, full_applyX, full_updX, h2]

theorem ph_a6 (b : Option Sym) (S1 : B1.K → List Bool) (S2 : B2.K → List Bool) (vM : M.tm.σ)
    (v1 : B1.State) (v2 : B2.State) :
    ∀ (U T : List Sym) (SM : (k : M.tm.K) → List (M.tm.Γ k)) (X : XC → List Sym) (a : Option Sym),
    SM M.tm.k₁ = U.map M.outputAlphabet.symm → X .t1 = T →
    Trace (cstep M B1 B2) (U.length + 1)
      ⟨some (pl M B1 B2 .a6), (vM, (v1, (v2, (a, b)))), full M B1 B2 SM S1 S2 X⟩
      ⟨some (pl M B1 B2 .a7), (vM, (v1, (v2, (none, b)))), full M B1 B2
        (Function.update SM M.tm.k₁ []) S1 S2 (Function.update X .t1 (U.reverse ++ T))⟩ := by
  intro U
  induction U with
  | nil =>
    intro T SM X a h1 h2
    refine Trace.cons ?_ (Trace.refl _)
    simp only [List.map_nil] at h1
    simp only [cstep, TM2.step, code, TM2.stepAux, full, h1, List.head?_nil, setA, getA,
      Option.map_none, Option.isSome_none, cond_false, Option.some.injEq, List.tail_nil, full_updM]
    rw [List.reverse_nil, List.nil_append, ← h2, Function.update_eq_self]
  | cons u U ih =>
    intro T SM X a h1 h2
    have h := ih (u :: T) (Function.update SM M.tm.k₁ (U.map M.outputAlphabet.symm))
      (Function.update X .t1 (u :: T)) (some u) (by simp) (by simp)
    rw [Function.update_idem, Function.update_idem,
      show U.reverse ++ u :: T = (u :: U).reverse ++ T by simp] at h
    refine Trace.cons ?_ h
    simp only [List.map_cons] at h1
    simp only [cstep, TM2.step, code, TM2.stepAux, full, h1, List.head?_cons, setA, getA,
      Option.map_some, Equiv.apply_symm_apply, Option.isSome_some, cond_true, Option.getD_some,
      Option.some.injEq, List.tail_cons, full_updM, full_updX, h2]

theorem ph_a8 (b : Option Sym) (SM : (k : M.tm.K) → List (M.tm.Γ k)) (S1 : B1.K → List Bool) (vM : M.tm.σ)
    (v1 : B1.State) (v2 : B2.State) :
    ∀ (U : List Sym) (V : List Bool) (S2 : B2.K → List Bool) (X : XC → List Sym) (a : Option Sym),
    X .t1 = U → S2 B2.input = V →
    Trace (cstep M B1 B2) (U.length + 1)
      ⟨some (pl M B1 B2 .a8), (vM, (v1, (v2, (a, b)))), full M B1 B2 SM S1 S2 X⟩
      ⟨some (pl M B1 B2 .a9), (vM, (v1, (v2, (none, b)))), full M B1 B2 SM S1
        (Function.update S2 B2.input (symBits U.reverse ++ V)) (Function.update X .t1 [])⟩ := by
  intro U
  induction U with
  | nil =>
    intro V S2 X a h1 h2
    refine Trace.cons ?_ (Trace.refl _)
    simp only [cstep, TM2.step, code, TM2.stepAux, setA, getA, full_applyX, h1, List.head?_nil,
      Option.isSome_none, cond_false, Option.some.injEq, List.tail_nil, full_updX]
    simp only [List.reverse_nil, symBits, List.flatMap_nil, List.nil_append]
    rw [← h2, Function.update_eq_self]
  | cons u U ih =>
    intro V S2 X a h1 h2
    have h := ih (hiS u :: loS u :: V) (Function.update S2 B2.input (hiS u :: loS u :: V))
      (Function.update X .t1 U) (some u) (by simp) (by simp)
    rw [Function.update_idem, Function.update_idem,
      show symBits U.reverse ++ hiS u :: loS u :: V = symBits (u :: U).reverse ++ V by
        simp [symBits]] at h
    refine Trace.cons ?_ h
    simp only [cstep, TM2.step, code, TM2.stepAux, setA, getA, full_applyX, h1, List.head?_cons,
      Option.isSome_some, cond_true, Option.getD_some, Option.some.injEq, List.tail_cons, full_updX]
    rw [full_apply2, full_push2, full_apply2, full_push2, Function.update_self, Function.update_idem, h2]

theorem ph_a9 (b : Option Sym) (SM : (k : M.tm.K) → List (M.tm.Γ k)) (S1 : B1.K → List Bool) (vM : M.tm.σ)
    (v1 : B1.State) (v2 : B2.State) :
    ∀ (U : List Sym) (V : List Bool) (S2 : B2.K → List Bool) (X : XC → List Sym) (a : Option Sym),
    X .t3 = U → S2 B2.input = V →
    Trace (cstep M B1 B2) (U.length + 1)
      ⟨some (pl M B1 B2 .a9), (vM, (v1, (v2, (a, b)))), full M B1 B2 SM S1 S2 X⟩
      ⟨some (.inr (.inr (.inl B2.main))), (vM, (v1, (v2, (none, b)))), full M B1 B2 SM S1
        (Function.update S2 B2.input (symBits U.reverse ++ V)) (Function.update X .t3 [])⟩ := by
  intro U
  induction U with
  | nil =>
    intro V S2 X a h1 h2
    refine Trace.cons ?_ (Trace.refl _)
    simp only [cstep, TM2.step, code, TM2.stepAux, setA, getA, full_applyX, h1, List.head?_nil,
      Option.isSome_none, cond_false, Option.some.injEq, List.tail_nil, full_updX]
    simp only [List.reverse_nil, symBits, List.flatMap_nil, List.nil_append]
    rw [← h2, Function.update_eq_self]
  | cons u U ih =>
    intro V S2 X a h1 h2
    have h := ih (hiS u :: loS u :: V) (Function.update S2 B2.input (hiS u :: loS u :: V))
      (Function.update X .t3 U) (some u) (by simp) (by simp)
    rw [Function.update_idem, Function.update_idem,
      show symBits U.reverse ++ hiS u :: loS u :: V = symBits (u :: U).reverse ++ V by
        simp [symBits]] at h
    refine Trace.cons ?_ h
    simp only [cstep, TM2.step, code, TM2.stepAux, setA, getA, full_applyX, h1, List.head?_cons,
      Option.isSome_some, cond_true, Option.getD_some, Option.some.injEq, List.tail_cons, full_updX]
    rw [full_apply2, full_push2, full_apply2, full_push2, Function.update_self, Function.update_idem, h2]

theorem ph_a10 (SM : (k : M.tm.K) → List (M.tm.Γ k)) (S1 : B1.K → List Bool) (vM : M.tm.σ)
    (v1 : B1.State) (v2 : B2.State) :
    ∀ (out T : List Sym) (S2 : B2.K → List Bool) (X : XC → List Sym) (a b : Option Sym),
    S2 B2.output = symBits out → X .t1 = T →
    Trace (cstep M B1 B2) (out.length + 1)
      ⟨some (pl M B1 B2 .a10), (vM, (v1, (v2, (a, b)))), full M B1 B2 SM S1 S2 X⟩
      ⟨some (pl M B1 B2 .a11), (vM, (v1, (v2, (none, none)))), full M B1 B2 SM S1
        (Function.update S2 B2.output []) (Function.update X .t1 (out.reverse ++ T))⟩ := by
  intro out
  induction out with
  | nil =>
    intro T S2 X a b h1 h2
    refine Trace.cons ?_ (Trace.refl _)
    simp only [symBits, List.flatMap_nil] at h1
    simp only [cstep, TM2.step, code, TM2.stepAux, setA, getA, setB, getB, Option.some.injEq, full_apply2]
    rw [full_pop2]
    simp only [full_apply2, Function.update_self, h1, List.tail_nil, List.map_nil, List.head?_nil,
      Option.isSome_none, cond_false, List.reverse_nil, List.nil_append]
    rw [show ([] : List Sym) = ([] : List Bool).map bitS from rfl, full_upd2, Function.update_idem,
      ← h2, Function.update_eq_self]
  | cons s out ih =>
    intro T S2 X a b h1 h2
    have h1' : S2 B2.output = hiS s :: loS s :: symBits out := by rw [h1]; simp [symBits]
    have h := ih (s :: T) (Function.update S2 B2.output (symBits out)) (Function.update X .t1 (s :: T))
      (some (bitS (hiS s))) (some (bitS (loS s))) (by simp) (by simp)
    rw [Function.update_idem, Function.update_idem,
      show out.reverse ++ s :: T = (s :: out).reverse ++ T by simp] at h
    refine Trace.cons ?_ h
    simp only [cstep, TM2.step, code, TM2.stepAux, setA, getA, setB, getB, Option.some.injEq, full_apply2]
    rw [full_pop2]
    simp only [full_apply2, Function.update_self, h1', List.tail_cons, List.map_cons, List.head?_cons,
      Option.isSome_some, cond_true, combine_bits]
    rw [full_upd2, Function.update_idem, full_applyX, full_updX, h2]

theorem ph_a11 (SM : (k : M.tm.K) → List (M.tm.Γ k)) (S1 : B1.K → List Bool) (S2 : B2.K → List Bool)
    (vM : M.tm.σ) (v1 : B1.State) (v2 : B2.State) :
    ∀ (U V : List Sym) (X : XC → List Sym) (a b : Option Sym), X .t1 = U → X .out = V →
    Trace (cstep M B1 B2) (U.length + 1)
      ⟨some (pl M B1 B2 .a11), (vM, (v1, (v2, (a, b)))), full M B1 B2 SM S1 S2 X⟩
      ⟨none, (vM, (v1, (v2, (none, none)))), full M B1 B2 SM S1 S2
        (Function.update (Function.update X .t1 []) .out (U.reverse ++ V))⟩ := by
  intro U
  induction U with
  | nil =>
    intro V X a b h1 h2
    refine Trace.cons ?_ (Trace.refl _)
    simp only [cstep, TM2.step, code, TM2.stepAux, setA, getA, setB, full_applyX, h1, List.head?_nil,
      Option.isSome_none, cond_false, Option.some.injEq, List.tail_nil, full_updX]
    congr 2
    funext k
    simp only [Function.update_apply, List.reverse_nil, List.nil_append]
    split_ifs <;> simp_all
  | cons c U ih =>
    intro V X a b h1 h2
    let X1 := Function.update (Function.update X .t1 U) .out (c :: V)
    have h := ih (c :: V) X1 (some c) b (by simp [X1]) (by simp [X1])
    have heq : Function.update (Function.update X1 .t1 []) .out (U.reverse ++ c :: V) =
        Function.update (Function.update X .t1 []) .out ((c :: U).reverse ++ V) := by
      funext k
      simp only [X1, Function.update_apply, List.reverse_cons, List.append_assoc, List.cons_append,
        List.nil_append]
      split_ifs <;> simp_all
    rw [heq] at h
    refine Trace.cons ?_ h
    simp only [cstep, TM2.step, code, TM2.stepAux, full_applyX, h1, List.head?_cons, setA, getA,
      Option.isSome_some, cond_true, Option.getD_some, Option.some.injEq, List.tail_cons, full_updX]
    congr 2
    funext k
    simp only [X1, Function.update_apply, h2]
    split_ifs <;> simp_all

theorem init_eq (w : List Sym) : initList (ctm M B1 B2) w =
    (⟨some (pl M B1 B2 .a1), (M.tm.initialState, (B1.initial, (B2.initial, (none, none)))),
      full M B1 B2 (fun _ => []) (fun _ => []) (fun _ => []) (fun x => if x = .inp then w else [])⟩ :
      CCfg M B1 B2) := by
  unfold initList
  congr 1
  funext k
  rcases k with k | (k | (k | x))
  · simp [ctm, full]
  · simp [ctm, full]
  · simp [ctm, full]
  · by_cases hx : x = .inp
    · subst hx; simp [ctm, full]; rfl
    · simp [ctm, full, hx]

theorem halt_eq (z : List Sym) : haltList (ctm M B1 B2) z =
    (⟨none, (M.tm.initialState, (B1.initial, (B2.initial, (none, none)))),
      full M B1 B2 (fun _ => []) (fun _ => []) (fun _ => []) (fun x => if x = .out then z else [])⟩ :
      CCfg M B1 B2) := by
  unfold haltList
  congr 1
  funext k
  rcases k with k | (k | (k | x))
  · simp [ctm, full]
  · simp [ctm, full]
  · simp [ctm, full]
  · by_cases hx : x = .out
    · subst hx; simp [ctm, full]; rfl
    · simp [ctm, full, hx]

theorem embB1_full (SM : (k : M.tm.K) → List (M.tm.Γ k)) (S1 S1' : B1.K → List Bool) (S2 : B2.K → List Bool)
    (X : XC → List Sym) : embB1 M B1 B2 (full M B1 B2 SM S1' S2 X) S1 = full M B1 B2 SM S1 S2 X := by
  funext k; rcases k with k | (k | (k | k)) <;> rfl

theorem embB2_full (SM : (k : M.tm.K) → List (M.tm.Γ k)) (S1 : B1.K → List Bool) (S2 S2' : B2.K → List Bool)
    (X : XC → List Sym) : embB2 M B1 B2 (full M B1 B2 SM S1 S2' X) S2 = full M B1 B2 SM S1 S2 X := by
  funext k; rcases k with k | (k | (k | k)) <;> rfl

theorem embM_full (SM SM' : (k : M.tm.K) → List (M.tm.Γ k)) (S1 : B1.K → List Bool) (S2 : B2.K → List Bool)
    (X : XC → List Sym) : embM M B1 B2 (full M B1 B2 SM' S1 S2 X) SM = full M B1 B2 SM S1 S2 X := by
  funext k; rcases k with k | (k | (k | k)) <;> rfl

theorem combo_run {w w1 v z : List Sym} {n1 nM n2 : ℕ}
    (h1 : Trace B1.step n1 (B1.initialCfg (symBits w)) (B1.finalCfg (symBits w1)))
    (hM : Trace (TM2.step M.tm.m) nM (initList M.tm (w1.map M.inputAlphabet.symm))
      (haltList M.tm (v.map M.outputAlphabet.symm)))
    (h2 : Trace B2.step n2 (B2.initialCfg (symBits (w ++ v))) (B2.finalCfg (symBits z))) :
    ∃ N, N = (w.length + 1) + ((w.length) + 1) + ((symBits w).length + 1) + n1 + (w1.length + 1) +
        (w1.length + 1) + nM + (v.length + 1) + (w.length + 1) + (v.length + 1) + (w.length + 1) + n2 +
        (z.length + 1) + (z.length + 1) ∧
      Trace (cstep M B1 B2) N (initList (ctm M B1 B2) w) (haltList (ctm M B1 B2) z) := by
  set E1 : B1.K → List Bool := fun _ => []
  set E2 : B2.K → List Bool := fun _ => []
  set EM : (k : M.tm.K) → List (M.tm.Γ k) := fun _ => []
  set X0 : XC → List Sym := fun x => if x = .inp then w else []
  set vM := M.tm.initialState
  set v1 := B1.initial
  set v2 := B2.initial
  -- phase a1
  have t1 := ph_a1 EM E1 E2 vM v1 v2 none w [] [] X0 none (by simp [X0]) (by simp [X0]) (by simp [X0])
  set X1 := Function.update (Function.update (Function.update X0 .inp []) .t1 (w.reverse ++ [])) .t2
    (((symBits w).map bitS).reverse ++ [])
  have t2 := ph_a2 EM E1 E2 vM v1 v2 none (w.reverse ++ []) [] X1 none (by simp [X1]) (by simp [X1, X0])
  set X2 := Function.update (Function.update X1 .t1 []) .bak ((w.reverse ++ []).reverse ++ [])
  have t3 := ph_a3 none EM E2 vM v1 v2 (symBits w).reverse [] E1 X2 none
    (by simp [X2, X1, List.map_reverse]) rfl
  set X3 := Function.update X2 .t2 []
  -- run B1
  have eS1a : Function.update E1 B1.input ((symBits w).reverse.reverse ++ []) =
      fun k => if k = B1.input then symBits w else [] := by
    funext k; simp [E1, Function.update_apply]
  rw [eS1a] at t3
  have tB1 := runB1 M B1 B2 (full M B1 B2 EM E1 E2 X3) vM (v2, (none, none)) h1
  simp only [embCfgB1, Machine.initialCfg, Machine.finalCfg, embB1_full] at tB1
  -- phase a4
  have t4 := ph_a4 EM E2 vM v1 v2 w1 [] (fun k => if k = B1.output then symBits w1 else []) X3 none none
    (by simp) (by simp [X3, X2, X1, X0])
  set S1b := Function.update (fun k : B1.K => if k = B1.output then symBits w1 else []) B1.output []
  set X4 := Function.update X3 .t3 (w1.reverse ++ [])
  -- phase a5
  have t5 := ph_a5 none S1b E2 vM v1 v2 (w1.reverse ++ []) EM X4 none (by simp [X4])
  set X5 := Function.update X4 .t3 []
  have eSM5 : Function.update EM M.tm.k₀ (((w1.reverse ++ []).map M.inputAlphabet.symm).reverse ++ EM M.tm.k₀) =
      (initList M.tm (w1.map M.inputAlphabet.symm)).stk := by
    funext k
    unfold initList
    by_cases hk : k = M.tm.k₀
    · subst hk; simp [EM, List.map_reverse]
    · rw [Function.update_of_ne hk]; simp [EM, hk]
  rw [eSM5] at t5
  have tM := runM M B1 B2 (full M B1 B2 EM S1b E2 X5) (v1, (v2, (none, none))) hM
  simp only [embCfgM, embM_full] at tM
  -- phase a6
  set HS := (haltList M.tm (v.map M.outputAlphabet.symm)).stk
  have t6 := ph_a6 none S1b E2 vM v1 v2 v [] HS X5 none
    (by simp [HS, haltList]) (by simp [X5, X4, X3, X2, X1, X0])
  set SM7 := Function.update HS M.tm.k₁ []
  set X6 := Function.update X5 .t1 (v.reverse ++ [])
  -- phase a7
  have t7 := ph_a7 SM7 S1b E2 vM v1 v2 none ((w.reverse ++ []).reverse ++ []) [] X6 none
    (by simp [X6, X5, X4, X3, X2]) (by simp [X6, X5])
  set X7 := Function.update (Function.update X6 .bak []) .t3 (((w.reverse ++ []).reverse ++ []).reverse ++ [])
  -- phase a8
  have t8 := ph_a8 none SM7 S1b vM v1 v2 (v.reverse ++ []) [] E2 X7 none (by simp [X7, X6]) rfl
  set S2a := Function.update E2 B2.input (symBits (v.reverse ++ []).reverse ++ [])
  set X8 := Function.update X7 .t1 []
  -- phase a9
  have t9 := ph_a9 none SM7 S1b vM v1 v2 ((((w.reverse ++ []).reverse ++ []).reverse ++ []))
    (symBits (v.reverse ++ []).reverse ++ []) S2a X8 none
    (by simp [X8, X7]) (by simp [S2a])
  set X9 := Function.update X8 .t3 []
  have eS2b : Function.update S2a B2.input (symBits (((w.reverse ++ []).reverse ++ []).reverse ++ []).reverse ++
      (symBits (v.reverse ++ []).reverse ++ [])) = fun k => if k = B2.input then symBits (w ++ v) else [] := by
    funext k; by_cases hk : k = B2.input <;> simp [S2a, E2, Function.update_apply, symBits, List.flatMap_append, hk]
  rw [eS2b] at t9
  -- run B2
  have tB2 := runB2 M B1 B2 (full M B1 B2 SM7 S1b E2 X9) vM v1 (none, none) h2
  simp only [embCfgB2, Machine.initialCfg, Machine.finalCfg, embB2_full] at tB2
  -- phase a10
  have t10 := ph_a10 SM7 S1b vM v1 v2 z [] (fun k => if k = B2.output then symBits z else []) X9 none none
    (by simp) (by simp [X9, X8])
  set S2d := Function.update (fun k : B2.K => if k = B2.output then symBits z else []) B2.output []
  set X10 := Function.update X9 .t1 (z.reverse ++ [])
  -- phase a11
  have t11 := ph_a11 SM7 S1b S2d vM v1 v2 (z.reverse ++ []) [] X10 none none (by simp [X10])
    (by simp [X10, X9, X8, X7, X6, X5, X4, X3, X2, X1, X0])
  have efin : full M B1 B2 SM7 S1b S2d (Function.update (Function.update X10 .t1 []) .out
      ((z.reverse ++ []).reverse ++ [])) =
      full M B1 B2 EM E1 E2 (fun x => if x = .out then z else []) := by
    congr 1
    · funext k
      by_cases hk : k = M.tm.k₁
      · subst hk; simp [SM7]; rfl
      · show Function.update HS M.tm.k₁ [] k = EM k
        rw [Function.update_of_ne hk]; simp [HS, haltList, hk, EM]
    · funext k; by_cases hk : k = B1.output <;> simp [S1b, E1, Function.update_apply, hk]
    · funext k; by_cases hk : k = B2.output <;> simp [S2d, E2, Function.update_apply, hk]
    · funext x; cases x <;> simp [X10, X9, X8, X7, X6, X5, X4, X3, X2, X1, X0]
  rw [efin] at t11
  rw [init_eq, halt_eq]
  have T := t1.trans (t2.trans (t3.trans (tB1.trans (t4.trans (t5.trans (tM.trans (t6.trans (t7.trans
    (t8.trans (t9.trans (tB2.trans (t10.trans t11))))))))))))
  refine ⟨_, ?_, T⟩
  simp
  omega

end MNRCombo


namespace MNRCombo
open OAI.MetricKMedian.Binary Turing MNRBridge

section volume
variable {K Λ σ : Type} [DecidableEq K] [Fintype K] {Γ : K → Type}

def pushesG : TM2.Stmt Γ Λ σ → ℕ
  | .push _ _ q => 1 + pushesG q
  | .peek _ _ q => pushesG q
  | .pop _ _ q => pushesG q
  | .load _ q => pushesG q
  | .branch _ q r => max (pushesG q) (pushesG r)
  | .goto _ => 0
  | .halt => 0

def volG (s : (k : K) → List (Γ k)) : ℕ := ∑ k, (s k).length

theorem volG_update (s : (k : K) → List (Γ k)) (k : K) (v : List (Γ k)) :
    volG (Function.update s k v) + (s k).length = volG s + v.length := by
  unfold volG
  have he : (fun j => (Function.update s k v j).length) = Function.update (fun j => (s j).length) k v.length := by
    funext j
    by_cases h : j = k
    · subst h; simp
    · rw [Function.update_of_ne h, Function.update_of_ne h]
  rw [he, Finset.sum_update_of_mem (Finset.mem_univ k)]
  have hh := Finset.sum_erase_add (Finset.univ : Finset K) (fun j => (s j).length) (Finset.mem_univ k)
  simp only [Finset.sdiff_singleton_eq_erase]
  omega

theorem stepAux_volG (q : TM2.Stmt Γ Λ σ) (v : σ) (s : (k : K) → List (Γ k)) :
    volG (TM2.stepAux q v s).stk ≤ volG s + pushesG q := by
  induction q generalizing v s with
  | push k g q ih =>
      have h := ih v (Function.update s k (g v :: s k))
      have hv := volG_update s k (g v :: s k)
      simp only [List.length_cons] at hv
      simp only [TM2.stepAux, pushesG]
      omega
  | peek k g q ih => exact ih _ _
  | pop k g q ih =>
      have h := ih (g v (s k).head?) (Function.update s k (s k).tail)
      have hv := volG_update s k (s k).tail
      have hl := List.length_tail (l := s k)
      simp only [TM2.stepAux, pushesG]
      omega
  | load g q ih => exact ih _ _
  | branch g q r ihq ihr =>
      cases hg : g v
      · simpa only [TM2.stepAux, hg, Bool.false_eq_true, Bool.cond_false, pushesG] using
          (ihr v s).trans (Nat.add_le_add_left (le_max_right (pushesG q) _) _)
      · simpa only [TM2.stepAux, hg, Bool.cond_true, pushesG] using
          (ihq v s).trans (Nat.add_le_add_left (le_max_left _ (pushesG r)) _)
  | goto g => simp only [TM2.stepAux, pushesG, Nat.add_zero, le_refl]
  | halt => simp only [TM2.stepAux, pushesG, Nat.add_zero, le_refl]

theorem trace_volG [Fintype Λ] (m : Λ → TM2.Stmt Γ Λ σ) {n : ℕ} {a b : TM2.Cfg Γ Λ σ}
    (h : Trace (TM2.step m) n a b) : volG b.stk ≤ volG a.stk + n * ∑ l, pushesG (m l) := by
  induction h with
  | refl => simp
  | @cons n a b c hs _ ih =>
    rcases a with ⟨l, v, S⟩
    cases l with
    | none => simp [TM2.step] at hs
    | some l =>
      simp only [TM2.step, Option.some.injEq] at hs
      subst hs
      have h1 := stepAux_volG (m l) v S
      have h2 : pushesG (m l) ≤ ∑ l, pushesG (m l) :=
        Finset.single_le_sum (f := fun l => pushesG (m l)) (fun l _ => Nat.zero_le _) (Finset.mem_univ l)
      simp only at ih h1 ⊢
      nlinarith
end volume

theorem outputs_length (tm : FinTM2) {l : List (tm.Γ tm.k₀)} {l' : List (tm.Γ tm.k₁)} {n : ℕ}
    (h : Trace tm.step n (initList tm l) (haltList tm l')) :
    l'.length ≤ l.length + n * @Finset.sum _ _ _ (@Finset.univ _ tm.ΛFin) (fun lb => pushesG (tm.m lb)) := by
  have := @trace_volG tm.K tm.Λ tm.σ tm.kDecidableEq tm.kFin tm.Γ tm.ΛFin tm.m n _ _ h
  have e1 : @volG tm.K tm.kFin tm.Γ (initList tm l).stk = l.length := by
    unfold volG initList
    rw [Finset.sum_eq_single tm.k₀]
    · simp
    · intro k _ hk; simp [hk]
    · simp
  have e2 : @volG tm.K tm.kFin tm.Γ (haltList tm l').stk = l'.length := by
    unfold volG haltList
    rw [Finset.sum_eq_single tm.k₁]
    · simp
    · intro k _ hk; simp [hk]
    · simp
  rw [e1, e2] at this
  exact this

theorem outputsWithin_of_trace' (M : TM2ComputableAux Sym Sym) (B1 B2 : Machine) (w out : List Sym) (N t : ℕ)
    (h : Trace (cstep M B1 B2) N (initList (ctm M B1 B2) w) (haltList (ctm M B1 B2) out)) (hN : N ≤ t) :
    CFLOutliers.OutputsWithin ⟨ctm M B1 B2, Equiv.refl Sym, Equiv.refl Sym⟩ w out t := by
  unfold CFLOutliers.OutputsWithin
  refine ⟨⟨⟨N, ?_⟩, hN⟩⟩
  show (flip bind (cstep M B1 B2))^[N] (some (initList (ctm M B1 B2) (w.map (id : Sym → Sym)))) =
    some (haltList (ctm M B1 B2) (out.map (id : Sym → Sym)))
  have e1 : @List.map Sym ((ctm M B1 B2).Γ (ctm M B1 B2).k₀) id w = w := List.map_id w
  have e2 : @List.map Sym ((ctm M B1 B2).Γ (ctm M B1 B2).k₁) id out = out := List.map_id out
  rw [e1, e2]
  exact h.iterate_eq

theorem combo {α β γ δ : Type} (e1 : α → List Sym) (e1' : β → List Sym) (f1 : α → β)
    (P1 : PolyProgram (fun a => symBits (e1 a)) (fun b => symBits (e1' b)) f1)
    (M : TM2ComputableAux Sym Sym) (cM : ℕ) (eM : γ → List Sym) (Rel : β → γ → Prop)
    (hM : ∀ a, ∃ y, Rel (f1 a) y ∧
      CFLOutliers.OutputsWithin M (e1' (f1 a)) (eM y) (cM * ((e1' (f1 a)).length + 2) ^ cM))
    (ez : δ → List Sym) (f2 : α × γ → δ)
    (P2 : PolyProgram (fun p : α × γ => symBits (e1 p.1 ++ eM p.2)) (fun d => symBits (ez d)) f2) :
    ∃ (M' : TM2ComputableAux Sym Sym) (c : ℕ), ∀ a, ∃ y, Rel (f1 a) y ∧
      CFLOutliers.OutputsWithin M' (e1 a) (ez (f2 (a, y))) (c * ((e1 a).length + 2) ^ c) := by
  set gM := @Finset.sum _ _ _ (@Finset.univ _ M.tm.ΛFin) (fun lb => pushesG (M.tm.m lb)) with hgM
  let X : Polynomial ℕ := Polynomial.X
  let Bw1 : Polynomial ℕ := P1.sizeBound.comp (2 * X)
  let BM : Polynomial ℕ := Polynomial.C cM * (Bw1 + 2) ^ cM
  let Bv : Polynomial ℕ := Bw1 + BM * Polynomial.C gM
  let B2 : Polynomial ℕ := P2.time.comp (2 * (X + Bv))
  let Bz : Polynomial ℕ := P2.sizeBound.comp (2 * (X + Bv))
  let Q : Polynomial ℕ := 4 * (X + 1) + (2 * X + 1) + P1.time.comp (2 * X) + 2 * (Bw1 + 1) + BM +
    2 * (Bv + 1) + B2 + 2 * (Bz + 1)
  obtain ⟨c, hc⟩ := MNRBridge.poly_bound Q
  refine ⟨⟨ctm M P1.machine P2.machine, Equiv.refl Sym, Equiv.refl Sym⟩, c, fun a => ?_⟩
  obtain ⟨y, hRel, ⟨⟨⟨nM, hiM⟩, hsM⟩⟩⟩ := hM a
  refine ⟨y, hRel, ?_⟩
  obtain ⟨⟨n1, hi1⟩, hs1⟩ := P1.outputs a
  obtain ⟨⟨n2, hi2⟩, hs2⟩ := P2.outputs (a, y)
  have t1 : Trace P1.machine.step n1 (P1.machine.initialCfg (symBits (e1 a)))
      (P1.machine.finalCfg (symBits (e1' (f1 a)))) := Trace.of_iterate hi1
  have t2 : Trace P2.machine.step n2 (P2.machine.initialCfg (symBits (e1 a ++ eM y)))
      (P2.machine.finalCfg (symBits (ez (f2 (a, y))))) := Trace.of_iterate hi2
  have tM : Trace (TM2.step M.tm.m) nM (initList M.tm ((e1' (f1 a)).map M.inputAlphabet.symm))
      (haltList M.tm ((eM y).map M.outputAlphabet.symm)) := Trace.of_iterate hiM
  obtain ⟨N, hN, T⟩ := combo_run (M := M) (B1 := P1.machine) (B2 := P2.machine) t1 tM t2
  refine outputsWithin_of_trace' M P1.machine P2.machine _ _ N _ T ?_
  -- bounds
  have hl1 := P1.length_bound a
  have hlM := outputs_length M.tm tM
  rw [← hgM] at hlM
  have hl2 := P2.length_bound (a, y)
  simp only [symBits_length, List.length_map, List.length_append] at hs1 hl1 hs2 hl2 hlM hsM
  set n := (e1 a).length
  set w1 := (e1' (f1 a)).length
  set lv := (eM y).length
  set lz := (ez (f2 (a, y))).length
  have eBw1 : Bw1.eval n = P1.sizeBound.eval (2 * n) := by simp [Bw1, X]
  have bw1 : w1 ≤ Bw1.eval n := by
    rw [eBw1]; omega
  have eBM : BM.eval n = cM * (Bw1.eval n + 2) ^ cM := by simp [BM]
  have eBv : Bv.eval n = Bw1.eval n + BM.eval n * gM := by simp [Bv]
  have eB2 : B2.eval n = P2.time.eval (2 * (n + Bv.eval n)) := by simp [B2, X]
  have eBz : Bz.eval n = P2.sizeBound.eval (2 * (n + Bv.eval n)) := by simp [Bz, X]
  have eP1 : (P1.time.comp (2 * X)).eval n = P1.time.eval (2 * n) := by simp [X]
  have eQ : Q.eval n = 4 * (n + 1) + (2 * n + 1) + P1.time.eval (2 * n) + 2 * (Bw1.eval n + 1) +
      BM.eval n + 2 * (Bv.eval n + 1) + B2.eval n + 2 * (Bz.eval n + 1) := by
    simp only [Q, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_one, eP1]
    simp [X]
  have bM : nM ≤ BM.eval n := by
    rw [eBM]
    have hpow : (w1 + 2) ^ cM ≤ (Bw1.eval n + 2) ^ cM := Nat.pow_le_pow_left (by omega) _
    exact hsM.trans (Nat.mul_le_mul_left _ hpow)
  have bv : lv ≤ Bv.eval n := by
    rw [eBv]
    have := Nat.mul_le_mul_right gM bM
    omega
  have b2 : n2 ≤ B2.eval n := by
    rw [eB2]
    exact hs2.trans (polynomial_eval_mono _ (by omega))
  have bz : lz ≤ Bz.eval n := by
    rw [eBz]
    have := hl2.trans (polynomial_eval_mono P2.sizeBound (show 2 * (n + lv) ≤ 2 * (n + Bv.eval n) by omega))
    omega
  refine le_trans ?_ (hc n)
  rw [hN, eQ]
  simp only [symBits_length]
  omega

end MNRCombo


namespace MNRL21
open NashAmplification.Filtering Finset MNRL22

variable {m : ℕ} {n : Fin m → ℕ}

theorem hdrs_step (u : Utility n) (hu : BoundedGame u) (hn : ∀ j, 0 < n j) (α : ℝ) (hα0 : 0 ≤ α)
    (hα1 : α ≤ 1) (X : Mixed n) (hX : AGT.IsMixedProfile X) (R : Fin m) (hXR : X R = d0)
    (hreg : ∀ i : Fin m, i ≠ R → ∀ a, AGT.expectedPayoff u (Function.update X i (dlt a)) i ≤
      AGT.expectedPayoff u X i + α)
    (b : Fin (n R)) (hbr : ∀ c, AGT.expectedPayoff u (Function.update X R (dlt c)) R ≤
      AGT.expectedPayoff u (Function.update X R (dlt b)) R) :
    DGPNash.WellSupported.IsEpsApproxNash u
      (Function.update X R (fun a => (1 / (2 - α)) * d0 a + (1 - 1 / (2 - α)) * dlt b a)) (1 / (2 - α)) := by
  set p : ℝ := 1 / (2 - α) with hp
  have h2a : 0 < 2 - α := by linarith
  have hp0 : 0 ≤ p := by positivity
  have hp1 : p ≤ 1 := by rw [hp, div_le_one h2a]; linarith
  have hq0 : 0 ≤ 1 - p := by linarith
  have hpa : p * α + (1 - p) = p := by rw [hp]; field_simp; ring
  have hXself : Function.update X R d0 = X := by rw [← hXR, Function.update_eq_self]
  have hmixL : AGT.IsLottery (fun a => p * d0 a + (1 - p) * dlt b a) := by
    have h1 := d0_lottery (hn R)
    have h2 := dlt_lottery b
    constructor
    · intro a; have := h1.1 a; have := h2.1 a; positivity
    · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, h1.2, h2.2]; ring
  have hZm := update_mixed X hX R _ (dlt_lottery b)
  refine ⟨update_mixed X hX R _ hmixL, fun i y hy => ?_⟩
  have hEX : ∀ j, AGT.expectedPayoff u (Function.update X R (fun a => p * d0 a + (1 - p) * dlt b a)) j =
      p * AGT.expectedPayoff u X j + (1 - p) * AGT.expectedPayoff u (Function.update X R (dlt b)) j := by
    intro j; rw [ep_lin, hXself]
  by_cases hiR : i = R
  · subst hiR
    rw [Function.update_idem, hEX]
    have hB := ep_lottery_le u X i y hy i _ (fun c => hbr c)
    have hB1 := (ep_bounds u hu _ hZm i).2
    have hA0 := (ep_bounds u hu _ hX i).1
    nlinarith
  · rw [Function.update_comm (Ne.symm hiR), hEX, ep_lin, Function.update_comm hiR, hXself,
      Function.update_comm hiR]
    have hI : AGT.expectedPayoff u (Function.update X i y) i ≤ AGT.expectedPayoff u X i + α :=
      ep_lottery_le u X i y hy i _ (fun a => hreg i hiR a)
    have hC1 := (ep_bounds u hu _ (update_mixed _ hZm i y hy) i).2
    have hC0 := (ep_bounds u hu _ hZm i).1
    have e1 : p * AGT.expectedPayoff u (Function.update X i y) i ≤ p * (AGT.expectedPayoff u X i + α) :=
      mul_le_mul_of_nonneg_left hI hp0
    have e2 : (1 - p) * AGT.expectedPayoff u (Function.update (Function.update X R (dlt b)) i y) i ≤
        (1 - p) * (AGT.expectedPayoff u (Function.update X R (dlt b)) i + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) hq0
    nlinarith

end MNRL21


namespace MNRL21
open NashAmplification.Filtering MNRL22

variable {r : ℕ}

def nr (G : Table (r + 1)) : ℕ := G.sizes.getD r 0
def Np (G : Table (r + 1)) : ℕ := (G.sizes.take r).prod

theorem sizes_split (G : Table (r + 1)) : G.sizes = G.sizes.take r ++ [nr G] := by
  have hl : G.sizes.length = r + 1 := G.sizes_length
  conv_lhs => rw [← List.take_append_drop r G.sizes]
  congr 1
  apply List.ext_getElem
  · simp [hl]
  · intro i h1 h2
    have hi : i = 0 := by simp at h2; omega
    subst hi
    simp [nr, List.getElem?_eq_getElem (show r < G.sizes.length by omega)]

theorem prod_split (G : Table (r + 1)) : G.sizes.prod = Np G * nr G := by
  conv_lhs => rw [sizes_split G]
  simp [Np]

theorem nr_pos (G : Table (r + 1)) : 0 < nr G := by
  have hl : r < G.sizes.length := by rw [G.sizes_length]; omega
  have := G.sizes_pos _ (List.getElem_mem hl)
  simpa [nr, List.getElem?_eq_getElem hl] using this

def subEntries (G : Table (r + 1)) : List RawRat :=
  (List.range (r * Np G)).map (fun k => G.entries.getD ((k / Np G) * G.sizes.prod + (k % Np G) * nr G) zeroRat)

def sub (G : Table (r + 1)) : Table r where
  sizes := G.sizes.take r
  sizes_length := by simp [G.sizes_length]
  sizes_pos := fun n hn => G.sizes_pos n (List.mem_of_mem_take hn)
  entries := subEntries G
  entries_length := by simp [subEntries, Np]
  bounded := by
    intro x hx
    simp only [subEntries, List.mem_map, List.mem_range] at hx
    obtain ⟨k, _, rfl⟩ := hx
    rw [List.getD_eq_getElem?_getD]
    cases h : G.entries[(k / Np G) * G.sizes.prod + (k % Np G) * nr G]? with
    | none => simp [zeroRat]
    | some e => exact G.bounded e (List.mem_of_getElem? h)

theorem sum_range_mul {M : Type*} [AddCommMonoid M] (a b : ℕ) (f : ℕ → M) :
    ∑ k ∈ Finset.range (a * b), f k = ∑ i ∈ Finset.range a, ∑ j ∈ Finset.range b, f (i * b + j) := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]

theorem cG_len (G : Table (r + 1)) : (cG G).2.length = (r + 1) * G.sizes.prod := by
  simp [cG, G.entries_length]

theorem prob_take (y : List (List ℚ)) (j a : ℕ) (hj : j < r) : prob (y.take r) j a = prob y j a := by
  simp [prob, List.getElem?_take, hj]

theorem digit_last (G : Table (r + 1)) (pos : ℕ) : digit (cG G) r pos = pos % nr G := by
  rw [digit_eq]
  simp only [digitL, cG]
  have hd : G.sizes.drop (r + 1) = [] := List.drop_of_length_le (by simp [G.sizes_length])
  rw [hd]; simp [nr]

theorem digit_sub (G : Table (r + 1)) (j p' : ℕ) (hj : j < r) :
    digit (cG G) j (p' * nr G) = digit (cG (sub G)) j p' := by
  rw [digit_eq, digit_eq]
  simp only [digitL, cG, sub]
  have hs : (G.sizes.drop (j + 1)).prod = ((G.sizes.take r).drop (j + 1)).prod * nr G := by
    conv_lhs => rw [sizes_split G]
    rw [List.drop_append_of_le_length (by simp [G.sizes_length]; omega)]
    simp
  rw [hs, Nat.mul_div_mul_right _ _ (nr_pos G)]
  congr 1
  simp [List.getElem?_take, hj]

theorem weight_split (G : Table (r + 1)) (y : List (List ℚ)) (pos : ℕ) :
    weight (cG G) y pos = ((List.range r).map (fun j => prob y j (digit (cG G) j pos))).prod *
      prob y r (digit (cG G) r pos) := by
  unfold weight
  rw [show (cG G).1.length = r + 1 by simp [cG, G.sizes_length], List.range_succ, List.map_append,
    List.prod_append]
  simp

theorem weight_sub (G : Table (r + 1)) (y : List (List ℚ)) (p' : ℕ) :
    weight (cG (sub G)) (y.take r) p' = ((List.range r).map (fun j => prob y j (digit (cG G) j (p' * nr G)))).prod := by
  unfold weight
  rw [show (cG (sub G)).1.length = r by simp [cG, sub, G.sizes_length]]
  congr 1
  refine List.map_congr_left (fun j hj => ?_)
  have hj' : j < r := List.mem_range.1 hj
  rw [prob_take y j _ hj', digit_sub G j p' hj']

theorem payoff_sub (G : Table (r + 1)) (hr : 1 ≤ r) (y : List (List ℚ))
    (hy : ∀ t, t < nr G → prob y r t = if t = 0 then 1 else 0) (i : ℕ) (hi : i < r) :
    payoff (cG G) y i = payoff (cG (sub G)) (y.take r) i := by
  have hN := NOf_eq G (by omega)
  have hN' := NOf_eq (sub G) hr
  have hNsplit := prod_split G
  have hlenc := cG_len G
  unfold payoff
  rw [show cG G = (G.sizes, G.entries.map valQ) from rfl] at hlenc ⊢
  rw [show cG (sub G) = ((sub G).sizes, (sub G).entries.map valQ) from rfl]
  rw [hN, hN']
  rw [rng_eq _ _ (by rw [hlenc]; exact Nat.le_mul_of_pos_left _ (by omega)),
    rng_eq _ _ (by simp [sub, subEntries, Np]; exact Nat.le_mul_of_pos_left _ (by omega))]
  rw [list_sum_range, list_sum_range]
  rw [show (sub G).sizes.prod = Np G from rfl, hNsplit, sum_range_mul]
  refine Finset.sum_congr rfl (fun p' hp' => ?_)
  rw [Finset.sum_eq_single 0]
  · simp only [add_zero]
    have hp'N : p' < Np G := Finset.mem_range.1 hp'
    have hw : weight (G.sizes, G.entries.map valQ) y (p' * nr G) =
        weight ((sub G).sizes, (sub G).entries.map valQ) (y.take r) p' := by
      show weight (cG G) y (p' * nr G) = weight (cG (sub G)) (y.take r) p'
      rw [weight_split, weight_sub, digit_last, Nat.mul_mod_left, hy 0 (nr_pos G)]
      simp
    rw [hw]
    congr 1
    have hk : i * (Np G * nr G) + p' * nr G < G.entries.length := by
      rw [G.entries_length, hNsplit]
      have : i * (Np G * nr G) + p' * nr G < (i + 1) * (Np G * nr G) := by nlinarith [nr_pos G]
      calc _ < (i + 1) * (Np G * nr G) := this
        _ ≤ (r + 1) * (Np G * nr G) := Nat.mul_le_mul_right _ (by omega)
    have hk' : i * Np G + p' < (subEntries G).length := by
      simp [subEntries]; nlinarith
    simp only [sub, List.getElem?_map, List.getElem?_eq_getElem hk, List.getElem?_eq_getElem hk',
      Option.map_some, Option.getD_some]
    congr 1
    simp only [subEntries, List.getElem_map, List.getElem_range]
    have hNp : 0 < Np G := by omega
    rw [Nat.add_comm (i * Np G) p', Nat.add_mul_div_right _ _ hNp, Nat.div_eq_of_lt hp'N, zero_add,
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hp'N, hNsplit, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hk, Option.getD_some]
  · intro t ht ht0
    have htn : t < nr G := Finset.mem_range.1 ht
    have hw : weight (G.sizes, G.entries.map valQ) y (p' * nr G + t) = 0 := by
      show weight (cG G) y (p' * nr G + t) = 0
      rw [weight_split, digit_last, show (p' * nr G + t) % nr G = t by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt htn], hy t htn, if_neg ht0, mul_zero]
    rw [hw, zero_mul]
  · intro h; exact absurd (Finset.mem_range.2 (nr_pos G)) h

end MNRL21


namespace MNRL21
open NashAmplification.Filtering MNRL22
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

theorem poly_list_take {α : Type} [Coding α] [Inhabited α] :
    Poly (fun x : List α × ℕ => x.1.take x.2) := ⟨PolyProgram.listTake enc default⟩
@[fun_prop] theorem list_take_comp {γ β : Type} [Coding γ] [Coding β] [Inhabited β] {f : γ → List β}
    {g : γ → ℕ} (hf : Poly f) (hg : Poly g) : Poly (fun x => (f x).take (g x)) :=
  Poly.comp poly_list_take (Poly.pair hf hg)

/-- numeric value of an item `[num, den, 0]`. -/
def itVal (it : List ℕ) : ℚ := ((it[0]?.getD 0 : ℕ) : ℚ) / ((it[1]?.getD 0 : ℕ) : ℚ)

theorem poly_itVal : Poly itVal := by unfold itVal; fun_prop
@[fun_prop] theorem itVal_comp {γ : Type} [Coding γ] {f : γ → List ℕ} (hf : Poly f) :
    Poly (fun x => itVal (f x)) := Poly.comp (f := itVal) poly_itVal hf

noncomputable def natOfQ (q : ℚ) : ℕ := q.num.natAbs
theorem poly_natOfQ : Poly natOfQ := by unfold natOfQ; fun_prop
@[fun_prop] theorem natOfQ_comp {γ : Type} [Coding γ] {f : γ → ℚ} (hf : Poly f) :
    Poly (fun x => natOfQ (f x)) := Poly.comp (f := natOfQ) poly_natOfQ hf

/-- the parsed data: sizes of `G`, entries of `G`, entries of `x'` -/
noncomputable def pSizes (r : ℕ) (items : List (List ℕ)) : List ℕ :=
  (items.take (r + 1)).map (fun it => it.head?.getD 0)
noncomputable def pN (r : ℕ) (items : List (List ℕ)) : ℕ :=
  natOfQ (((pSizes r items).map (fun n : ℕ => (n : ℚ))).prod)
noncomputable def pGE (r : ℕ) (items : List (List ℕ)) : List (List ℕ) :=
  (items.drop (r + 1)).take ((r + 1) * pN r items)
noncomputable def pXE (r : ℕ) (items : List (List ℕ)) : List (List ℕ) :=
  (items.drop (r + 1 + (r + 1) * pN r items)).drop r
noncomputable def pCtx (r : ℕ) (items : List (List ℕ)) : Ctx :=
  (pSizes r items, (pGE r items).map itVal)
noncomputable def pOff (r : ℕ) (items : List (List ℕ)) (j : ℕ) : ℕ :=
  natOfQ ((((pSizes r items).take j).map (fun n : ℕ => (n : ℚ))).sum)
noncomputable def pRows (r : ℕ) (items : List (List ℕ)) : List (List ℚ) :=
  (List.range r).map (fun j => (rng (pCtx r items) ((pSizes r items)[j]?.getD 0)).map
    (fun a => itVal ((pXE r items)[pOff r items j + a]?.getD [])))
noncomputable def pProf (r : ℕ) (items : List (List ℕ)) (cc : ℕ) : List (List ℚ) :=
  pRows r items ++ [pureRow (pCtx r items) r cc]
noncomputable def pVals (r : ℕ) (items : List (List ℕ)) : List ℚ :=
  (rng (pCtx r items) ((pSizes r items)[r]?.getD 0)).map (fun cc => payoff (pCtx r items) (pProf r items cc) r)
noncomputable def pB (r : ℕ) (items : List (List ℕ)) : ℕ :=
  (pVals r items).findIdx (fun v => (pVals r items).all (fun v' => decide (v' ≤ v)))
def mixA (pp : ℚ) (b a : ℕ) : ℚ := (if a = 0 then pp else 0) + (if a = b then 1 - pp else 0)
noncomputable def pRow (r : ℕ) (pp : ℚ) (items : List (List ℕ)) : List ℚ :=
  (rng (pCtx r items) ((pSizes r items)[r]?.getD 0)).map (fun a => mixA pp (pB r items) a)
noncomputable def postF (r : ℕ) (pp : ℚ) (items : List (List ℕ)) : List (List ℕ) :=
  (pSizes r items).map (fun n => [n]) ++ pXE r items ++
    (pRow r pp items).map (fun q => [q.num.natAbs, q.den, 0])

theorem poly_pSizes (r : ℕ) : Poly (pSizes r) := by unfold pSizes; fun_prop
@[fun_prop] theorem pSizes_comp (r : ℕ) {γ : Type} [Coding γ] {f : γ → List (List ℕ)} (hf : Poly f) :
    Poly (fun x => pSizes r (f x)) := Poly.comp (f := pSizes r) (poly_pSizes r) hf
theorem poly_pN (r : ℕ) : Poly (pN r) := by unfold pN; fun_prop
@[fun_prop] theorem pN_comp (r : ℕ) {γ : Type} [Coding γ] {f : γ → List (List ℕ)} (hf : Poly f) :
    Poly (fun x => pN r (f x)) := Poly.comp (f := pN r) (poly_pN r) hf
theorem poly_pGE (r : ℕ) : Poly (pGE r) := by unfold pGE; fun_prop
theorem poly_pXE (r : ℕ) : Poly (pXE r) := by unfold pXE; fun_prop
@[fun_prop] theorem pGE_comp (r : ℕ) {γ : Type} [Coding γ] {f : γ → List (List ℕ)} (hf : Poly f) :
    Poly (fun x => pGE r (f x)) := Poly.comp (f := pGE r) (poly_pGE r) hf
@[fun_prop] theorem pXE_comp (r : ℕ) {γ : Type} [Coding γ] {f : γ → List (List ℕ)} (hf : Poly f) :
    Poly (fun x => pXE r (f x)) := Poly.comp (f := pXE r) (poly_pXE r) hf
theorem poly_pCtx (r : ℕ) : Poly (pCtx r) := by unfold pCtx; fun_prop
@[fun_prop] theorem pCtx_comp (r : ℕ) {γ : Type} [Coding γ] {f : γ → List (List ℕ)} (hf : Poly f) :
    Poly (fun x => pCtx r (f x)) := Poly.comp (f := pCtx r) (poly_pCtx r) hf
theorem poly_pOff (r : ℕ) : Poly (fun x : List (List ℕ) × ℕ => pOff r x.1 x.2) := by unfold pOff; fun_prop
@[fun_prop] theorem pOff_comp (r : ℕ) {γ : Type} [Coding γ] {f : γ → List (List ℕ)} {g : γ → ℕ}
    (hf : Poly f) (hg : Poly g) : Poly (fun x => pOff r (f x) (g x)) :=
  Poly.comp (f := fun x : List (List ℕ) × ℕ => pOff r x.1 x.2) (poly_pOff r) (Poly.pair hf hg)
theorem poly_pRows (r : ℕ) : Poly (pRows r) := by unfold pRows; fun_prop

@[fun_prop] theorem pRows_comp (r : ℕ) {γ : Type} [Coding γ] {f : γ → List (List ℕ)} (hf : Poly f) :
    Poly (fun x => pRows r (f x)) := Poly.comp (f := pRows r) (poly_pRows r) hf
theorem poly_pProf (r : ℕ) : Poly (fun x : List (List ℕ) × ℕ => pProf r x.1 x.2) := by unfold pProf; fun_prop
theorem poly_pVals (r : ℕ) : Poly (pVals r) := by
  unfold pVals
  refine Poly.list_map (f := fun items cc => payoff (pCtx r items) (pProf r items cc) r) ?_ ?_
  · exact payoff_comp (pCtx_comp r Poly.fst)
      (Poly.comp (f := fun x : List (List ℕ) × ℕ => pProf r x.1 x.2) (poly_pProf r) Poly.identity)
      (Automatic.Poly.const _)
  · fun_prop
theorem poly_pB (r : ℕ) : Poly (pB r) := by
  unfold pB
  refine Poly.list_findIdx (f := fun (x : List (List ℕ)) (v : ℚ) => (pVals r x).all (fun v' => decide (v' ≤ v)))
    ?_ (poly_pVals r)
  refine MNRL22.list_all (f := fun (p : List (List ℕ) × ℚ) (v' : ℚ) => decide (v' ≤ p.2)) ?_ ?_
  · exact Poly.rat_le_comp (Poly.comp Poly.snd Poly.identity) (Poly.comp Poly.snd Poly.fst)
  · exact Poly.comp (f := pVals r) (poly_pVals r) Poly.fst
@[fun_prop] theorem pB_comp (r : ℕ) {γ : Type} [Coding γ] {f : γ → List (List ℕ)} (hf : Poly f) :
    Poly (fun x => pB r (f x)) := Poly.comp (f := pB r) (poly_pB r) hf
theorem poly_pRow (r : ℕ) (pp : ℚ) : Poly (pRow r pp) := by unfold pRow mixA; fun_prop
@[fun_prop] theorem pRow_comp (r : ℕ) (pp : ℚ) {γ : Type} [Coding γ] {f : γ → List (List ℕ)} (hf : Poly f) :
    Poly (fun x => pRow r pp (f x)) := Poly.comp (f := pRow r pp) (poly_pRow r pp) hf
theorem poly_postF (r : ℕ) (pp : ℚ) : Poly (postF r pp) := by unfold postF; fun_prop

noncomputable def pNp (r : ℕ) (items : List (List ℕ)) : ℕ :=
  natOfQ ((((pSizes r items).take r).map (fun n : ℕ => (n : ℚ))).prod)
noncomputable def subF (r : ℕ) (items : List (List ℕ)) : List (List ℕ) :=
  ((pSizes r items).take r).map (fun n => [n]) ++
    (rng (pCtx r items) (r * pNp r items)).map (fun k =>
      (pGE r items)[(k / pNp r items) * pN r items + (k % pNp r items) * ((pSizes r items)[r]?.getD 0)]?.getD
        [0, 1, 0])

theorem poly_pNp (r : ℕ) : Poly (pNp r) := by unfold pNp; fun_prop
@[fun_prop] theorem pNp_comp (r : ℕ) {γ : Type} [Coding γ] {f : γ → List (List ℕ)} (hf : Poly f) :
    Poly (fun x => pNp r (f x)) := Poly.comp (f := pNp r) (poly_pNp r) hf
theorem poly_subF (r : ℕ) : Poly (subF r) := by unfold subF; fun_prop

end MNRL21


namespace MNRL21
open NashAmplification.Filtering MNRL22

variable {r : ℕ}

def item (e : RawRat) : List ℕ := [e.num, e.den, 0]

def itemsOfP {k : ℕ} (x : RawProfile k) : List (List ℕ) :=
  x.sizes.map (fun n => [n]) ++ x.entries.map item

theorem itemsOf_eq {k : ℕ} (G : Table k) : itemsOf G = G.sizes.map (fun n => [n]) ++ G.entries.map item := rfl

theorem itVal_item (e : RawRat) : itVal (item e) = valQ e := by simp [itVal, item, valQ]

theorem pSizes_eq (G : Table (r + 1)) (rest : List (List ℕ)) : pSizes r (itemsOf G ++ rest) = G.sizes := by
  unfold pSizes
  rw [itemsOf_eq, List.append_assoc, List.take_append_of_le_length (by simp [G.sizes_length]),
    List.take_of_length_le (by simp [G.sizes_length])]
  simp [List.map_map, Function.comp_def]

theorem natOfQ_prod (L : List ℕ) : natOfQ ((L.map (fun n : ℕ => (n : ℚ))).prod) = L.prod := by
  unfold natOfQ; rw [← Nat.cast_list_prod, Rat.num_natCast, Int.natAbs_natCast]

theorem natOfQ_sum (L : List ℕ) : natOfQ ((L.map (fun n : ℕ => (n : ℚ))).sum) = L.sum := by
  unfold natOfQ; rw [← Nat.cast_list_sum, Rat.num_natCast, Int.natAbs_natCast]

theorem pN_eq (G : Table (r + 1)) (rest : List (List ℕ)) : pN r (itemsOf G ++ rest) = G.sizes.prod := by
  unfold pN; rw [pSizes_eq, natOfQ_prod]

theorem pGE_eq (G : Table (r + 1)) (rest : List (List ℕ)) : pGE r (itemsOf G ++ rest) = G.entries.map item := by
  unfold pGE
  rw [pN_eq, itemsOf_eq, List.append_assoc, List.drop_append_of_le_length (by simp [G.sizes_length]),
    List.drop_of_length_le (by simp [G.sizes_length]), List.nil_append,
    List.take_append_of_le_length (by simp [G.entries_length]),
    List.take_of_length_le (by simp [G.entries_length])]

theorem pXE_eq (G : Table (r + 1)) (x : RawProfile r) : pXE r (itemsOf G ++ itemsOfP x) = x.entries.map item := by
  unfold pXE
  rw [pN_eq, itemsOf_eq, List.drop_left' (by simp [G.sizes_length, G.entries_length]), itemsOfP,
    List.drop_left' (by simp [x.sizes_length])]

theorem pCtx_eq (G : Table (r + 1)) (rest : List (List ℕ)) : pCtx r (itemsOf G ++ rest) = cG G := by
  unfold pCtx; rw [pSizes_eq, pGE_eq]
  simp [cG, List.map_map, Function.comp_def, itVal_item]

theorem subF_eq (G : Table (r + 1)) : subF r (itemsOf G) = itemsOf (sub G) := by
  have hI : itemsOf G = itemsOf G ++ [] := (List.append_nil _).symm
  unfold subF
  rw [hI, pSizes_eq, pCtx_eq, pGE_eq, pN_eq]
  have hNp : pNp r (itemsOf G ++ []) = Np G := by unfold pNp; rw [pSizes_eq, natOfQ_prod]; rfl
  have hle : r * Np G ≤ (cG G).2.length := by
    rw [cG_len, prod_split]
    calc r * Np G ≤ r * (Np G * nr G) := Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ (nr_pos G))
      _ ≤ (r + 1) * (Np G * nr G) := Nat.mul_le_mul_right _ (by omega)
  rw [hNp, rng_eq _ _ hle]
  rw [itemsOf_eq (sub G)]
  congr 1
  simp only [sub, subEntries, List.map_map]
  refine List.map_congr_left (fun k _ => ?_)
  simp only [Function.comp_apply, List.getElem?_map, List.getD_eq_getElem?_getD]
  have hnr : G.sizes[r]?.getD 0 = nr G := rfl
  rw [hnr]
  cases G.entries[k / Np G * G.sizes.prod + k % Np G * nr G]? <;> rfl

theorem encProfile_hIn {k : ℕ} (x : RawProfile k) :
    (encProfile x).flatMap hIn = (OAI.MetricKMedian.Binary.Automatic.enc (itemsOfP x) : List Bool) := by
  show _ = OAI.MetricKMedian.Binary.encodeList (OAI.MetricKMedian.Binary.encodeList Nat.bits) (itemsOfP x)
  simp only [encProfile, pack, itemsOfP, encodeList_eq, List.flatMap_append, List.flatMap_map,
    List.flatMap_assoc, item]
  congr 1
  · refine List.flatMap_congr (fun n _ => ?_)
    simp [encNat_eq, bitsMap_hIn, quote_eq, escAll_append, hIn]
    simp [escAll]
  · refine List.flatMap_congr (fun r _ => ?_)
    simp [encRaw, pack, encNat_eq, bitsMap_hIn, quote_eq, escAll_append, hIn]
    simp [escAll]

theorem Tin_concat (G : Table (r + 1)) (x : RawProfile r) :
    Tin.run none (MNRBridge.symBits (encGame G ++ encProfile x)) =
      (OAI.MetricKMedian.Binary.Automatic.enc (itemsOf G ++ itemsOfP x) : List Bool) := by
  rw [Tin_run, List.flatMap_append, encGame_hIn, encProfile_hIn]
  show _ = OAI.MetricKMedian.Binary.encodeList (OAI.MetricKMedian.Binary.encodeList Nat.bits) (itemsOf G ++ itemsOfP x)
  rw [OAI.MetricKMedian.Binary.EncodedList.append]; rfl

theorem encGame_pack {k : ℕ} (G : Table k) : encGame G = packItems (itemsOf G) := by
  simp only [packItems, itemsOf, encGame, pack, List.flatMap_append, List.flatMap_map]
  congr 1
  · refine List.flatMap_congr (fun n _ => ?_); simp
  · refine List.flatMap_congr (fun q _ => ?_)
    simp [encRaw, pack, encNat_zero, List.intercalate_cons_cons]

end MNRL21


namespace MNRL21
open NashAmplification.Filtering MNRL22

variable {r : ℕ}

theorem prob_append_lt (L : List (List ℚ)) (v : List ℚ) (j a : ℕ) (hj : j < L.length) :
    prob (L ++ [v]) j a = prob L j a := by
  simp [prob, List.getElem?_append_left hj]

theorem prob_append_eq (L : List (List ℚ)) (v : List ℚ) (a : ℕ) :
    prob (L ++ [v]) L.length a = v[a]?.getD 0 := by
  simp [prob]

theorem prob_set_eq (L : List (List ℚ)) (i : ℕ) (v : List ℚ) (a : ℕ) (hi : i < L.length) :
    prob (L.set i v) i a = v[a]?.getD 0 := by
  simp [prob, List.getElem?_set_self hi]

theorem prob_set_ne (L : List (List ℚ)) (i j : ℕ) (v : List ℚ) (a : ℕ) (hij : j ≠ i) :
    prob (L.set i v) j a = prob L j a := by
  simp [prob, List.getElem?_set_ne (Ne.symm hij)]

theorem pRows_len (G : Table (r + 1)) (rest : List (List ℕ)) : (pRows r (itemsOf G ++ rest)).length = r := by
  simp [pRows]

theorem valQ_getD (L : List RawRat) (k : ℕ) :
    itVal ((L.map item)[k]?.getD []) = valQ (L.getD k zeroRat) := by
  rw [List.getElem?_map, List.getD_eq_getElem?_getD]
  cases L[k]? with
  | none => simp [itVal, valQ, zeroRat]
  | some e => simp [itVal_item]

theorem valQ_cast (e : RawRat) : ((valQ e : ℚ) : ℝ) = e.value := by
  simp [valQ, RawRat.value]

theorem off_eq (G : Table (r + 1)) (x : RawProfile r) (hxs : x.sizes = (sub G).sizes) (j : ℕ) (hj : j ≤ r) :
    pOff r (itemsOf G ++ itemsOfP x) j = (x.sizes.take j).sum := by
  unfold pOff; rw [pSizes_eq, natOfQ_sum, hxs]
  simp [sub, List.take_take, Nat.min_eq_left hj]

theorem prob_pRows (G : Table (r + 1)) (hr : 1 ≤ r) (x : RawProfile r) (hxs : x.sizes = (sub G).sizes)
    (j : ℕ) (hj : j < r) (a : ℕ) (ha : a < G.sizes.getD j 0) :
    ((prob (pRows r (itemsOf G ++ itemsOfP x)) j a : ℚ) : ℝ) = x.at j a := by
  have hjr : j < (List.range r).length := by simpa using hj
  unfold pRows
  rw [prob_rows _ _ _ _ hj, pCtx_eq, pSizes_eq]
  have hnle : G.sizes.getD j 0 ≤ (cG G).2.length := by
    have hjs : j < G.sizes.length := by rw [G.sizes_length]; omega
    have := counts_le G (by omega) ⟨j, by omega⟩
    simpa [Table.counts] using this
  rw [show G.sizes[j]?.getD 0 = G.sizes.getD j 0 by simp [List.getD_eq_getElem?_getD]]
  rw [rng_eq _ _ hnle]
  simp only [List.getElem?_map, List.getElem?_range ha, Option.map_some, Option.getD_some]
  rw [pXE_eq, valQ_getD, off_eq G x hxs j (by omega), valQ_cast]
  rfl

noncomputable def Xp (G : Table (r + 1)) (x : RawProfile r) : Mixed G.counts :=
  fun j a => if j.val < r then x.at j.val a.val else d0 a

theorem counts_val (G : Table (r + 1)) (j : Fin (r + 1)) : G.counts j = G.sizes.getD j.val 0 := rfl

theorem prob_pProf (G : Table (r + 1)) (hr : 1 ≤ r) (x : RawProfile r) (hxs : x.sizes = (sub G).sizes)
    (cc : Fin (G.counts (Fin.last r))) :
    (fun (j : Fin (r + 1)) (a : Fin (G.counts j)) =>
      ((prob (pProf r (itemsOf G ++ itemsOfP x) cc.val) j a : ℚ) : ℝ)) =
      Function.update (Xp G x) (Fin.last r) (dlt cc) := by
  funext j a
  unfold pProf
  by_cases hj : j = Fin.last r
  · subst hj
    simp only [Function.update_self, dlt]
    have hl := pRows_len G (itemsOfP x)
    rw [show (Fin.last r).val = (pRows r (itemsOf G ++ itemsOfP x)).length by simp [hl], prob_append_eq,
      pCtx_eq]
    have := pureRow_get G (by omega) (Fin.last r) cc.val a
    simp only [Fin.val_last] at this ⊢
    rw [this]
    simp only [Fin.ext_iff]
    split_ifs <;> simp
  · rw [Function.update_of_ne hj]
    have hjr : j.val < r := by
      have := j.isLt; have : j.val ≠ r := fun e => hj (Fin.ext (by simp [e])); omega
    rw [prob_append_lt _ _ _ _ (by rw [pRows_len]; exact hjr),
      prob_pRows G hr x hxs j.val hjr a.val (by rw [← counts_val]; exact a.isLt)]
    simp [Xp, hjr]

theorem sub_counts (G : Table (r + 1)) (j : Fin r) : (sub G).counts j = G.counts (Fin.castSucc j) := by
  simp [Table.counts, sub, List.getD_eq_getElem?_getD, List.getElem?_take, j.isLt]

theorem Xp_mixed (G : Table (r + 1)) (x : RawProfile r) (α : ℝ)
    (hx : DGPNash.WellSupported.IsEpsApproxNash (sub G).utility (x.on (sub G).counts) α) :
    AGT.IsMixedProfile (Xp G x) := by
  intro j
  by_cases hjr : j.val < r
  · have hl := hx.1 ⟨j.val, hjr⟩
    have hc : (sub G).counts ⟨j.val, hjr⟩ = G.counts j := by
      rw [sub_counts]; rfl
    have e : Xp G x j = fun a => x.at j.val a.val := by funext a; simp [Xp, hjr]
    rw [e]
    constructor
    · intro a
      have := hl.1 ⟨a.val, by rw [hc]; exact a.isLt⟩
      simpa [RawProfile.on] using this
    · have h2 := hl.2
      simp only [RawProfile.on] at h2
      rw [Fin.sum_univ_eq_sum_range (fun a => x.at j.val a)] at h2 ⊢
      rw [hc] at h2
      exact h2
  · have e : Xp G x j = d0 := by funext a; simp [Xp, hjr]
    rw [e]; exact d0_lottery (counts_pos G j)

theorem findIdx_argmax (c : Ctx) (n : ℕ) (hpos : 0 < n) (hle : n ≤ c.2.length) (g : ℕ → ℚ) :
    let V := (rng c n).map g
    V.findIdx (fun v => V.all (fun v' => decide (v' ≤ v))) < n ∧
      ∀ cc, cc < n → g cc ≤ g (V.findIdx (fun v => V.all (fun v' => decide (v' ≤ v)))) := by
  intro V
  have hV : V = (List.range n).map g := by simp only [V]; rw [rng_eq c n hle]
  obtain ⟨i, hi, himax⟩ := Finset.exists_max_image (Finset.range n) g ⟨0, Finset.mem_range.2 hpos⟩
  have hex : ∃ v ∈ V, (V.all (fun v' => decide (v' ≤ v))) = true := by
    refine ⟨g i, ?_, ?_⟩
    · rw [hV]; exact List.mem_map.2 ⟨i, List.mem_range.2 (Finset.mem_range.1 hi), rfl⟩
    · rw [List.all_eq_true, hV]
      intro v hv
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hv
      simpa using himax j (Finset.mem_range.2 (List.mem_range.1 hj))
  have hlt := List.findIdx_lt_length_of_exists hex
  have hP := List.findIdx_getElem (w := hlt)
  have hlen : V.length = n := by rw [hV]; simp
  refine ⟨by rw [← hlen]; exact hlt, fun cc hcc => ?_⟩
  rw [List.all_eq_true] at hP
  have hmem : g cc ∈ V := by rw [hV]; exact List.mem_map.2 ⟨cc, List.mem_range.2 hcc, rfl⟩
  have h1 := hP (g cc) hmem
  simp only [decide_eq_true_eq] at h1
  have h2 : V[V.findIdx (fun v => V.all (fun v' => decide (v' ≤ v)))] =
      g (V.findIdx (fun v => V.all (fun v' => decide (v' ≤ v)))) := by
    simp only [hV, List.getElem_map, List.getElem_range]
  rw [h2] at h1
  exact h1

theorem pB_spec (G : Table (r + 1)) (hr : 1 ≤ r) (x : RawProfile r) (hxs : x.sizes = (sub G).sizes) :
    pB r (itemsOf G ++ itemsOfP x) < G.counts (Fin.last r) ∧
      ∀ cc : Fin (G.counts (Fin.last r)),
        AGT.expectedPayoff G.utility (Function.update (Xp G x) (Fin.last r) (dlt cc)) (Fin.last r) ≤
          AGT.expectedPayoff G.utility (Function.update (Xp G x) (Fin.last r)
            (dlt (⟨pB r (itemsOf G ++ itemsOfP x), by
              have := findIdx_argmax (cG G) (G.counts (Fin.last r)) (counts_pos G _)
                (counts_le G (by omega) _) (fun cc => payoff (cG G) (pProf r (itemsOf G ++ itemsOfP x) cc) r)
              simp only [pB, pVals, pCtx_eq, pSizes_eq]
              exact this.1⟩ : Fin (G.counts (Fin.last r))))) (Fin.last r) := by
  have hA := findIdx_argmax (cG G) (G.counts (Fin.last r)) (counts_pos G _)
    (counts_le G (by omega) _) (fun cc => payoff (cG G) (pProf r (itemsOf G ++ itemsOfP x) cc) r)
  have hpB : pB r (itemsOf G ++ itemsOfP x) =
      ((rng (cG G) (G.counts (Fin.last r))).map (fun cc => payoff (cG G) (pProf r (itemsOf G ++ itemsOfP x) cc) r)).findIdx
        (fun v => ((rng (cG G) (G.counts (Fin.last r))).map
          (fun cc => payoff (cG G) (pProf r (itemsOf G ++ itemsOfP x) cc) r)).all (fun v' => decide (v' ≤ v))) := by
    simp only [pB, pVals, pCtx_eq, pSizes_eq]; rfl
  refine ⟨by rw [hpB]; exact hA.1, fun cc => ?_⟩
  have h1 := hA.2 cc.val cc.isLt
  rw [← hpB] at h1
  have h2 : ((payoff (cG G) (pProf r (itemsOf G ++ itemsOfP x) cc.val) r : ℚ) : ℝ) ≤
      ((payoff (cG G) (pProf r (itemsOf G ++ itemsOfP x) (pB r (itemsOf G ++ itemsOfP x))) r : ℚ) : ℝ) := by
    exact_mod_cast h1
  have e1 := payoff_eq G (by omega) (pProf r (itemsOf G ++ itemsOfP x) cc.val) (Fin.last r)
  have e2 := payoff_eq G (by omega) (pProf r (itemsOf G ++ itemsOfP x) (pB r (itemsOf G ++ itemsOfP x))) (Fin.last r)
  simp only [Fin.val_last] at e1 e2
  rw [show (G.sizes, G.entries.map valQ) = cG G from rfl] at e1 e2
  rw [e1, e2, prob_pProf G hr x hxs cc] at h2
  rw [prob_pProf G hr x hxs ⟨pB r (itemsOf G ++ itemsOfP x), by rw [hpB]; exact hA.1⟩] at h2
  exact h2

theorem prob_rows_sub (G : Table (r + 1)) (hr : 1 ≤ r) (x : RawProfile r) (hxs : x.sizes = (sub G).sizes) :
    (fun (j : Fin r) (b : Fin ((sub G).counts j)) =>
      ((prob (pRows r (itemsOf G ++ itemsOfP x)) j b : ℚ) : ℝ)) = x.on (sub G).counts := by
  funext j b
  have hb : b.val < G.sizes.getD j.val 0 := lt_of_lt_of_eq b.isLt (sub_counts G j)
  rw [prob_pRows G hr x hxs j.val j.isLt b.val hb]; rfl

theorem prob_Xp (G : Table (r + 1)) (hr : 1 ≤ r) (x : RawProfile r) (hxs : x.sizes = (sub G).sizes) :
    (fun (j : Fin (r + 1)) (a : Fin (G.counts j)) =>
      ((prob (pRows r (itemsOf G ++ itemsOfP x) ++ [pureRow (cG G) r 0]) j a : ℚ) : ℝ)) = Xp G x := by
  funext j a
  by_cases hj : j.val < r
  · rw [prob_append_lt _ _ _ _ (by rw [pRows_len]; exact hj),
      prob_pRows G hr x hxs j.val hj a.val (by rw [← counts_val]; exact a.isLt)]
    simp [Xp, hj]
  · have hjr : j = Fin.last r := Fin.ext (by have := j.isLt; simp; omega)
    subst hjr
    have hl := pRows_len G (itemsOfP x)
    rw [show (Fin.last r).val = (pRows r (itemsOf G ++ itemsOfP x)).length by simp [hl], prob_append_eq]
    have := pureRow_get G (by omega) (Fin.last r) 0 a
    simp only [Fin.val_last] at this ⊢
    rw [this]
    simp only [Xp, Fin.val_last, lt_irrefl, if_false, d0]
    split_ifs <;> simp

theorem hreg_21 (G : Table (r + 1)) (hr : 1 ≤ r) (x : RawProfile r) (hxs : x.sizes = (sub G).sizes)
    (α : ℝ) (hx : DGPNash.WellSupported.IsEpsApproxNash (sub G).utility (x.on (sub G).counts) α)
    (i : Fin (r + 1)) (hi : i ≠ Fin.last r) (a : Fin (G.counts i)) :
    AGT.expectedPayoff G.utility (Function.update (Xp G x) i (dlt a)) i ≤
      AGT.expectedPayoff G.utility (Xp G x) i + α := by
  have hir : i.val < r := by
    have := i.isLt; have : i.val ≠ r := fun e => hi (Fin.ext (by simp [e])); omega
  set items := itemsOf G ++ itemsOfP x
  set rows := pRows r items
  have hrl : rows.length = r := pRows_len G _
  set yA := rows.set i.val (pureRow (cG G) i.val a.val) ++ [pureRow (cG G) r 0]
  -- yA realizes the deviation
  have hyA : (fun (j : Fin (r + 1)) (b : Fin (G.counts j)) => ((prob yA j b : ℚ) : ℝ)) =
      Function.update (Xp G x) i (dlt a) := by
    funext j b
    by_cases hji : j = i
    · subst hji
      simp only [Function.update_self, dlt]
      rw [prob_append_lt _ _ _ _ (by simp [hrl, hir]), prob_set_eq _ _ _ _ (by rw [hrl]; exact hir),
        pureRow_get G (by omega)]
      simp only [Fin.ext_iff]; split_ifs <;> simp
    · rw [Function.update_of_ne hji]
      have hne : j.val ≠ i.val := fun e => hji (Fin.ext e)
      by_cases hj : j.val < r
      · rw [prob_append_lt _ _ _ _ (by simp [hrl, hj]), prob_set_ne _ _ _ _ _ hne]
        have := congrFun (congrFun (prob_Xp G hr x hxs) j) b
        rw [prob_append_lt _ _ _ _ (by rw [hrl]; exact hj)] at this
        exact this
      · have := congrFun (congrFun (prob_Xp G hr x hxs) j) b
        have hjr : j.val = rows.length := by rw [hrl]; have := j.isLt; omega
        rw [show j.val = (rows.set i.val (pureRow (cG G) i.val a.val)).length by simp [hjr],
          prob_append_eq]
        rw [show j.val = rows.length from hjr, prob_append_eq] at this
        exact this
  have hyr : ∀ t, t < nr G → prob yA r t = if t = 0 then 1 else 0 := by
    intro t ht
    rw [show r = (rows.set i.val (pureRow (cG G) i.val a.val)).length by simp [hrl], prob_append_eq]
    have := pureRow_get G (by omega) (Fin.last r) 0 ⟨t, by rw [counts_val]; exact ht⟩
    simpa using this
  -- the subgame view
  set i' : Fin r := ⟨i.val, hir⟩
  have hca : a.val < (sub G).counts i' := by rw [sub_counts]; exact a.isLt
  set a' : Fin ((sub G).counts i') := ⟨a.val, hca⟩
  have hyA' : (fun (j : Fin r) (b : Fin ((sub G).counts j)) => ((prob (yA.take r) j b : ℚ) : ℝ)) =
      Function.update (x.on (sub G).counts) i' (dlt a') := by
    funext j b
    have htake : yA.take r = rows.set i.val (pureRow (cG G) i.val a.val) := by
      simp only [yA]; rw [List.take_left' (by simp [hrl])]
    rw [htake]
    by_cases hji : j = i'
    · subst hji
      simp only [Function.update_self, dlt]
      rw [prob_set_eq _ _ _ _ (by rw [hrl]; exact hir)]
      have := pureRow_get G (by omega) i a.val ⟨b.val, lt_of_lt_of_eq b.isLt (sub_counts G _)⟩
      simp only at this; rw [this]
      simp only [a', Fin.ext_iff]; split_ifs <;> simp
    · rw [Function.update_of_ne hji]
      have hne : j.val ≠ i.val := fun e => hji (Fin.ext e)
      rw [prob_set_ne _ _ _ _ _ hne]
      exact congrFun (congrFun (prob_rows_sub G hr x hxs) j) b
  have E1 := payoff_eq G (by omega) yA i
  rw [show (G.sizes, G.entries.map valQ) = cG G from rfl, hyA] at E1
  have E2 := payoff_sub G hr yA hyr i.val hir
  have E3 := payoff_eq (sub G) hr (yA.take r) i'
  rw [show ((sub G).sizes, (sub G).entries.map valQ) = cG (sub G) from rfl, hyA'] at E3
  have E4 := hx.2 i' (dlt a') (dlt_lottery a')
  have E5 := payoff_eq (sub G) hr rows i'
  rw [show ((sub G).sizes, (sub G).entries.map valQ) = cG (sub G) from rfl, prob_rows_sub G hr x hxs] at E5
  have E6 := payoff_sub G hr (rows ++ [pureRow (cG G) r 0]) (by
    intro t ht
    have h := prob_append_eq rows (pureRow (cG G) r 0) t
    rw [hrl] at h
    rw [h]
    have := pureRow_get G (by omega) (Fin.last r) 0 ⟨t, by rw [counts_val]; exact ht⟩
    simpa using this) i.val hir
  rw [List.take_left' hrl] at E6
  have E7 := payoff_eq G (by omega) (rows ++ [pureRow (cG G) r 0]) i
  rw [show (G.sizes, G.entries.map valQ) = cG G from rfl, prob_Xp G hr x hxs] at E7
  rw [← E1, E2, E3]
  rw [← E7, E6]
  have E5' : ((payoff (cG (sub G)) rows i.val : ℚ) : ℝ) =
      AGT.expectedPayoff (sub G).utility (x.on (sub G).counts) i' := E5
  rw [E5']
  linarith

end MNRL21


namespace MNRL21
open NashAmplification.Filtering MNRL22

variable {r : ℕ}

theorem pRow_len (G : Table (r + 1)) (hr : 1 ≤ r) (x : RawProfile r) (pp : ℚ) :
    (pRow r pp (itemsOf G ++ itemsOfP x)).length = G.counts (Fin.last r) := by
  unfold pRow
  rw [pCtx_eq, pSizes_eq, List.length_map]
  have h := rng_eq (cG G) (G.counts (Fin.last r)) (counts_le G (by omega) _)
  rw [show G.sizes[r]?.getD 0 = G.counts (Fin.last r) by simp [Table.counts, List.getD_eq_getElem?_getD], h]
  simp

theorem counts_last (G : Table (r + 1)) : G.counts (Fin.last r) = nr G := by
  simp [Table.counts, nr]

noncomputable def xFin (G : Table (r + 1)) (hr : 1 ≤ r) (x : RawProfile r) (hxs : x.sizes = (sub G).sizes)
    (pp : ℚ) : RawProfile (r + 1) where
  sizes := G.sizes
  sizes_length := G.sizes_length
  sizes_pos := G.sizes_pos
  entries := x.entries ++ (pRow r pp (itemsOf G ++ itemsOfP x)).map toRaw
  entries_length := by
    rw [List.length_append, List.length_map, pRow_len G hr, x.entries_length, hxs, counts_last]
    conv_rhs => rw [sizes_split G]
    simp [sub]

theorem mixA_nonneg (pp : ℚ) (h0 : 0 ≤ pp) (h1 : pp ≤ 1) (b a : ℕ) : 0 ≤ mixA pp b a := by
  unfold mixA; split_ifs <;> linarith

theorem xFin_on (G : Table (r + 1)) (hr : 1 ≤ r) (x : RawProfile r) (hxs : x.sizes = (sub G).sizes)
    (pp : ℚ) (h0 : 0 ≤ pp) (h1 : pp ≤ 1) (hb : pB r (itemsOf G ++ itemsOfP x) < G.counts (Fin.last r)) :
    (xFin G hr x hxs pp).on G.counts = Function.update (Xp G x) (Fin.last r)
      (fun a => (pp : ℝ) * d0 a + (1 - (pp : ℝ)) * dlt (⟨pB r (itemsOf G ++ itemsOfP x), hb⟩ :
        Fin (G.counts (Fin.last r))) a) := by
  funext j a
  have hxl : x.entries.length = (G.sizes.take r).sum := by
    rw [x.entries_length, hxs]; simp [sub]
  by_cases hj : j = Fin.last r
  · subst hj
    simp only [Function.update_self, RawProfile.on, RawProfile.at, xFin, Fin.val_last]
    rw [List.getD_eq_getElem?_getD, ← hxl, List.getElem?_append_right (by omega),
      show x.entries.length + a.val - x.entries.length = a.val by omega, List.getElem?_map]
    unfold pRow
    rw [pCtx_eq, pSizes_eq]
    rw [show G.sizes[r]?.getD 0 = G.counts (Fin.last r) by simp [Table.counts, List.getD_eq_getElem?_getD],
      rng_eq _ _ (counts_le G (by omega) _)]
    simp only [List.getElem?_map, List.getElem?_range a.isLt, Option.map_some, Option.getD_some]
    rw [toRaw_value _ (mixA_nonneg pp h0 h1 _ _)]
    simp only [mixA, d0, dlt, Fin.ext_iff]
    split_ifs <;> push_cast <;> ring
  · rw [Function.update_of_ne hj]
    have hjr : j.val < r := by
      have := j.isLt; have : j.val ≠ r := fun e => hj (Fin.ext (by simp [e])); omega
    simp only [Xp, hjr, if_true, RawProfile.on, RawProfile.at, xFin]
    have htj : (G.sizes.take j.val).sum = (x.sizes.take j.val).sum := by
      rw [hxs]; simp [sub, List.take_take, Nat.min_eq_left hjr.le]
    have hidx : (G.sizes.take j.val).sum + a.val < x.entries.length := by
      rw [hxl]
      have ha : a.val < G.sizes.getD j.val 0 := lt_of_lt_of_eq a.isLt (counts_val G j)
      have hjs : j.val < G.sizes.length := by rw [G.sizes_length]; omega
      have : (G.sizes.take (j.val + 1)).sum ≤ (G.sizes.take r).sum := by
        have e := List.take_append_drop (j.val + 1) (G.sizes.take r)
        rw [List.take_take, Nat.min_eq_left (show j.val + 1 ≤ r by omega)] at e
        have := congrArg List.sum e
        rw [List.sum_append] at this
        omega
      rw [List.sum_take_succ _ _ hjs] at this
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjs] at ha
      omega
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hidx, htj]

theorem postF_eq (G : Table (r + 1)) (hr : 1 ≤ r) (x : RawProfile r) (hxs : x.sizes = (sub G).sizes) (pp : ℚ) :
    postF r pp (itemsOf G ++ itemsOfP x) = itemsOfP (xFin G hr x hxs pp) := by
  unfold postF
  rw [pSizes_eq, pXE_eq]
  simp only [itemsOfP, xFin, List.map_append, List.map_map, List.append_assoc]
  rfl

theorem encProfile_pack {k : ℕ} (x : RawProfile k) : encProfile x = packItems (itemsOfP x) := by
  simp only [packItems, itemsOfP, encProfile, pack, List.flatMap_append, List.flatMap_map, item]
  congr 1
  · refine List.flatMap_congr (fun n _ => ?_); simp
  · refine List.flatMap_congr (fun q _ => ?_)
    simp [encRaw, pack, encNat_zero, List.intercalate_cons_cons]

theorem eps_mono {k : ℕ} {n : Fin k → ℕ} (u : Utility n) (x : Mixed n) (ε₁ ε₂ : ℝ) (h : ε₁ ≤ ε₂)
    (hx : DGPNash.WellSupported.IsEpsApproxNash u x ε₁) : DGPNash.WellSupported.IsEpsApproxNash u x ε₂ :=
  ⟨hx.1, fun p y hy => by have := hx.2 p y hy; linarith⟩

theorem Xp_last (G : Table (r + 1)) (x : RawProfile r) : Xp G x (Fin.last r) = d0 := by
  funext a; simp [Xp]

open OAI.MetricKMedian.Binary in
theorem lemma21_main (r : ℕ) (α : ℚ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (h : MultiNashRepair.PolyANE r α) :
    MultiNashRepair.PolyANE (r + 1) (1 / (2 - (α : ℝ))) := by
  have hαR1 : (α : ℝ) ≤ 1 := by exact_mod_cast hα1
  have hαR0 : (0 : ℝ) ≤ α := by exact_mod_cast hα0
  rcases Nat.eq_zero_or_pos r with hr0 | hrpos
  · subst hr0
    obtain ⟨M, c, hM⟩ := MNRL22.lemma22_main
    refine ⟨M, c, fun G => ?_⟩
    obtain ⟨x, hx1, hx2, hx3⟩ := hM 1 le_rfl G
    refine ⟨x, hx1, hx2, eps_mono _ _ _ _ ?_ hx3⟩
    have : (0 : ℝ) ≤ 1 / (2 - (α : ℝ)) := by
      have : (0 : ℝ) < 2 - α := by linarith
      positivity
    norm_num; linarith
  · have hr : 1 ≤ r := hrpos
    obtain ⟨M, cM, hM⟩ := h
    set pp : ℚ := 1 / (2 - α) with hpp
    have hpp0 : 0 ≤ pp := by
      rw [hpp]
      have : (0 : ℚ) < 2 - α := by linarith
      positivity
    have hpp1 : pp ≤ 1 := by
      rw [hpp, div_le_one (by linarith)]; linarith
    let P1a : PolyProgram (fun G : Table (r + 1) => MNRBridge.symBits (encGame G))
        (Automatic.enc : List (List ℕ) → List Bool) itemsOf :=
      Tin.program.of_word (fun G => by
        show Tin.run none _ = _
        rw [Tin_run, encGame_hIn])
    let Pout : PolyProgram (Automatic.enc : List (List ℕ) → List Bool)
        (fun items => MNRBridge.symBits (packItems items)) id :=
      Tout.program.of_word (fun items => by
        show Tout.run (false, false, false) _ = _
        rw [Tout_items]; rfl)
    let P1 : PolyProgram (fun G : Table (r + 1) => MNRBridge.symBits (encGame G))
        (fun G' : Table r => MNRBridge.symBits (encGame G')) sub :=
      ((P1a.comp (poly_subF r).program).comp Pout).recode id (fun _ => rfl) (fun G => by
        show MNRBridge.symBits (packItems (subF r (itemsOf G))) = _
        rw [subF_eq, ← encGame_pack])
    let P2a : PolyProgram (fun p : Table (r + 1) × RawProfile r =>
        MNRBridge.symBits (encGame p.1 ++ encProfile p.2))
        (Automatic.enc : List (List ℕ) → List Bool) (fun p => itemsOf p.1 ++ itemsOfP p.2) :=
      Tin.program.of_word (fun p => by
        show Tin.run none _ = _
        exact Tin_concat p.1 p.2)
    let P2 := (P2a.comp (poly_postF r pp).program).comp Pout
    obtain ⟨M', c, hM'⟩ := MNRCombo.combo (e1 := encGame) (e1' := encGame) (f1 := sub) P1 M cM encProfile
      (fun (G' : Table r) (x' : RawProfile r) => x'.sizes = G'.sizes ∧
        DGPNash.WellSupported.IsEpsApproxNash G'.utility (x'.on G'.counts) α)
      (fun G => by
        obtain ⟨x', h1, h2, h3⟩ := hM (sub G)
        exact ⟨x', ⟨h1, h3⟩, h2⟩) packItems _ P2
    refine ⟨M', c, fun G => ?_⟩
    obtain ⟨x', ⟨hxs, hx⟩, hout⟩ := hM' G
    have hspec := pB_spec G hr x' hxs
    refine ⟨xFin G hr x' hxs pp, rfl, ?_, ?_⟩
    · have e : (id ∘ (postF r pp ∘ fun p : Table (r + 1) × RawProfile r => itemsOf p.1 ++ itemsOfP p.2)) (G, x') =
          itemsOfP (xFin G hr x' hxs pp) := postF_eq G hr x' hxs pp
      rw [e, ← encProfile_pack] at hout
      exact hout
    · rw [xFin_on G hr x' hxs pp hpp0 hpp1 hspec.1]
      have H := hdrs_step G.utility (bounded_G G) (counts_pos G) (α : ℝ) hαR0 hαR1 (Xp G x')
        (Xp_mixed G x' α hx) (Fin.last r) (Xp_last G x') (hreg_21 G hr x' hxs α hx) _ hspec.2
      have hc : ((pp : ℚ) : ℝ) = 1 / (2 - (α : ℝ)) := by rw [hpp]; push_cast; ring
      rw [hc]
      exact H

end MNRL21

theorem solution (r : ℕ) (α : ℚ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (h : MultiNashRepair.PolyANE r α) :
    MultiNashRepair.PolyANE (r + 1) (1 / (2 - (α : ℝ))) :=
  MNRL21.lemma21_main r α hα0 hα1 h
