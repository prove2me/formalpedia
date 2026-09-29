-- Prove2me | solution 1 for LinearOptimization.max_flow_min_cut
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-08-06T20:53:50.710596+00:00
-- url     : https://prove2.me/submissions/02865594-1060-4223-abfb-a940a8f6ad0e

import Mathlib.Data.ENNReal.BigOperators
import Definitions.Def_LinearOptimization_AugmentingPath
import Definitions.Def_LinearOptimization_Cut
import Definitions.Def_Polyhedron
import Theorems.Thm_LinearOptimization_lp_attains_or_unbounded

/-!
# Max-flow min-cut (Bertsimas & Tsitsiklis, Theorem 7.10, p. 310)

The proof follows the book: weak duality `v ≤ C(S)` (Eq. (7.14)), the labelled
set at Ford-Fulkerson termination as a minimum cut, and attainment of the
maximum via the LP attainment theorem (Corollary 2.3, imported).
-/



open Matrix
open scoped ENNReal

namespace MFMC

open LinearOptimization

variable {n m : ℕ} {arcs : Fin m → Fin n × Fin n}

/-- `walkNodes` of a concatenation splits. -/
lemma walkNodes_append (s : Fin n) (P Q : List (Fin m × Bool)) :
    walkNodes arcs s (P ++ Q) = walkNodes arcs s P ++ Q.map (stepEnd arcs) := by
  simp [walkNodes]

/-- A walk along a concatenation splits at an intermediate node. -/
lemma isWalkFrom_append_iff (s t : Fin n) (P Q : List (Fin m × Bool)) :
    IsWalkFrom arcs s t (P ++ Q) ↔
      ∃ w, IsWalkFrom arcs s w P ∧ IsWalkFrom arcs w t Q := by
  induction P generalizing s with
  | nil =>
      simp only [List.nil_append, IsWalkFrom]
      exact ⟨fun h => ⟨s, rfl, h⟩, fun ⟨_, hw, h⟩ => hw ▸ h⟩
  | cons st rest ih =>
      simp only [List.cons_append, IsWalkFrom]
      constructor
      · rintro ⟨h1, h2⟩
        obtain ⟨w, hw1, hw2⟩ := (ih (stepEnd arcs st)).1 h2
        exact ⟨w, ⟨h1, hw1⟩, hw2⟩
      · rintro ⟨w, ⟨h1, hw1⟩, hw2⟩
        exact ⟨h1, (ih (stepEnd arcs st)).2 ⟨w, hw1, hw2⟩⟩

/-- The endpoint of a walk is determined by the walk. -/
lemma isWalkFrom_unique {s t t' : Fin n} {P : List (Fin m × Bool)}
    (h : IsWalkFrom arcs s t P) (h' : IsWalkFrom arcs s t' P) : t = t' := by
  induction P generalizing s with
  | nil => exact h ▸ h'
  | cons st rest ih =>
      exact ih h.2 h'.2

/-- Every node visited by a walk is the endpoint of an initial segment. -/
lemma exists_prefix_of_mem_walkNodes {s t : Fin n} {P : List (Fin m × Bool)}
    (hw : IsWalkFrom arcs s t P) {w : Fin n} (hmem : w ∈ walkNodes arcs s P) :
    ∃ P₁ P₂ : List (Fin m × Bool), P = P₁ ++ P₂ ∧ IsWalkFrom arcs s w P₁ := by
  rcases List.mem_cons.1 hmem with h | h
  · exact ⟨[], P, by simp, by simpa [IsWalkFrom] using h.symm⟩
  · obtain ⟨st, hst, hend⟩ := List.mem_map.1 h
    obtain ⟨P₁, P₂, rfl⟩ := List.append_of_mem hst
    refine ⟨P₁ ++ [st], P₂, by simp, ?_⟩
    have h1 : IsWalkFrom arcs s t ((P₁ ++ [st]) ++ P₂) := by
      simpa using hw
    obtain ⟨w', hw1, _⟩ := (isWalkFrom_append_iff s t (P₁ ++ [st]) P₂).1 h1
    obtain ⟨w'', _, hw''⟩ := (isWalkFrom_append_iff s w' P₁ [st]).1 hw1
    have : stepEnd arcs st = w' := hw''.2
    rw [← hend, this]
    exact hw1

/-- A path uses each arc at most once. -/
lemma nodup_arcs_of_path {s t : Fin n} {P : List (Fin m × Bool)}
    (hw : IsWalkFrom arcs s t P) (hnd : (walkNodes arcs s P).Nodup) :
    (P.map Prod.fst).Nodup := by
  induction P generalizing s with
  | nil => simp
  | cons st rest ih =>
      have hwalk : stepStart arcs st = s ∧ IsWalkFrom arcs (stepEnd arcs st) t rest := hw
      have hnd' : (walkNodes arcs (stepEnd arcs st) rest).Nodup := by
        have : walkNodes arcs s (st :: rest) = s :: walkNodes arcs (stepEnd arcs st) rest := by
          simp [walkNodes]
        rw [this] at hnd
        exact hnd.of_cons
      have hs : s ∉ walkNodes arcs (stepEnd arcs st) rest := by
        have : walkNodes arcs s (st :: rest) = s :: walkNodes arcs (stepEnd arcs st) rest := by
          simp [walkNodes]
        rw [this] at hnd
        exact (List.nodup_cons.1 hnd).1
      have hrest := ih hwalk.2 hnd'
      refine List.nodup_cons.2 ⟨?_, hrest⟩
      intro hmem
      obtain ⟨st', hst', hfst⟩ := List.mem_map.1 hmem
      -- `st'` uses the same arc as `st`
      have hendmem : stepEnd arcs st' ∈ rest.map (stepEnd arcs) :=
        List.mem_map.2 ⟨st', hst', rfl⟩
      have hnd2 : (stepEnd arcs st :: rest.map (stepEnd arcs)).Nodup := by
        simpa [walkNodes] using hnd'
      by_cases hdir : st'.2 = st.2
      · -- same arc, same direction: same endpoint, contradicting nodup
        have heq : stepEnd arcs st' = stepEnd arcs st := by
          simp only [stepEnd, hfst, hdir]
        rw [heq] at hendmem
        exact (List.nodup_cons.1 hnd2).1 hendmem
      · -- same arc, opposite direction: the endpoint is `s`
        have heq : stepEnd arcs st' = stepStart arcs st := by
          simp only [stepEnd, stepStart, hfst]
          cases hst2 : st.2 <;> cases hst'2 : st'.2 <;> simp_all
        rw [heq, hwalk.1] at hendmem
        exact hs (by simp only [walkNodes, List.mem_cons]; exact Or.inr hendmem)

end MFMC



open Matrix
open scoped ENNReal

namespace MFMC

open LinearOptimization

variable {n m : ℕ} {arcs : Fin m → Fin n × Fin n}

/-- `e_s − e_t`, the divergence of a unit flow from `s` to `t`. -/
def unitDiff (s t : Fin n) : Fin n → ℝ :=
  fun i => (if i = s then (1 : ℝ) else 0) - (if i = t then 1 else 0)

lemma unitDiff_trans (a b c : Fin n) :
    unitDiff a b + unitDiff b c = unitDiff a c := by
  funext i; simp only [unitDiff, Pi.add_apply]; ring

lemma unitDiff_self (a : Fin n) : unitDiff a a = 0 := by
  funext i; simp [unitDiff]

/-- If the arc of `st` does not occur in `rest`, the traversal vector of
`st :: rest` splits off the signed unit vector of `st`. -/
lemma traversalVector_cons {st : Fin m × Bool} {rest : List (Fin m × Bool)}
    (h : st.1 ∉ rest.map Prod.fst) (k : Fin m) :
    traversalVector (st :: rest) k =
      (if k = st.1 then (if st.2 then (1 : ℝ) else -1) else 0) + traversalVector rest k := by
  by_cases hk : k = st.1
  · have hnot : ∀ b : Bool, (k, b) ∉ rest := fun b hb =>
      h (List.mem_map.2 ⟨(k, b), hb, hk⟩)
    subst hk
    cases hst : st.2 <;>
      simp [traversalVector, List.mem_cons, hnot true, hnot false, Prod.ext_iff, hst]
  · have : ∀ b : Bool, ((k, b) ∈ st :: rest) ↔ ((k, b) ∈ rest) := by
      intro b
      simp only [List.mem_cons, or_iff_right_iff_imp]
      intro hb
      exact absurd (congrArg Prod.fst hb) hk
    simp [traversalVector, this true, this false, hk]

/-- The divergence of the traversal vector of a walk with pairwise distinct
arcs is `e_s − e_t`. -/
lemma incidence_mulVec_traversalVector {s t : Fin n} {P : List (Fin m × Bool)}
    (hw : IsWalkFrom arcs s t P) (hnd : (P.map Prod.fst).Nodup) :
    (incidenceMatrix arcs).mulVec (traversalVector P) = unitDiff s t := by
  induction P generalizing s with
  | nil =>
      have : s = t := hw
      subst this
      funext i
      simp [Matrix.mulVec, dotProduct, traversalVector, unitDiff]
  | cons st rest ih =>
      obtain ⟨hstart, hrest⟩ := hw
      have hnotmem : st.1 ∉ rest.map Prod.fst := (List.nodup_cons.1 (by simpa using hnd)).1
      have hndrest : (rest.map Prod.fst).Nodup := (List.nodup_cons.1 (by simpa using hnd)).2
      have IH := ih hrest hndrest
      funext i
      have hsplit : ∀ k, traversalVector (st :: rest) k =
          (if k = st.1 then (if st.2 then (1 : ℝ) else -1) else 0) + traversalVector rest k :=
        traversalVector_cons hnotmem
      have : (incidenceMatrix arcs).mulVec (traversalVector (st :: rest)) i
          = incidenceMatrix arcs i st.1 * (if st.2 then (1 : ℝ) else -1)
            + (incidenceMatrix arcs).mulVec (traversalVector rest) i := by
        simp only [Matrix.mulVec, dotProduct]
        have hterm : ∀ k : Fin m, incidenceMatrix arcs i k * traversalVector (st :: rest) k
            = (if k = st.1 then
                incidenceMatrix arcs i st.1 * (if st.2 then (1 : ℝ) else -1) else 0)
              + incidenceMatrix arcs i k * traversalVector rest k := by
          intro k
          rw [hsplit k, mul_add]
          congr 1
          by_cases hk : k = st.1
          · subst hk; simp
          · simp [hk]
        rw [Finset.sum_congr rfl (fun k _ => hterm k), Finset.sum_add_distrib]
        simp
      rw [this, IH]
      have hcol : incidenceMatrix arcs i st.1 * (if st.2 then (1 : ℝ) else -1)
          = unitDiff (stepStart arcs st) (stepEnd arcs st) i := by
        have hcomm1 : ((arcs st.1).1 = i) = (i = (arcs st.1).1) := propext eq_comm
        have hcomm2 : ((arcs st.1).2 = i) = (i = (arcs st.1).2) := propext eq_comm
        cases hst : st.2 <;>
          simp only [incidenceMatrix, stepStart, stepEnd, unitDiff, Matrix.of_apply, hst,
            hcomm1, hcomm2, Bool.false_eq_true, reduceIte, if_true] <;> ring
      rw [hcol, hstart]
      exact congrFun (unitDiff_trans s (stepEnd arcs st) t) i

end MFMC



open Matrix
open scoped ENNReal

namespace MFMC

open LinearOptimization

variable {n m : ℕ} {arcs : Fin m → Fin n × Fin n}

/-- The column sums of the incidence matrix over a set of nodes. -/
lemma sum_incidence_col (S : Finset (Fin n)) (k : Fin m) :
    ∑ i ∈ S, incidenceMatrix arcs i k =
      (if (arcs k).1 ∈ S then (1 : ℝ) else 0) - (if (arcs k).2 ∈ S then 1 else 0) := by
  simp only [incidenceMatrix, Matrix.of_apply, Finset.sum_sub_distrib]
  rw [Finset.sum_ite_eq S (arcs k).1 (fun _ => (1 : ℝ)),
    Finset.sum_ite_eq S (arcs k).2 (fun _ => (1 : ℝ))]

/-- The net divergence over a set of nodes equals the net flow crossing its
boundary. -/
lemma sum_div_eq_cross (S : Finset (Fin n)) (f : Fin m → ℝ) :
    ∑ i ∈ S, (incidenceMatrix arcs).mulVec f i =
      (∑ k, if (arcs k).1 ∈ S ∧ (arcs k).2 ∉ S then f k else 0) -
      (∑ k, if (arcs k).1 ∉ S ∧ (arcs k).2 ∈ S then f k else 0) := by
  have h1 : ∑ i ∈ S, (incidenceMatrix arcs).mulVec f i
      = ∑ k, (∑ i ∈ S, incidenceMatrix arcs i k) * f k := by
    simp only [Matrix.mulVec, dotProduct, Finset.sum_mul]
    exact Finset.sum_comm
  rw [h1, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [sum_incidence_col S k]
  by_cases h1 : (arcs k).1 ∈ S <;> by_cases h2 : (arcs k).2 ∈ S <;>
    simp [h1, h2]

/-- For a feasible max-flow vector and a cut `S`, the value of the flow is the
net flow crossing the cut. -/
lemma flowValue_eq_cross {u : Fin m → ℝ≥0∞} {s t : Fin n} {f : Fin m → ℝ}
    (hf : IsFeasibleMaxFlow arcs u s t f) {S : Finset (Fin n)} (hS : IsCut s t S) :
    flowValue arcs s f =
      (∑ k, if (arcs k).1 ∈ S ∧ (arcs k).2 ∉ S then f k else 0) -
      (∑ k, if (arcs k).1 ∉ S ∧ (arcs k).2 ∈ S then f k else 0) := by
  rw [← sum_div_eq_cross S f]
  have : ∀ i ∈ S, (incidenceMatrix arcs).mulVec f i = if i = s then flowValue arcs s f else 0 := by
    intro i hi
    by_cases his : i = s
    · subst his; simp [flowValue]
    · have hit : i ≠ t := fun h => hS.2 (h ▸ hi)
      simp [his, hf.1 i his hit]
  rw [Finset.sum_congr rfl this, Finset.sum_ite_eq' S s (fun _ => flowValue arcs s f),
    if_pos hS.1]

/-- **Weak duality (Bertsimas & Tsitsiklis, Eq. (7.14), p. 310).** The value of any
feasible flow is at most the capacity of any cut. -/
lemma weak_duality {u : Fin m → ℝ≥0∞} {s t : Fin n} {f : Fin m → ℝ}
    (hf : IsFeasibleMaxFlow arcs u s t f) {S : Finset (Fin n)} (hS : IsCut s t S) :
    ENNReal.ofReal (flowValue arcs s f) ≤ cutCapacity arcs u S := by
  have hle : flowValue arcs s f ≤ ∑ k, if (arcs k).1 ∈ S ∧ (arcs k).2 ∉ S then f k else 0 := by
    rw [flowValue_eq_cross hf hS]
    have : (0 : ℝ) ≤ ∑ k, if (arcs k).1 ∉ S ∧ (arcs k).2 ∈ S then f k else 0 :=
      Finset.sum_nonneg (fun k _ => by
        by_cases h : (arcs k).1 ∉ S ∧ (arcs k).2 ∈ S
        · simpa [h] using (hf.2.2 k).1
        · simp [h])
    linarith
  refine le_trans (ENNReal.ofReal_le_ofReal hle) ?_
  rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => by
    by_cases h : (arcs k).1 ∈ S ∧ (arcs k).2 ∉ S
    · simpa [h] using (hf.2.2 k).1
    · simp [h])]
  refine Finset.sum_le_sum (fun k _ => ?_)
  by_cases h : (arcs k).1 ∈ S ∧ (arcs k).2 ∉ S
  · simpa [h] using (hf.2.2 k).2
  · simp [h]

end MFMC



open Matrix
open scoped ENNReal

namespace MFMC

open LinearOptimization

variable {n m : ℕ} {arcs : Fin m → Fin n × Fin n}

open Classical in
/-- The set of nodes reachable from `s` by an augmenting path for `f`
(the "labelled" set of the Ford–Fulkerson labelling algorithm). -/
noncomputable def reachSet (arcs : Fin m → Fin n × Fin n) (u : Fin m → ℝ≥0∞)
    (s : Fin n) (f : Fin m → ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun v => ∃ steps, IsAugmentingPath arcs u s v f steps)

lemma mem_reachSet {u : Fin m → ℝ≥0∞} {s : Fin n} {f : Fin m → ℝ} {v : Fin n} :
    v ∈ reachSet arcs u s f ↔ ∃ steps, IsAugmentingPath arcs u s v f steps := by
  classical
  simp [reachSet]

lemma self_mem_reachSet {u : Fin m → ℝ≥0∞} {s : Fin n} {f : Fin m → ℝ} :
    s ∈ reachSet arcs u s f :=
  mem_reachSet.2 ⟨[], ⟨rfl, by simp [walkNodes]⟩, by simp, by simp⟩

/-- Every node visited by an augmenting path is itself reachable. -/
lemma reach_of_mem_walkNodes {u : Fin m → ℝ≥0∞} {s v : Fin n} {f : Fin m → ℝ}
    {P : List (Fin m × Bool)} (h : IsAugmentingPath arcs u s v f P)
    {w : Fin n} (hw : w ∈ walkNodes arcs s P) : w ∈ reachSet arcs u s f := by
  obtain ⟨P₁, P₂, hP, hwalk⟩ := exists_prefix_of_mem_walkNodes h.1.1 hw
  refine mem_reachSet.2 ⟨P₁, ⟨hwalk, ?_⟩, ?_, ?_⟩
  · have hnd := h.1.2
    rw [hP, walkNodes_append] at hnd
    exact hnd.of_append_left
  · intro st hst hdir
    exact h.2.1 st (by rw [hP]; exact List.mem_append_left _ hst) hdir
  · intro st hst hdir
    exact h.2.2 st (by rw [hP]; exact List.mem_append_left _ hst) hdir

/-- Arcs leaving the labelled set are saturated. -/
lemma saturated_of_cross_out {u : Fin m → ℝ≥0∞} {s : Fin n} {f : Fin m → ℝ}
    {k : Fin m} (h1 : (arcs k).1 ∈ reachSet arcs u s f)
    (h2 : (arcs k).2 ∉ reachSet arcs u s f) :
    ¬ (ENNReal.ofReal (f k) < u k) := by
  intro hres
  obtain ⟨P, hP⟩ := mem_reachSet.1 h1
  refine h2 (mem_reachSet.2 ⟨P ++ [(k, true)], ⟨?_, ?_⟩, ?_, ?_⟩)
  · refine (isWalkFrom_append_iff s (arcs k).2 P [(k, true)]).2 ⟨(arcs k).1, hP.1.1, ?_⟩
    exact ⟨rfl, rfl⟩
  · rw [walkNodes_append]
    refine List.nodup_append.2 ⟨hP.1.2, by simp, ?_⟩
    intro a ha b hb
    have hb' : b = (arcs k).2 := by simpa [stepEnd] using hb
    subst hb'
    exact fun heq => h2 (heq ▸ reach_of_mem_walkNodes hP ha)
  · intro st hst _
    rcases List.mem_append.1 hst with h | h
    · exact hP.2.1 st h (by assumption)
    · simp only [List.mem_singleton] at h; subst h; exact hres
  · intro st hst hdir
    rcases List.mem_append.1 hst with h | h
    · exact hP.2.2 st h hdir
    · simp only [List.mem_singleton] at h; subst h; simp at hdir

/-- Arcs entering the labelled set carry no flow. -/
lemma zero_of_cross_in {u : Fin m → ℝ≥0∞} {s : Fin n} {f : Fin m → ℝ}
    {k : Fin m} (h1 : (arcs k).1 ∉ reachSet arcs u s f)
    (h2 : (arcs k).2 ∈ reachSet arcs u s f) :
    ¬ (0 < f k) := by
  intro hres
  obtain ⟨P, hP⟩ := mem_reachSet.1 h2
  refine h1 (mem_reachSet.2 ⟨P ++ [(k, false)], ⟨?_, ?_⟩, ?_, ?_⟩)
  · refine (isWalkFrom_append_iff s (arcs k).1 P [(k, false)]).2 ⟨(arcs k).2, hP.1.1, ?_⟩
    exact ⟨rfl, rfl⟩
  · rw [walkNodes_append]
    refine List.nodup_append.2 ⟨hP.1.2, by simp, ?_⟩
    intro a ha b hb
    have hb' : b = (arcs k).1 := by simpa [stepEnd] using hb
    subst hb'
    exact fun heq => h1 (heq ▸ reach_of_mem_walkNodes hP ha)
  · intro st hst hdir
    rcases List.mem_append.1 hst with h | h
    · exact hP.2.1 st h hdir
    · simp only [List.mem_singleton] at h; subst h; simp at hdir
  · intro st hst _
    rcases List.mem_append.1 hst with h | h
    · exact hP.2.2 st h (by assumption)
    · simp only [List.mem_singleton] at h; subst h; exact hres

/-- **Bertsimas & Tsitsiklis, Theorem 7.10, p. 310–311.** If no augmenting path exists,
the labelled set is a cut whose capacity equals the value of the flow. -/
lemma cut_of_no_augmenting {u : Fin m → ℝ≥0∞} {s t : Fin n} {f : Fin m → ℝ}
    (hf : IsFeasibleMaxFlow arcs u s t f)
    (hno : ¬ ∃ steps, IsAugmentingPath arcs u s t f steps) :
    ∃ S : Finset (Fin n), IsCut s t S ∧ 0 ≤ flowValue arcs s f ∧
      ENNReal.ofReal (flowValue arcs s f) = cutCapacity arcs u S := by
  classical
  set S := reachSet arcs u s f with hSdef
  have hcut : IsCut s t S := ⟨self_mem_reachSet, fun h => hno (mem_reachSet.1 h)⟩
  -- crossing-in arcs carry no flow
  have hin : ∀ k, ((arcs k).1 ∉ S ∧ (arcs k).2 ∈ S) → f k = 0 := by
    intro k hk
    exact le_antisymm (not_lt.1 (zero_of_cross_in hk.1 hk.2)) (hf.2.2 k).1
  have hsumin : (∑ k, if (arcs k).1 ∉ S ∧ (arcs k).2 ∈ S then f k else 0) = 0 := by
    refine Finset.sum_eq_zero (fun k _ => ?_)
    by_cases h : (arcs k).1 ∉ S ∧ (arcs k).2 ∈ S
    · simp [h, hin k h]
    · simp [h]
  have hval : flowValue arcs s f = ∑ k, if (arcs k).1 ∈ S ∧ (arcs k).2 ∉ S then f k else 0 := by
    rw [flowValue_eq_cross hf hcut, hsumin, sub_zero]
  have hnonneg : 0 ≤ flowValue arcs s f := by
    rw [hval]
    refine Finset.sum_nonneg (fun k _ => ?_)
    by_cases h : (arcs k).1 ∈ S ∧ (arcs k).2 ∉ S
    · simpa [h] using (hf.2.2 k).1
    · simp [h]
  refine ⟨S, hcut, hnonneg, ?_⟩
  rw [hval, ENNReal.ofReal_sum_of_nonneg (fun k _ => by
    by_cases h : (arcs k).1 ∈ S ∧ (arcs k).2 ∉ S
    · simpa [h] using (hf.2.2 k).1
    · simp [h])]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  by_cases h : (arcs k).1 ∈ S ∧ (arcs k).2 ∉ S
  · simp only [h]
    exact le_antisymm (hf.2.2 k).2 (not_lt.1 (saturated_of_cross_out h.1 h.2))
  · simp [h]

end MFMC



open Matrix
open scoped ENNReal

namespace MFMC

open LinearOptimization

variable {n m : ℕ} {arcs : Fin m → Fin n × Fin n}

lemma tv_of_true {P : List (Fin m × Bool)} (hnd : (P.map Prod.fst).Nodup) {k : Fin m}
    (h : (k, true) ∈ P) : traversalVector P k = 1 := by
  have h2 : (k, false) ∉ P := by
    intro hc
    have := List.inj_on_of_nodup_map hnd h hc rfl
    simp at this
  simp [traversalVector, h, h2]

lemma tv_of_false {P : List (Fin m × Bool)} (hnd : (P.map Prod.fst).Nodup) {k : Fin m}
    (h : (k, false) ∈ P) : traversalVector P k = -1 := by
  have h2 : (k, true) ∉ P := by
    intro hc
    have := List.inj_on_of_nodup_map hnd h hc rfl
    simp at this
  simp [traversalVector, h, h2]

lemma tv_of_none {P : List (Fin m × Bool)} {k : Fin m}
    (h1 : (k, true) ∉ P) (h2 : (k, false) ∉ P) : traversalVector P k = 0 := by
  simp [traversalVector, h1, h2]

lemma foldr_min_le (l : List ℝ≥0∞) {x : ℝ≥0∞} (hx : x ∈ l) : l.foldr min ⊤ ≤ x := by
  induction l with
  | nil => simp at hx
  | cons a rest ih =>
      rcases List.mem_cons.1 hx with h | h
      · subst h; exact min_le_left _ _
      · exact le_trans (min_le_right _ _) (ih h)

lemma foldr_min_pos (l : List ℝ≥0∞) (h : ∀ x ∈ l, 0 < x) : 0 < l.foldr min ⊤ := by
  induction l with
  | nil => simp
  | cons a rest ih =>
      exact lt_min (h a (List.mem_cons_self ..))
        (ih (fun x hx => h x (List.mem_cons_of_mem _ hx)))

lemma augmentingDelta_le {u : Fin m → ℝ≥0∞} {f : Fin m → ℝ} {steps : List (Fin m × Bool)}
    {st : Fin m × Bool} (hst : st ∈ steps) :
    augmentingDelta u f steps ≤
      (if st.2 then u st.1 - ENNReal.ofReal (f st.1) else ENNReal.ofReal (f st.1)) :=
  foldr_min_le _ (List.mem_map.2 ⟨st, hst, rfl⟩)

lemma augmentingDelta_pos {u : Fin m → ℝ≥0∞} {s t : Fin n} {f : Fin m → ℝ}
    {steps : List (Fin m × Bool)} (h : IsAugmentingPath arcs u s t f steps) :
    0 < augmentingDelta u f steps := by
  refine foldr_min_pos _ (fun x hx => ?_)
  obtain ⟨st, hst, rfl⟩ := List.mem_map.1 hx
  by_cases hd : st.2
  · simp only [hd, if_true]
    exact tsub_pos_of_lt (h.2.1 st hst hd)
  · simp only [Bool.not_eq_true] at hd
    simp only [hd, Bool.false_eq_true, if_false]
    exact ENNReal.ofReal_pos.2 (h.2.2 st hst hd)

lemma push_feasible {u : Fin m → ℝ≥0∞} {s t : Fin n} {f : Fin m → ℝ}
    (hst : s ≠ t) (hf : IsFeasibleMaxFlow arcs u s t f)
    {P : List (Fin m × Bool)} (hP : IsAugmentingPath arcs u s t f P)
    {ε : ℝ} (hε : 0 < ε) (hεδ : ENNReal.ofReal ε ≤ augmentingDelta u f P) :
    IsFeasibleMaxFlow arcs u s t (fun k => f k + ε * traversalVector P k) ∧
      flowValue arcs s (fun k => f k + ε * traversalVector P k) = flowValue arcs s f + ε := by
  classical
  have hnd : (P.map Prod.fst).Nodup := nodup_arcs_of_path hP.1.1 hP.1.2
  have key : (incidenceMatrix arcs).mulVec (traversalVector P) = unitDiff s t :=
    incidence_mulVec_traversalVector hP.1.1 hnd
  set f' : Fin m → ℝ := fun k => f k + ε * traversalVector P k with hf'
  have hdiv : ∀ i, (incidenceMatrix arcs).mulVec f' i
      = (incidenceMatrix arcs).mulVec f i + ε * unitDiff s t i := by
    intro i
    rw [← congrFun key i]
    simp only [Matrix.mulVec, dotProduct, hf', Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  have hus : unitDiff s t s = 1 := by simp [unitDiff, hst]
  have hut : unitDiff s t t = -1 := by simp [unitDiff, Ne.symm hst]
  have hvalue : flowValue arcs s f' = flowValue arcs s f + ε := by
    have h := hdiv s
    rw [hus] at h
    simpa [flowValue] using h
  -- capacity constraints
  have hcap : ∀ k, 0 ≤ f' k ∧ ENNReal.ofReal (f' k) ≤ u k := by
    intro k
    by_cases h1 : (k, true) ∈ P
    · have htv : traversalVector P k = 1 := tv_of_true hnd h1
      have hεk : ENNReal.ofReal ε ≤ u k - ENNReal.ofReal (f k) := by
        refine le_trans hεδ ?_
        simpa using augmentingDelta_le (u := u) (f := f) h1
      constructor
      · simp only [hf', htv, mul_one]
        linarith [(hf.2.2 k).1, hε.le]
      · simp only [hf', htv, mul_one]
        rw [ENNReal.ofReal_add (hf.2.2 k).1 hε.le]
        calc ENNReal.ofReal (f k) + ENNReal.ofReal ε
            ≤ ENNReal.ofReal (f k) + (u k - ENNReal.ofReal (f k)) := by
              gcongr
          _ = u k := add_tsub_cancel_of_le (hf.2.2 k).2
    · by_cases h2 : (k, false) ∈ P
      · have htv : traversalVector P k = -1 := tv_of_false hnd h2
        have hεk : ENNReal.ofReal ε ≤ ENNReal.ofReal (f k) := by
          refine le_trans hεδ ?_
          simpa using augmentingDelta_le (u := u) (f := f) h2
        have hle : ε ≤ f k := (ENNReal.ofReal_le_ofReal_iff (hf.2.2 k).1).1 hεk
        constructor
        · simp only [hf', htv]; linarith
        · simp only [hf', htv]
          refine le_trans (ENNReal.ofReal_le_ofReal (by linarith)) (hf.2.2 k).2
      · have htv : traversalVector P k = 0 := tv_of_none h1 h2
        simpa [hf', htv] using hf.2.2 k
  refine ⟨⟨?_, ?_, hcap⟩, hvalue⟩
  · intro i his hit
    rw [hdiv i, hf.1 i his hit]
    simp [unitDiff, his, hit]
  · rw [hdiv t, hf.2.1, hut, hvalue]
    ring

end MFMC



open Matrix
open scoped ENNReal

namespace MFMC

open LinearOptimization

variable {n m : ℕ} {arcs : Fin m → Fin n × Fin n}

/-- Index type for the constraints of the max-flow polyhedron. -/
abbrev RowIdx (n m : ℕ) := (Fin n ⊕ Fin n) ⊕ (Bool ⊕ (Fin m ⊕ Fin m))

/-- The constraint matrix of the max-flow problem written as `Bf ≥ d`. -/
noncomputable def rowMat (arcs : Fin m → Fin n × Fin n) (u : Fin m → ℝ≥0∞) (s t : Fin n) :
    Matrix (RowIdx n m) (Fin m) ℝ :=
  Matrix.of fun r k =>
    match r with
    | Sum.inl (Sum.inl i) => if i = s ∨ i = t then 0 else incidenceMatrix arcs i k
    | Sum.inl (Sum.inr i) => if i = s ∨ i = t then 0 else -incidenceMatrix arcs i k
    | Sum.inr (Sum.inl true) => incidenceMatrix arcs s k + incidenceMatrix arcs t k
    | Sum.inr (Sum.inl false) => -(incidenceMatrix arcs s k + incidenceMatrix arcs t k)
    | Sum.inr (Sum.inr (Sum.inl j)) => if k = j then 1 else 0
    | Sum.inr (Sum.inr (Sum.inr j)) => if k = j then (if u j = ⊤ then 0 else -1) else 0

/-- The right-hand side of the max-flow constraints. -/
noncomputable def rowRhs (u : Fin m → ℝ≥0∞) : RowIdx n m → ℝ :=
  fun r =>
    match r with
    | Sum.inr (Sum.inr (Sum.inr j)) => if u j = ⊤ then 0 else -(u j).toReal
    | _ => 0

lemma rowMat_mulVec_scalar (c : ℝ) (j : Fin m) (f : Fin m → ℝ) :
    ∑ k, (if k = j then c else 0) * f k = c * f j := by
  rw [Finset.sum_congr rfl (fun k _ => by
    by_cases h : k = j
    · subst h; simp
    · simp [h] : ∀ k ∈ Finset.univ, (if k = j then c else 0) * f k
        = if k = j then c * f j else 0)]
  simp

lemma rowMat_mulVec (u : Fin m → ℝ≥0∞) (s t : Fin n) (f : Fin m → ℝ) :
    (∀ r : RowIdx n m, rowRhs u r ≤ (rowMat arcs u s t).mulVec f r) ↔
      IsFeasibleMaxFlow arcs u s t f := by
  classical
  have hrow : ∀ i : Fin n, (rowMat arcs u s t).mulVec f (Sum.inl (Sum.inl i))
      = if i = s ∨ i = t then 0 else (incidenceMatrix arcs).mulVec f i := by
    intro i
    by_cases h : i = s ∨ i = t <;>
      simp [Matrix.mulVec, dotProduct, rowMat, h]
  have hrow' : ∀ i : Fin n, (rowMat arcs u s t).mulVec f (Sum.inl (Sum.inr i))
      = if i = s ∨ i = t then 0 else -(incidenceMatrix arcs).mulVec f i := by
    intro i
    by_cases h : i = s ∨ i = t <;>
      simp [Matrix.mulVec, dotProduct, rowMat, h, Finset.sum_neg_distrib]
  have hsum : (rowMat arcs u s t).mulVec f (Sum.inr (Sum.inl true))
      = (incidenceMatrix arcs).mulVec f s + (incidenceMatrix arcs).mulVec f t := by
    simp [Matrix.mulVec, dotProduct, rowMat, add_mul, Finset.sum_add_distrib]
  have hsum' : (rowMat arcs u s t).mulVec f (Sum.inr (Sum.inl false))
      = -((incidenceMatrix arcs).mulVec f s + (incidenceMatrix arcs).mulVec f t) := by
    simp [Matrix.mulVec, dotProduct, rowMat, add_mul, Finset.sum_add_distrib,
      Finset.sum_neg_distrib, neg_add]
  have hpos : ∀ j : Fin m, (rowMat arcs u s t).mulVec f (Sum.inr (Sum.inr (Sum.inl j))) = f j := by
    intro j
    have h := rowMat_mulVec_scalar (1 : ℝ) j f
    rw [one_mul] at h
    exact h
  have hcap : ∀ j : Fin m, (rowMat arcs u s t).mulVec f (Sum.inr (Sum.inr (Sum.inr j)))
      = (if u j = ⊤ then 0 else -1) * f j := by
    intro j
    exact rowMat_mulVec_scalar _ j f
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro i his hit
      have h1 := h (Sum.inl (Sum.inl i))
      have h2 := h (Sum.inl (Sum.inr i))
      rw [hrow i, if_neg (by tauto)] at h1
      rw [hrow' i, if_neg (by tauto)] at h2
      simp only [rowRhs] at h1 h2
      linarith
    · have h1 := h (Sum.inr (Sum.inl true))
      have h2 := h (Sum.inr (Sum.inl false))
      rw [hsum] at h1
      rw [hsum'] at h2
      simp only [rowRhs] at h1 h2
      simp only [flowValue]
      linarith
    · intro k
      have h1 := h (Sum.inr (Sum.inr (Sum.inl k)))
      rw [hpos k] at h1
      simp only [rowRhs] at h1
      refine ⟨h1, ?_⟩
      by_cases hu : u k = ⊤
      · simp [hu]
      · have h2 := h (Sum.inr (Sum.inr (Sum.inr k)))
        rw [hcap k, if_neg hu] at h2
        simp only [rowRhs, if_neg hu] at h2
        have : f k ≤ (u k).toReal := by linarith
        calc ENNReal.ofReal (f k) ≤ ENNReal.ofReal ((u k).toReal) :=
              ENNReal.ofReal_le_ofReal this
          _ = u k := ENNReal.ofReal_toReal hu
  · intro hf r
    match r with
    | Sum.inl (Sum.inl i) =>
        rw [hrow i]
        by_cases h : i = s ∨ i = t
        · simp [h, rowRhs]
        · push_neg at h
          simp [h, rowRhs, hf.1 i h.1 h.2]
    | Sum.inl (Sum.inr i) =>
        rw [hrow' i]
        by_cases h : i = s ∨ i = t
        · simp [h, rowRhs]
        · push_neg at h
          simp [h, rowRhs, hf.1 i h.1 h.2]
    | Sum.inr (Sum.inl true) =>
        rw [hsum]
        simp only [rowRhs]
        have := hf.2.1
        simp only [flowValue] at this
        linarith
    | Sum.inr (Sum.inl false) =>
        rw [hsum']
        simp only [rowRhs]
        have := hf.2.1
        simp only [flowValue] at this
        linarith
    | Sum.inr (Sum.inr (Sum.inl j)) =>
        rw [hpos j]
        simpa [rowRhs] using (hf.2.2 j).1
    | Sum.inr (Sum.inr (Sum.inr j)) =>
        rw [hcap j]
        by_cases hu : u j = ⊤
        · simp [hu, rowRhs]
        · simp only [rowRhs, if_neg hu]
          have h2 := (hf.2.2 j).2
          have : f j ≤ (u j).toReal := by
            have := (ENNReal.ofReal_le_iff_le_toReal hu).1 h2
            exact this
          linarith

/-- The max-flow feasible set as a polyhedron over `Fin`-indexed constraints. -/
noncomputable def mfMat (arcs : Fin m → Fin n × Fin n) (u : Fin m → ℝ≥0∞) (s t : Fin n) :
    Matrix (Fin (Fintype.card (RowIdx n m))) (Fin m) ℝ :=
  (rowMat arcs u s t).submatrix (Fintype.equivFin (RowIdx n m)).symm id

/-- The right-hand side of the max-flow polyhedron. -/
noncomputable def mfRhs (u : Fin m → ℝ≥0∞) : Fin (Fintype.card (RowIdx n m)) → ℝ :=
  fun i => rowRhs u ((Fintype.equivFin (RowIdx n m)).symm i)

lemma mem_polyhedron_iff (u : Fin m → ℝ≥0∞) (s t : Fin n) (f : Fin m → ℝ) :
    f ∈ polyhedron (mfMat arcs u s t) (mfRhs (n := n) u) ↔ IsFeasibleMaxFlow arcs u s t f := by
  rw [← rowMat_mulVec (arcs := arcs) u s t f]
  constructor
  · intro h r
    have := h ((Fintype.equivFin (RowIdx n m)) r)
    simpa [mfMat, mfRhs, Matrix.mulVec, dotProduct] using this
  · intro h i
    have := h ((Fintype.equivFin (RowIdx n m)).symm i)
    simpa [mfMat, mfRhs, Matrix.mulVec, dotProduct] using this

/-- The zero flow is feasible. -/
lemma zero_feasible (u : Fin m → ℝ≥0∞) (s t : Fin n) :
    IsFeasibleMaxFlow arcs u s t 0 := by
  refine ⟨fun i _ _ => by simp, ?_, fun k => by simp⟩
  simp [flowValue]

lemma flowValue_zero (u : Fin m → ℝ≥0∞) (s : Fin n) :
    flowValue arcs s (0 : Fin m → ℝ) = 0 := by
  simp [flowValue]

/-- **Attainment (Bertsimas & Tsitsiklis, Corollary 2.3, p. 67).** If the values of feasible
flows are bounded above then a maximum flow exists. -/
lemma exists_max_flow {u : Fin m → ℝ≥0∞} {s t : Fin n} {R : ℝ}
    (hR : ∀ f, IsFeasibleMaxFlow arcs u s t f → flowValue arcs s f ≤ R) :
    ∃ f, IsFeasibleMaxFlow arcs u s t f ∧
      ∀ f', IsFeasibleMaxFlow arcs u s t f' → flowValue arcs s f' ≤ flowValue arcs s f := by
  classical
  set c : Fin m → ℝ := fun k => -incidenceMatrix arcs s k with hc
  have hcdot : ∀ f : Fin m → ℝ, c ⬝ᵥ f = -flowValue arcs s f := by
    intro f
    simp only [hc, dotProduct, flowValue, Matrix.mulVec, neg_mul, Finset.sum_neg_distrib]
  have hne : (polyhedron (mfMat arcs u s t) (mfRhs (n := n) u)).Nonempty :=
    ⟨0, (mem_polyhedron_iff u s t 0).2 (zero_feasible u s t)⟩
  rcases LinearOptimization.lp_attains_or_unbounded (mfMat arcs u s t) (mfRhs (n := n) u) c hne with
    hbot | ⟨x, hx⟩
  · exfalso
    have hlow : ((-R : ℝ) : EReal) ≤ lpValue c (polyhedron (mfMat arcs u s t) (mfRhs (n := n) u)) := by
      refine le_iInf₂ (fun x hx => ?_)
      rw [hcdot x]
      exact_mod_cast neg_le_neg (hR x ((mem_polyhedron_iff u s t x).1 hx))
    rw [hbot] at hlow
    exact absurd (le_bot_iff.1 hlow) (by simp)
  · refine ⟨x, (mem_polyhedron_iff u s t x).1 hx.1, ?_⟩
    intro f' hf'
    have := hx.2 f' ((mem_polyhedron_iff u s t f').2 hf')
    rw [hcdot, hcdot] at this
    linarith

end MFMC



open Matrix
open scoped ENNReal

namespace MFMC

open LinearOptimization

variable {n m : ℕ} {arcs : Fin m → Fin n × Fin n}

lemma le_maxFlowValue {u : Fin m → ℝ≥0∞} {s t : Fin n} {f : Fin m → ℝ}
    (hf : IsFeasibleMaxFlow arcs u s t f) :
    ((flowValue arcs s f : ℝ) : EReal) ≤ maxFlowValue arcs u s t :=
  le_iSup₂ (f := fun f (_ : f ∈ {f | IsFeasibleMaxFlow arcs u s t f}) =>
    ((flowValue arcs s f : ℝ) : EReal)) f hf

lemma maxFlowValue_ne_bot (u : Fin m → ℝ≥0∞) (s t : Fin n) :
    maxFlowValue arcs u s t ≠ ⊥ := by
  intro h
  have h0 : flowValue arcs s (0 : Fin m → ℝ) = 0 := by simp [flowValue]
  have hle := le_maxFlowValue (zero_feasible (arcs := arcs) u s t)
  rw [h, h0] at hle
  simp at hle

/-- If a maximum flow exists, no augmenting path can exist for it. -/
lemma no_augmenting_of_max {u : Fin m → ℝ≥0∞} {s t : Fin n} (hst : s ≠ t) {f : Fin m → ℝ}
    (hf : IsFeasibleMaxFlow arcs u s t f)
    (hmax : ∀ f', IsFeasibleMaxFlow arcs u s t f' → flowValue arcs s f' ≤ flowValue arcs s f) :
    ¬ ∃ steps, IsAugmentingPath arcs u s t f steps := by
  rintro ⟨P, hP⟩
  have hδ : 0 < augmentingDelta u f P := augmentingDelta_pos hP
  by_cases htop : augmentingDelta u f P = ⊤
  · obtain ⟨hfeas, hval⟩ := push_feasible hst hf hP (ε := 1) one_pos (by rw [htop]; exact le_top)
    have := hmax _ hfeas
    rw [hval] at this
    linarith
  · have hpos : 0 < (augmentingDelta u f P).toReal := ENNReal.toReal_pos hδ.ne' htop
    obtain ⟨hfeas, hval⟩ := push_feasible hst hf hP hpos
      (by rw [ENNReal.ofReal_toReal htop])
    have := hmax _ hfeas
    rw [hval] at this
    linarith

end MFMC

open LinearOptimization MFMC
open Matrix
open scoped ENNReal

theorem solution {n m : ℕ} (arcs : Fin m → Fin n × Fin n)
    (u : Fin m → ℝ≥0∞) (s t : Fin n)
    (hst : s ≠ t) (hloop : HasNoSelfLoops arcs) (hupos : ∀ k, 0 < u k) :
    (∀ f, IsFeasibleMaxFlow arcs u s t f →
      (¬∃ steps, IsAugmentingPath arcs u s t f steps) →
      ∀ f', IsFeasibleMaxFlow arcs u s t f' →
        flowValue arcs s f' ≤ flowValue arcs s f) ∧
    maxFlowValue arcs u s t =
      ⨅ S ∈ {S : Finset (Fin n) | IsCut s t S},
        ((cutCapacity arcs u S : ℝ≥0∞) : EReal) ∧
    (maxFlowValue arcs u s t ≠ ⊤ →
      ∃ f, IsFeasibleMaxFlow arcs u s t f ∧
        ((flowValue arcs s f : ℝ) : EReal) = maxFlowValue arcs u s t) := by
  classical
  -- Part (a): a flow admitting no augmenting path is optimal.
  have parta : ∀ f, IsFeasibleMaxFlow arcs u s t f →
      (¬∃ steps, IsAugmentingPath arcs u s t f steps) →
      ∀ f', IsFeasibleMaxFlow arcs u s t f' →
        flowValue arcs s f' ≤ flowValue arcs s f := by
    intro f hf hno f' hf'
    obtain ⟨S, hcut, hnn, heq⟩ := cut_of_no_augmenting hf hno
    have h1 : ENNReal.ofReal (flowValue arcs s f') ≤ ENNReal.ofReal (flowValue arcs s f) := by
      rw [heq]; exact weak_duality hf' hcut
    exact (ENNReal.ofReal_le_ofReal_iff hnn).1 h1
  refine ⟨parta, ?_⟩
  by_cases htop : maxFlowValue arcs u s t = ⊤
  · -- every cut has infinite capacity
    have hall : ∀ S : Finset (Fin n), IsCut s t S → cutCapacity arcs u S = ⊤ := by
      intro S hS
      by_contra hne
      have hbound : ∀ f, IsFeasibleMaxFlow arcs u s t f →
          flowValue arcs s f ≤ (cutCapacity arcs u S).toReal := by
        intro f hf
        have h1 := weak_duality hf hS
        rw [← ENNReal.ofReal_toReal hne] at h1
        exact (ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg).1 h1
      have : maxFlowValue arcs u s t ≤ (((cutCapacity arcs u S).toReal : ℝ) : EReal) := by
        refine iSup₂_le (fun f hf => ?_)
        exact_mod_cast hbound f hf
      rw [htop] at this
      exact absurd (top_le_iff.1 this) (by simp)
    refine ⟨?_, fun h => absurd htop h⟩
    rw [htop]
    refine le_antisymm (le_iInf₂ (fun S hS => ?_)) le_top
    rw [hall S hS, EReal.coe_ennreal_top]
  · -- the maximum is attained
    have hbot := maxFlowValue_ne_bot (arcs := arcs) u s t
    have hR : ∀ f, IsFeasibleMaxFlow arcs u s t f →
        flowValue arcs s f ≤ (maxFlowValue arcs u s t).toReal := by
      intro f hf
      have h1 := le_maxFlowValue hf
      rw [← EReal.coe_toReal htop hbot] at h1
      exact_mod_cast h1
    obtain ⟨g, hg, hgmax⟩ := exists_max_flow hR
    have hnoaug := no_augmenting_of_max hst hg hgmax
    obtain ⟨S₀, hcut₀, hnn₀, heq₀⟩ := cut_of_no_augmenting hg hnoaug
    have hmaxval : maxFlowValue arcs u s t = ((flowValue arcs s g : ℝ) : EReal) := by
      refine le_antisymm (iSup₂_le (fun f hf => ?_)) (le_maxFlowValue hg)
      exact_mod_cast hgmax f hf
    have hcoe : ((cutCapacity arcs u S₀ : ℝ≥0∞) : EReal) = ((flowValue arcs s g : ℝ) : EReal) := by
      rw [← heq₀, EReal.coe_ennreal_ofReal, max_eq_left hnn₀]
    refine ⟨?_, fun _ => ⟨g, hg, hmaxval.symm⟩⟩
    rw [hmaxval]
    refine le_antisymm (le_iInf₂ (fun S hS => ?_)) ?_
    · rw [← hcoe]
      exact EReal.coe_ennreal_le_coe_ennreal_iff.2 (heq₀ ▸ weak_duality hg hS)
    · rw [← hcoe]
      exact iInf₂_le S₀ hcut₀
