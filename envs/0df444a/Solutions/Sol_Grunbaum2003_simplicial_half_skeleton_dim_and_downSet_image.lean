-- Prove2me | solution 1 for Grunbaum2003.simplicial_half_skeleton_dim_and_downSet_image
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-01T19:52:43.123446+00:00
-- url     : https://prove2.me/submissions/74b301c1-6b8b-4cb7-bb5a-00f07389fbcc

import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.InnerProductSpace.PiL2
import Definitions.Def_Grunbaum2003_IsSimplicialDPolytope
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Order.Hom.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Analysis.Convex.Hull
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_Grunbaum2003_SkeletonFace
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd

-- Ingredient: simplicial_disproof_p/build4331/FiniteHullFaces.lean

set_option autoImplicit false

namespace Grunbaum2003

/-- Any exposed face of a finite hull is the hull of its incident input points.
The input need not be an irredundant vertex list. -/
theorem exposedFace_eq_convexHull_incident_range {d n : ℕ}
    (v : Fin n → Fin d → ℝ) {F : Set (Fin d → ℝ)}
    (hF : IsExposed ℝ (convexHull ℝ (Set.range v)) F) :
    F = convexHull ℝ (F ∩ Set.range v) := by
  have hPcomp : IsCompact (convexHull ℝ (Set.range v)) :=
    (Set.finite_range v).isCompact_convexHull ℝ
  have hFcomp : IsCompact F := hF.isCompact hPcomp
  have hFconv : Convex ℝ F := hF.convex (convex_convexHull ℝ (Set.range v))
  have hExtRange : F.extremePoints ℝ ⊆ Set.range v := by
    intro x hx
    rw [hF.isExtreme.extremePoints_eq] at hx
    exact extremePoints_convexHull_subset hx.2
  have hExtFin : (F.extremePoints ℝ).Finite := (Set.finite_range v).subset hExtRange
  have hKM := closure_convexHull_extremePoints hFcomp hFconv
  rw [(hExtFin.isCompact_convexHull ℝ).isClosed.closure_eq] at hKM
  apply Set.Subset.antisymm
  · apply hKM.symm.subset.trans
    apply convexHull_mono
    intro x hx
    exact ⟨extremePoints_subset hx, hExtRange hx⟩
  · exact convexHull_min Set.inter_subset_left hFconv

/-- Containment of finite-hull faces is exactly containment of their incident
input-label sets. This provides the order embedding used by finite certificates. -/
theorem exposedFace_subset_iff_incident_labels {d n : ℕ}
    (v : Fin n → Fin d → ℝ) {F G : Set (Fin d → ℝ)}
    (hF : IsExposed ℝ (convexHull ℝ (Set.range v)) F)
    (hG : IsExposed ℝ (convexHull ℝ (Set.range v)) G) :
    F ⊆ G ↔ ∀ i : Fin n, v i ∈ F → v i ∈ G := by
  constructor
  · intro h i hi
    exact h hi
  · intro h
    rw [exposedFace_eq_convexHull_incident_range v hF,
      exposedFace_eq_convexHull_incident_range v hG]
    apply convexHull_mono
    rintro x ⟨hx, i, rfl⟩
    exact ⟨h i hx, ⟨i, rfl⟩⟩

/-- A finite rational/linear support certificate realizes a face and certifies
its exact input-label incidence set. -/
theorem exposedFace_of_label_maximizers {d n : ℕ}
    (v : Fin n → Fin d → ℝ) (s : Set (Fin n)) (hs : s.Nonempty)
    (l : (Fin d → ℝ) →L[ℝ] ℝ) (b : ℝ)
    (hbound : ∀ i : Fin n, l (v i) ≤ b)
    (heq : ∀ i : Fin n, l (v i) = b ↔ i ∈ s) :
    IsExposed ℝ (convexHull ℝ (Set.range v)) (convexHull ℝ (v '' s)) ∧
      ∀ i : Fin n, v i ∈ convexHull ℝ (v '' s) ↔ i ∈ s := by
  let P := convexHull ℝ (Set.range v)
  let F := l.toExposed P
  have hPbound : ∀ x ∈ P, l x ≤ b := by
    have hconv : Convex ℝ {x : Fin d → ℝ | l x ≤ b} := by
      intro x hx y hy a c ha hc hac
      change l (a • x + c • y) ≤ b
      rw [map_add, map_smul, map_smul]
      change a * l x + c * l y ≤ b
      calc a * l x + c * l y ≤ a * b + c * b :=
          add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hc)
        _ = b := by rw [← add_mul, hac, one_mul]
    exact convexHull_min (by rintro _ ⟨i, rfl⟩; exact hbound i) hconv
  have hFlabels : ∀ i : Fin n, v i ∈ F ↔ i ∈ s := by
    intro i
    constructor
    · intro hi
      obtain ⟨j, hj⟩ := hs
      have hbj : l (v j) = b := (heq j).mpr hj
      have hbi : b ≤ l (v i) := by
        rw [← hbj]
        exact hi.2 (v j) (subset_convexHull ℝ _ (Set.mem_range_self j))
      exact (heq i).mp (le_antisymm (hbound i) hbi)
    · intro hi
      refine ⟨subset_convexHull ℝ _ (Set.mem_range_self i), ?_⟩
      intro x hx
      rw [(heq i).mpr hi]
      exact hPbound x hx
  have hInc : F ∩ Set.range v = v '' s := by
    ext x
    constructor
    · rintro ⟨hx, i, rfl⟩
      exact ⟨i, (hFlabels i).mp hx, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨(hFlabels i).mpr hi, Set.mem_range_self i⟩
  have hFhull : F = convexHull ℝ (v '' s) := by
    calc F = convexHull ℝ (F ∩ Set.range v) :=
          exposedFace_eq_convexHull_incident_range v
            (ContinuousLinearMap.toExposed.isExposed (l := l) (A := P))
      _ = convexHull ℝ (v '' s) := congrArg (convexHull ℝ) hInc
  constructor
  · rw [← hFhull]
    exact (ContinuousLinearMap.toExposed.isExposed (l := l) (A := P))
  · intro i
    rw [← hFhull]
    exact hFlabels i

/-- A complete finite incidence certificate identifies the actual exposed-face
poset. The two certificate obligations concern only its finite label family. -/
theorem exposedFaces_orderIso_of_incidence_certificate {d n : ℕ}
    (v : Fin n → Fin d → ℝ) (family : Finset (Finset (Fin n)))
    (hSound : ∀ F : Set (Fin d → ℝ),
      IsExposed ℝ (convexHull ℝ (Set.range v)) F →
      ∀ s : Finset (Fin n), (∀ i : Fin n, i ∈ s ↔ v i ∈ F) → s ∈ family)
    (hComplete : ∀ s ∈ family,
      IsExposed ℝ (convexHull ℝ (Set.range v)) (convexHull ℝ (v '' (s : Set (Fin n)))) ∧
        ∀ i : Fin n, v i ∈ convexHull ℝ (v '' (s : Set (Fin n))) ↔ i ∈ s) :
    Nonempty ({F : Set (Fin d → ℝ) // IsExposed ℝ (convexHull ℝ (Set.range v)) F} ≃o
      ↥family) := by
  classical
  let f : {F : Set (Fin d → ℝ) // IsExposed ℝ (convexHull ℝ (Set.range v)) F} ↪o ↥family := {
    toFun := fun F => ⟨Finset.univ.filter (fun i => v i ∈ F.val),
      hSound F.val F.property _ (by intro i; simp only [Finset.mem_filter, Finset.mem_univ, true_and])⟩
    inj' := by
      intro F G h
      have hfg : (Finset.univ.filter fun i => v i ∈ F.val) =
          (Finset.univ.filter fun i => v i ∈ G.val) := congrArg Subtype.val h
      have hi : ∀ i : Fin n, v i ∈ F.val ↔ v i ∈ G.val := by
        intro i
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using
          (Finset.ext_iff.mp hfg i)
      apply Subtype.ext
      apply Set.Subset.antisymm
      · exact (exposedFace_subset_iff_incident_labels v F.property G.property).mpr
          (fun i hv => (hi i).mp hv)
      · exact (exposedFace_subset_iff_incident_labels v G.property F.property).mpr
          (fun i hv => (hi i).mpr hv)
    map_rel_iff' := by
      intro F G
      change (Finset.univ.filter (fun i => v i ∈ F.val)) ⊆
        (Finset.univ.filter (fun i => v i ∈ G.val)) ↔ F.val ⊆ G.val
      simpa only [Finset.subset_iff, Finset.mem_filter,
        Finset.mem_univ, true_and] using
        (exposedFace_subset_iff_incident_labels v F.property G.property).symm }
  have hf : Function.Surjective f := by
    intro s
    refine ⟨⟨convexHull ℝ (v '' (s.val : Set (Fin n))), (hComplete s.val s.property).1⟩, ?_⟩
    apply Subtype.ext
    ext i
    change i ∈ Finset.univ.filter (fun i => v i ∈ convexHull ℝ (v '' (s.val : Set (Fin n)))) ↔
      i ∈ s.val
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using
      (hComplete s.val s.property).2 i
  exact ⟨OrderIso.ofSurjective f hf⟩

/-- The complete certificate isomorphism retains the actual vertex incidences. -/
theorem exposedFaces_orderIso_of_incidence_certificate_with_incidence {d n : ℕ}
    (v : Fin n → Fin d → ℝ) (family : Finset (Finset (Fin n)))
    (hSound : ∀ F : Set (Fin d → ℝ),
      IsExposed ℝ (convexHull ℝ (Set.range v)) F →
      ∀ s : Finset (Fin n), (∀ i : Fin n, i ∈ s ↔ v i ∈ F) → s ∈ family)
    (hComplete : ∀ s ∈ family,
      IsExposed ℝ (convexHull ℝ (Set.range v)) (convexHull ℝ (v '' (s : Set (Fin n)))) ∧
        ∀ i : Fin n, v i ∈ convexHull ℝ (v '' (s : Set (Fin n))) ↔ i ∈ s) :
    ∃ Φ : {F : Set (Fin d → ℝ) // IsExposed ℝ (convexHull ℝ (Set.range v)) F} ≃o ↥family,
      ∀ F i, i ∈ (Φ F).val ↔ v i ∈ F.val := by
  classical
  let f : {F : Set (Fin d → ℝ) // IsExposed ℝ (convexHull ℝ (Set.range v)) F} ↪o ↥family := {
    toFun := fun F => ⟨Finset.univ.filter (fun i => v i ∈ F.val),
      hSound F.val F.property _ (by intro i; simp only [Finset.mem_filter, Finset.mem_univ, true_and])⟩
    inj' := by
      intro F G h
      have hfg : (Finset.univ.filter fun i => v i ∈ F.val) =
          (Finset.univ.filter fun i => v i ∈ G.val) := congrArg Subtype.val h
      have hi : ∀ i : Fin n, v i ∈ F.val ↔ v i ∈ G.val := by
        intro i
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using
          (Finset.ext_iff.mp hfg i)
      apply Subtype.ext
      apply Set.Subset.antisymm
      · exact (exposedFace_subset_iff_incident_labels v F.property G.property).mpr
          (fun i hv => (hi i).mp hv)
      · exact (exposedFace_subset_iff_incident_labels v G.property F.property).mpr
          (fun i hv => (hi i).mpr hv)
    map_rel_iff' := by
      intro F G
      change (Finset.univ.filter (fun i => v i ∈ F.val)) ⊆
        (Finset.univ.filter (fun i => v i ∈ G.val)) ↔ F.val ⊆ G.val
      simpa only [Finset.subset_iff, Finset.mem_filter,
        Finset.mem_univ, true_and] using
        (exposedFace_subset_iff_incident_labels v F.property G.property).symm }
  have hf : Function.Surjective f := by
    intro s
    refine ⟨⟨convexHull ℝ (v '' (s.val : Set (Fin n))), (hComplete s.val s.property).1⟩, ?_⟩
    apply Subtype.ext
    ext i
    change i ∈ Finset.univ.filter (fun i => v i ∈ convexHull ℝ (v '' (s.val : Set (Fin n)))) ↔
      i ∈ s.val
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using
      (hComplete s.val s.property).2 i
  refine ⟨OrderIso.ofSurjective f hf, ?_⟩
  intro F i
  change i ∈ Finset.univ.filter (fun i => v i ∈ F.val) ↔ v i ∈ F.val
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

end Grunbaum2003



-- Ingredient: simplicial_disproof_p/build4331/PGeometry.lean

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section

namespace Grunbaum2003.CounterexampleGeometry

def pVertices (i : Fin 7) (j : Fin 5) : ℝ :=
  match i.val, j.val with
  | 1, 0 => 1
  | 2, 1 => 1
  | 3, 2 => 1
  | 4, 3 => 1
  | 5, 4 => 1
  | 6, 4 => -1
  | 5, _ => 1/5
  | 6, _ => 1/5
  | _, _ => 0

def pBody : Set (Fin 5 → ℝ) := convexHull ℝ (Set.range pVertices)

private def omitIndex (j : Fin 7) (i : Fin 6) : Fin 7 :=
  ⟨if i.val < j.val then i.val else i.val + 1, by split_ifs <;> omega⟩

private theorem omitIndex_eq_succAbove (j : Fin 7) (i : Fin 6) :
    omitIndex j i = j.succAbove i := by
  fin_cases j <;> fin_cases i <;> decide

/-- Every six of the seven bipyramid vertices are affinely independent. -/
theorem pVertices_six_independent (j : Fin 7) :
    AffineIndependent ℝ (fun i : Fin 6 => pVertices (j.succAbove i)) := by
  simp_rw [← omitIndex_eq_succAbove]
  rw [affineIndependent_iff_of_fintype]
  intro w hw hv i
  obtain ⟨a0, a1, a2, a3, a4, a5, heq⟩ :
      ∃ a0 a1 a2 a3 a4 a5 : ℝ,
        w = (fun i : Fin 6 => match i.val with
          | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3 | 4 => a4 | _ => a5) := by
    refine ⟨w 0, w 1, w 2, w 3, w 4, w 5, ?_⟩
    ext i
    fin_cases i <;> rfl
  subst w
  rw [Finset.weightedVSub_eq_linear_combination _ hw] at hv
  have h0 := congrFun hv 0
  have h1 := congrFun hv 1
  have h2 := congrFun hv 2
  have h3 := congrFun hv 3
  have h4 := congrFun hv 4
  fin_cases j <;>
    norm_num [Fin.sum_univ_succ, pVertices, omitIndex,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hw h0 h1 h2 h3 h4 ⊢ <;>
    fin_cases i <;>
      (first | change a0 = 0 | change a1 = 0 | change a2 = 0 |
        change a3 = 0 | change a4 = 0 | change a5 = 0) <;>
      linarith only [hw, h0, h1, h2, h3, h4]

theorem pBody_affineSpan : affineSpan ℝ pBody = ⊤ := by
  have htop : affineSpan ℝ (Set.range (fun i : Fin 6 => pVertices ((6 : Fin 7).succAbove i))) = ⊤ := by
    apply (pVertices_six_independent 6).affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr
    norm_num
  apply top_unique
  rw [← htop]
  apply affineSpan_mono
  rintro x ⟨i, rfl⟩
  exact subset_convexHull ℝ _ (Set.mem_range_self _)

theorem pBody_isDPolytope : IsDPolytope pBody :=
  ⟨⟨Set.range pVertices, Set.finite_range _, Set.range_nonempty _, rfl⟩, pBody_affineSpan⟩

end Grunbaum2003.CounterexampleGeometry


namespace Grunbaum2003.CounterexampleGeometry

theorem pBody_isSimplicialDPolytope : IsSimplicialDPolytope pBody := by
  classical
  refine ⟨pBody_isDPolytope, ?_⟩
  intro F hne hF hdim
  have hFne : F ≠ pBody := by
    intro hEq
    rw [hEq, pBody_affineSpan] at hdim
    rw [AffineSubspace.direction_top] at hdim
    norm_num at hdim
  obtain ⟨j, hj⟩ : ∃ j : Fin 7, pVertices j ∉ F := by
    by_contra! hall
    apply hFne
    apply Set.Subset.antisymm hF.subset
    exact convexHull_min (by rintro _ ⟨i, rfl⟩; exact hall i)
      (hF.convex (convex_convexHull ℝ _))
  let I := {i : Fin 7 // pVertices i ∈ F}
  let V : I → Fin 5 → ℝ := fun i => pVertices i.val
  have hFrange : F = convexHull ℝ (Set.range V) := by
    rw [exposedFace_eq_convexHull_incident_range pVertices hF]
    congr 1
    ext x
    constructor
    · rintro ⟨hx, i, rfl⟩
      exact ⟨⟨i, hx⟩, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i.property, Set.mem_range_self i.val⟩
  have hIne : Nonempty I := by
    have hh : (convexHull ℝ (Set.range V)).Nonempty := hFrange ▸ hne
    obtain ⟨x, i, rfl⟩ := convexHull_nonempty_iff.mp hh
    exact ⟨i⟩
  let emb : I ↪ {i : Fin 7 // i ≠ j} := {
    toFun := fun i => ⟨i.val, fun hij => hj (hij ▸ i.property)⟩
    inj' := by intro i k h; exact Subtype.ext (congrArg (fun t => t.val) h) }
  have hi6 : AffineIndependent ℝ (fun i : {i : Fin 7 // i ≠ j} => pVertices i.val) := by
    apply (affineIndependent_equiv (finSuccAboveEquiv j)).mp
    exact pVertices_six_independent j
  have hi : AffineIndependent ℝ V := hi6.comp_embedding emb
  have : Nonempty I := hIne
  have hCard : Fintype.card I = 5 := by
    have hRank := hi.finrank_vectorSpan_add_one
    rw [← direction_affineSpan, ← affineSpan_convexHull, ← hFrange] at hRank
    omega
  let e : Fin 5 ≃ I := Fintype.equivOfCardEq (by simpa only [Fintype.card_fin] using hCard.symm)
  refine ⟨V ∘ e, hi.comp_embedding e.toEmbedding, ?_⟩
  rw [e.surjective.range_comp V]
  exact hFrange

end Grunbaum2003.CounterexampleGeometry

end

-- Ingredient: skeleton_work/exact4331/CounterexampleGeometry.lean

set_option autoImplicit false

noncomputable section

namespace Grunbaum2003.CounterexampleGeometry

def qVertices (i : Fin 7) (j : Fin 5) : ℝ :=
  match i.val, j.val with
  | 1, 0 => 1
  | 2, 1 => 1
  | 3, 2 => 1
  | 4, 4 => 1
  | 5, 0 | 5, 1 | 5, 2 => 1/4
  | 6, 0 | 6, 1 | 6, 2 => 1/4
  | 5, 3 => 1
  | 6, 3 => -1
  | _, _ => 0

def qBody : Set (Fin 5 → ℝ) := convexHull ℝ (Set.range qVertices)

def tetrahedron : Set (Fin 5 → ℝ) :=
  convexHull ℝ (qVertices '' ({0, 1, 2, 3} : Set (Fin 7)))

theorem q_midpoint_circuit :
    midpoint ℝ (qVertices 5) (qVertices 6) =
      midpoint ℝ (midpoint ℝ (qVertices 0) (qVertices 1))
        (midpoint ℝ (qVertices 2) (qVertices 3)) := by
  ext j
  fin_cases j <;>
    norm_num [qVertices, midpoint_eq_smul_add, Pi.add_apply, Pi.smul_apply]

/-- The central tetrahedron is not exposed in the pyramid over the bipyramid.
Its barycenter is the midpoint of two vertices outside the tetrahedron. -/
theorem tetrahedron_not_exposed : ¬ IsExposed ℝ qBody tetrahedron := by
  intro h
  have htconv : Convex ℝ tetrahedron := convex_convexHull ℝ _
  have hi : ∀ i ∈ ({0, 1, 2, 3} : Set (Fin 7)), qVertices i ∈ tetrahedron := by
    intro i hi
    exact subset_convexHull ℝ _ (Set.mem_image_of_mem qVertices hi)
  have hm : midpoint ℝ (qVertices 5) (qVertices 6) ∈ tetrahedron := by
    have hmid := htconv.midpoint_mem
      (htconv.midpoint_mem (hi 0 (by simp)) (hi 1 (by simp)))
      (htconv.midpoint_mem (hi 2 (by simp)) (hi 3 (by simp)))
    rw [q_midpoint_circuit]
    exact hmid
  have hu : qVertices 5 ∈ tetrahedron :=
    h.isExtreme.left_mem_of_mem_openSegment
      (subset_convexHull ℝ _ (Set.mem_range_self 5))
      (subset_convexHull ℝ _ (Set.mem_range_self 6)) hm
      (midpoint_mem_openSegment (qVertices 5) (qVertices 6))
  have hzero : tetrahedron ⊆ {x : Fin 5 → ℝ | x 3 = 0} := by
    refine convexHull_min ?_ ?_
    · rintro x ⟨i, hi, rfl⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi
      rcases hi with rfl | rfl | rfl | rfl <;> norm_num [qVertices]
    · intro x hx y hy a b ha hb hab
      change a * x 3 + b * y 3 = 0
      rw [hx, hy, mul_zero, mul_zero, add_zero]
  have := hzero hu
  norm_num [qVertices] at this

/-- The unique nontrivial positive circuit controls which input-label sets
can be exposed faces, including the nonsimplicial base facet. -/
theorem exposedFace_q_circuit_iff {F : Set (Fin 5 → ℝ)}
    (hF : IsExposed ℝ qBody F) :
    (∀ i ∈ ({0, 1, 2, 3} : Set (Fin 7)), qVertices i ∈ F) ↔
      qVertices 5 ∈ F ∧ qVertices 6 ∈ F := by
  have hPconv : Convex ℝ qBody := convex_convexHull ℝ _
  have hFconv : Convex ℝ F := hF.convex hPconv
  have hv : ∀ i : Fin 7, qVertices i ∈ qBody :=
    fun i => subset_convexHull ℝ _ (Set.mem_range_self i)
  have h01P := hPconv.midpoint_mem (hv 0) (hv 1)
  have h23P := hPconv.midpoint_mem (hv 2) (hv 3)
  constructor
  · intro hi
    have hm := hFconv.midpoint_mem
      (hFconv.midpoint_mem (hi 0 (by simp)) (hi 1 (by simp)))
      (hFconv.midpoint_mem (hi 2 (by simp)) (hi 3 (by simp)))
    rw [← q_midpoint_circuit] at hm
    exact ⟨hF.isExtreme.left_mem_of_mem_openSegment (hv 5) (hv 6) hm
        (midpoint_mem_openSegment _ _),
      hF.isExtreme.right_mem_of_mem_openSegment (hv 5) (hv 6) hm
        (midpoint_mem_openSegment _ _)⟩
  · rintro ⟨hu, hv'⟩
    have hm := hFconv.midpoint_mem hu hv'
    rw [q_midpoint_circuit] at hm
    have h01F := hF.isExtreme.left_mem_of_mem_openSegment h01P h23P hm
      (midpoint_mem_openSegment _ _)
    have h23F := hF.isExtreme.right_mem_of_mem_openSegment h01P h23P hm
      (midpoint_mem_openSegment _ _)
    intro i hi
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact hF.isExtreme.left_mem_of_mem_openSegment (hv 0) (hv 1) h01F
        (midpoint_mem_openSegment _ _)
    · exact hF.isExtreme.right_mem_of_mem_openSegment (hv 0) (hv 1) h01F
        (midpoint_mem_openSegment _ _)
    · exact hF.isExtreme.left_mem_of_mem_openSegment (hv 2) (hv 3) h23F
        (midpoint_mem_openSegment _ _)
    · exact hF.isExtreme.right_mem_of_mem_openSegment (hv 2) (hv 3) h23F
        (midpoint_mem_openSegment _ _)

end Grunbaum2003.CounterexampleGeometry


end

-- Ingredient: simplicial_disproof_p/build4331/CounterexampleIncidences.lean

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Grunbaum2003.CounterexampleIncidences

def pFaces : Finset (Finset (Fin 7)) :=
  (Finset.univ : Finset (Fin 7)).powerset.filter fun s => s = Finset.univ ∨
    (¬ ({5, 6} : Finset (Fin 7)) ⊆ s ∧ ¬ ({0, 1, 2, 3, 4} : Finset (Fin 7)) ⊆ s)

def qFaces : Finset (Finset (Fin 7)) :=
  (Finset.univ : Finset (Fin 7)).powerset.filter fun s => s.erase 4 = {0, 1, 2, 3, 5, 6} ∨
    (¬ ({5, 6} : Finset (Fin 7)) ⊆ s.erase 4 ∧
      ¬ ({0, 1, 2, 3} : Finset (Fin 7)) ⊆ s.erase 4)

theorem pFaces_card : pFaces.card = 94 := by decide

theorem qFaces_card : qFaces.card = 92 := by decide

theorem two_skeleton_eq :
    pFaces.filter (fun s => s.card ≤ 3) = qFaces.filter (fun s => s.card ≤ 3) := by decide

theorem tetrahedron_only_in_p :
    ({0, 1, 2, 3} : Finset (Fin 7)) ∈ pFaces ∧
      ({0, 1, 2, 3} : Finset (Fin 7)) ∉ qFaces := by decide

theorem two_skeleton_orderIso :
    Nonempty (↥(pFaces.filter (fun s => s.card ≤ 3)) ≃o
      ↥(qFaces.filter (fun s => s.card ≤ 3))) := by
  rw [two_skeleton_eq]
  exact ⟨OrderIso.refl _⟩

theorem no_full_orderIso : IsEmpty (↥pFaces ≃o ↥qFaces) := by
  constructor
  intro φ
  have hc := Fintype.card_congr φ.toEquiv
  rw [Fintype.card_coe, Fintype.card_coe, pFaces_card, qFaces_card] at hc
  exact (by decide : (94 : ℕ) ≠ 92) hc

theorem pFaces_of_circuit : ∀ s : Finset (Fin 7),
    (({0, 1, 2, 3, 4} : Finset (Fin 7)) ⊆ s ↔ ({5, 6} : Finset (Fin 7)) ⊆ s) →
      s ∈ pFaces := by decide

theorem qFaces_of_circuit : ∀ s : Finset (Fin 7),
    (({0, 1, 2, 3} : Finset (Fin 7)) ⊆ s ↔ ({5, 6} : Finset (Fin 7)) ⊆ s) →
      s ∈ qFaces := by decide

end Grunbaum2003.CounterexampleIncidences


-- Ingredient: simplicial_disproof_p/build4331/PSoundness.lean

set_option autoImplicit false

namespace Grunbaum2003.CounterexampleGeometry
open Grunbaum2003.CounterexampleIncidences

theorem p_values_circuit (l : (Fin 5 → ℝ) →L[ℝ] ℝ) :
    5 * (l (pVertices 5) + l (pVertices 6)) =
      2 * (l (pVertices 0) + l (pVertices 1) + l (pVertices 2) +
        l (pVertices 3) + l (pVertices 4)) := by
  have hv : (5 : ℝ) • (pVertices 5 + pVertices 6) =
      (2 : ℝ) • (pVertices 0 + pVertices 1 + pVertices 2 + pVertices 3 + pVertices 4) := by
    ext i
    fin_cases i <;> norm_num [pVertices, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have h := congrArg l hv
  simpa only [map_smul, map_add, smul_eq_mul] using h

theorem exposedFace_p_circuit_iff {F : Set (Fin 5 → ℝ)}
    (hF : IsExposed ℝ pBody F) :
    (∀ i ∈ ({0, 1, 2, 3, 4} : Set (Fin 7)), pVertices i ∈ F) ↔
      pVertices 5 ∈ F ∧ pVertices 6 ∈ F := by
  classical
  by_cases hne : F.Nonempty
  · obtain ⟨x, hx⟩ := hne
    obtain ⟨l, hl⟩ := hF ⟨x, hx⟩
    have hx' : x ∈ pBody ∧ ∀ y ∈ pBody, l y ≤ l x := by
      simpa only [hl, Set.mem_ofPred_eq] using hx
    have hP : ∀ i : Fin 7, pVertices i ∈ pBody :=
      fun i => subset_convexHull ℝ _ (Set.mem_range_self i)
    have hbound : ∀ i : Fin 7, l (pVertices i) ≤ l x := fun i => hx'.2 _ (hP i)
    have hmem : ∀ i : Fin 7, pVertices i ∈ F ↔ l (pVertices i) = l x := by
      intro i
      constructor
      · intro hi
        have hi' : pVertices i ∈ pBody ∧ ∀ y ∈ pBody, l y ≤ l (pVertices i) := by
          simpa only [hl, Set.mem_ofPred_eq] using hi
        exact le_antisymm (hbound i) (hi'.2 x hx'.1)
      · intro hi
        rw [hl]
        exact ⟨hP i, fun y hy => hi ▸ hx'.2 y hy⟩
    have hc := p_values_circuit l
    have h0 := hbound 0
    have h1 := hbound 1
    have h2 := hbound 2
    have h3 := hbound 3
    have h4 := hbound 4
    have h5 := hbound 5
    have h6 := hbound 6
    constructor
    · intro hi
      have he0 := (hmem 0).mp (hi 0 (by simp))
      have he1 := (hmem 1).mp (hi 1 (by simp))
      have he2 := (hmem 2).mp (hi 2 (by simp))
      have he3 := (hmem 3).mp (hi 3 (by simp))
      have he4 := (hmem 4).mp (hi 4 (by simp))
      exact ⟨(hmem 5).mpr (by linarith only [hc, h5, h6, he0, he1, he2, he3, he4]),
        (hmem 6).mpr (by linarith only [hc, h5, h6, he0, he1, he2, he3, he4])⟩
    · rintro ⟨hu, hv⟩
      have he5 := (hmem 5).mp hu
      have he6 := (hmem 6).mp hv
      have he0 : l (pVertices 0) = l x := by linarith only [hc, h0, h1, h2, h3, h4, he5, he6]
      have he1 : l (pVertices 1) = l x := by linarith only [hc, h0, h1, h2, h3, h4, he5, he6]
      have he2 : l (pVertices 2) = l x := by linarith only [hc, h0, h1, h2, h3, h4, he5, he6]
      have he3 : l (pVertices 3) = l x := by linarith only [hc, h0, h1, h2, h3, h4, he5, he6]
      have he4 : l (pVertices 4) = l x := by linarith only [hc, h0, h1, h2, h3, h4, he5, he6]
      intro i hi
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl
      · exact (hmem 0).mpr he0
      · exact (hmem 1).mpr he1
      · exact (hmem 2).mpr he2
      · exact (hmem 3).mpr he3
      · exact (hmem 4).mpr he4
  · constructor
    · intro h
      exact False.elim (hne ⟨pVertices 0, h 0 (by simp)⟩)
    · intro h
      exact False.elim (hne ⟨pVertices 5, h.1⟩)

theorem pFace_incidence_sound (F : Set (Fin 5 → ℝ)) (hF : IsExposed ℝ pBody F)
    (s : Finset (Fin 7)) (hs : ∀ i : Fin 7, i ∈ s ↔ pVertices i ∈ F) :
    s ∈ pFaces := by
  apply pFaces_of_circuit s
  constructor
  · intro hbase
    have hbase' : ∀ i ∈ ({0, 1, 2, 3, 4} : Set (Fin 7)), pVertices i ∈ F := by
      intro i hi
      apply (hs i).mp
      apply hbase
      simpa only [Finset.mem_insert, Finset.mem_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] using hi
    obtain ⟨hu, hv⟩ := (exposedFace_p_circuit_iff hF).mp hbase'
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact (hs 5).mpr hu
    · exact (hs 6).mpr hv
  · intro hpoles
    have hu : pVertices 5 ∈ F := (hs 5).mp (hpoles (by simp))
    have hv : pVertices 6 ∈ F := (hs 6).mp (hpoles (by simp))
    have hbase := (exposedFace_p_circuit_iff hF).mpr ⟨hu, hv⟩
    intro i hi
    apply (hs i).mpr
    apply hbase i
    simpa only [Finset.mem_insert, Finset.mem_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] using hi

end Grunbaum2003.CounterexampleGeometry


-- Ingredient: simplicial_disproof_p/build4331/PAnyFour.lean

set_option autoImplicit false

noncomputable section

namespace Grunbaum2003.CounterexampleGeometry

theorem pVertices_independent_of_card_le_six (s : Finset (Fin 7)) (hs : s.card ≤ 6) :
    AffineIndependent ℝ (fun i : ↥s => pVertices i.val) := by
  classical
  obtain ⟨j, hj⟩ : ∃ j : Fin 7, j ∉ s := by
    by_contra! h
    have heq : s = Finset.univ := Finset.eq_univ_iff_forall.mpr h
    rw [heq] at hs
    norm_num at hs
  let emb : ↥s ↪ {i : Fin 7 // i ≠ j} := {
    toFun := fun i => ⟨i.val, fun hij => hj (hij ▸ i.property)⟩
    inj' := by intro i k h; exact Subtype.ext (congrArg (fun t => t.val) h) }
  have hi : AffineIndependent ℝ (fun i : {i : Fin 7 // i ≠ j} => pVertices i.val) := by
    apply (affineIndependent_equiv (finSuccAboveEquiv j)).mp
    exact pVertices_six_independent j
  exact hi.comp_embedding emb

theorem pVertices_independent_of_card_le_four (s : Finset (Fin 7)) (hs : s.card ≤ 4) :
    AffineIndependent ℝ (fun i : ↥s => pVertices i.val) :=
  pVertices_independent_of_card_le_six s (by omega)

/-- Four distinct labels avoid some deletion other than any one specified label. -/
theorem four_independent_of_six_independent_except (v : Fin 7 → Fin 5 → ℝ)
    (b : Fin 7)
    (hSix : ∀ j : Fin 7, j ≠ b → AffineIndependent ℝ (fun i : Fin 6 => v (j.succAbove i)))
    (w : Fin 4 → Fin 7) (hw : Function.Injective w) :
    AffineIndependent ℝ (v ∘ w) := by
  classical
  let s := insert b (Finset.univ.image w)
  have hcard : s.card ≤ 5 := by
    have himage := Finset.card_image_le (f := w) (s := Finset.univ)
    have hinsert := Finset.card_insert_le b (Finset.univ.image w)
    simp only [Finset.card_univ, Fintype.card_fin] at himage
    exact hinsert.trans (by omega)
  obtain ⟨j, hj⟩ : ∃ j : Fin 7, j ∉ s := by
    by_contra! h
    have heq : s = Finset.univ := Finset.eq_univ_iff_forall.mpr h
    rw [heq] at hcard
    norm_num at hcard
  have hjb : j ≠ b := fun h => hj (h.symm ▸ Finset.mem_insert_self _ _)
  have hnot : ∀ i : Fin 4, w i ≠ j := by
    intro i h
    apply hj
    exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, h⟩)
  let e : Fin 4 ↪ {i : Fin 7 // i ≠ j} := {
    toFun := fun i => ⟨w i, hnot i⟩
    inj' := fun i k h => hw (congrArg Subtype.val h) }
  have hi : AffineIndependent ℝ (fun i : {i : Fin 7 // i ≠ j} => v i.val) := by
    apply (affineIndependent_equiv (finSuccAboveEquiv j)).mp
    exact hSix j hjb
  exact hi.comp_embedding e

theorem pVertices_any_four (w : Fin 4 → Fin 7) (hw : Function.Injective w) :
    AffineIndependent ℝ (pVertices ∘ w) :=
  four_independent_of_six_independent_except pVertices 0
    (fun j _ => pVertices_six_independent j) w hw

theorem pVertices_finrank_hull_card (s : Finset (Fin 7)) (hs : s.card ≤ 6)
    (hne : s.Nonempty) :
    Module.finrank ℝ (affineSpan ℝ (convexHull ℝ (pVertices '' (s : Set (Fin 7))))).direction + 1 =
      s.card := by
  classical
  have : Nonempty ↥s := ⟨⟨hne.choose, hne.choose_spec⟩⟩
  have hi := pVertices_independent_of_card_le_six s hs
  have hRange : Set.range (fun i : ↥s => pVertices i.val) = pVertices '' (s : Set (Fin 7)) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i.val, i.property, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, rfl⟩
  rw [affineSpan_convexHull, direction_affineSpan, ← hRange]
  simpa only [Fintype.card_coe] using hi.finrank_vectorSpan_add_one

end Grunbaum2003.CounterexampleGeometry

end

-- Ingredient: skeleton_work/exact4331/QWorkBatch.lean


set_option autoImplicit false
noncomputable section

namespace Grunbaum2003.CounterexampleGeometry

/-- The concrete pyramid-over-bipyramid hull is a full-dimensional nonempty
finite convex hull, the expanded `IsDPolytope` predicate. -/
theorem qBody_full_dimensional :
    (∃ V : Set (Fin 5 → ℝ), V.Finite ∧ V.Nonempty ∧ qBody = convexHull ℝ V) ∧
      affineSpan ℝ qBody = ⊤ := by
  constructor
  · exact ⟨Set.range qVertices, Set.finite_range qVertices, Set.range_nonempty qVertices, rfl⟩
  · change affineSpan ℝ (convexHull ℝ (Set.range qVertices)) = ⊤
    rw [affineSpan_convexHull]
    apply (AffineSubspace.affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty ℝ (Fin 5 → ℝ) (Fin 5 → ℝ)
      (Set.range_nonempty qVertices)).mpr
    let W := vectorSpan ℝ (Set.range qVertices)
    have hzero : qVertices 0 = 0 := by
      ext j
      fin_cases j <;> norm_num [qVertices]
    have hv : ∀ i : Fin 7, qVertices i ∈ W := by
      intro i
      have h : qVertices i -ᵥ qVertices 0 ∈ vectorSpan ℝ (Set.range qVertices) :=
        vsub_mem_vectorSpan ℝ (Set.mem_range_self i) (Set.mem_range_self (0 : Fin 7))
      simpa only [hzero, vsub_eq_sub, sub_zero] using h
    have he0 : (Pi.basisFun ℝ (Fin 5)) 0 ∈ W := by
      convert hv 1 using 1
      ext j
      fin_cases j <;> norm_num [qVertices, Pi.basisFun_apply, Pi.single_apply, Fin.ext_iff]
    have he1 : (Pi.basisFun ℝ (Fin 5)) 1 ∈ W := by
      convert hv 2 using 1
      ext j
      fin_cases j <;> norm_num [qVertices, Pi.basisFun_apply, Pi.single_apply, Fin.ext_iff]
    have he2 : (Pi.basisFun ℝ (Fin 5)) 2 ∈ W := by
      convert hv 3 using 1
      ext j
      fin_cases j <;> norm_num [qVertices, Pi.basisFun_apply, Pi.single_apply, Fin.ext_iff]
    have he4 : (Pi.basisFun ℝ (Fin 5)) 4 ∈ W := by
      convert hv 4 using 1
      ext j
      fin_cases j <;> norm_num [qVertices, Pi.basisFun_apply, Pi.single_apply, Fin.ext_iff]
    have he3 : (Pi.basisFun ℝ (Fin 5)) 3 ∈ W := by
      have h := W.sub_mem (hv 5) (W.smul_mem (1/4 : ℝ) (W.add_mem (W.add_mem (hv 1) (hv 2)) (hv 3)))
      convert h using 1
      ext j
      fin_cases j <;>
        norm_num [qVertices, Pi.basisFun_apply, Pi.single_apply, Fin.ext_iff,
          Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
    have hbasis : Set.range (Pi.basisFun ℝ (Fin 5)) ⊆ W := by
      rintro _ ⟨i, rfl⟩
      fin_cases i
      · exact he0
      · exact he1
      · exact he2
      · exact he3
      · exact he4
    apply top_unique
    rw [← (Pi.basisFun ℝ (Fin 5)).span_eq]
    exact Submodule.span_le.mpr hbasis

end Grunbaum2003.CounterexampleGeometry



set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section

namespace Grunbaum2003.CounterexampleGeometry

private def qOmitIndex (j : Fin 7) (i : Fin 6) : Fin 7 :=
  ⟨if i.val < j.val then i.val else i.val + 1, by split_ifs <;> omega⟩

private theorem qOmitIndex_eq_succAbove (j : Fin 7) (i : Fin 6) :
    qOmitIndex j i = j.succAbove i := by
  fin_cases j <;> fin_cases i <;> decide

/-- Deleting any circuit vertex leaves an affine basis. Deleting the pyramid
apex alone does not: the six remaining points form the affine circuit. -/
theorem qVertices_six_independent (j : Fin 7) (hj : j ≠ 4) :
    AffineIndependent ℝ (fun i : Fin 6 => qVertices (j.succAbove i)) := by
  simp_rw [← qOmitIndex_eq_succAbove]
  rw [affineIndependent_iff_of_fintype]
  intro w hw hv i
  obtain ⟨a0, a1, a2, a3, a4, a5, heq⟩ :
      ∃ a0 a1 a2 a3 a4 a5 : ℝ,
        w = (fun i : Fin 6 => match i.val with
          | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3 | 4 => a4 | _ => a5) := by
    refine ⟨w 0, w 1, w 2, w 3, w 4, w 5, ?_⟩
    ext i
    fin_cases i <;> rfl
  subst w
  rw [Finset.weightedVSub_eq_linear_combination _ hw] at hv
  have h0 := congrFun hv 0
  have h1 := congrFun hv 1
  have h2 := congrFun hv 2
  have h3 := congrFun hv 3
  have h4 := congrFun hv 4
  fin_cases j
  all_goals first | exact (hj rfl).elim | skip
  all_goals norm_num [Fin.sum_univ_succ, qVertices, qOmitIndex,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hw h0 h1 h2 h3 h4 ⊢
  all_goals fin_cases i <;>
    (first | change a0 = 0 | change a1 = 0 | change a2 = 0 |
      change a3 = 0 | change a4 = 0 | change a5 = 0) <;>
    linarith only [hw, h0, h1, h2, h3, h4]

end Grunbaum2003.CounterexampleGeometry



set_option autoImplicit false

namespace Grunbaum2003

/-- For a configuration with every four distinct inputs affinely independent,
the convex hulls of labelled sets have affine dimension at most two exactly
when the label set has cardinality at most three. Empty hulls are included. -/
theorem lowFaceRank_iff_card_le_three {d n : ℕ} (v : Fin n → Fin d → ℝ)
    (h4 : ∀ w : Fin 4 → Fin n, Function.Injective w →
      AffineIndependent ℝ (v ∘ w)) (s : Finset (Fin n)) :
    (convexHull ℝ (v '' (s : Set (Fin n))) = ∅ ∨
      Module.finrank ℝ (affineSpan ℝ (convexHull ℝ (v '' (s : Set (Fin n))))).direction ≤ 2) ↔
      s.card ≤ 3 := by
  classical
  have hrank :
      (affineSpan ℝ (convexHull ℝ (v '' (s : Set (Fin n))))).direction =
        vectorSpan ℝ (s.image v : Set (Fin d → ℝ)) := by
    rw [affineSpan_convexHull, direction_affineSpan, Finset.coe_image]
  constructor
  · intro h
    by_contra hcard
    have hfour : Fintype.card (Fin 4) ≤ s.card := by
      simpa only [Fintype.card_fin] using Nat.succ_le_of_lt (Nat.lt_of_not_ge hcard)
    obtain ⟨w, hw⟩ := Function.Embedding.exists_of_card_le_finset hfour
    have hIndependent := h4 w w.injective
    have hd : Module.finrank ℝ (vectorSpan ℝ (Set.range (v ∘ w))) = 3 :=
      hIndependent.finrank_vectorSpan (by decide)
    have hmono : vectorSpan ℝ (Set.range (v ∘ w)) ≤
        vectorSpan ℝ (s.image v : Set (Fin d → ℝ)) := by
      apply vectorSpan_mono
      rintro _ ⟨i, rfl⟩
      rw [Finset.coe_image]
      exact ⟨w i, hw (Set.mem_range_self i), rfl⟩
    rcases h with hempty | hdim
    · have hi : v (w 0) ∈ convexHull ℝ (v '' (s : Set (Fin n))) :=
        subset_convexHull ℝ _ ⟨w 0, hw (Set.mem_range_self 0), rfl⟩
      rw [hempty] at hi
      exact hi
    · rw [hrank] at hdim
      have hle := (Submodule.finrank_mono hmono).trans hdim
      rw [hd] at hle
      exact (by decide : ¬ (3 : ℕ) ≤ 2) hle
  · intro hcard
    rcases s.eq_empty_or_nonempty with rfl | hs
    · left
      simp only [Finset.coe_empty, Set.image_empty, convexHull_empty]
    · right
      rw [hrank]
      have hpos : 1 ≤ s.card := Finset.card_pos.mpr hs
      have hbound := finrank_vectorSpan_image_finset_le ℝ v s
        (Nat.sub_add_cancel hpos).symm
      exact hbound.trans (Nat.sub_le_sub_right hcard 1)

end Grunbaum2003



set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003

/-- Cast a finite rational support certificate to a genuine real exposed face.
The coefficients and input point coordinates are entirely rational. -/
theorem exposedFace_of_rational_label_maximizers {d n : ℕ}
    (v : Fin n → Fin d → ℚ) (s : Set (Fin n)) (hs : s.Nonempty)
    (a : Fin d → ℚ) (b : ℚ)
    (hbound : ∀ i : Fin n, (∑ j : Fin d, a j * v i j) ≤ b)
    (heq : ∀ i : Fin n, (∑ j : Fin d, a j * v i j) = b ↔ i ∈ s) :
    IsExposed ℝ (convexHull ℝ (Set.range fun i j => (v i j : ℝ)))
      (convexHull ℝ ((fun i j => (v i j : ℝ)) '' s)) ∧
    ∀ i : Fin n,
      (fun j => (v i j : ℝ)) ∈ convexHull ℝ ((fun i j => (v i j : ℝ)) '' s) ↔ i ∈ s := by
  let l : (Fin d → ℝ) →L[ℝ] ℝ :=
    ∑ j : Fin d, (a j : ℝ) • ContinuousLinearMap.proj j
  have hl : ∀ i : Fin n,
      l (fun j => (v i j : ℝ)) = ((∑ j : Fin d, a j * v i j : ℚ) : ℝ) := by
    intro i
    simp only [l, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.proj_apply, smul_eq_mul, Rat.cast_sum, Rat.cast_mul]
  apply exposedFace_of_label_maximizers (fun i j => (v i j : ℝ)) s hs l (b : ℝ)
  · intro i
    rw [hl i]
    exact Rat.cast_le.mpr (hbound i)
  · intro i
    rw [hl i, Rat.cast_inj]
    exact heq i

end Grunbaum2003



namespace Grunbaum2003.CounterexampleSupports
open Grunbaum2003.CounterexampleIncidences
open scoped BigOperators

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def supportNormal {m : ℕ} (facets : Fin m → Finset (Fin 7))
    (normals : Fin m → Fin 5 → ℚ) (s : Finset (Fin 7)) (j : Fin 5) : ℚ :=
  ∑ r : Fin m, if s ⊆ facets r then normals r j else 0

def supportOffset {m : ℕ} (facets : Fin m → Finset (Fin 7))
    (offsets : Fin m → ℚ) (s : Finset (Fin 7)) : ℚ :=
  ∑ r : Fin m, if s ⊆ facets r then offsets r else 0

def pVertices (i : Fin 7) (j : Fin 5) : ℚ :=
  match i.val, j.val with
  | 1, 0 => (1)
  | 2, 1 => (1)
  | 3, 2 => (1)
  | 4, 3 => (1)
  | 5, 0 => (1/5)
  | 5, 1 => (1/5)
  | 5, 2 => (1/5)
  | 5, 3 => (1/5)
  | 5, 4 => (1)
  | 6, 0 => (1/5)
  | 6, 1 => (1/5)
  | 6, 2 => (1/5)
  | 6, 3 => (1/5)
  | 6, 4 => (-1)
  | _, _ => 0

def pFacets (r : Fin 10) : Finset (Fin 7) :=
  match r.val with
  | 0 => {0, 1, 2, 3, 5}
  | 1 => {0, 1, 2, 3, 6}
  | 2 => {0, 1, 2, 4, 5}
  | 3 => {0, 1, 2, 4, 6}
  | 4 => {0, 1, 3, 4, 5}
  | 5 => {0, 1, 3, 4, 6}
  | 6 => {0, 2, 3, 4, 5}
  | 7 => {0, 2, 3, 4, 6}
  | 8 => {1, 2, 3, 4, 5}
  | 9 => {1, 2, 3, 4, 6}
  | _ => ∅

def pNormals (r : Fin 10) (j : Fin 5) : ℚ :=
  match r.val, j.val with
  | 0, 3 => (-5)
  | 0, 4 => (1)
  | 1, 3 => (-5)
  | 1, 4 => (-1)
  | 2, 2 => (-5)
  | 2, 4 => (1)
  | 3, 2 => (-5)
  | 3, 4 => (-1)
  | 4, 1 => (-5)
  | 4, 4 => (1)
  | 5, 1 => (-5)
  | 5, 4 => (-1)
  | 6, 0 => (-5)
  | 6, 4 => (1)
  | 7, 0 => (-5)
  | 7, 4 => (-1)
  | 8, 0 => (5)
  | 8, 1 => (5)
  | 8, 2 => (5)
  | 8, 3 => (5)
  | 8, 4 => (1)
  | 9, 0 => (5)
  | 9, 1 => (5)
  | 9, 2 => (5)
  | 9, 3 => (5)
  | 9, 4 => (-1)
  | _, _ => 0

def pOffsets (r : Fin 10) : ℚ :=
  match r.val with
  | 0 => (0)
  | 1 => (0)
  | 2 => (0)
  | 3 => (0)
  | 4 => (0)
  | 5 => (0)
  | 6 => (0)
  | 7 => (0)
  | 8 => (5)
  | 9 => (5)
  | _ => 0

def pDotValues (r : Fin 10) (i : Fin 7) : ℚ :=
  match r.val, i.val with
  | 0, 4 => (-5)
  | 0, 6 => (-2)
  | 1, 4 => (-5)
  | 1, 5 => (-2)
  | 2, 3 => (-5)
  | 2, 6 => (-2)
  | 3, 3 => (-5)
  | 3, 5 => (-2)
  | 4, 2 => (-5)
  | 4, 6 => (-2)
  | 5, 2 => (-5)
  | 5, 5 => (-2)
  | 6, 1 => (-5)
  | 6, 6 => (-2)
  | 7, 1 => (-5)
  | 7, 5 => (-2)
  | 8, 1 => (5)
  | 8, 2 => (5)
  | 8, 3 => (5)
  | 8, 4 => (5)
  | 8, 5 => (5)
  | 8, 6 => (3)
  | 9, 1 => (5)
  | 9, 2 => (5)
  | 9, 3 => (5)
  | 9, 4 => (5)
  | 9, 5 => (3)
  | 9, 6 => (5)
  | _, _ => 0

private theorem p_dot_evaluation_0 (i : Fin 7) :
    (∑ j : Fin 5, pNormals 0 j * pVertices i j) = pDotValues 0 i := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  fin_cases i
  · change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-5) * (0) + ((1) * (0) + (0))))) : ℚ) = (0 : ℚ)
    norm_num1
  · change ((0) * (1) + ((0) * (0) + ((0) * (0) + ((-5) * (0) + ((1) * (0) + (0))))) : ℚ) = (0 : ℚ)
    norm_num1
  · change ((0) * (0) + ((0) * (1) + ((0) * (0) + ((-5) * (0) + ((1) * (0) + (0))))) : ℚ) = (0 : ℚ)
    norm_num1
  · change ((0) * (0) + ((0) * (0) + ((0) * (1) + ((-5) * (0) + ((1) * (0) + (0))))) : ℚ) = (0 : ℚ)
    norm_num1
  · change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-5) * (1) + ((1) * (0) + (0))))) : ℚ) = (-5 : ℚ)
    norm_num1
  · change ((0) * (1/5) + ((0) * (1/5) + ((0) * (1/5) + ((-5) * (1/5) + ((1) * (1) + (0))))) : ℚ) = (0 : ℚ)
    norm_num1
  · change ((0) * (1/5) + ((0) * (1/5) + ((0) * (1/5) + ((-5) * (1/5) + ((1) * (-1) + (0))))) : ℚ) = (-2 : ℚ)
    norm_num1

private theorem p_dot_evaluation_1 (i : Fin 7) :
    (∑ j : Fin 5, pNormals 1 j * pVertices i j) = pDotValues 1 i := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  fin_cases i
  · change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-5) * (0) + ((-1) * (0) + (0))))) : ℚ) = (0 : ℚ)
    norm_num1
  · change ((0) * (1) + ((0) * (0) + ((0) * (0) + ((-5) * (0) + ((-1) * (0) + (0))))) : ℚ) = (0 : ℚ)
    norm_num1
  · change ((0) * (0) + ((0) * (1) + ((0) * (0) + ((-5) * (0) + ((-1) * (0) + (0))))) : ℚ) = (0 : ℚ)
    norm_num1
  · change ((0) * (0) + ((0) * (0) + ((0) * (1) + ((-5) * (0) + ((-1) * (0) + (0))))) : ℚ) = (0 : ℚ)
    norm_num1
  · change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-5) * (1) + ((-1) * (0) + (0))))) : ℚ) = (-5 : ℚ)
    norm_num1
  · change ((0) * (1/5) + ((0) * (1/5) + ((0) * (1/5) + ((-5) * (1/5) + ((-1) * (1) + (0))))) : ℚ) = (-2 : ℚ)
    norm_num1
  · change ((0) * (1/5) + ((0) * (1/5) + ((0) * (1/5) + ((-5) * (1/5) + ((-1) * (-1) + (0))))) : ℚ) = (0 : ℚ)
    norm_num1

private theorem p_dot_evaluation_2 (i : Fin 7) :
    (∑ j : Fin 5, pNormals 2 j * pVertices i j) = pDotValues 2 i := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  fin_cases i
  · change ((0) * (0) + ((0) * (0) + ((-5) * (0) + ((0) * (0) + ((1) * (0) + (0))))) : ℚ) = (0 : ℚ)
    norm_num1
  · change ((0) * (1) + ((0) * (0) + ((-5) * (0) + ((0) * (0) + ((1) * (0) + (0))))) : ℚ) = (0 : ℚ)
    norm_num1
  · change ((0) * (0) + ((0) * (1) + ((-5) * (0) + ((0) * (0) + ((1) * (0) + (0))))) : ℚ) = (0 : ℚ)
    norm_num1
  · change ((0) * (0) + ((0) * (0) + ((-5) * (1) + ((0) * (0) + ((1) * (0) + (0))))) : ℚ) = (-5 : ℚ)
    norm_num1
  · change ((0) * (0) + ((0) * (0) + ((-5) * (0) + ((0) * (1) + ((1) * (0) + (0))))) : ℚ) = (0 : ℚ)
    norm_num1
  · change ((0) * (1/5) + ((0) * (1/5) + ((-5) * (1/5) + ((0) * (1/5) + ((1) * (1) + (0))))) : ℚ) = (0 : ℚ)
    norm_num1
  · change ((0) * (1/5) + ((0) * (1/5) + ((-5) * (1/5) + ((0) * (1/5) + ((1) * (-1) + (0))))) : ℚ) = (-2 : ℚ)
    norm_num1

private theorem p_dot_evaluation_3 (i : Fin 7) :
    (∑ j : Fin 5, pNormals 3 j * pVertices i j) = pDotValues 3 i := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  fin_cases i
  · change ((0) * (0) + ((0) * (0) + ((-5) * (0) + ((0) * (0) + ((-1) * (0) + (0))))) : ℚ) = (0 : ℚ)
    norm_num1
  · change ((0) * (1) + ((0) * (0) + ((-5) * (0) + ((0) * (0) + ((-1) * (0) + (0))))) : ℚ) = (0 : ℚ)
    norm_num1
  · change ((0) * (0) + ((0) * (1) + ((-5) * (0) + ((0) * (0) + ((-1) * (0) + (0))))) : ℚ) = (0 : ℚ)
    norm_num1
  · change ((0) * (0) + ((0) * (0) + ((-5) * (1) + ((0) * (0) + ((-1) * (0) + (0))))) : ℚ) = (-5 : ℚ)
    norm_num1
  · change ((0) * (0) + ((0) * (0) + ((-5) * (0) + ((0) * (1) + ((-1) * (0) + (0))))) : ℚ) = (0 : ℚ)
    norm_num1
  · change ((0) * (1/5) + ((0) * (1/5) + ((-5) * (1/5) + ((0) * (1/5) + ((-1) * (1) + (0))))) : ℚ) = (-2 : ℚ)
    norm_num1
  · change ((0) * (1/5) + ((0) * (1/5) + ((-5) * (1/5) + ((0) * (1/5) + ((-1) * (-1) + (0))))) : ℚ) = (0 : ℚ)
    norm_num1

private theorem p_dot_evaluation_4 (i : Fin 7) :
    (∑ j : Fin 5, pNormals 4 j * pVertices i j) = pDotValues 4 i := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  fin_cases i
  · change ((0) * (0) + ((-5) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + (0))))) : ℚ) = (0 : ℚ)
    norm_num1
  · change ((0) * (1) + ((-5) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + (0))))) : ℚ) = (0 : ℚ)
    norm_num1
  · change ((0) * (0) + ((-5) * (1) + ((0) * (0) + ((0) * (0) + ((1) * (0) + (0))))) : ℚ) = (-5 : ℚ)
    norm_num1
  · change ((0) * (0) + ((-5) * (0) + ((0) * (1) + ((0) * (0) + ((1) * (0) + (0))))) : ℚ) = (0 : ℚ)
    norm_num1
  · change ((0) * (0) + ((-5) * (0) + ((0) * (0) + ((0) * (1) + ((1) * (0) + (0))))) : ℚ) = (0 : ℚ)
    norm_num1
  · change ((0) * (1/5) + ((-5) * (1/5) + ((0) * (1/5) + ((0) * (1/5) + ((1) * (1) + (0))))) : ℚ) = (0 : ℚ)
    norm_num1
  · change ((0) * (1/5) + ((-5) * (1/5) + ((0) * (1/5) + ((0) * (1/5) + ((1) * (-1) + (0))))) : ℚ) = (-2 : ℚ)
    norm_num1

private theorem p_dot_evaluation_5 (i : Fin 7) :
    (∑ j : Fin 5, pNormals 5 j * pVertices i j) = pDotValues 5 i := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  fin_cases i
  · change ((0) * (0) + ((-5) * (0) + ((0) * (0) + ((0) * (0) + ((-1) * (0) + (0))))) : ℚ) = (0 : ℚ)
    norm_num1
  · change ((0) * (1) + ((-5) * (0) + ((0) * (0) + ((0) * (0) + ((-1) * (0) + (0))))) : ℚ) = (0 : ℚ)
    norm_num1
  · change ((0) * (0) + ((-5) * (1) + ((0) * (0) + ((0) * (0) + ((-1) * (0) + (0))))) : ℚ) = (-5 : ℚ)
    norm_num1
  · change ((0) * (0) + ((-5) * (0) + ((0) * (1) + ((0) * (0) + ((-1) * (0) + (0))))) : ℚ) = (0 : ℚ)
    norm_num1
  · change ((0) * (0) + ((-5) * (0) + ((0) * (0) + ((0) * (1) + ((-1) * (0) + (0))))) : ℚ) = (0 : ℚ)
    norm_num1
  · change ((0) * (1/5) + ((-5) * (1/5) + ((0) * (1/5) + ((0) * (1/5) + ((-1) * (1) + (0))))) : ℚ) = (-2 : ℚ)
    norm_num1
  · change ((0) * (1/5) + ((-5) * (1/5) + ((0) * (1/5) + ((0) * (1/5) + ((-1) * (-1) + (0))))) : ℚ) = (0 : ℚ)
    norm_num1

private theorem p_dot_evaluation_6 (i : Fin 7) :
    (∑ j : Fin 5, pNormals 6 j * pVertices i j) = pDotValues 6 i := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  fin_cases i
  · change ((-5) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + (0))))) : ℚ) = (0 : ℚ)
    norm_num1
  · change ((-5) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + (0))))) : ℚ) = (-5 : ℚ)
    norm_num1
  · change ((-5) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((1) * (0) + (0))))) : ℚ) = (0 : ℚ)
    norm_num1
  · change ((-5) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((1) * (0) + (0))))) : ℚ) = (0 : ℚ)
    norm_num1
  · change ((-5) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((1) * (0) + (0))))) : ℚ) = (0 : ℚ)
    norm_num1
  · change ((-5) * (1/5) + ((0) * (1/5) + ((0) * (1/5) + ((0) * (1/5) + ((1) * (1) + (0))))) : ℚ) = (0 : ℚ)
    norm_num1
  · change ((-5) * (1/5) + ((0) * (1/5) + ((0) * (1/5) + ((0) * (1/5) + ((1) * (-1) + (0))))) : ℚ) = (-2 : ℚ)
    norm_num1

private theorem p_dot_evaluation_7 (i : Fin 7) :
    (∑ j : Fin 5, pNormals 7 j * pVertices i j) = pDotValues 7 i := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  fin_cases i
  · change ((-5) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-1) * (0) + (0))))) : ℚ) = (0 : ℚ)
    norm_num1
  · change ((-5) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-1) * (0) + (0))))) : ℚ) = (-5 : ℚ)
    norm_num1
  · change ((-5) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((-1) * (0) + (0))))) : ℚ) = (0 : ℚ)
    norm_num1
  · change ((-5) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((-1) * (0) + (0))))) : ℚ) = (0 : ℚ)
    norm_num1
  · change ((-5) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((-1) * (0) + (0))))) : ℚ) = (0 : ℚ)
    norm_num1
  · change ((-5) * (1/5) + ((0) * (1/5) + ((0) * (1/5) + ((0) * (1/5) + ((-1) * (1) + (0))))) : ℚ) = (-2 : ℚ)
    norm_num1
  · change ((-5) * (1/5) + ((0) * (1/5) + ((0) * (1/5) + ((0) * (1/5) + ((-1) * (-1) + (0))))) : ℚ) = (0 : ℚ)
    norm_num1

private theorem p_dot_evaluation_8 (i : Fin 7) :
    (∑ j : Fin 5, pNormals 8 j * pVertices i j) = pDotValues 8 i := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  fin_cases i
  · change ((5) * (0) + ((5) * (0) + ((5) * (0) + ((5) * (0) + ((1) * (0) + (0))))) : ℚ) = (0 : ℚ)
    norm_num1
  · change ((5) * (1) + ((5) * (0) + ((5) * (0) + ((5) * (0) + ((1) * (0) + (0))))) : ℚ) = (5 : ℚ)
    norm_num1
  · change ((5) * (0) + ((5) * (1) + ((5) * (0) + ((5) * (0) + ((1) * (0) + (0))))) : ℚ) = (5 : ℚ)
    norm_num1
  · change ((5) * (0) + ((5) * (0) + ((5) * (1) + ((5) * (0) + ((1) * (0) + (0))))) : ℚ) = (5 : ℚ)
    norm_num1
  · change ((5) * (0) + ((5) * (0) + ((5) * (0) + ((5) * (1) + ((1) * (0) + (0))))) : ℚ) = (5 : ℚ)
    norm_num1
  · change ((5) * (1/5) + ((5) * (1/5) + ((5) * (1/5) + ((5) * (1/5) + ((1) * (1) + (0))))) : ℚ) = (5 : ℚ)
    norm_num1
  · change ((5) * (1/5) + ((5) * (1/5) + ((5) * (1/5) + ((5) * (1/5) + ((1) * (-1) + (0))))) : ℚ) = (3 : ℚ)
    norm_num1

private theorem p_dot_evaluation_9 (i : Fin 7) :
    (∑ j : Fin 5, pNormals 9 j * pVertices i j) = pDotValues 9 i := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  fin_cases i
  · change ((5) * (0) + ((5) * (0) + ((5) * (0) + ((5) * (0) + ((-1) * (0) + (0))))) : ℚ) = (0 : ℚ)
    norm_num1
  · change ((5) * (1) + ((5) * (0) + ((5) * (0) + ((5) * (0) + ((-1) * (0) + (0))))) : ℚ) = (5 : ℚ)
    norm_num1
  · change ((5) * (0) + ((5) * (1) + ((5) * (0) + ((5) * (0) + ((-1) * (0) + (0))))) : ℚ) = (5 : ℚ)
    norm_num1
  · change ((5) * (0) + ((5) * (0) + ((5) * (1) + ((5) * (0) + ((-1) * (0) + (0))))) : ℚ) = (5 : ℚ)
    norm_num1
  · change ((5) * (0) + ((5) * (0) + ((5) * (0) + ((5) * (1) + ((-1) * (0) + (0))))) : ℚ) = (5 : ℚ)
    norm_num1
  · change ((5) * (1/5) + ((5) * (1/5) + ((5) * (1/5) + ((5) * (1/5) + ((-1) * (1) + (0))))) : ℚ) = (3 : ℚ)
    norm_num1
  · change ((5) * (1/5) + ((5) * (1/5) + ((5) * (1/5) + ((5) * (1/5) + ((-1) * (-1) + (0))))) : ℚ) = (5 : ℚ)
    norm_num1

theorem p_dot_evaluation (r : Fin 10) (i : Fin 7) :
    (∑ j : Fin 5, pNormals r j * pVertices i j) = pDotValues r i := by
  fin_cases r
  · exact p_dot_evaluation_0 i
  · exact p_dot_evaluation_1 i
  · exact p_dot_evaluation_2 i
  · exact p_dot_evaluation_3 i
  · exact p_dot_evaluation_4 i
  · exact p_dot_evaluation_5 i
  · exact p_dot_evaluation_6 i
  · exact p_dot_evaluation_7 i
  · exact p_dot_evaluation_8 i
  · exact p_dot_evaluation_9 i

private theorem p_value_certificate : ∀ r : Fin 10, ∀ i : Fin 7,
      pDotValues r i ≤ pOffsets r ∧
      (pDotValues r i = pOffsets r ↔ i ∈ pFacets r) := by
  intro r i
  fin_cases r <;> fin_cases i <;>
    first | decide | norm_num [pDotValues, pOffsets, pFacets, Fin.ext_iff]

theorem p_facet_certificate (r : Fin 10) (i : Fin 7) :
      (∑ j : Fin 5, pNormals r j * pVertices i j) ≤ pOffsets r ∧
      ((∑ j : Fin 5, pNormals r j * pVertices i j) = pOffsets r ↔
        i ∈ pFacets r) := by
  rw [p_dot_evaluation r i]
  exact p_value_certificate r i

theorem p_intersection_certificate : ∀ s : Finset (Fin 7), s ∈ pFaces →
    ∀ i : Fin 7, (∀ r : Fin 10, s ⊆ pFacets r → i ∈ pFacets r) ↔ i ∈ s := by decide

def qVertices (i : Fin 7) (j : Fin 5) : ℚ :=
  match i.val, j.val with
  | 1, 0 => (1)
  | 2, 1 => (1)
  | 3, 2 => (1)
  | 4, 4 => (1)
  | 5, 0 => (1/4)
  | 5, 1 => (1/4)
  | 5, 2 => (1/4)
  | 5, 3 => (1)
  | 6, 0 => (1/4)
  | 6, 1 => (1/4)
  | 6, 2 => (1/4)
  | 6, 3 => (-1)
  | _, _ => 0

def qFacets (r : Fin 9) : Finset (Fin 7) :=
  match r.val with
  | 0 => {0, 1, 2, 3, 5, 6}
  | 1 => {0, 1, 2, 4, 5}
  | 2 => {0, 1, 2, 4, 6}
  | 3 => {0, 1, 3, 4, 5}
  | 4 => {0, 1, 3, 4, 6}
  | 5 => {0, 2, 3, 4, 5}
  | 6 => {0, 2, 3, 4, 6}
  | 7 => {1, 2, 3, 4, 5}
  | 8 => {1, 2, 3, 4, 6}
  | _ => ∅

def qNormals (r : Fin 9) (j : Fin 5) : ℚ :=
  match r.val, j.val with
  | 0, 4 => (-1)
  | 1, 2 => (-4)
  | 1, 3 => (1)
  | 2, 2 => (-4)
  | 2, 3 => (-1)
  | 3, 1 => (-4)
  | 3, 3 => (1)
  | 4, 1 => (-4)
  | 4, 3 => (-1)
  | 5, 0 => (-4)
  | 5, 3 => (1)
  | 6, 0 => (-4)
  | 6, 3 => (-1)
  | 7, 0 => (1)
  | 7, 1 => (1)
  | 7, 2 => (1)
  | 7, 3 => (1/4)
  | 7, 4 => (1)
  | 8, 0 => (1)
  | 8, 1 => (1)
  | 8, 2 => (1)
  | 8, 3 => (-1/4)
  | 8, 4 => (1)
  | _, _ => 0

def qOffsets (r : Fin 9) : ℚ :=
  match r.val with
  | 0 => (0)
  | 1 => (0)
  | 2 => (0)
  | 3 => (0)
  | 4 => (0)
  | 5 => (0)
  | 6 => (0)
  | 7 => (1)
  | 8 => (1)
  | _ => 0

def qDotValues (r : Fin 9) (i : Fin 7) : ℚ :=
  match r.val, i.val with
  | 0, 4 => (-1)
  | 1, 3 => (-4)
  | 1, 6 => (-2)
  | 2, 3 => (-4)
  | 2, 5 => (-2)
  | 3, 2 => (-4)
  | 3, 6 => (-2)
  | 4, 2 => (-4)
  | 4, 5 => (-2)
  | 5, 1 => (-4)
  | 5, 6 => (-2)
  | 6, 1 => (-4)
  | 6, 5 => (-2)
  | 7, 1 => (1)
  | 7, 2 => (1)
  | 7, 3 => (1)
  | 7, 4 => (1)
  | 7, 5 => (1)
  | 7, 6 => (1/2)
  | 8, 1 => (1)
  | 8, 2 => (1)
  | 8, 3 => (1)
  | 8, 4 => (1)
  | 8, 5 => (1/2)
  | 8, 6 => (1)
  | _, _ => 0

private theorem q_dot_evaluation_0 (i : Fin 7) :
    (∑ j : Fin 5, qNormals 0 j * qVertices i j) = qDotValues 0 i := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  fin_cases i
  · change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-1) * (0) + (0))))) : ℚ) = (0 : ℚ)
    norm_num1
  · change ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-1) * (0) + (0))))) : ℚ) = (0 : ℚ)
    norm_num1
  · change ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((-1) * (0) + (0))))) : ℚ) = (0 : ℚ)
    norm_num1
  · change ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((-1) * (0) + (0))))) : ℚ) = (0 : ℚ)
    norm_num1
  · change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-1) * (1) + (0))))) : ℚ) = (-1 : ℚ)
    norm_num1
  · change ((0) * (1/4) + ((0) * (1/4) + ((0) * (1/4) + ((0) * (1) + ((-1) * (0) + (0))))) : ℚ) = (0 : ℚ)
    norm_num1
  · change ((0) * (1/4) + ((0) * (1/4) + ((0) * (1/4) + ((0) * (-1) + ((-1) * (0) + (0))))) : ℚ) = (0 : ℚ)
    norm_num1

private theorem q_dot_evaluation_1 (i : Fin 7) :
    (∑ j : Fin 5, qNormals 1 j * qVertices i j) = qDotValues 1 i := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  fin_cases i
  · change ((0) * (0) + ((0) * (0) + ((-4) * (0) + ((1) * (0) + ((0) * (0) + (0))))) : ℚ) = (0 : ℚ)
    norm_num1
  · change ((0) * (1) + ((0) * (0) + ((-4) * (0) + ((1) * (0) + ((0) * (0) + (0))))) : ℚ) = (0 : ℚ)
    norm_num1
  · change ((0) * (0) + ((0) * (1) + ((-4) * (0) + ((1) * (0) + ((0) * (0) + (0))))) : ℚ) = (0 : ℚ)
    norm_num1
  · change ((0) * (0) + ((0) * (0) + ((-4) * (1) + ((1) * (0) + ((0) * (0) + (0))))) : ℚ) = (-4 : ℚ)
    norm_num1
  · change ((0) * (0) + ((0) * (0) + ((-4) * (0) + ((1) * (0) + ((0) * (1) + (0))))) : ℚ) = (0 : ℚ)
    norm_num1
  · change ((0) * (1/4) + ((0) * (1/4) + ((-4) * (1/4) + ((1) * (1) + ((0) * (0) + (0))))) : ℚ) = (0 : ℚ)
    norm_num1
  · change ((0) * (1/4) + ((0) * (1/4) + ((-4) * (1/4) + ((1) * (-1) + ((0) * (0) + (0))))) : ℚ) = (-2 : ℚ)
    norm_num1

private theorem q_dot_evaluation_2 (i : Fin 7) :
    (∑ j : Fin 5, qNormals 2 j * qVertices i j) = qDotValues 2 i := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  fin_cases i
  · change ((0) * (0) + ((0) * (0) + ((-4) * (0) + ((-1) * (0) + ((0) * (0) + (0))))) : ℚ) = (0 : ℚ)
    norm_num1
  · change ((0) * (1) + ((0) * (0) + ((-4) * (0) + ((-1) * (0) + ((0) * (0) + (0))))) : ℚ) = (0 : ℚ)
    norm_num1
  · change ((0) * (0) + ((0) * (1) + ((-4) * (0) + ((-1) * (0) + ((0) * (0) + (0))))) : ℚ) = (0 : ℚ)
    norm_num1
  · change ((0) * (0) + ((0) * (0) + ((-4) * (1) + ((-1) * (0) + ((0) * (0) + (0))))) : ℚ) = (-4 : ℚ)
    norm_num1
  · change ((0) * (0) + ((0) * (0) + ((-4) * (0) + ((-1) * (0) + ((0) * (1) + (0))))) : ℚ) = (0 : ℚ)
    norm_num1
  · change ((0) * (1/4) + ((0) * (1/4) + ((-4) * (1/4) + ((-1) * (1) + ((0) * (0) + (0))))) : ℚ) = (-2 : ℚ)
    norm_num1
  · change ((0) * (1/4) + ((0) * (1/4) + ((-4) * (1/4) + ((-1) * (-1) + ((0) * (0) + (0))))) : ℚ) = (0 : ℚ)
    norm_num1

private theorem q_dot_evaluation_3 (i : Fin 7) :
    (∑ j : Fin 5, qNormals 3 j * qVertices i j) = qDotValues 3 i := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  fin_cases i
  · change ((0) * (0) + ((-4) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + (0))))) : ℚ) = (0 : ℚ)
    norm_num1
  · change ((0) * (1) + ((-4) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + (0))))) : ℚ) = (0 : ℚ)
    norm_num1
  · change ((0) * (0) + ((-4) * (1) + ((0) * (0) + ((1) * (0) + ((0) * (0) + (0))))) : ℚ) = (-4 : ℚ)
    norm_num1
  · change ((0) * (0) + ((-4) * (0) + ((0) * (1) + ((1) * (0) + ((0) * (0) + (0))))) : ℚ) = (0 : ℚ)
    norm_num1
  · change ((0) * (0) + ((-4) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (1) + (0))))) : ℚ) = (0 : ℚ)
    norm_num1
  · change ((0) * (1/4) + ((-4) * (1/4) + ((0) * (1/4) + ((1) * (1) + ((0) * (0) + (0))))) : ℚ) = (0 : ℚ)
    norm_num1
  · change ((0) * (1/4) + ((-4) * (1/4) + ((0) * (1/4) + ((1) * (-1) + ((0) * (0) + (0))))) : ℚ) = (-2 : ℚ)
    norm_num1

private theorem q_dot_evaluation_4 (i : Fin 7) :
    (∑ j : Fin 5, qNormals 4 j * qVertices i j) = qDotValues 4 i := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  fin_cases i
  · change ((0) * (0) + ((-4) * (0) + ((0) * (0) + ((-1) * (0) + ((0) * (0) + (0))))) : ℚ) = (0 : ℚ)
    norm_num1
  · change ((0) * (1) + ((-4) * (0) + ((0) * (0) + ((-1) * (0) + ((0) * (0) + (0))))) : ℚ) = (0 : ℚ)
    norm_num1
  · change ((0) * (0) + ((-4) * (1) + ((0) * (0) + ((-1) * (0) + ((0) * (0) + (0))))) : ℚ) = (-4 : ℚ)
    norm_num1
  · change ((0) * (0) + ((-4) * (0) + ((0) * (1) + ((-1) * (0) + ((0) * (0) + (0))))) : ℚ) = (0 : ℚ)
    norm_num1
  · change ((0) * (0) + ((-4) * (0) + ((0) * (0) + ((-1) * (0) + ((0) * (1) + (0))))) : ℚ) = (0 : ℚ)
    norm_num1
  · change ((0) * (1/4) + ((-4) * (1/4) + ((0) * (1/4) + ((-1) * (1) + ((0) * (0) + (0))))) : ℚ) = (-2 : ℚ)
    norm_num1
  · change ((0) * (1/4) + ((-4) * (1/4) + ((0) * (1/4) + ((-1) * (-1) + ((0) * (0) + (0))))) : ℚ) = (0 : ℚ)
    norm_num1

private theorem q_dot_evaluation_5 (i : Fin 7) :
    (∑ j : Fin 5, qNormals 5 j * qVertices i j) = qDotValues 5 i := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  fin_cases i
  · change ((-4) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + (0))))) : ℚ) = (0 : ℚ)
    norm_num1
  · change ((-4) * (1) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + (0))))) : ℚ) = (-4 : ℚ)
    norm_num1
  · change ((-4) * (0) + ((0) * (1) + ((0) * (0) + ((1) * (0) + ((0) * (0) + (0))))) : ℚ) = (0 : ℚ)
    norm_num1
  · change ((-4) * (0) + ((0) * (0) + ((0) * (1) + ((1) * (0) + ((0) * (0) + (0))))) : ℚ) = (0 : ℚ)
    norm_num1
  · change ((-4) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (1) + (0))))) : ℚ) = (0 : ℚ)
    norm_num1
  · change ((-4) * (1/4) + ((0) * (1/4) + ((0) * (1/4) + ((1) * (1) + ((0) * (0) + (0))))) : ℚ) = (0 : ℚ)
    norm_num1
  · change ((-4) * (1/4) + ((0) * (1/4) + ((0) * (1/4) + ((1) * (-1) + ((0) * (0) + (0))))) : ℚ) = (-2 : ℚ)
    norm_num1

private theorem q_dot_evaluation_6 (i : Fin 7) :
    (∑ j : Fin 5, qNormals 6 j * qVertices i j) = qDotValues 6 i := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  fin_cases i
  · change ((-4) * (0) + ((0) * (0) + ((0) * (0) + ((-1) * (0) + ((0) * (0) + (0))))) : ℚ) = (0 : ℚ)
    norm_num1
  · change ((-4) * (1) + ((0) * (0) + ((0) * (0) + ((-1) * (0) + ((0) * (0) + (0))))) : ℚ) = (-4 : ℚ)
    norm_num1
  · change ((-4) * (0) + ((0) * (1) + ((0) * (0) + ((-1) * (0) + ((0) * (0) + (0))))) : ℚ) = (0 : ℚ)
    norm_num1
  · change ((-4) * (0) + ((0) * (0) + ((0) * (1) + ((-1) * (0) + ((0) * (0) + (0))))) : ℚ) = (0 : ℚ)
    norm_num1
  · change ((-4) * (0) + ((0) * (0) + ((0) * (0) + ((-1) * (0) + ((0) * (1) + (0))))) : ℚ) = (0 : ℚ)
    norm_num1
  · change ((-4) * (1/4) + ((0) * (1/4) + ((0) * (1/4) + ((-1) * (1) + ((0) * (0) + (0))))) : ℚ) = (-2 : ℚ)
    norm_num1
  · change ((-4) * (1/4) + ((0) * (1/4) + ((0) * (1/4) + ((-1) * (-1) + ((0) * (0) + (0))))) : ℚ) = (0 : ℚ)
    norm_num1

private theorem q_dot_evaluation_7 (i : Fin 7) :
    (∑ j : Fin 5, qNormals 7 j * qVertices i j) = qDotValues 7 i := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  fin_cases i
  · change ((1) * (0) + ((1) * (0) + ((1) * (0) + ((1/4) * (0) + ((1) * (0) + (0))))) : ℚ) = (0 : ℚ)
    norm_num1
  · change ((1) * (1) + ((1) * (0) + ((1) * (0) + ((1/4) * (0) + ((1) * (0) + (0))))) : ℚ) = (1 : ℚ)
    norm_num1
  · change ((1) * (0) + ((1) * (1) + ((1) * (0) + ((1/4) * (0) + ((1) * (0) + (0))))) : ℚ) = (1 : ℚ)
    norm_num1
  · change ((1) * (0) + ((1) * (0) + ((1) * (1) + ((1/4) * (0) + ((1) * (0) + (0))))) : ℚ) = (1 : ℚ)
    norm_num1
  · change ((1) * (0) + ((1) * (0) + ((1) * (0) + ((1/4) * (0) + ((1) * (1) + (0))))) : ℚ) = (1 : ℚ)
    norm_num1
  · change ((1) * (1/4) + ((1) * (1/4) + ((1) * (1/4) + ((1/4) * (1) + ((1) * (0) + (0))))) : ℚ) = (1 : ℚ)
    norm_num1
  · change ((1) * (1/4) + ((1) * (1/4) + ((1) * (1/4) + ((1/4) * (-1) + ((1) * (0) + (0))))) : ℚ) = (1/2 : ℚ)
    norm_num1

private theorem q_dot_evaluation_8 (i : Fin 7) :
    (∑ j : Fin 5, qNormals 8 j * qVertices i j) = qDotValues 8 i := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  fin_cases i
  · change ((1) * (0) + ((1) * (0) + ((1) * (0) + ((-1/4) * (0) + ((1) * (0) + (0))))) : ℚ) = (0 : ℚ)
    norm_num1
  · change ((1) * (1) + ((1) * (0) + ((1) * (0) + ((-1/4) * (0) + ((1) * (0) + (0))))) : ℚ) = (1 : ℚ)
    norm_num1
  · change ((1) * (0) + ((1) * (1) + ((1) * (0) + ((-1/4) * (0) + ((1) * (0) + (0))))) : ℚ) = (1 : ℚ)
    norm_num1
  · change ((1) * (0) + ((1) * (0) + ((1) * (1) + ((-1/4) * (0) + ((1) * (0) + (0))))) : ℚ) = (1 : ℚ)
    norm_num1
  · change ((1) * (0) + ((1) * (0) + ((1) * (0) + ((-1/4) * (0) + ((1) * (1) + (0))))) : ℚ) = (1 : ℚ)
    norm_num1
  · change ((1) * (1/4) + ((1) * (1/4) + ((1) * (1/4) + ((-1/4) * (1) + ((1) * (0) + (0))))) : ℚ) = (1/2 : ℚ)
    norm_num1
  · change ((1) * (1/4) + ((1) * (1/4) + ((1) * (1/4) + ((-1/4) * (-1) + ((1) * (0) + (0))))) : ℚ) = (1 : ℚ)
    norm_num1

theorem q_dot_evaluation (r : Fin 9) (i : Fin 7) :
    (∑ j : Fin 5, qNormals r j * qVertices i j) = qDotValues r i := by
  fin_cases r
  · exact q_dot_evaluation_0 i
  · exact q_dot_evaluation_1 i
  · exact q_dot_evaluation_2 i
  · exact q_dot_evaluation_3 i
  · exact q_dot_evaluation_4 i
  · exact q_dot_evaluation_5 i
  · exact q_dot_evaluation_6 i
  · exact q_dot_evaluation_7 i
  · exact q_dot_evaluation_8 i

private theorem q_value_certificate : ∀ r : Fin 9, ∀ i : Fin 7,
      qDotValues r i ≤ qOffsets r ∧
      (qDotValues r i = qOffsets r ↔ i ∈ qFacets r) := by
  intro r i
  fin_cases r <;> fin_cases i <;>
    first | decide | norm_num [qDotValues, qOffsets, qFacets, Fin.ext_iff]

theorem q_facet_certificate (r : Fin 9) (i : Fin 7) :
      (∑ j : Fin 5, qNormals r j * qVertices i j) ≤ qOffsets r ∧
      ((∑ j : Fin 5, qNormals r j * qVertices i j) = qOffsets r ↔
        i ∈ qFacets r) := by
  rw [q_dot_evaluation r i]
  exact q_value_certificate r i

theorem q_intersection_certificate : ∀ s : Finset (Fin 7), s ∈ qFaces →
    ∀ i : Fin 7, (∀ r : Fin 9, s ⊆ qFacets r → i ∈ qFacets r) ↔ i ∈ s := by decide

end Grunbaum2003.CounterexampleSupports



set_option autoImplicit false

namespace Grunbaum2003.CounterexampleGeometry
open Grunbaum2003.CounterexampleIncidences

theorem qFace_incidence_sound (F : Set (Fin 5 → ℝ)) (hF : IsExposed ℝ qBody F)
    (s : Finset (Fin 7)) (hs : ∀ i : Fin 7, i ∈ s ↔ qVertices i ∈ F) :
    s ∈ qFaces := by
  apply qFaces_of_circuit s
  constructor
  · intro hbase
    have hbase' : ∀ i ∈ ({0, 1, 2, 3} : Set (Fin 7)), qVertices i ∈ F := by
      intro i hi
      apply (hs i).mp
      apply hbase
      simpa only [Finset.mem_insert, Finset.mem_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] using hi
    obtain ⟨hu, hv⟩ := (exposedFace_q_circuit_iff hF).mp hbase'
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact (hs 5).mpr hu
    · exact (hs 6).mpr hv
  · intro hpoles
    have hu : qVertices 5 ∈ F := (hs 5).mp (hpoles (by simp))
    have hv : qVertices 6 ∈ F := (hs 6).mp (hpoles (by simp))
    have hbase := (exposedFace_q_circuit_iff hF).mpr ⟨hu, hv⟩
    intro i hi
    apply (hs i).mpr
    apply hbase i
    simpa only [Finset.mem_insert, Finset.mem_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] using hi

end Grunbaum2003.CounterexampleGeometry



set_option autoImplicit false

namespace Grunbaum2003

/-- A finite family of certified exposed faces realizes every label set which
is the intersection of the certified incidence sets containing it. -/
theorem exposedFace_of_facet_intersection_certificate {d n m : ℕ}
    (v : Fin n → Fin d → ℝ) (facets : Fin m → Finset (Fin n))
    (faces : Fin m → Set (Fin d → ℝ))
    (hfaces : ∀ r : Fin m,
      IsExposed ℝ (convexHull ℝ (Set.range v)) (faces r) ∧
        ∀ i : Fin n, v i ∈ faces r ↔ i ∈ facets r)
    (s : Finset (Fin n))
    (hintersection : ∀ i : Fin n,
      (∀ r : Fin m, s ⊆ facets r → i ∈ facets r) ↔ i ∈ s) :
    IsExposed ℝ (convexHull ℝ (Set.range v)) (convexHull ℝ (v '' (s : Set (Fin n)))) ∧
      ∀ i : Fin n, v i ∈ convexHull ℝ (v '' (s : Set (Fin n))) ↔ i ∈ s := by
  classical
  let P := convexHull ℝ (Set.range v)
  let K : Finset (Set (Fin d → ℝ)) :=
    insert P ((Finset.univ.filter (fun r => s ⊆ facets r)).image faces)
  let F := ⋂₀ (K : Set (Set (Fin d → ℝ)))
  have hF : IsExposed ℝ P F := by
    apply IsExposed.sInter (F := K) (Finset.insert_nonempty _ _) 
    intro G hG
    rcases Finset.mem_insert.mp hG with rfl | hG
    · exact IsExposed.refl P
    · obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hG
      exact (hfaces r).1
  have hlabels : ∀ i : Fin n, v i ∈ F ↔ i ∈ s := by
    intro i
    constructor
    · intro hi
      apply (hintersection i).mp
      intro r hr
      apply (hfaces r).2 i |>.mp
      apply Set.mem_sInter.mp hi
      apply Finset.mem_coe.mpr
      apply Finset.mem_insert_of_mem
      apply Finset.mem_image_of_mem
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ r, hr⟩
    · intro hi
      apply Set.mem_sInter.mpr
      intro G hG
      rcases Finset.mem_insert.mp (Finset.mem_coe.mp hG) with rfl | hG
      · exact subset_convexHull ℝ _ (Set.mem_range_self i)
      · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hG
        apply (hfaces r).2 i |>.mpr
        exact (Finset.mem_filter.mp hr).2 hi
  have hInc : F ∩ Set.range v = v '' (s : Set (Fin n)) := by
    ext x
    constructor
    · rintro ⟨hx, i, rfl⟩
      exact ⟨i, (hlabels i).mp hx, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨(hlabels i).mpr hi, Set.mem_range_self i⟩
  have heq : F = convexHull ℝ (v '' (s : Set (Fin n))) := by
    calc F = convexHull ℝ (F ∩ Set.range v) :=
          exposedFace_eq_convexHull_incident_range v hF
      _ = convexHull ℝ (v '' (s : Set (Fin n))) := congrArg (convexHull ℝ) hInc
  constructor
  · rw [← heq]
    exact hF
  · intro i
    rw [← heq]
    exact hlabels i

end Grunbaum2003


end
end

-- Ingredient: skeleton_work/exact4331/ConcreteFaceCertificates.lean

set_option autoImplicit false

namespace Grunbaum2003.CounterexampleGeometry
open Grunbaum2003.CounterexampleIncidences

 theorem pVertices_eq_rat_cast : pVertices =
    (fun i j => (Grunbaum2003.CounterexampleSupports.pVertices i j : ℝ)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pVertices, Grunbaum2003.CounterexampleSupports.pVertices]

 theorem qVertices_eq_rat_cast : qVertices =
    (fun i j => (Grunbaum2003.CounterexampleSupports.qVertices i j : ℝ)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [qVertices, Grunbaum2003.CounterexampleSupports.qVertices]

 theorem pFace_incidence_complete (s : Finset (Fin 7)) (hs : s ∈ pFaces) :
    IsExposed ℝ pBody (convexHull ℝ (pVertices '' (s : Set (Fin 7)))) ∧
      ∀ i : Fin 7, pVertices i ∈ convexHull ℝ (pVertices '' (s : Set (Fin 7))) ↔ i ∈ s := by
  have hne : ∀ r : Fin 10, (Grunbaum2003.CounterexampleSupports.pFacets r).Nonempty := by decide
  have hfacets : ∀ r : Fin 10,
      IsExposed ℝ pBody (convexHull ℝ (pVertices ''
        (Grunbaum2003.CounterexampleSupports.pFacets r : Set (Fin 7)))) ∧
      ∀ i : Fin 7, pVertices i ∈ convexHull ℝ (pVertices ''
        (Grunbaum2003.CounterexampleSupports.pFacets r : Set (Fin 7))) ↔
        i ∈ Grunbaum2003.CounterexampleSupports.pFacets r := by
    intro r
    change IsExposed ℝ (convexHull ℝ (Set.range pVertices)) _ ∧ _
    rw [pVertices_eq_rat_cast]
    exact exposedFace_of_rational_label_maximizers
      Grunbaum2003.CounterexampleSupports.pVertices
      (Grunbaum2003.CounterexampleSupports.pFacets r : Set (Fin 7))
      (Finset.coe_nonempty.mpr (hne r))
      (Grunbaum2003.CounterexampleSupports.pNormals r)
      (Grunbaum2003.CounterexampleSupports.pOffsets r)
      (fun i => (Grunbaum2003.CounterexampleSupports.p_facet_certificate r i).1)
      (fun i => (Grunbaum2003.CounterexampleSupports.p_facet_certificate r i).2)
  exact exposedFace_of_facet_intersection_certificate pVertices
    Grunbaum2003.CounterexampleSupports.pFacets
    (fun r => convexHull ℝ (pVertices ''
      (Grunbaum2003.CounterexampleSupports.pFacets r : Set (Fin 7))))
    hfacets s (Grunbaum2003.CounterexampleSupports.p_intersection_certificate s hs)

 theorem qFace_incidence_complete (s : Finset (Fin 7)) (hs : s ∈ qFaces) :
    IsExposed ℝ qBody (convexHull ℝ (qVertices '' (s : Set (Fin 7)))) ∧
      ∀ i : Fin 7, qVertices i ∈ convexHull ℝ (qVertices '' (s : Set (Fin 7))) ↔ i ∈ s := by
  have hne : ∀ r : Fin 9, (Grunbaum2003.CounterexampleSupports.qFacets r).Nonempty := by decide
  have hfacets : ∀ r : Fin 9,
      IsExposed ℝ qBody (convexHull ℝ (qVertices ''
        (Grunbaum2003.CounterexampleSupports.qFacets r : Set (Fin 7)))) ∧
      ∀ i : Fin 7, qVertices i ∈ convexHull ℝ (qVertices ''
        (Grunbaum2003.CounterexampleSupports.qFacets r : Set (Fin 7))) ↔
        i ∈ Grunbaum2003.CounterexampleSupports.qFacets r := by
    intro r
    change IsExposed ℝ (convexHull ℝ (Set.range qVertices)) _ ∧ _
    rw [qVertices_eq_rat_cast]
    exact exposedFace_of_rational_label_maximizers
      Grunbaum2003.CounterexampleSupports.qVertices
      (Grunbaum2003.CounterexampleSupports.qFacets r : Set (Fin 7))
      (Finset.coe_nonempty.mpr (hne r))
      (Grunbaum2003.CounterexampleSupports.qNormals r)
      (Grunbaum2003.CounterexampleSupports.qOffsets r)
      (fun i => (Grunbaum2003.CounterexampleSupports.q_facet_certificate r i).1)
      (fun i => (Grunbaum2003.CounterexampleSupports.q_facet_certificate r i).2)
  exact exposedFace_of_facet_intersection_certificate qVertices
    Grunbaum2003.CounterexampleSupports.qFacets
    (fun r => convexHull ℝ (qVertices ''
      (Grunbaum2003.CounterexampleSupports.qFacets r : Set (Fin 7))))
    hfacets s (Grunbaum2003.CounterexampleSupports.q_intersection_certificate s hs)

end Grunbaum2003.CounterexampleGeometry


-- Ingredient: skeleton_work/exact4331/LowSkeletonIso.lean

set_option autoImplicit false
noncomputable section

namespace Grunbaum2003

 theorem exposedFace_eq_hull_of_incident_finset {d n : ℕ}
    (v : Fin n → Fin d → ℝ) {F : Set (Fin d → ℝ)}
    (hF : IsExposed ℝ (convexHull ℝ (Set.range v)) F)
    (s : Finset (Fin n)) (hs : ∀ i : Fin n, i ∈ s ↔ v i ∈ F) :
    F = convexHull ℝ (v '' (s : Set (Fin n))) := by
  have hInc : F ∩ Set.range v = v '' (s : Set (Fin n)) := by
    ext x
    constructor
    · rintro ⟨hx, i, rfl⟩
      exact ⟨i, (hs i).mpr hx, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨(hs i).mp hi, Set.mem_range_self i⟩
  calc F = convexHull ℝ (F ∩ Set.range v) := exposedFace_eq_convexHull_incident_range v hF
    _ = convexHull ℝ (v '' (s : Set (Fin n))) := congrArg (convexHull ℝ) hInc

 theorem skeletonTwo_orderIso_of_incidence_certificate {d n : ℕ}
    (v : Fin n → Fin d → ℝ) (family : Finset (Finset (Fin n)))
    (hSound : ∀ F : SkeletonFace (convexHull ℝ (Set.range v)) 2,
      ∀ s : Finset (Fin n), (∀ i : Fin n, i ∈ s ↔ v i ∈ F.val.val) → s ∈ family)
    (hComplete : ∀ s ∈ family,
      IsExposed ℝ (convexHull ℝ (Set.range v)) (convexHull ℝ (v '' (s : Set (Fin n)))) ∧
      (convexHull ℝ (v '' (s : Set (Fin n))) = ∅ ∨
        Module.finrank ℝ (affineSpan ℝ (convexHull ℝ (v '' (s : Set (Fin n))))).direction ≤ 2) ∧
      ∀ i : Fin n, v i ∈ convexHull ℝ (v '' (s : Set (Fin n))) ↔ i ∈ s) :
    ∃ Φ : SkeletonFace (convexHull ℝ (Set.range v)) 2 ≃o ↥family,
      ∀ F i, i ∈ (Φ F).val ↔ v i ∈ F.val.val := by
  classical
  let f : SkeletonFace (convexHull ℝ (Set.range v)) 2 ↪o ↥family := {
    toFun := fun F => ⟨Finset.univ.filter (fun i => v i ∈ F.val.val),
      hSound F _ (by intro i; simp only [Finset.mem_filter, Finset.mem_univ, true_and])⟩
    inj' := by
      intro F G h
      have hfg : (Finset.univ.filter fun i => v i ∈ F.val.val) =
          (Finset.univ.filter fun i => v i ∈ G.val.val) := congrArg Subtype.val h
      have hi : ∀ i : Fin n, v i ∈ F.val.val ↔ v i ∈ G.val.val := by
        intro i
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using
          (Finset.ext_iff.mp hfg i)
      apply Subtype.ext
      apply Subtype.ext
      apply Set.Subset.antisymm
      · exact (exposedFace_subset_iff_incident_labels v F.val.property G.val.property).mpr
          (fun i hv => (hi i).mp hv)
      · exact (exposedFace_subset_iff_incident_labels v G.val.property F.val.property).mpr
          (fun i hv => (hi i).mpr hv)
    map_rel_iff' := by
      intro F G
      change (Finset.univ.filter (fun i => v i ∈ F.val.val)) ⊆
        (Finset.univ.filter (fun i => v i ∈ G.val.val)) ↔ F.val.val ⊆ G.val.val
      simpa only [Finset.subset_iff, Finset.mem_filter, Finset.mem_univ, true_and] using
        (exposedFace_subset_iff_incident_labels v F.val.property G.val.property).symm }
  have hf : Function.Surjective f := by
    intro s
    refine ⟨⟨⟨convexHull ℝ (v '' (s.val : Set (Fin n))),
      (hComplete s.val s.property).1⟩, (hComplete s.val s.property).2.1⟩, ?_⟩
    apply Subtype.ext
    ext i
    change i ∈ Finset.univ.filter
      (fun i => v i ∈ convexHull ℝ (v '' (s.val : Set (Fin n)))) ↔ i ∈ s.val
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using
      (hComplete s.val s.property).2.2 i
  refine ⟨OrderIso.ofSurjective f hf, ?_⟩
  intro F i
  change i ∈ Finset.univ.filter (fun i => v i ∈ F.val.val) ↔ v i ∈ F.val.val
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

end Grunbaum2003

namespace Grunbaum2003.CounterexampleGeometry
open Grunbaum2003.CounterexampleIncidences

 theorem qVertices_any_four (w : Fin 4 → Fin 7) (hw : Function.Injective w) :
    AffineIndependent ℝ (qVertices ∘ w) :=
  four_independent_of_six_independent_except qVertices 4 qVertices_six_independent w hw

 theorem counterexample_two_skeleton_orderIso :
    ∃ φ : SkeletonFace pBody 2 ≃o SkeletonFace qBody 2,
      ∀ F i, pVertices i ∈ F.val.val ↔ qVertices i ∈ (φ F).val.val := by
  classical
  let L := pFaces.filter (fun s => s.card ≤ 3)
  have hP : ∃ Φ : SkeletonFace pBody 2 ≃o ↥L,
      ∀ F i, i ∈ (Φ F).val ↔ pVertices i ∈ F.val.val := by
    apply skeletonTwo_orderIso_of_incidence_certificate pVertices L
    · intro F s hs
      have hmem := pFace_incidence_sound F.val.val F.val.property s hs
      have heq := exposedFace_eq_hull_of_incident_finset pVertices F.val.property s hs
      have hlow := F.property
      rw [heq] at hlow
      exact Finset.mem_filter.mpr ⟨hmem,
        (lowFaceRank_iff_card_le_three pVertices pVertices_any_four s).mp hlow⟩
    · intro s hs
      obtain ⟨hmem, hcard⟩ := Finset.mem_filter.mp hs
      obtain ⟨hface, hlabels⟩ := pFace_incidence_complete s hmem
      exact ⟨hface, (lowFaceRank_iff_card_le_three pVertices pVertices_any_four s).mpr hcard,
        hlabels⟩
  have hQ : ∃ Φ : SkeletonFace qBody 2 ≃o ↥L,
      ∀ F i, i ∈ (Φ F).val ↔ qVertices i ∈ F.val.val := by
    apply skeletonTwo_orderIso_of_incidence_certificate qVertices L
    · intro F s hs
      have hmem := qFace_incidence_sound F.val.val F.val.property s hs
      have heq := exposedFace_eq_hull_of_incident_finset qVertices F.val.property s hs
      have hlow := F.property
      rw [heq] at hlow
      have hcard := (lowFaceRank_iff_card_le_three qVertices qVertices_any_four s).mp hlow
      have hmem' : s ∈ qFaces.filter (fun s => s.card ≤ 3) :=
        Finset.mem_filter.mpr ⟨hmem, hcard⟩
      rw [← two_skeleton_eq] at hmem'
      exact hmem'
    · intro s hs
      have hs' : s ∈ qFaces.filter (fun s => s.card ≤ 3) := by
        rw [← two_skeleton_eq]
        exact hs
      obtain ⟨hmem, hcard⟩ := Finset.mem_filter.mp hs'
      obtain ⟨hface, hlabels⟩ := qFace_incidence_complete s hmem
      exact ⟨hface, (lowFaceRank_iff_card_le_three qVertices qVertices_any_four s).mpr hcard,
        hlabels⟩
  obtain ⟨ΦP, hΦP⟩ := hP
  obtain ⟨ΦQ, hΦQ⟩ := hQ
  refine ⟨ΦP.trans ΦQ.symm, ?_⟩
  intro F i
  have hQ' := hΦQ (ΦQ.symm (ΦP F)) i
  rw [ΦQ.apply_symm_apply] at hQ'
  exact (hΦP F i).symm.trans hQ'

end Grunbaum2003.CounterexampleGeometry

end

-- Ingredient: simplicial_disproof_p/build4331/PVertexSingletons.lean

set_option autoImplicit false

noncomputable section

namespace Grunbaum2003.CounterexampleGeometry

private def pCoord (j : Fin 5) : (Fin 5 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj j

private def pVertexSupport (i : Fin 7) : (Fin 5 → ℝ) →L[ℝ] ℝ :=
  match i.val with
  | 0 => -(pCoord (0 : Fin 5) + pCoord (1 : Fin 5) +
      pCoord (2 : Fin 5) + pCoord (3 : Fin 5))
  | 1 => pCoord (0 : Fin 5)
  | 2 => pCoord (1 : Fin 5)
  | 3 => pCoord (2 : Fin 5)
  | 4 => pCoord (3 : Fin 5)
  | 5 => pCoord (4 : Fin 5)
  | _ => -pCoord (4 : Fin 5)

private def pVertexSupportBound (i : Fin 7) : ℝ := if i.val = 0 then 0 else 1

private theorem pVertexSupport_bound (i j : Fin 7) :
    pVertexSupport i (pVertices j) ≤ pVertexSupportBound i := by
  fin_cases i <;> fin_cases j <;>
    norm_num [pVertexSupport, pVertexSupportBound, pVertices, pCoord, ContinuousLinearMap.proj_apply,
      add_apply, neg_apply]

private theorem pVertexSupport_eq_iff (i j : Fin 7) :
    pVertexSupport i (pVertices j) = pVertexSupportBound i ↔ j = i := by
  fin_cases i <;> fin_cases j <;>
    norm_num [pVertexSupport, pVertexSupportBound, pVertices, pCoord, ContinuousLinearMap.proj_apply,
      add_apply, neg_apply, Fin.ext_iff]

theorem pVertices_singleton_exposed (i : Fin 7) : IsExposed ℝ pBody {pVertices i} := by
  have h := exposedFace_of_label_maximizers pVertices ({i} : Set (Fin 7))
    ⟨i, Set.mem_singleton i⟩ (pVertexSupport i) (pVertexSupportBound i)
    (pVertexSupport_bound i) (by intro j; exact pVertexSupport_eq_iff i j)
  simpa only [pBody, Set.image_singleton, convexHull_singleton] using h.1

theorem pVertices_injective : Function.Injective pVertices := by
  intro i j hij
  have hval : pVertexSupport j (pVertices i) = pVertexSupportBound j := by
    rw [hij]
    exact (pVertexSupport_eq_iff j j).mpr rfl
  exact (pVertexSupport_eq_iff j i).mp hval

theorem pVertex_singleton_incidence (i j : Fin 7) :
    pVertices i ∈ ({pVertices j} : Set (Fin 5 → ℝ)) ↔ i = j := by
  simp only [Set.mem_singleton_iff]
  exact pVertices_injective.eq_iff

end Grunbaum2003.CounterexampleGeometry

end

-- Ingredient: child_disproof_work/ChildDisproof.lean

set_option autoImplicit false

namespace Grunbaum2003.CounterexampleGeometry

private def childTetra : Set (Fin 5 → ℝ) :=
  convexHull ℝ (pVertices '' ({0, 1, 2, 3} : Set (Fin 7)))

private theorem childTetra_support :
    IsExposed ℝ pBody childTetra ∧
      ∀ i : Fin 7, pVertices i ∈ childTetra ↔ i ∈ ({0,1,2,3} : Set (Fin 7)) := by
  let l : StrongDual ℝ (Fin 5 → ℝ) := -ContinuousLinearMap.proj (3 : Fin 5)
  have hbound : ∀ i : Fin 7, l (pVertices i) ≤ 0 := by
    intro i
    fin_cases i <;> norm_num [l, pVertices, ContinuousLinearMap.proj_apply, Fin.ext_iff]
  have heq : ∀ i : Fin 7, l (pVertices i) = 0 ↔ i ∈ ({0,1,2,3} : Set (Fin 7)) := by
    intro i
    fin_cases i <;> norm_num [l, pVertices, ContinuousLinearMap.proj_apply, Fin.ext_iff]
  exact exposedFace_of_label_maximizers pVertices ({0,1,2,3} : Set (Fin 7))
    ⟨0, by simp⟩ l 0 hbound heq

end Grunbaum2003.CounterexampleGeometry

open Grunbaum2003 Grunbaum2003.CounterexampleGeometry

theorem solution : ¬ (∀ (d e : ℕ)
    (P : Set (Fin d → ℝ)) (Q : Set (Fin e → ℝ)),
    IsSimplicialDPolytope P → IsDPolytope Q →
    ∀ φ : SkeletonFace P (d / 2) ≃o SkeletonFace Q (d / 2),
    e = d ∧
    (∀ F : PolytopeFace P, ∃ G : PolytopeFace Q,
      ∀ T : SkeletonFace Q (d / 2), T.val ≤ G ↔ (φ.symm T).val ≤ F) ∧
    (∀ G : PolytopeFace Q, ∃ F : PolytopeFace P,
      ∀ S : SkeletonFace P (d / 2), S.val ≤ F ↔ (φ S).val ≤ G)) := by
  intro h
  obtain ⟨φ, hInc⟩ := counterexample_two_skeleton_orderIso
  have hq : IsDPolytope qBody := qBody_full_dimensional
  have hc := h 5 5 pBody qBody pBody_isSimplicialDPolytope hq φ
  let F : PolytopeFace pBody := ⟨childTetra, childTetra_support.1⟩
  obtain ⟨G, hG⟩ := hc.2.1 F
  let S (i : Fin 7) : SkeletonFace pBody 2 :=
    ⟨⟨{pVertices i}, pVertices_singleton_exposed i⟩, Or.inr (by
      rw [direction_affineSpan, vectorSpan_singleton, finrank_bot]
      exact Nat.zero_le 2)⟩
  have hMap : ∀ i : Fin 7, (φ (S i)).val.val = {qVertices i} := by
    intro i
    have hlabels : ∀ j : Fin 7, qVertices j ∈ (φ (S i)).val.val ↔ j = i := by
      intro j
      rw [← hInc (S i) j]
      change pVertices j ∈ ({pVertices i} : Set (Fin 5 → ℝ)) ↔ j = i
      simpa only [Set.mem_singleton_iff] using pVertices_injective.eq_iff
    have hInter : (φ (S i)).val.val ∩ Set.range qVertices = {qVertices i} := by
      ext x
      constructor
      · rintro ⟨hx, j, rfl⟩
        exact Set.mem_singleton_iff.mpr (congrArg qVertices ((hlabels j).mp hx))
      · intro hx
        have hx' : x = qVertices i := Set.mem_singleton_iff.mp hx
        subst x
        exact ⟨(hlabels i).mpr rfl, Set.mem_range_self i⟩
    calc (φ (S i)).val.val = convexHull ℝ ((φ (S i)).val.val ∩ Set.range qVertices) :=
          exposedFace_eq_convexHull_incident_range qVertices (φ (S i)).val.property
      _ = convexHull ℝ ({qVertices i} : Set (Fin 5 → ℝ)) := congrArg (convexHull ℝ) hInter
      _ = {qVertices i} := convexHull_singleton _
  have hGlabels : ∀ i : Fin 7, qVertices i ∈ G.val ↔ pVertices i ∈ childTetra := by
    intro i
    have hi := hG (φ (S i))
    rw [OrderIso.symm_apply_apply] at hi
    change (φ (S i)).val.val ⊆ G.val ↔ (S i).val.val ⊆ F.val at hi
    rw [hMap i] at hi
    change {qVertices i} ⊆ G.val ↔ {pVertices i} ⊆ childTetra at hi
    simpa only [Set.singleton_subset_iff] using hi
  have hcentral : ∀ i ∈ ({0,1,2,3} : Set (Fin 7)), qVertices i ∈ G.val := by
    intro i hi
    exact (hGlabels i).mpr ((childTetra_support.2 i).mpr hi)
  have hq5 : qVertices 5 ∈ G.val := ((exposedFace_q_circuit_iff G.property).mp hcentral).1
  have hp5 := (hGlabels 5).mp hq5
  have himpossible := (childTetra_support.2 5).mp hp5
  norm_num [Fin.ext_iff] at himpossible

