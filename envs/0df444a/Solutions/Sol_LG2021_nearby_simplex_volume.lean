-- Prove2me | solution 1 for LG2021.nearby_simplex_volume
-- status  : ACCEPTED   (prove)
-- author  : @sim2000dg
-- created : 2026-11-14T15:26:20.947178+00:00
-- url     : https://prove2.me/submissions/5ee2ef9d-4d9e-4ce5-9c2a-e56ec93ba823

import Mathlib
import Definitions.Def_ModernConvex_Ellipsoids_Ellipsoid
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplexVolume_succ_mul_volume
set_option autoImplicit false

namespace LG2021
private abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)
end LG2021

section
namespace LG2021
open Matrix ModernConvex.Ellipsoids
private def matrixAffineMap {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (c : Fin m → ℝ) :
    (Fin m → ℝ) →ᵃ[ℝ] (Fin m → ℝ) :=
  A.mulVecLin.toAffineMap + AffineMap.const ℝ (Fin m → ℝ) c
private theorem euclidean_unitBall_iff {m : ℕ} (x : EuclideanSpace ℝ (Fin m)) :
    EuclideanSpace.equiv (Fin m) ℝ x ∈ unitBall m ↔
      x ∈ Metric.closedBall 0 1 := by
  have hdot : (EuclideanSpace.equiv (Fin m) ℝ x) ⬝ᵥ
      (EuclideanSpace.equiv (Fin m) ℝ x) = ‖x‖ ^ 2 := by
    simpa only [EuclideanSpace.equiv, PiLp.coe_continuousLinearEquiv, dotProduct, pow_two]
      using (EuclideanSpace.real_norm_sq_eq x).symm
  simp only [ModernConvex.Ellipsoids.unitBall, Set.mem_setOf_eq]
  rw [hdot, Metric.mem_closedBall, dist_zero_right]
  constructor <;> intro h <;> nlinarith [norm_nonneg x]

end LG2021
namespace LG2021.JohnHelpers
open MeasureTheory
private lemma volume_translate {n : ℕ} (S : Set (Fin n → ℝ)) (c : Fin n → ℝ) :
    volume ((fun x => x+c) '' S) = volume S := by
  have he : (fun x => x+c) '' S = (fun x => x+(-c)) ⁻¹' S := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      simpa using hy
    · intro hx
      exact ⟨x+(-c), hx, by simp⟩
  rw [he, measure_preimage_add_right]

end LG2021.JohnHelpers

end

section

/-!
The simplex construction of Lemma7 in Lattimore and György (2021).
Within the same slice at first coordinate -1/2, a right simplex gives exactly
the stated lower bound; maximization over regular simplices is unnecessary.
The protected set remains the source's d+1 nearby vertices and their hull.
-/

noncomputable section
namespace LG2021.Algorithm

open Matrix MeasureTheory Set
open scoped BigOperators Classical

private def sliceRadius : ℝ := Real.sqrt (3 / 4)

private def sliceVertex {m : ℕ} (j : Fin (m + 1)) : Fin (m + 1) → ℝ :=
  fun i => if i = 0 then -1 / 2 else if i = j then sliceRadius else 0

private def axisPoint {m : ℕ} (α : ℝ) : Fin (m + 1) → ℝ := Pi.single 0 α

private def sliceEdgeMatrix (m : ℕ) (α : ℝ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
  fun i j => if i = 0 then -(α + 1 / 2) else if i = j then sliceRadius else 0

private theorem sliceRadius_pos : 0 < sliceRadius := Real.sqrt_pos.mpr (by norm_num)

private theorem sliceRadius_sq : sliceRadius^2 = 3 / 4 := Real.sq_sqrt (by norm_num)

private theorem sliceRadius_pow (m : ℕ) :
    sliceRadius^m = (3 / 4 : ℝ)^((m : ℝ) / 2) := by
  rw [sliceRadius, Real.sqrt_eq_rpow, ← Real.rpow_natCast,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3 / 4)]
  congr 1
  ring

private theorem sliceVertex_first {m : ℕ} (j : Fin (m + 1)) : sliceVertex j 0 = -1 / 2 := by
  simp [sliceVertex]

private theorem sliceVertex_unitBall {m : ℕ} (j : Fin (m + 1)) :
    sliceVertex j ∈ ModernConvex.Ellipsoids.unitBall (m + 1) := by
  change (∑ i, sliceVertex j i * sliceVertex j i) ≤ 1
  rw [Fin.sum_univ_succ]
  simp only [sliceVertex_first]
  refine Fin.cases ?_ (fun j => ?_) j
  · simp [sliceVertex]
    norm_num
  · have he : (∑ i : Fin m, sliceVertex j.succ i.succ * sliceVertex j.succ i.succ) = sliceRadius^2 := by
      simp [sliceVertex, pow_two]
    rw [he, sliceRadius_sq]
    norm_num

private theorem sliceEdgeMatrix_column {m : ℕ} (α : ℝ) (j : Fin (m + 1)) :
    (fun i => sliceEdgeMatrix m α i j) = sliceVertex j - axisPoint α := by
  ext i
  by_cases hi : i = 0
  · subst i
    simp [sliceEdgeMatrix, sliceVertex, axisPoint]
    ring
  · simp [sliceEdgeMatrix, sliceVertex, axisPoint, hi]

private theorem sliceEdgeMatrix_triangular (m : ℕ) (α : ℝ) :
    (sliceEdgeMatrix m α).IsUpperTriangular := by
  intro i j hij
  have hi : i ≠ 0 := by intro hi; subst i; exact (not_lt_of_ge (Fin.zero_le _)) hij
  have hne : i ≠ j := ne_of_gt hij
  simp [sliceEdgeMatrix, hi, hne]

private theorem sliceEdgeMatrix_det (m : ℕ) (α : ℝ) :
    (sliceEdgeMatrix m α).det = -(α + 1 / 2) * sliceRadius^m := by
  rw [Matrix.det_of_isUpperTriangular (sliceEdgeMatrix_triangular m α), Fin.prod_univ_succ]
  simp [sliceEdgeMatrix]

private theorem sliceEdgeMatrix_abs_det (m : ℕ) {α : ℝ} (hα : 0 ≤ α) :
    |(sliceEdgeMatrix m α).det| = (α + 1 / 2) * sliceRadius^m := by
  rw [sliceEdgeMatrix_det, abs_mul, abs_neg, abs_of_nonneg (by linarith),
    abs_of_nonneg (pow_nonneg sliceRadius_pos.le _)]

private theorem sliceEdgeMatrix_abs_det_lower (m : ℕ) {α : ℝ} (hα : 0 ≤ α) :
    (1 / 2) * sliceRadius^m ≤ |(sliceEdgeMatrix m α).det| := by
  rw [sliceEdgeMatrix_abs_det m hα]
  exact mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg sliceRadius_pos.le _)

private theorem sliceEdgeMatrix_det_ne_zero (m : ℕ) {α : ℝ} (hα : 0 ≤ α) :
    (sliceEdgeMatrix m α).det ≠ 0 := by
  rw [sliceEdgeMatrix_det]
  exact mul_ne_zero (neg_ne_zero.mpr (by linarith)) (pow_pos sliceRadius_pos _).ne'

private def coordinateSimplex (d : ℕ) : Set (Fin d → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ 1}

private theorem coordinateSimplex_convex (d : ℕ) : Convex ℝ (coordinateSimplex d) := by
  intro x hx y hy a b ha hb hab
  constructor
  · intro i
    exact add_nonneg (mul_nonneg ha (hx.1 i)) (mul_nonneg hb (hy.1 i))
  · change (∑ i : Fin d, (a * x i + b * y i)) ≤ 1
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    nlinarith [mul_le_mul_of_nonneg_left hx.2 ha, mul_le_mul_of_nonneg_left hy.2 hb]

private theorem coordinateSimplex_eq_convexHull (d : ℕ) :
    coordinateSimplex d = convexHull ℝ (insert 0 (range fun i : Fin d => Pi.single i (1 : ℝ))) := by
  apply le_antisymm
  · intro x hx
    apply mem_convexHull_of_exists_fintype
      (fun i : Option (Fin d) => i.elim (1 - ∑ j, x j) x)
      (fun i : Option (Fin d) => i.elim 0 (fun j => Pi.single j 1))
    · intro i
      cases i with
      | none => exact sub_nonneg.mpr hx.2
      | some j => exact hx.1 j
    · simp
    · intro i
      cases i with
      | none => exact mem_insert _ _
      | some j => exact mem_insert_of_mem _ (mem_range_self j)
    · simp only [Fintype.sum_option, Option.elim_none, Option.elim_some, smul_zero, zero_add]
      ext i
      simp [Pi.single_apply, Finset.sum_apply, Pi.smul_apply]
  · apply convexHull_min ?_ (coordinateSimplex_convex d)
    intro x hx
    rcases hx with rfl | ⟨i, rfl⟩
    · simp [coordinateSimplex]
    · simp only [coordinateSimplex, mem_setOf_eq]
      constructor
      · intro j
        simp only [Pi.single_apply]
        split_ifs <;> norm_num
      · simp [Pi.single_apply]

private def affineSimplex {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (c : Fin d → ℝ) : Set (Fin d → ℝ) :=
  (matrixAffineMap A c) '' coordinateSimplex d

private theorem affineSimplex_eq_convexHull {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (c : Fin d → ℝ) :
    affineSimplex A c = convexHull ℝ (insert c
      (range fun i : Fin d => A *ᵥ Pi.single i 1 + c)) := by
  rw [affineSimplex, coordinateSimplex_eq_convexHull, AffineMap.image_convexHull]
  congr 1
  rw [image_insert_eq, ← range_comp]
  change insert (A *ᵥ 0 + c) (range fun i => A *ᵥ Pi.single i 1 + c) = _
  simp

private theorem volume_affineSimplex {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (c : Fin d → ℝ) :
    volume (affineSimplex A c) = ENNReal.ofReal |A.det| * volume (coordinateSimplex d) := by
  have he : affineSimplex A c = (fun x => x + c) '' (Matrix.toLin' A '' coordinateSimplex d) := by
    rw [affineSimplex, image_image]
    rfl
  rw [he, LG2021.JohnHelpers.volume_translate,
    MeasureTheory.Measure.addHaar_image_linearMap, LinearMap.det_toLin']

private def sliceVertices (m : ℕ) (α : ℝ) : Fin (m + 2) → (Fin (m + 1) → ℝ) :=
  Fin.cons (axisPoint α) sliceVertex

private theorem sliceVertices_hull (m : ℕ) (α : ℝ) :
    convexHull ℝ (range (sliceVertices m α)) = affineSimplex (sliceEdgeMatrix m α) (axisPoint α) := by
  rw [affineSimplex_eq_convexHull, sliceVertices, Fin.range_cons]
  have he (i : Fin (m + 1)) : sliceEdgeMatrix m α *ᵥ Pi.single i 1 + axisPoint α = sliceVertex i := by
    rw [Matrix.mulVec_single_one]
    have h := sliceEdgeMatrix_column α i
    change (fun j => sliceEdgeMatrix m α j i) + axisPoint α = sliceVertex i
    rw [h]
    simp
  simp_rw [he]

private theorem sliceVertex_injective (m : ℕ) : Function.Injective (@sliceVertex m) := by
  intro i j hij
  by_contra hne
  by_cases hi : i = 0
  · subst i
    have hj : j ≠ 0 := Ne.symm hne
    have h := congrFun hij j
    simp [sliceVertex, hj] at h
    exact sliceRadius_pos.ne' h.symm
  · have h := congrFun hij i
    simp [sliceVertex, hi, hne] at h
    exact sliceRadius_pos.ne' h

private theorem sliceVertices_injective (m : ℕ) {α : ℝ} (hα : 0 ≤ α) :
    Function.Injective (sliceVertices m α) := by
  apply Fin.cons_injective_of_injective ?_ (sliceVertex_injective m)
  rintro ⟨j, hj⟩
  have h := congrFun hj 0
  simp [sliceVertex, axisPoint] at h
  linarith

private theorem sliceVertices_card (m : ℕ) {α : ℝ} (hα : 0 ≤ α) :
    (range (sliceVertices m α)).ncard = m + 2 := by
  rw [Set.ncard_range_of_injective (sliceVertices_injective m hα)]
  simp

private theorem coordinateSimplex_volume (d : ℕ) :
    volume (coordinateSimplex d) = ENNReal.ofReal (1 / (d.factorial : ℝ)) := by
  induction d with
  | zero =>
      have he : coordinateSimplex 0 = (univ : Set (Fin 0 → ℝ)) := by
        ext x
        simp [coordinateSimplex]
      rw [he, ← Set.pi_univ (Set.univ : Set (Fin 0)), MeasureTheory.volume_pi_pi]
      simp
  | succ d ih =>
      have h := OAI.PiExponent.DeterminantContradiction.simplexVolume_succ_mul_volume d
      change volume (coordinateSimplex (d + 1)) =
        volume (coordinateSimplex d) * ENNReal.ofReal (1 / ((d + 1 : ℕ) : ℝ)) at h
      rw [h, ih, ← ENNReal.ofReal_mul (by positivity), Nat.factorial_succ]
      congr 1
      push_cast
      field_simp

private theorem sliceVertices_volume (m : ℕ) {α : ℝ} (hα : 0 ≤ α) :
    volume (convexHull ℝ (range (sliceVertices m α))) =
      ENNReal.ofReal ((α + 1 / 2) * sliceRadius^m / ((m + 1).factorial : ℝ)) := by
  rw [sliceVertices_hull, volume_affineSimplex, coordinateSimplex_volume,
    sliceEdgeMatrix_abs_det m hα, ← ENNReal.ofReal_mul (mul_nonneg (by linarith) (pow_nonneg sliceRadius_pos.le _))]
  congr 1
  ring

private def scaledSliceVertices (m : ℕ) (α ε : ℝ) : Fin (m + 2) → (Fin (m + 1) → ℝ) :=
  fun i => (1 - ε) • axisPoint α + ε • sliceVertices m α i

private theorem scaledSliceVertices_zero (m : ℕ) (α ε : ℝ) :
    scaledSliceVertices m α ε 0 = axisPoint α := by
  simp only [scaledSliceVertices, sliceVertices, Fin.cons_zero]
  module

private theorem scaledSliceVertices_hull (m : ℕ) (α ε : ℝ) :
    convexHull ℝ (range (scaledSliceVertices m α ε)) =
      affineSimplex (ε • sliceEdgeMatrix m α) (axisPoint α) := by
  have hcons : scaledSliceVertices m α ε = Fin.cons (axisPoint α)
      (fun j => (1 - ε) • axisPoint α + ε • sliceVertex j) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact scaledSliceVertices_zero m α ε
    · rfl
  rw [hcons, Fin.range_cons, affineSimplex_eq_convexHull]
  have he (i : Fin (m + 1)) : (ε • sliceEdgeMatrix m α) *ᵥ Pi.single i 1 + axisPoint α =
      (1 - ε) • axisPoint α + ε • sliceVertex i := by
    rw [smul_mulVec, Matrix.mulVec_single_one]
    change ε • (fun j => sliceEdgeMatrix m α j i) + axisPoint α = _
    rw [sliceEdgeMatrix_column α i]
    module
  simp_rw [he]

private theorem scaledSliceVertices_volume (m : ℕ) {α ε : ℝ} (hα : 0 ≤ α) (hε : 0 ≤ ε) :
    volume (convexHull ℝ (range (scaledSliceVertices m α ε))) =
      ENNReal.ofReal (ε^(m + 1) * (α + 1 / 2) * sliceRadius^m / ((m + 1).factorial : ℝ)) := by
  have ht : 0 ≤ sliceRadius := sliceRadius_pos.le
  rw [scaledSliceVertices_hull, volume_affineSimplex, coordinateSimplex_volume,
    det_smul, Fintype.card_fin, abs_mul, abs_of_nonneg (pow_nonneg hε _),
    sliceEdgeMatrix_abs_det m hα, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

private theorem scaledSliceVertices_volume_lower (m : ℕ) {α ε : ℝ} (hα : 0 ≤ α) (hε : 0 ≤ ε) :
    ENNReal.ofReal (ε^(m + 1) * sliceRadius^m / (2 * ((m + 1).factorial : ℝ))) ≤
      volume (convexHull ℝ (range (scaledSliceVertices m α ε))) := by
  rw [scaledSliceVertices_volume m hα hε]
  apply ENNReal.ofReal_le_ofReal
  have hfac : 0 < ((m + 1).factorial : ℝ) := by positivity
  have he : ε^(m + 1) * sliceRadius^m / (2 * ((m + 1).factorial : ℝ)) =
      (ε^(m + 1) * (1 / 2) * sliceRadius^m) / ((m + 1).factorial : ℝ) := by ring
  rw [he]
  gcongr
  · exact pow_nonneg sliceRadius_pos.le _
  · linarith

private theorem scaledSliceVertices_injective (m : ℕ) {α ε : ℝ} (hα : 0 ≤ α) (hε : ε ≠ 0) :
    Function.Injective (scaledSliceVertices m α ε) := by
  intro i j hij
  apply sliceVertices_injective m hα
  change (1 - ε) • axisPoint α + ε • sliceVertices m α i =
    (1 - ε) • axisPoint α + ε • sliceVertices m α j at hij
  exact (smul_right_injective _ hε) (add_left_cancel hij)

private theorem axis_rotation (m : ℕ) (x : Space (m + 1)) :
    ∃ ρ : Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1),
      ρ ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (axisPoint ‖x‖)) = x := by
  let v := (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (axisPoint ‖x‖)
  have hnorm : ‖v‖ = ‖x‖ := by
    change ‖EuclideanSpace.single (0 : Fin (m + 1)) ‖x‖‖ = ‖x‖
    simp
  exact ⟨(ℝ ∙ (v - x))ᗮ.reflection, Submodule.reflection_sub hnorm⟩

/-- The source's nearby d+1-vertex simplex, with its exact stated volume
constant. The upper bound D on pairwise distances can be taken to be diam(K). -/
private theorem source_simplex (m : ℕ) {K : Set (Space (m + 1))} (hcv : Convex ℝ K)
    (hball : Metric.closedBall (0 : Space (m + 1)) 1 ⊆ K)
    {D δ : ℝ} (hD : 0 < D) (hδ : 0 < δ) (hδD : δ ≤ D)
    (hdiam : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D)
    {x : Space (m + 1)} (hx : x ∈ K) :
    ∃ v : Fin (m + 2) → Space (m + 1), Function.Injective v ∧ v 0 = x ∧
      (∀ i, v i ∈ K) ∧ (∀ i, dist x (v i) ≤ δ) ∧
      ENNReal.ofReal ((δ / D)^(m + 1) * sliceRadius^m / (2 * ((m + 1).factorial : ℝ))) ≤
        volume (convexHull ℝ (range v)) := by
  obtain ⟨ρ, hρ⟩ := axis_rotation m x
  let q := EuclideanSpace.equiv (Fin (m + 1)) ℝ
  let e : (Fin (m + 1) → ℝ) ≃L[ℝ] Space (m + 1) := q.symm.trans ρ.toContinuousLinearEquiv
  have heaxis : e (axisPoint ‖x‖) = x := hρ
  let ε := δ / D
  have hε : 0 < ε := div_pos hδ hD
  have hε1 : ε ≤ 1 := (div_le_one hD).mpr hδD
  let v : Fin (m + 2) → Space (m + 1) := e ∘ scaledSliceVertices m ‖x‖ ε
  have hv0 : v 0 = x := by
    change e (scaledSliceVertices m ‖x‖ ε 0) = x
    rw [scaledSliceVertices_zero, heaxis]
  have hbase (j : Fin (m + 1)) : e (sliceVertex j) ∈ K := by
    apply hball
    have hu := (LG2021.euclidean_unitBall_iff (q.symm (sliceVertex j))).mp
      (by
        change q (q.symm (sliceVertex j)) ∈ ModernConvex.Ellipsoids.unitBall (m + 1)
        rw [q.apply_symm_apply]
        exact sliceVertex_unitBall j)
    have hu' : ‖q.symm (sliceVertex j)‖ ≤ 1 := by simpa using hu
    change ‖ρ (q.symm (sliceVertex j)) - 0‖ ≤ 1
    simpa using hu'
  have hvs (j : Fin (m + 1)) : v j.succ = (1 - ε) • x + ε • e (sliceVertex j) := by
    change e ((1 - ε) • axisPoint ‖x‖ + ε • sliceVertex j) = _
    rw [map_add, map_smul, map_smul, heaxis]
  refine ⟨v, e.injective.comp (scaledSliceVertices_injective m (norm_nonneg x) hε.ne'), hv0, ?_, ?_, ?_⟩
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · rwa [hv0]
    · rw [hvs]
      exact hcv hx (hbase j) (sub_nonneg.mpr hε1) hε.le (by ring)
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa [hv0] using hδ.le
    · rw [hvs, dist_eq_norm]
      have he : x - ((1 - ε) • x + ε • e (sliceVertex j)) = ε • (x - e (sliceVertex j)) := by module
      rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos hε]
      have hd := hdiam x hx (e (sliceVertex j)) (hbase j)
      rw [dist_eq_norm] at hd
      calc
        ε * ‖x - e (sliceVertex j)‖ ≤ ε * D := mul_le_mul_of_nonneg_left hd hε.le
        _ = δ := by dsimp [ε]; field_simp
  · have himage : convexHull ℝ (range v) =
        e '' convexHull ℝ (range (scaledSliceVertices m ‖x‖ ε)) := by
      have h := e.toLinearMap.image_convexHull (range (scaledSliceVertices m ‖x‖ ε))
      rw [← range_comp] at h
      exact h.symm
    have hp : MeasurePreserving e (volume : Measure (Fin (m + 1) → ℝ)) volume := by
      exact ρ.measurePreserving.comp (PiLp.volume_preserving_toLp (Fin (m + 1)))
    have hvol : ∀ S : Set (Fin (m + 1) → ℝ), volume (e '' S) = volume S := by
      intro S
      have h := hp.measure_preimage_emb e.toHomeomorph.measurableEmbedding (e '' S)
      simpa only [e.injective.preimage_image] using h.symm
    rw [himage, hvol]
    exact scaledSliceVertices_volume_lower m (norm_nonneg x) hε.le

private theorem source_simplex_dim {d : ℕ} (hd : 0 < d) {K : Set (Space d)} (hcv : Convex ℝ K)
    (hball : Metric.closedBall (0 : Space d) 1 ⊆ K)
    {D δ : ℝ} (hD : 0 < D) (hδ : 0 < δ) (hδD : δ ≤ D)
    (hdiam : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D) {x : Space d} (hx : x ∈ K) :
    ∃ v : Fin (d + 1) → Space d, Function.Injective v ∧ v 0 = x ∧
      (∀ i, v i ∈ K) ∧ (∀ i, dist x (v i) ≤ δ) ∧
      ENNReal.ofReal ((δ / D)^d * sliceRadius^(d - 1) / (2 * (d.factorial : ℝ))) ≤
        volume (convexHull ℝ (range v)) := by
  cases d with
  | zero => omega
  | succ m =>
      simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel] using
        source_simplex m hcv hball hD hδ hδD hdiam hx

private theorem source_protected_simplex {d : ℕ} (hd : 0 < d) {K : Set (Space d)} (hcv : Convex ℝ K)
    (hball : Metric.closedBall (0 : Space d) 1 ⊆ K)
    {D δ : ℝ} (hD : 0 < D) (hδ : 0 < δ) (hδD : δ ≤ D)
    (hdiam : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D) {x : Space d} (hx : x ∈ K)
    (f : Space d → ℝ) (hf : LipschitzOnWith 1 f K) :
    ∃ v : Fin (d + 1) → Space d, Function.Injective v ∧ v 0 = x ∧
      (∀ i, v i ∈ K) ∧ (∀ i, f (v i) ≤ f x + δ) ∧
      ENNReal.ofReal ((δ / D)^d * sliceRadius^(d - 1) / (2 * (d.factorial : ℝ))) ≤
        volume (convexHull ℝ (range v)) := by
  obtain ⟨v, hinj, hv0, hvK, hdist, hvol⟩ := source_simplex_dim hd hcv hball hD hδ hδD hdiam hx
  refine ⟨v, hinj, hv0, hvK, ?_, hvol⟩
  intro i
  have h := hf.le_add_mul (hvK i) hx
  simp only [NNReal.coe_one, one_mul] at h
  have hd' : dist (v i) x ≤ δ := by simpa [dist_comm] using hdist i
  linarith

end LG2021.Algorithm

end
end

namespace LG2021
open MeasureTheory Set

/-- The nearby simplex from Lattimore and Gyorgy (COLT 2021), Lemma 7.
The same slice, `d+1` vertices, homothety and volume lower bound are retained;
a triangular determinant computes the volume directly. -/
theorem nearby_simplex_volume {d : ℕ} (hd : 0 < d)
    {K : Set (EuclideanSpace ℝ (Fin d))} (hcv : Convex ℝ K)
    (hball : Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 ⊆ K)
    {D δ : ℝ} (hD : 0 < D) (hδ : 0 < δ) (hδD : δ ≤ D)
    (hdiam : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D)
    {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ K) :
    ∃ v : Fin (d + 1) → EuclideanSpace ℝ (Fin d), Function.Injective v ∧ v 0 = x ∧
      (∀ i, v i ∈ K) ∧ (∀ i, dist x (v i) ≤ δ) ∧
      ENNReal.ofReal ((δ / D)^d * (Real.sqrt (3 / 4))^(d - 1) / (2 * (d.factorial : ℝ))) ≤
        volume (convexHull ℝ (range v)) := by
  exact Algorithm.source_simplex_dim hd hcv hball hD hδ hδD hdiam hx

end LG2021

open MeasureTheory Set
theorem solution {d : ℕ} (hd : 0 < d)
    {K : Set (EuclideanSpace ℝ (Fin d))} (hcv : Convex ℝ K)
    (hball : Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 ⊆ K)
    {D δ : ℝ} (hD : 0 < D) (hδ : 0 < δ) (hδD : δ ≤ D)
    (hdiam : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D)
    {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ K) :
    ∃ v : Fin (d + 1) → EuclideanSpace ℝ (Fin d), Function.Injective v ∧ v 0 = x ∧
      (∀ i, v i ∈ K) ∧ (∀ i, dist x (v i) ≤ δ) ∧
      ENNReal.ofReal ((δ / D)^d * (Real.sqrt (3 / 4))^(d - 1) / (2 * (d.factorial : ℝ))) ≤
        volume (convexHull ℝ (range v)) := by
  exact LG2021.nearby_simplex_volume hd hcv hball hD hδ hδD hdiam hx
