-- Prove2me | solution 1 for MeasureTheory.Measure.gram_smul_map_volume_eq_of_span_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/3abe6c83-7cbd-52fb-a8c3-faf04baca442

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MeasureTheory_Measure_gram_smul_map_volume_eq_of_span_eq

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace P2mGramBasis

variable {V : Type} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [ContinuousAdd V]
  [ContinuousSMul ℝ V] [MeasurableSpace V] [BorelSpace V]

def coordMap {n : ℕ} (e : Fin n → V) : (Fin n → ℝ) → V := fun c => ∑ i, c i • e i

theorem continuous_coordMap {n : ℕ} (e : Fin n → V) : Continuous (coordMap e) := by
  unfold coordMap
  exact continuous_finsetSum _ fun i _ => (continuous_apply i).smul continuous_const

theorem measurable_coordMap {n : ℕ} (e : Fin n → V) : Measurable (coordMap e) :=
  (continuous_coordMap e).measurable

def gramDet (B : LinearMap.BilinForm ℝ V) {n : ℕ} (e : Fin n → V) : ℝ :=
  (Matrix.of fun i j : Fin n => B (e i) (e j)).det

def gramMeasure (B : LinearMap.BilinForm ℝ V) {n : ℕ} (e : Fin n → V) : Measure V :=
  ENNReal.ofReal (Real.sqrt |gramDet B e|) • Measure.map (coordMap e) volume

theorem coordMap_eq_comp {n : ℕ} (e e' : Fin n → V) (P : Matrix (Fin n) (Fin n) ℝ)
    (hP : ∀ j, e' j = ∑ i, P i j • e i) :
    coordMap e' = coordMap e ∘ (Matrix.toLin' P) := by
  funext c
  simp only [coordMap, Function.comp_apply, Matrix.toLin'_apply]
  calc ∑ j, c j • e' j = ∑ j, ∑ i, (c j * P i j) • e i := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hP j, Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [smul_smul]
    _ = ∑ i, ∑ j, (c j * P i j) • e i := Finset.sum_comm
    _ = ∑ i, (P.mulVec c) i • e i := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.sum_smul]
        congr 1
        change ∑ j, c j * P i j = ∑ j, P i j * c j
        exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem gramDet_eq_of_comp (B : LinearMap.BilinForm ℝ V) {n : ℕ} (e e' : Fin n → V)
    (P : Matrix (Fin n) (Fin n) ℝ) (hP : ∀ j, e' j = ∑ i, P i j • e i) :
    gramDet B e' = P.det ^ 2 * gramDet B e := by
  have hG : (Matrix.of fun i j : Fin n => B (e' i) (e' j)) =
      P.transpose * (Matrix.of fun i j : Fin n => B (e i) (e j)) * P := by
    ext j k
    have hjk : B (e' j) (e' k) = ∑ i, ∑ l, P i j * P l k * B (e i) (e l) := by
      have h1 : B (e' j) = ∑ i, P i j • B (e i) := by rw [hP j, map_sum]; simp only [map_smul]
      rw [h1, LinearMap.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [LinearMap.smul_apply, hP k, map_sum, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [map_smul, smul_eq_mul]
      ring
    simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply]
    rw [hjk, Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [gramDet, gramDet, hG, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  ring

theorem gramMeasure_eq_of_comp (B : LinearMap.BilinForm ℝ V) {n : ℕ} (e e' : Fin n → V)
    (P : Matrix (Fin n) (Fin n) ℝ) (hP : ∀ j, e' j = ∑ i, P i j • e i) (hdet : P.det ≠ 0) :
    gramMeasure B e' = gramMeasure B e := by
  rw [gramMeasure, gramMeasure, coordMap_eq_comp e e' P hP, gramDet_eq_of_comp B e e' P hP,
    ← Measure.map_map (measurable_coordMap e) (Matrix.toLin' P).continuous_of_finiteDimensional.measurable,
    Real.map_matrix_volume_pi_eq_smul_volume_pi hdet, Measure.map_smul, smul_smul]
  congr 1
  rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _), abs_mul, abs_pow, Real.sqrt_mul' _ (abs_nonneg _),
    Real.sqrt_sq (abs_nonneg _), abs_inv]
  congr 1
  rw [mul_comm, ← mul_assoc, inv_mul_cancel₀ (abs_ne_zero.mpr hdet), one_mul]

theorem exists_matrix_of_span_le {n : ℕ} (e e' : Fin n → V)
    (he' : LinearIndependent ℝ e')
    (hspan : Submodule.span ℝ (Set.range e') ≤ Submodule.span ℝ (Set.range e)) :
    ∃ P : Matrix (Fin n) (Fin n) ℝ, (∀ j, e' j = ∑ i, P i j • e i) ∧ P.det ≠ 0 := by
  have hmem : ∀ j, e' j ∈ Submodule.span ℝ (Set.range e) := fun j =>
    hspan (Submodule.subset_span ⟨j, rfl⟩)
  choose c hc using fun j => (Submodule.mem_span_range_iff_exists_fun ℝ).mp (hmem j)
  refine ⟨Matrix.of fun i j => c j i, fun j => ?_, ?_⟩
  · simp only [Matrix.of_apply]; exact (hc j).symm
  · intro hdet
    obtain ⟨v, hv, hPv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    have hP : ∀ j, e' j = ∑ i, (Matrix.of fun i j => c j i) i j • e i := fun j => by
      simp only [Matrix.of_apply]; exact (hc j).symm
    have h0 : coordMap e' v = 0 := by
      rw [coordMap_eq_comp e e' _ hP, Function.comp_apply, Matrix.toLin'_apply, hPv]
      simp [coordMap]
    apply hv
    funext j
    exact Fintype.linearIndependent_iff.mp he' v h0 j

theorem card_eq_of_span_eq {n n' : ℕ} (e : Fin n → V) (e' : Fin n' → V) (he : LinearIndependent ℝ e)
    (he' : LinearIndependent ℝ e')
    (hspan : Submodule.span ℝ (Set.range e') = Submodule.span ℝ (Set.range e)) : n' = n := by
  have h1 := finrank_span_eq_card he
  have h2 := finrank_span_eq_card he'
  rw [hspan, h1, Fintype.card_fin, Fintype.card_fin] at h2
  exact h2.symm

theorem main (B : LinearMap.BilinForm ℝ V) {n n' : ℕ} (e : Fin n → V) (e' : Fin n' → V)
    (he : LinearIndependent ℝ e) (he' : LinearIndependent ℝ e')
    (hspan : Submodule.span ℝ (Set.range e') = Submodule.span ℝ (Set.range e)) :
    (ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n' => B (e' i) (e' j)).det|)) •
        Measure.map (fun c : Fin n' → ℝ => ∑ i, c i • e' i) volume =
      (ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n => B (e i) (e j)).det|)) •
        Measure.map (fun c : Fin n → ℝ => ∑ i, c i • e i) volume := by
  obtain rfl : n' = n := card_eq_of_span_eq e e' he he' hspan
  obtain ⟨P, hP, hdet⟩ := exists_matrix_of_span_le e e' he' hspan.le
  exact gramMeasure_eq_of_comp B e e' P hP hdet

end P2mGramBasis

end

open MeasureTheory in
theorem solution
    {V : Type} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [ContinuousAdd V] [ContinuousSMul ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    (B : LinearMap.BilinForm ℝ V) {n n' : ℕ} (e : Fin n → V) (e' : Fin n' → V)
    (he : LinearIndependent ℝ e) (he' : LinearIndependent ℝ e')
    (hspan : Submodule.span ℝ (Set.range e') = Submodule.span ℝ (Set.range e)) :
    (ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n' => B (e' i) (e' j)).det|)) •
        Measure.map (fun c : Fin n' → ℝ => ∑ i, c i • e' i) volume =
      (ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n => B (e i) (e j)).det|)) •
        Measure.map (fun c : Fin n → ℝ => ∑ i, c i • e i) volume :=
  P2mGramBasis.main B e e' he he' hspan

end S_MeasureTheory_Measure_gram_smul_map_volume_eq_of_span_eq
end P2MW
export P2MW.S_MeasureTheory_Measure_gram_smul_map_volume_eq_of_span_eq (solution)
