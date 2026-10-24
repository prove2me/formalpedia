-- Prove2me | solution 1 for K24.Global.FlatTorus.metric_positivity
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T18:35:15.629491+00:00
-- url     : https://prove2.me/submissions/79a435ca-f86f-44f8-b58e-2f238cede322

import Definitions.Def_K24GlobalStatement

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter Topology
open scoped Manifold ContDiff BigOperators NNReal ENNReal Matrix.Norms.Elementwise

namespace K24.Global.FlatTorus

theorem chartAt_eq_localInverse (p : Torus) :
    (chartAt FourSpace p : Torus → FourSpace) =
      quotientMap_isLocalHomeomorph.localInverseAt (representative p) := by
  rfl

theorem chartAt_quotient_eventually (p : Torus) :
    (fun x => chartAt FourSpace p (quotientMap x)) =ᶠ[𝓝 (representative p)] id := by
  let e := quotientMap_isLocalHomeomorph.localInverseAt (representative p)
  have he : e.target ∈ 𝓝 (representative p) :=
    e.open_target.mem_nhds (quotientMap_isLocalHomeomorph.self_mem_localInverseAt_target)
  filter_upwards [he] with x hx
  rw [chartAt_eq_localInverse]
  change e (quotientMap x) = x
  rw [← quotientMap_isLocalHomeomorph.localInverseAt_symm (representative p)]
  exact e.right_inv hx

theorem coverDifferential_representative (p : Torus) :
    coverDifferential (representative p) = ContinuousLinearMap.id ℝ FourSpace := by
  apply HasMFDerivAt.mfderiv
  refine ⟨quotientMap_isLocalHomeomorph.continuous.continuousAt, ?_⟩
  have h := (hasFDerivAt_id (𝕜 := ℝ) (representative p)).congr_of_eventuallyEq
    (chartAt_quotient_eventually p)
  convert h.hasFDerivWithinAt (s := Set.univ) using 1 <;>
    first | rfl | simp [writtenInExtChartAt, quotientMap_representative, Function.comp_def]

@[simp] theorem frame_eq_basisVector (p : Torus) (i : Fin 4) :
    frame p i = basisVector i := by
  unfold frame
  rw [coverDifferential_representative]
  rfl

@[simp] theorem coframe_eq_coordProj (p : Torus) (i : Fin 4) :
    coframe p i = coordProj i := by
  unfold coframe
  rw [coverDifferential_representative]
  simp only [ContinuousLinearMap.inverse_id]
  rfl

@[simp] theorem flatMetric_apply (p : Torus) (v w : FourSpace) :
    flatMetric p v w = ∑ i : Fin 4, v i * w i := by
  simp only [flatMetric, coframe_eq_coordProj, sum_apply,
    ContinuousLinearMap.smulRight_apply]
  rfl

@[simp] theorem perturbation_apply (alpha : ℝ) (n : ℕ) (p : Torus)
    (v w : FourSpace) :
    perturbation alpha n p v w = oscillatingScalar alpha n p * v 0 * w 0 := by
  simp only [perturbation, coframe_eq_coordProj, smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  change oscillatingScalar alpha n p * (v 0 * w 0) = _
  ring

theorem sum_coord_squares_pos (v : FourSpace) (hv : v ≠ 0) :
    0 < ∑ i : Fin 4, v i * v i := by
  have hi : ∃ i : Fin 4, v i ≠ 0 := by
    by_contra h
    apply hv
    ext i
    simpa using not_exists.mp h i
  obtain ⟨i, hi⟩ := hi
  exact Finset.sum_pos' (fun j _ => mul_self_nonneg (v j))
    ⟨i, Finset.mem_univ i, mul_self_pos.mpr hi⟩

theorem flatMetric_isMetric : IsMetric flatMetric := by
  constructor
  · intro p v w
    rw [flatMetric_apply, flatMetric_apply]
    simp only [mul_comm]
  · intro p v hv
    rw [flatMetric_apply]
    exact sum_coord_squares_pos v hv

theorem oscillatingScalar_abs_le (alpha : ℝ) (n : ℕ) (p : Torus) :
    |oscillatingScalar alpha n p| ≤ amplitude alpha n := by
  have ha : 0 ≤ amplitude alpha n := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have him : |((p 0 ^ n : Circle) : ℂ).im| ≤ 1 := by
    simpa only [Circle.norm_coe] using Complex.abs_im_le_norm ((p 0 ^ n : Circle) : ℂ)
  rw [oscillatingScalar, abs_mul, abs_of_nonneg ha]
  exact (mul_le_mul_of_nonneg_left him ha).trans_eq (mul_one _)

theorem oscillatingScalar_abs_lt_one (alpha : HolderExponent) (n : ℕ)
    (hn : 2 ≤ n) (p : Torus) : |oscillatingScalar alpha.value n p| < 1 := by
  apply (oscillatingScalar_abs_le alpha.value n p).trans_lt
  apply Real.rpow_lt_one_of_one_lt_of_neg
  · exact_mod_cast (show 1 < n by omega)
  · have := alpha.value.coe_nonneg
    linarith

theorem nearbyMetric_isMetric (alpha : HolderExponent) (n : ℕ) (hn : 2 ≤ n) :
    IsMetric (nearbyMetric alpha.value n) := by
  constructor
  · intro p v w
    change flatMetric p v w + perturbation alpha.value n p v w =
      flatMetric p w v + perturbation alpha.value n p w v
    rw [flatMetric_isMetric.1 p v w, perturbation_apply, perturbation_apply]
    ring
  · intro p v hv
    change FourSpace at v
    change flatMetric p v v + perturbation alpha.value n p v v > 0
    rw [flatMetric_apply, perturbation_apply]
    have hs := sum_coord_squares_pos v hv
    have hdiag : v 0 * v 0 ≤ ∑ i : Fin 4, v i * v i :=
      Finset.single_le_sum (fun j _ => mul_self_nonneg (v j)) (Finset.mem_univ 0)
    have ha : 0 < 1 + oscillatingScalar alpha.value n p := by
      have h := (abs_lt.mp (oscillatingScalar_abs_lt_one alpha n hn p)).1
      linarith
    by_cases hzero : v 0 = 0
    · simpa [hzero] using hs
    · have hp := mul_pos ha (mul_self_pos.mpr hzero)
      nlinarith

/-- The geometric positivity fields of the original sharpness statement. -/
theorem metric_positivity_proof :
    IsMetric flatMetric ∧ ∀ (alpha : HolderExponent) (n : ℕ),
      2 ≤ n → IsMetric (nearbyMetric alpha.value n) :=
  ⟨flatMetric_isMetric, nearbyMetric_isMetric⟩

/-- Submission entry point; its type repeats the literal registered child type. -/
theorem _root_.solution :
    IsMetric flatMetric ∧ ∀ (alpha : HolderExponent) (n : ℕ),
      2 ≤ n → IsMetric (nearbyMetric alpha.value n) :=
  metric_positivity_proof

end K24.Global.FlatTorus
