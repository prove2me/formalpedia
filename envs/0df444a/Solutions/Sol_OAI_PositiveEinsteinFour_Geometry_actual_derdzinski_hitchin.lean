-- Prove2me | solution 1 for OAI.PositiveEinsteinFour.Geometry.actual_derdzinski_hitchin
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T21:05:14.617461+00:00
-- url     : https://prove2.me/submissions/18fffa73-8f0a-4726-8df4-7fa674d32575

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_EinsteinFour
import Definitions.Def_OAIQ091C034
import Theorems.Thm_OAI_PositiveEinsteinFour_Geometry_actual_frameExponential_injOn_sqrt_three

section
-- module Solutions.OAIQ091_EF.EinsteinFour_FlatDirichletGreen
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.ScalarPartition.instFintypeι _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The explicit positive Green kernel for the flat discrete Dirichlet operator. -/
namespace PositiveEinsteinFour.Jacobi
open Matrix
noncomputable section

private theorem tent_second_difference (i j : ℕ) :
    2 * (min (i + 1) j : ℕ) - (min i j : ℕ) - (min (i + 2) j : ℕ) =
      (if i + 1 = j then (1 : ℝ) else 0) := by
  by_cases h : j ≤ i
  · have h1 : j ≤ i + 1 := by omega
    have h2 : j ≤ i + 2 := by omega
    have hn : i + 1 ≠ j := by omega
    simp only [min_eq_right h, min_eq_right h1, min_eq_right h2, ite_eq_right hn]
    ring
  · by_cases he : i + 1 = j
    · subst j
      simp only [min_eq_left (by omega : i ≤ i + 1), min_self,
        min_eq_right (by omega : i + 1 ≤ i + 2), ite_true, if_true, Nat.cast_add, Nat.cast_one]
      ring
    · have h2 : i + 2 ≤ j := by omega
      simp only [min_eq_left (by omega : i ≤ j), min_eq_left (by omega : i + 1 ≤ j),
        min_eq_left h2, ite_eq_right he, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
      ring

theorem flatGreenValue_second_difference (N i j : ℕ) :
    2 * flatGreenValue N j (i + 1) - flatGreenValue N j i -
      flatGreenValue N j (i + 2) = if i + 1 = j then 1 else 0 := by
  have h := tent_second_difference i j
  simp only [flatGreenValue, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  linear_combination h

theorem scalarDirichlet_mul_flatGreen (N : ℕ) : scalarDirichlet N 2 * flatGreen N = 1 := by
  ext i j
  have h0 : flatGreenValue N (j.val + 1) 0 = 0 := by simp [flatGreenValue]
  have hN : flatGreenValue N (j.val + 1) (N + 1) = 0 := by
    have hj : j.val + 1 ≤ N + 1 := by omega
    simp only [flatGreenValue, min_eq_right hj, Nat.cast_add, Nat.cast_one]
    field_simp
    ring
  have h := scalarDirichlet_apply_sequence 2 (flatGreenValue N (j.val + 1)) h0 hN i
  change (scalarDirichlet N 2 *ᵥ fun k => flatGreenValue N (j.val + 1) (k.val + 1)) i = _
  rw [h, flatGreenValue_second_difference]
  by_cases hij : i = j
  · subst j
    simp
  · have hv : i.val ≠ j.val := fun he => hij (Fin.ext he)
    simp [hv, hij]

theorem flatGreen_nonneg (N : ℕ) (i j : Fin N) : 0 ≤ flatGreen N i j := by
  have hd : (0 : ℝ) < N + 1 := by positivity
  have hi : (i.val : ℝ) + 1 ≤ N + 1 := by exact_mod_cast Nat.succ_le_succ (Nat.le_of_lt i.isLt)
  have hj : (j.val : ℝ) + 1 ≤ N + 1 := by exact_mod_cast Nat.succ_le_succ (Nat.le_of_lt j.isLt)
  change 0 ≤ flatGreenValue N (j.val + 1) (i.val + 1)
  unfold flatGreenValue
  by_cases hij : i.val ≤ j.val
  · rw [min_eq_left (by omega : i.val + 1 ≤ j.val + 1)]
    push_cast
    apply sub_nonneg.mpr
    apply (div_le_iff₀ hd).mpr
    nlinarith
  · rw [min_eq_right (by omega : j.val + 1 ≤ i.val + 1)]
    push_cast
    apply sub_nonneg.mpr
    apply (div_le_iff₀ hd).mpr
    nlinarith

end
end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_FlatDirichletGreenTrace
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.ScalarPartition.instFintypeι _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Trace and mesh limit of the flat Green matrix. -/
namespace PositiveEinsteinFour.Jacobi
open Matrix Filter
open scoped _root_.Topology
noncomputable section

private theorem sum_nodes (N : ℕ) :
    (∑ i ∈ Finset.range N, ((i : ℝ) + 1)) = (N : ℝ) * (N + 1) / 2 := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

private theorem sum_nodes_sq (N : ℕ) :
    (∑ i ∈ Finset.range N, ((i : ℝ) + 1) ^ 2) = (N : ℝ) * (N + 1) * (2 * N + 1) / 6 := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

theorem flatGreen_trace (N : ℕ) : (flatGreen N).trace = N * (N + 2) / 6 := by
  simp only [Matrix.trace, Matrix.diag_apply, flatGreen, flatGreenValue, min_self,
    Nat.cast_add, Nat.cast_one]
  change (∑ i : Fin N, (fun j : ℕ => ((j : ℝ) + 1) -
    ((j : ℝ) + 1) * ((j : ℝ) + 1) / (N + 1)) i.val) = _
  rw [← Finset.sum_range (fun j : ℕ => ((j : ℝ) + 1) -
    ((j : ℝ) + 1) * ((j : ℝ) + 1) / (N + 1))]
  simp only [Finset.sum_sub_distrib, ← pow_two, ← Finset.sum_div]
  rw [sum_nodes, sum_nodes_sq]
  field_simp
  ring

theorem scaledFlatGreen_trace (t : ℝ) (N : ℕ) :
    (scaledFlatGreen t N).trace = (t ^ 2 / 6) * (1 - (1 / ((N : ℝ) + 1)) ^ 2) := by
  rw [scaledFlatGreen, Matrix.trace_smul, smul_eq_mul, flatGreen_trace]
  field_simp
  ring

theorem scaledFlatGreen_trace_tendsto (t : ℝ) :
    Tendsto (fun N => (scaledFlatGreen t N).trace) atTop (𝓝 (t ^ 2 / 6)) := by
  simp_rw [scaledFlatGreen_trace]
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 2
  simpa only [zero_pow (by decide : 2 ≠ 0), sub_zero, mul_one] using
    ((tendsto_const_nhds (x := (1 : ℝ))).sub h).const_mul (t ^ 2 / 6)

theorem scaledFlatGreen_nonneg (t : ℝ) (N : ℕ) (i j : Fin N) :
    0 ≤ scaledFlatGreen t N i j :=
  mul_nonneg (sq_nonneg _) (flatGreen_nonneg N i j)

end
end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_FlatDirichletNormalizer
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.ScalarPartition.instFintypeι _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual square-root normalizer for the flat Green kernel. -/
namespace PositiveEinsteinFour.Jacobi
open Matrix
noncomputable section

theorem flatDirichlet_posDef (N : ℕ) : (scalarDirichlet N 2).PosDef := by
  apply scalarDirichlet_posDef
  rw [two_sub_two_cos]
  have hx : 0 < firstSineAngle N / 2 := by unfold firstSineAngle; positivity
  have hxπ : firstSineAngle N / 2 < Real.pi := by
    unfold firstSineAngle
    rw [div_div, div_lt_iff₀ (by positivity : (0 : ℝ) < (N + 1) * 2)]
    have hn : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    nlinarith [Real.pi_pos]
  exact mul_pos (by norm_num) (sq_pos_of_pos (Real.sin_pos_of_pos_of_lt_pi hx hxπ))

theorem flatGreen_eq_inverse (N : ℕ) : flatGreen N = (scalarDirichlet N 2)⁻¹ :=
  (Matrix.inv_eq_right_inv (scalarDirichlet_mul_flatGreen N)).symm

theorem flatGreen_posDef (N : ℕ) : (flatGreen N).PosDef := by
  rw [flatGreen_eq_inverse]
  exact (flatDirichlet_posDef N).inv

theorem scaledFlatGreen_posSemidef (t : ℝ) (N : ℕ) : (scaledFlatGreen t N).PosSemidef :=
  (flatGreen_posDef N).posSemidef.smul (sq_nonneg _)

theorem flatGreenRoot_square (t : ℝ) (N : ℕ) :
    flatGreenRoot t N * flatGreenRoot t N = scaledFlatGreen t N := by
  rw [flatGreenRoot, scaledFlatGreen, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, ← pow_two, scalarNormalizer_square (flatDirichlet_posDef N),
    ← flatGreen_eq_inverse]

theorem flatGreenRoot_transpose (t : ℝ) (N : ℕ) :
    (flatGreenRoot t N)ᵀ = flatGreenRoot t N := by
  have h := (scalarNormalizer_posSemidef (scalarDirichlet N 2)).isHermitian.eq
  simp only [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  simp only [flatGreenRoot, Matrix.transpose_smul, h]

end
end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_FlatDirichletThreshold
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.ScalarPartition.instFintypeι _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The flat perturbation is positive below pi/sqrt(3). -/
namespace PositiveEinsteinFour.Jacobi
open Matrix Filter
open scoped _root_.Topology
noncomputable section

theorem referenceMatrix_sqrt_three (t : ℝ) (N : ℕ) :
    referenceMatrix (Real.sqrt 3 * t) N = scalarDirichlet N 2 -
      (3 * (t / (N + 1)) ^ 2) • 1 := by
  have hs : (Real.sqrt 3 * t / (N + 1)) ^ 2 = 3 * (t / (N + 1)) ^ 2 := by
    rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num), div_pow]
    ring
  ext i j
  simp only [referenceMatrix, scalarDirichlet, Matrix.sub_apply, Matrix.smul_apply,
    smul_eq_mul, Matrix.one_apply, hs]
  by_cases hij : i = j <;> simp [hij]

theorem scaledFlatGreen_threshold_posDef (t : ℝ) (N : ℕ)
    (hRef : (referenceMatrix (Real.sqrt 3 * t) N).PosDef) :
    (1 - (3 : ℝ) • scaledFlatGreen t N).PosDef := by
  let U := scalarNormalizer (scalarDirichlet N 2)
  have hu : U * scalarDirichlet N 2 * U = 1 :=
    scalarNormalizer_normalizes (flatDirichlet_posDef N)
  have hs : U * U = flatGreen N := by
    rw [flatGreen_eq_inverse]
    exact scalarNormalizer_square (flatDirichlet_posDef N)
  have ht : Uᴴ = U := (scalarNormalizer_posSemidef _).isHermitian.eq
  have hunit : IsUnit U := (Matrix.isUnit_iff_isUnit_det _).mpr
    (Matrix.isUnit_det_of_left_inverse hu)
  have hp := hRef.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit hunit)
  rw [ht, referenceMatrix_sqrt_three] at hp
  have he : U * (scalarDirichlet N 2 - (3 * (t / (N + 1)) ^ 2) • 1) * U =
      1 - (3 : ℝ) • scaledFlatGreen t N := by
    rw [Matrix.mul_sub, Matrix.sub_mul, hu, Matrix.mul_smul, Matrix.mul_one,
      Matrix.smul_mul, hs, scaledFlatGreen, smul_smul]
  rwa [he] at hp

theorem scaledFlatGreen_eventually_below_one {t : ℝ} (ht : 0 ≤ t)
    (htop : t < Real.pi / Real.sqrt 3) :
    ∀ᶠ N : ℕ in atTop, (1 - (3 : ℝ) • scaledFlatGreen t N).PosDef := by
  have hsqrt : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hlt : Real.sqrt 3 * t < Real.pi := by
    have h := (lt_div_iff₀ hsqrt).mp htop
    nlinarith
  filter_upwards [firstEigenvalue_eventually_pos (mul_nonneg hsqrt.le ht) hlt] with N hN
  apply scaledFlatGreen_threshold_posDef t N
  exact scalarDirichlet_posDef N _ hN

end
end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_RiemannianVolume
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Angular.instCompactSpaceDirections _root_.OAI.PositiveEinsteinFour.Geometry.ScalarPartition.instFintypeι _root_.OAI.PositiveEinsteinFour.Geometry.canonicalFrameMeasure_probability _root_.OAI.PositiveEinsteinFour.Geometry.canonicalUnitTangentMeasure_probability _root_.OAI.PositiveEinsteinFour.Geometry.chartBaseDensity_sfinite _root_.OAI.PositiveEinsteinFour.Geometry.chartCoordinateMeasure_sigmaFinite _root_.OAI.PositiveEinsteinFour.Geometry.frameBundle_pseudoMetrizable _root_.OAI.PositiveEinsteinFour.Geometry.frameBundle_secondCountable _root_.OAI.PositiveEinsteinFour.Geometry.instAddCommGroupSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instAddSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instBorelSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instBorelSpaceUnitTangentBundle _root_.OAI.PositiveEinsteinFour.Geometry.instCoeOutSmoothL2OneFormSubtypeForallCovariantCoordinatesOfNatNatMemSubmoduleRealSmoothCovariantFields _root_.OAI.PositiveEinsteinFour.Geometry.instCoeSmoothH1TwoFormSubtypeForallTwoFormFourMemSubmoduleRealSmoothTwoForms _root_.OAI.PositiveEinsteinFour.Geometry.instCoeSmoothL2TwoFormSubtypeForallTwoFormFourMemSubmoduleRealSmoothTwoForms _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceUnitTangentBundle _root_.OAI.PositiveEinsteinFour.Geometry.instModuleRealSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instNegSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instNonemptyOrthonormalFrame _root_.OAI.PositiveEinsteinFour.Geometry.instSMulIntSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instSMulNatSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instSMulRealSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instSubSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instT2SpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instT2SpaceUnitTangentBundle _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceUnitTangentBundle _root_.OAI.PositiveEinsteinFour.Geometry.instZeroSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.oneFormC0_complete _root_.OAI.PositiveEinsteinFour.Geometry.oneFormCoexactSpectralFinite _root_.OAI.PositiveEinsteinFour.Geometry.oneFormEigenIndex_countable _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_chartedSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_compactSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_isManifold _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_nonempty _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_secondCountable _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_t2Space _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_t3Space _root_.OAI.PositiveEinsteinFour.Geometry.orientedFiberMeasure_probability _root_.OAI.PositiveEinsteinFour.Geometry.polarAngularProbability_probability _root_.OAI.PositiveEinsteinFour.Geometry.polarDirectionProbability_probability _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos _root_.OAI.PositiveEinsteinFour.Geometry.scalarBaseEigenIndex_countable _root_.OAI.PositiveEinsteinFour.Geometry.scalarBaseSpectralSpaceFinite _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1MeanZero_complete _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1_complete _root_.OAI.PositiveEinsteinFour.Geometry.scalarWeightedH1_complete _root_.OAI.PositiveEinsteinFour.Geometry.smoothH1TwoFormInnerCore _root_.OAI.PositiveEinsteinFour.Geometry.smoothH1TwoFormInnerProductSpace _root_.OAI.PositiveEinsteinFour.Geometry.smoothH1TwoFormNormedAddCommGroup _root_.OAI.PositiveEinsteinFour.Geometry.smoothHarmonicNegative_finite _root_.OAI.PositiveEinsteinFour.Geometry.smoothHarmonicPositive_finite _root_.OAI.PositiveEinsteinFour.Geometry.smoothOneFormInnerCore _root_.OAI.PositiveEinsteinFour.Geometry.smoothOneFormInnerProductSpace _root_.OAI.PositiveEinsteinFour.Geometry.smoothOneFormNormedAddCommGroup _root_.OAI.PositiveEinsteinFour.Geometry.smoothTwoFormInnerCore _root_.OAI.PositiveEinsteinFour.Geometry.smoothTwoFormInnerProductSpace _root_.OAI.PositiveEinsteinFour.Geometry.smoothTwoFormNormedAddCommGroup _root_.OAI.PositiveEinsteinFour.Geometry.symmetricFrameMeasure_finite _root_.OAI.PositiveEinsteinFour.Geometry.tangentBundle_secondCountable _root_.OAI.PositiveEinsteinFour.Geometry.twoFormEigenIndexCountable _root_.OAI.PositiveEinsteinFour.Geometry.twoFormSmoothEigenFinite _root_.OAI.PositiveEinsteinFour.Geometry.twoFormSpectralSpaceFinite _root_.OAI.PositiveEinsteinFour.Geometry.twoFormWeitzenbockKernel_finite _root_.OAI.PositiveEinsteinFour.Geometry.unitTangentBundle_secondCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The measure in the geometric application is fixed by the metric. In four
Euclidean dimensions the diameter-normalized Hausdorff measure is multiplied
by the unit-ball factor `(pi^2 / 2) / 2^4`. Positivity and finiteness are kept
separate from the elementary probability normalization. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Bundle
open scoped Manifold ContDiff ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]

theorem volumeRatio_pos {g : SmoothMetric M} (h : FinitePositiveVolume g) :
    0 < volumeRatio g := by
  exact div_pos (totalVolume_pos h) (by positivity)

end

end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_FrameOrientation
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Angular.instCompactSpaceDirections _root_.OAI.PositiveEinsteinFour.Geometry.ScalarPartition.instFintypeι _root_.OAI.PositiveEinsteinFour.Geometry.canonicalFrameMeasure_probability _root_.OAI.PositiveEinsteinFour.Geometry.canonicalUnitTangentMeasure_probability _root_.OAI.PositiveEinsteinFour.Geometry.chartBaseDensity_sfinite _root_.OAI.PositiveEinsteinFour.Geometry.chartCoordinateMeasure_sigmaFinite _root_.OAI.PositiveEinsteinFour.Geometry.frameBundle_pseudoMetrizable _root_.OAI.PositiveEinsteinFour.Geometry.frameBundle_secondCountable _root_.OAI.PositiveEinsteinFour.Geometry.instAddCommGroupSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instAddSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instBorelSpaceUnitTangentBundle _root_.OAI.PositiveEinsteinFour.Geometry.instCoeOutSmoothL2OneFormSubtypeForallCovariantCoordinatesOfNatNatMemSubmoduleRealSmoothCovariantFields _root_.OAI.PositiveEinsteinFour.Geometry.instCoeSmoothH1TwoFormSubtypeForallTwoFormFourMemSubmoduleRealSmoothTwoForms _root_.OAI.PositiveEinsteinFour.Geometry.instCoeSmoothL2TwoFormSubtypeForallTwoFormFourMemSubmoduleRealSmoothTwoForms _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceUnitTangentBundle _root_.OAI.PositiveEinsteinFour.Geometry.instModuleRealSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instNegSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instSMulIntSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instSMulNatSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instSMulRealSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instSubSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instT2SpaceUnitTangentBundle _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceUnitTangentBundle _root_.OAI.PositiveEinsteinFour.Geometry.instZeroSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.oneFormC0_complete _root_.OAI.PositiveEinsteinFour.Geometry.oneFormCoexactSpectralFinite _root_.OAI.PositiveEinsteinFour.Geometry.oneFormEigenIndex_countable _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_chartedSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_compactSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_isManifold _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_nonempty _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_secondCountable _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_t2Space _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_t3Space _root_.OAI.PositiveEinsteinFour.Geometry.orientedFiberMeasure_probability _root_.OAI.PositiveEinsteinFour.Geometry.polarAngularProbability_probability _root_.OAI.PositiveEinsteinFour.Geometry.polarDirectionProbability_probability _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos _root_.OAI.PositiveEinsteinFour.Geometry.scalarBaseEigenIndex_countable _root_.OAI.PositiveEinsteinFour.Geometry.scalarBaseSpectralSpaceFinite _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1MeanZero_complete _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1_complete _root_.OAI.PositiveEinsteinFour.Geometry.scalarWeightedH1_complete _root_.OAI.PositiveEinsteinFour.Geometry.smoothH1TwoFormInnerCore _root_.OAI.PositiveEinsteinFour.Geometry.smoothH1TwoFormInnerProductSpace _root_.OAI.PositiveEinsteinFour.Geometry.smoothH1TwoFormNormedAddCommGroup _root_.OAI.PositiveEinsteinFour.Geometry.smoothHarmonicNegative_finite _root_.OAI.PositiveEinsteinFour.Geometry.smoothHarmonicPositive_finite _root_.OAI.PositiveEinsteinFour.Geometry.smoothOneFormInnerCore _root_.OAI.PositiveEinsteinFour.Geometry.smoothOneFormInnerProductSpace _root_.OAI.PositiveEinsteinFour.Geometry.smoothOneFormNormedAddCommGroup _root_.OAI.PositiveEinsteinFour.Geometry.smoothTwoFormInnerCore _root_.OAI.PositiveEinsteinFour.Geometry.smoothTwoFormInnerProductSpace _root_.OAI.PositiveEinsteinFour.Geometry.smoothTwoFormNormedAddCommGroup _root_.OAI.PositiveEinsteinFour.Geometry.symmetricFrameMeasure_finite _root_.OAI.PositiveEinsteinFour.Geometry.tangentBundle_secondCountable _root_.OAI.PositiveEinsteinFour.Geometry.twoFormEigenIndexCountable _root_.OAI.PositiveEinsteinFour.Geometry.twoFormSmoothEigenFinite _root_.OAI.PositiveEinsteinFour.Geometry.twoFormSpectralSpaceFinite _root_.OAI.PositiveEinsteinFour.Geometry.twoFormWeitzenbockKernel_finite _root_.OAI.PositiveEinsteinFour.Geometry.unitTangentBundle_secondCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An orientation is a continuous choice of one of the two orientation
classes in every orthonormal frame fiber. This separates the individual
Weyl norms used by the scalar argument from the orientation-independent sum
used in radial averaging. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem minusNorm_nonneg {g : SmoothMetric M} (o : FrameOrientation g) (c : M) :
    0 ≤ minusNorm o c := normalizedBlockNorm_nonneg _

end

end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_VolumeConstants
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact rational integrations for the two volume margins. -/

namespace PositiveEinsteinFour.VolumeConstants

open MeasureTheory intervalIntegral

noncomputable section

private theorem expansion3 (u : ℝ) :
    lowerIntegrand u = polynomial coefficients3 u := by
  norm_num [upperIntegrand, upperIntegrandMiddle, upperIntegrandEnd,
    lowerIntegrand, lowerIntegrandEnd, sineLower, initialFactor,
    polynomial, coefficients3, Finset.sum_range_succ]
  ring

/-- Row 4 of the manuscript's rational integration table. -/
theorem row4_lower : (698 / 1000000 : ℝ) <
    ∫ u in 0..(1 / 2), lowerIntegrand u := by
  simp_rw [expansion3]
  rw [integral_polynomial]
  norm_num [coefficients3, Finset.sum_range_succ]

private theorem expansion4 (u : ℝ) :
    lowerIntegrandEnd u = polynomial coefficients4 u := by
  norm_num [upperIntegrand, upperIntegrandMiddle, upperIntegrandEnd,
    lowerIntegrand, lowerIntegrandEnd, sineLower, initialFactor,
    polynomial, coefficients4, Finset.sum_range_succ]
  ring

/-- Row 5 of the manuscript's rational integration table. -/
theorem row5_lower : (40554 / 1000000 : ℝ) <
    ∫ u in (1 / 2)..1, lowerIntegrandEnd u := by
  simp_rw [expansion4]
  rw [integral_polynomial]
  norm_num [coefficients4, Finset.sum_range_succ]

theorem lower_margin : (4 / 3 : ℝ) <
    2 * ((157 / 50) ^ 2 - 4) / 9 +
    (∫ u in (0 : ℝ)..(1 / 2), lowerIntegrand u) +
    (∫ u in (1 / 2 : ℝ)..1, lowerIntegrandEnd u) := by
  linarith [row4_lower, row5_lower]

end

end PositiveEinsteinFour.VolumeConstants

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_RadialIntegrals
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two analytic integral margins in the volume comparison. All numerical
bounds here follow from exact polynomial integrals and the proved sine bound;
no numerical integration or decimal error premise is used. -/

namespace PositiveEinsteinFour.VolumeConstants

open MeasureTheory

noncomputable section

private theorem lower_comparison {u z : ℝ} (_hu : 0 ≤ u)
    (hz0 : 0 ≤ sineLower z) (hz : sineLower z ≤ Real.sin (Real.pi * u)) :
    ((157 / 50) ^ 3 / 27) * u ^ 2 * (u ^ 4 / 2 + u ^ 6 / 3) * sineLower z ≤
      lowerKernel u := by
  have hpi : (157 / 50 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d2]
  unfold lowerKernel
  gcongr

private theorem lower_integral_first :
    (∫ u in (0 : ℝ)..(1 / 2), lowerIntegrand u) ≤
      ∫ u in (0 : ℝ)..(1 / 2), lowerKernel u := by
  apply intervalIntegral.integral_mono_on (by norm_num)
    (by apply Continuous.intervalIntegrable; unfold lowerIntegrand sineLower; fun_prop)
    (by apply Continuous.intervalIntegrable; unfold lowerKernel; fun_prop)
  intro u hu
  exact lower_comparison hu.1 (sineLower_nonneg hu.1 hu.2) (sineLower_le_sin hu.1)

private theorem lower_integral_end :
    (∫ u in (1 / 2 : ℝ)..1, lowerIntegrandEnd u) ≤
      ∫ u in (1 / 2 : ℝ)..1, lowerKernel u := by
  apply intervalIntegral.integral_mono_on (by norm_num)
    (by apply Continuous.intervalIntegrable; unfold lowerIntegrandEnd sineLower; fun_prop)
    (by apply Continuous.intervalIntegrable; unfold lowerKernel; fun_prop)
  intro u hu
  have hsin := sine_reflected_bound hu.1 hu.2
  exact lower_comparison (by linarith [hu.1]) hsin.1 hsin.2

/-- The lower radial integral exceeds `4/3`, with its strict margin supplied
by the exact rational certificates. -/
theorem analytic_lower_margin : (4 / 3 : ℝ) <
    2 * (Real.pi ^ 2 - 4) / 9 + ∫ u in (0 : ℝ)..1, lowerKernel u := by
  have hpi : (157 / 50 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d2]
  have hbase : 2 * ((157 / 50 : ℝ) ^ 2 - 4) / 9 ≤ 2 * (Real.pi ^ 2 - 4) / 9 := by
    nlinarith [Real.pi_pos]
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (f := lowerKernel) (μ := volume) (a := (0 : ℝ)) (b := (1 / 2 : ℝ)) (c := (1 : ℝ))
    (by apply Continuous.intervalIntegrable; unfold lowerKernel; fun_prop) (by apply Continuous.intervalIntegrable; unfold lowerKernel; fun_prop)
  linarith [lower_margin, lower_integral_first, lower_integral_end]

end

end PositiveEinsteinFour.VolumeConstants

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_WeylEstimates03
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.ScalarPartition.instFintypeι _root_.OAI.PositiveEinsteinFour.Geometry.chartBaseDensity_sfinite _root_.OAI.PositiveEinsteinFour.Geometry.instAddCommGroupSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instAddSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instCoeOutSmoothL2OneFormSubtypeForallCovariantCoordinatesOfNatNatMemSubmoduleRealSmoothCovariantFields _root_.OAI.PositiveEinsteinFour.Geometry.instModuleRealSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instNegSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instSMulIntSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instSMulNatSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instSMulRealSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instSubSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instZeroSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.oneFormC0_complete _root_.OAI.PositiveEinsteinFour.Geometry.oneFormCoexactSpectralFinite _root_.OAI.PositiveEinsteinFour.Geometry.oneFormEigenIndex_countable _root_.OAI.PositiveEinsteinFour.Geometry.scalarBaseEigenIndex_countable _root_.OAI.PositiveEinsteinFour.Geometry.scalarBaseSpectralSpaceFinite _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1MeanZero_complete _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1_complete _root_.OAI.PositiveEinsteinFour.Geometry.scalarWeightedH1_complete _root_.OAI.PositiveEinsteinFour.Geometry.smoothHarmonicNegative_finite _root_.OAI.PositiveEinsteinFour.Geometry.smoothHarmonicPositive_finite _root_.OAI.PositiveEinsteinFour.Geometry.smoothOneFormInnerCore _root_.OAI.PositiveEinsteinFour.Geometry.smoothOneFormInnerProductSpace _root_.OAI.PositiveEinsteinFour.Geometry.smoothOneFormNormedAddCommGroup _root_.OAI.PositiveEinsteinFour.Geometry.twoFormEigenIndexCountable _root_.OAI.PositiveEinsteinFour.Geometry.twoFormSmoothEigenFinite _root_.OAI.PositiveEinsteinFour.Geometry.twoFormSpectralSpaceFinite _root_.OAI.PositiveEinsteinFour.Geometry.twoFormWeitzenbockKernel_finite
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.mem_scalarH1MeanZero _root_.OAI.PositiveEinsteinFour.Geometry.roundPolarPoint_tail _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_first _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_tail _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1Gradient_one _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1Gradient_smooth _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1Gradient_subtractMean _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1Mean_one _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1Mean_subtractMean _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1SubtractMean_idempotent _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1Value_one _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1Value_smooth _root_.OAI.PositiveEinsteinFour.Geometry.scalarWeightedH1ToH1_equiv _root_.OAI.PositiveEinsteinFour.Geometry.scalarWeightedH1ToH1_smooth _root_.OAI.PositiveEinsteinFour.Geometry.scalarWeightedJetEquiv_none _root_.OAI.PositiveEinsteinFour.Geometry.scalarWeightedJetEquiv_some _root_.OAI.PositiveEinsteinFour.Geometry.smoothScalarGradientL2_subtractMean _root_.OAI.PositiveEinsteinFour.Geometry.smoothScalarGradient_subtractMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The reconstruction direction of polar volume. It turns the spherical
probability and cubic radial density into actual Euclidean fiber volume,
including the null origin. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal

noncomputable section

theorem euclideanPolarReconstruction_norm (p : Directions × Ioi (0 : ℝ)) :
    ‖euclideanPolarReconstruction p‖ = p.2.val := by
  rw [euclideanPolarReconstruction, norm_smul, Real.norm_eq_abs,
    abs_of_pos p.2.property, p.1.property, mul_one]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The Weyl norm gap follows from the regularized energy estimate and
the sharp scalar Sobolev inequality. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory Set Filter
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

section Probability

variable {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
  [CompactSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

theorem continuous_integral_cauchy_schwarz (v F : C(Ω, ℝ)) (hv : ∀ x, 0 ≤ v x) :
    (∫ x, v x * F x ^ 2 ∂μ) ≤
      Real.sqrt (∫ x, v x ^ 2 ∂μ) * Real.sqrt (∫ x, F x ^ 4 ∂μ) := by
  have hm₁ : MemLp (fun x => v x) (ENNReal.ofReal (2 : ℝ)) μ :=
    v.continuous.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hm₂ : MemLp (fun x => F x ^ 2) (ENNReal.ofReal (2 : ℝ)) μ :=
    (F.continuous.pow 2).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall hv)
    (Filter.Eventually.of_forall (fun x => sq_nonneg (F x))) hm₁ hm₂
  simpa only [Real.rpow_two, ← Real.sqrt_eq_rpow, ← pow_mul,
    show (2 : ℕ) * 2 = 4 by norm_num] using h

/-- A uniform positive fourth moment and arbitrarily small regularization
errors turn the sharp scalar inequality into a norm gap. -/
theorem norm_gap_of_regularized_sobolev (v : C(Ω, ℝ)) (F : ℝ → C(Ω, ℝ))
    (E : ℝ → ℝ) (hv : ∀ x, 0 ≤ v x) (c : ℝ) (hc : 0 < c)
    (hminorant : ∀ ε > 0, c ≤ ∫ x, F ε x ^ 4 ∂μ)
    (hsob : ∀ ε > 0, Real.sqrt (∫ x, F ε x ^ 4 ∂μ) ≤
      (∫ x, F ε x ^ 2 ∂μ) + E ε / 2)
    (henergy : ∀ ε > 0, E ε + 2 * (∫ x, F ε x ^ 2 ∂μ) ≤
      2 * (∫ x, v x * F ε x ^ 2 ∂μ) + 2 * ε ^ (2 / 3 : ℝ)) :
    1 ≤ ∫ x, v x ^ 2 ∂μ := by
  by_contra hgap
  have hB : Real.sqrt (∫ x, v x ^ 2 ∂μ) < 1 := by
    simpa only [Real.sqrt_one] using Real.sqrt_lt_sqrt
      (integral_nonneg (fun x => sq_nonneg (v x))) (lt_of_not_ge hgap)
  have hfixed : 0 < (1 - Real.sqrt (∫ x, v x ^ 2 ∂μ)) * Real.sqrt c :=
    mul_pos (sub_pos.mpr hB) (Real.sqrt_pos.mpr hc)
  have hbound (ε : ℝ) (hε : 0 < ε) :
      (1 - Real.sqrt (∫ x, v x ^ 2 ∂μ)) * Real.sqrt c ≤ ε ^ (2 / 3 : ℝ) := by
    have hs := hsob ε hε
    have he := henergy ε hε
    have hcs := continuous_integral_cauchy_schwarz μ v (F ε) hv
    have hlo := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hminorant ε hε))
      (sub_pos.mpr hB).le
    nlinarith only [hs, he, hcs, hlo]
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have ht : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have ht' : Tendsto (fun n => ε n ^ (2 / 3 : ℝ)) atTop (𝓝 0) := by
    simpa only [Real.zero_rpow (by norm_num : (2 / 3 : ℝ) ≠ 0)] using
      ht.rpow_const (Or.inr (by norm_num : (0 : ℝ) ≤ 2 / 3))
  have hn := ge_of_tendsto ht' (Filter.Eventually.of_forall (fun n => hbound (ε n) (hε n)))
  linarith

end Probability

theorem regularizedWeylRoot_fourth_lower (ε : ℝ) (A : Mat) :
    normalizedBlockNorm A ^ (4 / 3 : ℝ) ≤ regularizedWeylRoot ε A ^ 4 := by
  have h := Real.rpow_le_rpow (normalizedBlockNorm_nonneg A)
    (norm_le_regularizedBlockNorm ε A) (by norm_num : (0 : ℝ) ≤ 4 / 3)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  unfold regularizedWeylRoot
  have hu : 0 ≤ regularizedBlockNorm ε A := Real.sqrt_nonneg _
  rw [← Real.rpow_mul_natCast hu]
  norm_num

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]

local instance weylGapFrameCompact (g : SmoothMetric M) : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g

theorem canonical_plusNorm_moment (g : SmoothMetric M) (o : FrameOrientation g)
    (p : ℝ) (hp : 0 ≤ p) :
    (∫ e : FrameBundle g, normalizedBlockNorm (plusWeyl g e.base e.frame) ^ p
      ∂canonicalFrameMeasure g o) = ∫ x, plusNorm o x ^ p ∂normalizedVolume g := by
  let : IsProbabilityMeasure (normalizedVolume g) :=
    normalizedVolume_isProbability (actual_finitePositiveVolume g)
  have hcont := (continuous_plusNorm g o).rpow_const (fun _ => Or.inr hp)
  calc
    _ = ∫ e : FrameBundle g, plusNorm o e.base ^ p ∂canonicalFrameMeasure g o := by
      apply integral_congr_ae
      filter_upwards [canonicalFrameMeasure_supported g o] with e he
      rw [actual_plusNorm_frame o e he]
    _ = _ := canonicalFrameMeasure_integral_base g o _
      (hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))

/-- The sharp Sobolev premise is exposed explicitly. All other ingredients
are the actual Weyl equation, canonical measure, and regularized energy. -/
theorem plus_gap_of_regularized_sharp_sobolev (g : SmoothMetric M) (o : FrameOrientation g)
    (d : MetricGreenData g (canonicalFrameMeasure g o))
    (hsob : ∀ (ε : ℝ) (hε : 0 < ε),
      Real.sqrt (∫ e, d.weylRootField ε e ^ 4 ∂canonicalFrameMeasure g o) ≤
        (∫ e, d.weylRootField ε e ^ 2 ∂canonicalFrameMeasure g o) +
          (∫ e, ∑ i, d.weylRootFirstField ε hε i e ^ 2
            ∂canonicalFrameMeasure g o) / 2)
    (hnonzero : ∃ x, plusNorm o x ≠ 0) :
    1 ≤ ∫ x, plusNorm o x ^ 2 ∂normalizedVolume g := by
  let : IsProbabilityMeasure (normalizedVolume g) :=
    normalizedVolume_isProbability (actual_finitePositiveVolume g)
  let μ := canonicalFrameMeasure g o
  let v : C(FrameBundle g, ℝ) := d.plusNormField
  let F : ℝ → C(FrameBundle g, ℝ) := d.weylRootField
  let E : ℝ → ℝ := fun ε => if hε : 0 < ε then
    ∫ e, ∑ i, d.weylRootFirstField ε hε i e ^ 2 ∂μ else 0
  let c := ∫ x, plusNorm o x ^ (4 / 3 : ℝ) ∂normalizedVolume g
  have hc : 0 < c := by
    let := normalizedVolume_isOpenPosMeasure g
    obtain ⟨x, hx⟩ := hnonzero
    have hcont := (continuous_plusNorm g o).rpow_const
      (fun _ => Or.inr (by norm_num : (0 : ℝ) ≤ 4 / 3))
    apply integral_pos_of_integrable_nonneg_nonzero hcont
      (hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      (fun x => Real.rpow_nonneg (plusNorm_nonneg o x) _)
    exact (Real.rpow_pos_of_pos (lt_of_le_of_ne (plusNorm_nonneg o x) (Ne.symm hx)) _).ne'
  have hm (ε : ℝ) (_hε : 0 < ε) : c ≤ ∫ e, F ε e ^ 4 ∂μ := by
    dsimp only [c]
    rw [← canonical_plusNorm_moment g o (4 / 3 : ℝ) (by norm_num)]
    apply integral_mono
      (((d.plusNormField.continuous).rpow_const
        (fun _ => Or.inr (by norm_num : (0 : ℝ) ≤ 4 / 3))).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _))
      (((F ε).continuous.pow 4).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))
    intro e
    exact regularizedWeylRoot_fourth_lower ε (plusWeyl g e.base e.frame)
  have hs (ε : ℝ) (hε : 0 < ε) : Real.sqrt (∫ e, F ε e ^ 4 ∂μ) ≤
      (∫ e, F ε e ^ 2 ∂μ) + E ε / 2 := by
    simpa only [E, dite_eq_left hε] using hsob ε hε
  have he (ε : ℝ) (hε : 0 < ε) : E ε + 2 * (∫ e, F ε e ^ 2 ∂μ) ≤
      2 * (∫ e, v e * F ε e ^ 2 ∂μ) + 2 * ε ^ (2 / 3 : ℝ) := by
    have h := d.weylRoot_energy_le ε hε
    have hi₁ : Integrable (fun e => ∑ i, d.weylRootFirstField ε hε i e ^ 2) μ :=
      (continuous_finsetSum _ (fun i _ => (d.weylRootFirstField ε hε i).continuous.pow 2))
        |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hi₂ : Integrable (fun e => 2 * F ε e ^ 2) μ :=
      (((F ε).continuous.pow 2).const_mul 2).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    rw [integral_add hi₁ hi₂, integral_const_mul] at h
    simpa only [E, dite_eq_left hε, probReal_univ, mul_one, v,
      MetricGreenData.plusNormField, MetricGreenData.plusMatrixMap,
      ContinuousMap.coe_mk] using h
  have h := norm_gap_of_regularized_sobolev μ v F E
    (fun e => normalizedBlockNorm_nonneg _) c hc hm hs he
  have hmoment : (∫ e, v e ^ 2 ∂μ) =
      ∫ x, plusNorm o x ^ 2 ∂normalizedVolume g := by
    simpa only [Real.rpow_two, v, MetricGreenData.plusNormField,
      MetricGreenData.plusMatrixMap, ContinuousMap.coe_mk] using
      canonical_plusNorm_moment g o 2 (by norm_num)
  rwa [hmoment] at h

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GeodesicGeometry04
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.ScalarPartition.instFintypeι _root_.OAI.PositiveEinsteinFour.Geometry.oneFormC0_complete _root_.OAI.PositiveEinsteinFour.Geometry.oneFormCoexactSpectralFinite _root_.OAI.PositiveEinsteinFour.Geometry.oneFormEigenIndex_countable _root_.OAI.PositiveEinsteinFour.Geometry.scalarBaseEigenIndex_countable _root_.OAI.PositiveEinsteinFour.Geometry.scalarBaseSpectralSpaceFinite _root_.OAI.PositiveEinsteinFour.Geometry.smoothHarmonicNegative_finite _root_.OAI.PositiveEinsteinFour.Geometry.smoothHarmonicPositive_finite _root_.OAI.PositiveEinsteinFour.Geometry.twoFormEigenIndexCountable _root_.OAI.PositiveEinsteinFour.Geometry.twoFormSmoothEigenFinite _root_.OAI.PositiveEinsteinFour.Geometry.twoFormSpectralSpaceFinite _root_.OAI.PositiveEinsteinFour.Geometry.twoFormWeitzenbockKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The regularized Weyl cube root is an actual smooth base scalar.
Its moments and Dirichlet energy agree with the frame quantities in the
regularized gap argument. The sharp scalar inequality remains explicit. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M}

variable [T3Space M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.weylScalarFrameCompact
/-- Actual smooth scalar Sobolev suffices for the Weyl gap. No special
Sobolev premise on frame fields or their derivatives is needed. -/
theorem plus_gap_of_sharpScalarSobolev (o : FrameOrientation g) (hRic : RicciThree g)
    (hsharp : SharpScalarSobolev o (canonicalParallelMetricData g o hRic))
    (hnonzero : ∃ x, plusNorm o x ≠ 0) :
    1 ≤ ∫ x, plusNorm o x ^ 2 ∂normalizedVolume g := by
  apply plus_gap_of_regularized_sharp_sobolev g o
    (canonicalParallelMetricData g o hRic).toMetricGreenData
  · exact sharpScalarSobolev_regularized o (canonicalParallelMetricData g o hRic)
      (canonicalParallelMetricData_orientation o hRic) hsharp
  · exact hnonzero

end
end PositiveEinsteinFour.Geometry
end


section

/-! Reversing the actual frame orientation exchanges the two Weyl norms.
The plus-block Sobolev argument therefore proves both norm gaps, without
assuming reflection preservation of a fixed oriented frame measure. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M}

theorem plusNorm_reversed (o : FrameOrientation g) (x : M) :
    plusNorm o.reversed x = minusNorm o x := by
  let e := o.reversed.frame x
  have hp : (⟨x, e.reflect⟩ : FrameBundle g) ∈ o.positive := o.reversed.frame_positive x
  have he := actual_minusNorm_frame o (⟨x, e.reflect⟩ : FrameBundle g) hp
  change minusNorm o x = normalizedBlockNorm (minusWeyl g x e.reflect) at he
  rw [minusWeyl_reflect] at he
  exact he.symm

theorem minusNorm_reversed (o : FrameOrientation g) (x : M) :
    minusNorm o.reversed x = plusNorm o x := by
  let e := o.reversed.frame x
  have hp : (⟨x, e.reflect⟩ : FrameBundle g) ∈ o.positive := o.reversed.frame_positive x
  have he := actual_plusNorm_frame o (⟨x, e.reflect⟩ : FrameBundle g) hp
  change plusNorm o x = normalizedBlockNorm (plusWeyl g x e.reflect) at he
  rw [plusWeyl_reflect] at he
  exact he.symm

variable [T3Space M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]

local instance oppositeGap_frameCompact_ra5163b_1 : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g
/-- The same sharp scalar inequality, used with the opposite orientation,
gives the minus-block gap. -/
theorem minus_gap_of_sharpScalarSobolev (o : FrameOrientation g) (hRic : RicciThree g)
    (hsharp : SharpScalarSobolev o.reversed (canonicalParallelMetricData g o.reversed hRic))
    (hnonzero : ∃ x, minusNorm o x ≠ 0) :
    1 ≤ ∫ x, minusNorm o x ^ 2 ∂normalizedVolume g := by
  have hn : ∃ x, plusNorm o.reversed x ≠ 0 := by
    simpa only [plusNorm_reversed] using hnonzero
  simpa only [plusNorm_reversed] using
    plus_gap_of_sharpScalarSobolev o.reversed hRic hsharp hn

/-- Both scalar Sobolev instances suffice for the original geometric gap
input. The sharp scalar premise remains explicit. -/
theorem gurskyLeBrunGap_of_sharpScalarSobolev (o : FrameOrientation g) (hRic : RicciThree g)
    (hplus : SharpScalarSobolev o (canonicalParallelMetricData g o hRic))
    (hminus : SharpScalarSobolev o.reversed (canonicalParallelMetricData g o.reversed hRic)) :
    GurskyLeBrunGapInput g o :=
  ⟨plus_gap_of_sharpScalarSobolev o hRic hplus,
    minus_gap_of_sharpScalarSobolev o hRic hminus⟩

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GeodesicGeometry05
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.ScalarPartition.instFintypeι _root_.OAI.PositiveEinsteinFour.Geometry.oneFormC0_complete _root_.OAI.PositiveEinsteinFour.Geometry.oneFormCoexactSpectralFinite _root_.OAI.PositiveEinsteinFour.Geometry.oneFormEigenIndex_countable _root_.OAI.PositiveEinsteinFour.Geometry.scalarBaseEigenIndex_countable _root_.OAI.PositiveEinsteinFour.Geometry.scalarBaseSpectralSpaceFinite _root_.OAI.PositiveEinsteinFour.Geometry.smoothHarmonicNegative_finite _root_.OAI.PositiveEinsteinFour.Geometry.smoothHarmonicPositive_finite _root_.OAI.PositiveEinsteinFour.Geometry.twoFormEigenIndexCountable _root_.OAI.PositiveEinsteinFour.Geometry.twoFormSmoothEigenFinite _root_.OAI.PositiveEinsteinFour.Geometry.twoFormSpectralSpaceFinite _root_.OAI.PositiveEinsteinFour.Geometry.twoFormWeitzenbockKernel_finite
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.roundPolarPoint_tail _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_first _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! A single convex linear chart carries both sharp metric comparison bounds. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Filter
open scoped Manifold ContDiff _root_.Topology ENNReal NNReal
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [PreconnectedSpace M]

theorem exists_sharp_linear_chart_neighborhood (g : SmoothMetric M) (c : M)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ A : FourSpace ≃L[ℝ] FourSpace, ∃ V : Set FourSpace,
      IsOpen V ∧ Convex ℝ V ∧ A.symm (chartAt FourSpace c c) ∈ V ∧
      (∀ x ∈ V, A x ∈ (chartAt FourSpace c).target) ∧
      (∀ x ∈ V, ∀ y ∈ V,
        metricDistance g ((chartAt FourSpace c).symm (A x)) ((chartAt FourSpace c).symm (A y)) ≤
          Real.sqrt (1+δ)*dist x y) ∧
      (∀ x ∈ V, ∀ y ∈ V,
        dist x y ≤ (1 / Real.sqrt (1-δ))*
          metricDistance g ((chartAt FourSpace c).symm (A x)) ((chartAt FourSpace c).symm (A y))) := by
  let Z := chartAt FourSpace c
  let z₀ : ChartTarget c := ⟨Z c,Z.map_source (mem_chart_source FourSpace c)⟩
  let A := frozenFrameLinearEquiv g c z₀
  let x₀ := A.symm (Z c)
  let T : FourSpace → M := fun x => Z.symm (A x)
  have hAc : A x₀ = Z c := A.apply_symm_apply _
  have hTc : T x₀ = c := by rw [show T x₀ = Z.symm (A x₀) from rfl,hAc,Z.left_inv (mem_chart_source FourSpace c)]
  obtain ⟨r,hr,htarget,hforward⟩ := exists_frozenFrame_symm_lipschitz g c z₀ δ hδ hδ1.le
  obtain ⟨s,hs,_,hreverse⟩ := exists_frozenFrame_chart_lipschitz_at g c z₀ δ hδ hδ1
  have hsc : s ∈ 𝓝 c := by
    change s ∈ 𝓝 (Z.symm (Z c)) at hs
    simpa only [Z.left_inv (mem_chart_source FourSpace c)] using hs
  have hT : ContinuousAt T x₀ :=
    (Z.symm.continuousAt (by rw [hAc]; exact z₀.property)).comp A.continuous.continuousAt
  have hn : (A ⁻¹' Metric.ball z₀.val r) ∩ T ⁻¹' s ∈ 𝓝 x₀ := by
    apply inter_mem
    · exact A.continuous.continuousAt (by rw [hAc]; exact Metric.ball_mem_nhds _ hr)
    · exact hT (by rwa [hTc])
  obtain ⟨ρ,hρ,hsmall⟩ := Metric.mem_nhds_iff.mp hn
  let V := Metric.ball x₀ ρ
  have hball (x : FourSpace) (hx : x ∈ V) : A x ∈ Metric.closedBall z₀.val r :=
    Metric.ball_subset_closedBall (hsmall hx).1
  have hVT (x : FourSpace) (hx : x ∈ V) : A x ∈ Z.target := htarget (hball x hx)
  refine ⟨A,V,Metric.isOpen_ball,convex_ball _ _,Metric.mem_ball_self hρ,hVT,?_,?_⟩
  · intro x hx y hy
    have hh := hforward (A x) (hball x hx) (A y) (hball y hy)
    change metricEDistance g (T x) (T y) ≤ ENNReal.ofReal (Real.sqrt (1+δ)) *
      edist (A.symm (A x)) (A.symm (A y)) at hh
    simp only [A.symm_apply_apply] at hh
    rw [← ofReal_metricDistance g,edist_dist,← ENNReal.ofReal_mul (Real.sqrt_nonneg _)] at hh
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (Real.sqrt_nonneg _) dist_nonneg)).mp hh
  · intro x hx y hy
    have hh := hreverse (T x) (hsmall hx).2 (T y) (hsmall hy).2
    have hTx : Z (T x) = A x := Z.right_inv (hVT x hx)
    have hTy : Z (T y) = A y := Z.right_inv (hVT y hy)
    change edist (A.symm (Z (T x))) (A.symm (Z (T y))) ≤ _ at hh
    rw [hTx,hTy,A.symm_apply_apply,A.symm_apply_apply,edist_dist,
      ← ofReal_metricDistance g,← ENNReal.ofReal_mul (by positivity : 0 ≤ 1 / Real.sqrt (1-δ))] at hh
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (by positivity) (metricDistance_nonneg g _ _))).mp hh

end
end PositiveEinsteinFour.Geometry
end


section

/-! The reverse area inequality on an injective exponential ball. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped Manifold ContDiff _root_.Topology ENNReal
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [MeasurableSpace M] [BorelSpace M] [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem exponentialBallAreaMeasure_apply (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) (r : ℝ) (A : Set M) (hA : MeasurableSet A) :
    exponentialBallAreaMeasure g o e r A = riemannianChartFactor *
      ∫⁻ v in (frameExponential g o e) ⁻¹' A ∩ ball 0 r,
        ENNReal.ofReal (frameExponentialJacobian g o e v) := by
  rw [exponentialBallAreaMeasure, Measure.smul_apply, smul_eq_mul,
    Measure.map_apply (frameExponential_continuous g o e).measurable hA,
    withDensity_apply _ ((frameExponential_continuous g o e).measurable hA),
    Measure.restrict_restrict ((frameExponential_continuous g o e).measurable hA)]

theorem exponentialBallAreaMeasure_le_on_chart (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) (r : ℝ) (hinj : InjOn (frameExponential g o e) (ball 0 r))
    (c : M) (A : Set M) (hA : MeasurableSet A)
    (hAc : A ⊆ (chartAt FourSpace c).source) :
    exponentialBallAreaMeasure g o e r A ≤ volumeMeasure g A := by
  let s := (frameExponential g o e) ⁻¹' A ∩ ball 0 r
  let F := fun v => chartCoordinateExtension c (frameExponential g o e v)
  let D := fun v => fderiv ℝ (fun w => chartAt FourSpace c (frameExponential g o e w)) v
  have hs : MeasurableSet s := ((frameExponential_continuous g o e).measurable hA).inter
    isOpen_ball.measurableSet
  have hD : ∀ v ∈ s, HasFDerivWithinAt F (D v) s v := by
    intro v hv
    have hx := hAc hv.1
    have hd := (frameExponential_chart_contDiffAt g o c e v hx).differentiableAt (by first | simp | exact_mod_cast le_top)
    have hnear := (frameExponential_continuous g o e).continuousAt.preimage_mem_nhds
      ((chartAt FourSpace c).open_source.mem_nhds hx)
    have heq : F =ᶠ[𝓝 v] (fun w => chartAt FourSpace c (frameExponential g o e w)) := by
      filter_upwards [hnear] with w hw
      exact chartCoordinateExtension_eq c _ hw
    exact (hd.hasFDerivAt.congr_of_eventuallyEq heq).hasFDerivWithinAt
  have hF : InjOn F s := by
    intro v hv w hw heq
    apply hinj hv.2 hw.2
    apply (chartAt FourSpace c).injOn (hAc hv.1) (hAc hw.1)
    simpa only [F, chartCoordinateExtension_eq c _ (hAc hv.1),
      chartCoordinateExtension_eq c _ (hAc hw.1)] using heq
  have himage : F '' s ⊆ (chartAt FourSpace c) '' A := by
    rintro z ⟨v,hv,rfl⟩
    exact ⟨_,hv.1,(chartCoordinateExtension_eq c _ (hAc hv.1)).symm⟩
  have hb := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hs hD hF (chartWeight g c)
  have hle := lintegral_mono_set (μ := volume) (f := chartWeight g c) himage
  rw [hb] at hle
  have hleft : (∫⁻ z in (chartAt FourSpace c) '' A, chartWeight g c z) =
      ∫⁻ z in (chartAt FourSpace c) '' A, ENNReal.ofReal (chartVolumeDensity g c z) := by
    apply setLIntegral_congr_fun (chart_image_measurable c A hA hAc)
    rintro z ⟨x,hx,rfl⟩
    exact chartWeight_eq g c _ ((chartAt FourSpace c).map_source (hAc hx))
  have hright : (∫⁻ v in s, ENNReal.ofReal |(D v).det| * chartWeight g c (F v)) =
      ∫⁻ v in s, ENNReal.ofReal (frameExponentialJacobian g o e v) := by
    apply setLIntegral_congr_fun hs
    intro v hv
    have hx := hAc hv.1
    dsimp [F,D]
    rw [chartCoordinateExtension_eq c _ hx,
      chartWeight_eq g c _ ((chartAt FourSpace c).map_source hx),
      ← ENNReal.ofReal_mul (abs_nonneg _), mul_comm,
      ← frameExponentialJacobian_chart g o e c v hx]
  rw [hleft, hright] at hle
  rw [exponentialBallAreaMeasure_apply g o e r A hA, volumeMeasure_chart_image g c A hA hAc]
  exact mul_le_mul_right hle riemannianChartFactor

variable [SecondCountableTopology M]

theorem exponentialBallAreaMeasure_le (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) (r : ℝ) (hinj : InjOn (frameExponential g o e) (ball 0 r)) :
    exponentialBallAreaMeasure g o e r ≤ volumeMeasure g := by
  have h := measure_restrict_le_of_local (exponentialBallAreaMeasure g o e r)
    (volumeMeasure g) univ isOpen_univ (fun x _ => ?_)
  · simpa only [Measure.restrict_univ] using h
  refine ⟨(chartAt FourSpace x).source, (chartAt FourSpace x).open_source,
    mem_chart_source FourSpace x, subset_univ _, ?_⟩
  apply Measure.le_iff.mpr
  intro A hA
  rw [Measure.restrict_apply hA, Measure.restrict_apply hA]
  exact exponentialBallAreaMeasure_le_on_chart g o e r hinj x
    (A ∩ (chartAt FourSpace x).source) (hA.inter (chartAt FourSpace x).open_source.measurableSet)
    inter_subset_right

theorem exponential_ball_integral_le_volume (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) (r : ℝ) (hinj : InjOn (frameExponential g o e) (ball 0 r)) :
    riemannianChartFactor * (∫⁻ v in ball 0 r,
      ENNReal.ofReal (frameExponentialJacobian g o e v)) ≤ volumeMeasure g univ := by
  have h := exponentialBallAreaMeasure_le g o e r hinj univ
  rwa [exponentialBallAreaMeasure_apply g o e r univ MeasurableSet.univ,
    preimage_univ, univ_inter] at h

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GeodesicGeometry06
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.ScalarPartition.instFintypeι _root_.OAI.PositiveEinsteinFour.Geometry.oneFormC0_complete _root_.OAI.PositiveEinsteinFour.Geometry.oneFormCoexactSpectralFinite _root_.OAI.PositiveEinsteinFour.Geometry.oneFormEigenIndex_countable _root_.OAI.PositiveEinsteinFour.Geometry.scalarBaseEigenIndex_countable _root_.OAI.PositiveEinsteinFour.Geometry.scalarBaseSpectralSpaceFinite _root_.OAI.PositiveEinsteinFour.Geometry.smoothHarmonicNegative_finite _root_.OAI.PositiveEinsteinFour.Geometry.smoothHarmonicPositive_finite _root_.OAI.PositiveEinsteinFour.Geometry.twoFormEigenIndexCountable _root_.OAI.PositiveEinsteinFour.Geometry.twoFormSmoothEigenFinite _root_.OAI.PositiveEinsteinFour.Geometry.twoFormSpectralSpaceFinite _root_.OAI.PositiveEinsteinFour.Geometry.twoFormWeitzenbockKernel_finite
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.roundPolarPoint_first _root_.OAI.PositiveEinsteinFour.Geometry.roundPolarPoint_tail _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_first _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The exact radial determinant integral over an exponential ball. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular MeasureTheory Set Metric
open scoped Manifold ContDiff _root_.Topology ENNReal
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem exponential_ball_integral_radial (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) (e : FrameBundle g) (he : e ∈ o.positive) (R : ℝ) :
    (∫⁻ v in ball 0 R, ENNReal.ofReal (frameExponentialJacobian g o e v)) =
      polarAngularMass * ∫⁻ q : Directions, ∫⁻ r : Ioi (0 : ℝ),
        (if r.val < R then ENNReal.ofReal |((actualJacobiSolution g hRic
          (e.rotate (orientedToOrthogonal (directionOrientedMatrix q)))).J r.val).det|
          else 0) ∂((volume : Measure ℝ).comap Subtype.val) ∂sphereMeasure := by
  classical
  let J := fun v => ENNReal.ofReal (frameExponentialJacobian g o e v)
  let F : Directions × Ioi (0 : ℝ) → ℝ≥0∞ := fun p =>
    if p.2.val < R then ENNReal.ofReal |((actualJacobiSolution g hRic
      (e.rotate (orientedToOrthogonal (directionOrientedMatrix p.1)))).J p.2.val).det /
      p.2.val ^ 3| else 0
  have hJ : Measurable J := (ENNReal.continuous_ofReal.comp
    (frameExponentialJacobian_continuous g o e)).measurable
  have hid (p : Directions × Ioi (0 : ℝ)) :
      (ball 0 R).indicator J (euclideanPolarReconstruction p) = F p := by
    have hb : euclideanPolarReconstruction p ∈ ball (0 : FourSpace) R ↔ p.2.val < R := by
      rw [mem_ball, dist_zero_right, euclideanPolarReconstruction_norm]
    by_cases hp : p.2.val < R
    · rw [Set.indicator_of_mem (hb.mpr hp)]
      dsimp only [F,J]
      rw [ite_eq_left hp]
      exact congrArg ENNReal.ofReal (frameExponentialJacobian_direction g o hRic e he
        p.1 p.2.val p.2.property)
    · rw [Set.indicator_of_notMem (fun hh => hp (hb.mp hh))]
      exact (ite_eq_right hp).symm
  have hF : Measurable F := by
    have hh := (hJ.indicator (isOpen_ball.measurableSet : MeasurableSet (ball (0 : FourSpace) R))).comp
      euclideanPolarReconstruction_measurePreserving.measurable
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    funext p
    exact (hid p).symm
  calc
    _ = ∫⁻ v, (ball 0 R).indicator J v := (lintegral_indicator isOpen_ball.measurableSet J).symm
    _ = ∫⁻ p, (ball 0 R).indicator J (euclideanPolarReconstruction p)
        ∂((polarAngularMass • sphereMeasure).prod (Measure.volumeIoiPow 3)) :=
      (euclideanPolarReconstruction_measurePreserving.lintegral_comp
        (hJ.indicator isOpen_ball.measurableSet)).symm
    _ = ∫⁻ p, F p ∂((polarAngularMass • sphereMeasure).prod (Measure.volumeIoiPow 3)) :=
      lintegral_congr hid
    _ = _ := by
      rw [lintegral_prod _ hF.aemeasurable, lintegral_smul_measure]
      congr 1
      apply lintegral_congr
      intro q
      have hrmeas : Measurable (fun r : Ioi (0 : ℝ) => ENNReal.ofReal (r.val ^ 3)) := by fun_prop
      rw [Measure.volumeIoiPow,
        lintegral_withDensity_eq_lintegral_mul_non_measurable _ hrmeas
          (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
      apply lintegral_congr
      intro r
      dsimp [F]
      split_ifs with hc
      · have hr3 : 0 < r.val ^ 3 := pow_pos r.property 3
        rw [← ENNReal.ofReal_mul hr3.le]
        congr 1
        rw [abs_div, abs_of_pos hr3]
        field_simp [ne_of_gt (show 0 < r.val from r.property)]
      · exact mul_zero _

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HodgeTheory08
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.oneFormC0_complete _root_.OAI.PositiveEinsteinFour.Geometry.oneFormCoexactSpectralFinite _root_.OAI.PositiveEinsteinFour.Geometry.oneFormEigenIndex_countable _root_.OAI.PositiveEinsteinFour.Geometry.twoFormEigenIndexCountable _root_.OAI.PositiveEinsteinFour.Geometry.twoFormSmoothEigenFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The sharp scalar Sobolev inequality and the two Weyl gaps follow from
actual variational minima, their proved positive smooth regularity, Euler
rigidity and the critical exponent limit. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M] [PreconnectedSpace M]

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.sharpScalar_frameCompact
theorem actual_gurskyLeBrunGap (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) : GurskyLeBrunGapInput g o :=
  gurskyLeBrunGap_of_sharpScalarSobolev o hRic
    (actual_sharpScalarSobolev g o hRic (canonicalParallelMetricData g o hRic))
    (actual_sharpScalarSobolev g o.reversed hRic
      (canonicalParallelMetricData g o.reversed hRic))

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GeodesicGeometry11
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.roundPolarPoint_tail _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_first _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The nonround half-flat branch has an actual nonzero self-dual harmonic
two-form, by the proved signature formula and Weyl gap. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour MeasureTheory
open scoped Manifold ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

omit [SecondCountableTopology M] in
theorem halfFlat_positive_signature (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hplus : ∃ x, plusWeyl g x (o.frame x) ≠ 0) :
    0 < (deRhamSignature (o := o) hRic : ℝ) := by
  have hm : ∀ x, minusNorm o x = 0 :=
    fun x => (minusNorm_eq_zero_iff o x).mpr (hminus x)
  have hp : ∃ x, plusNorm o x ≠ 0 := by
    obtain ⟨x, hx⟩ := hplus
    exact ⟨x, fun h => hx ((plusNorm_eq_zero_iff o x).mp h)⟩
  have hgap := (actual_gurskyLeBrunGap g o hRic).1 hp
  have hsig := deRhamSignature_curvature_counts (o := o) hRic
  have hmI : (∫ x, minusNorm o x ^ 2 ∂normalizedVolume g) = 0 := by
    simp only [hm, zero_pow (by decide : 2 ≠ 0), integral_zero]
  rw [hmI, sub_zero] at hsig
  have hrhs : 0 < (4 / 3 : ℝ) * volumeRatio g *
      (∫ x, plusNorm o x ^ 2 ∂normalizedVolume g) :=
    mul_pos (mul_pos (by norm_num) (volumeRatio_pos (actual_finitePositiveVolume g)))
      (lt_of_lt_of_le zero_lt_one hgap)
  have hprod : 0 < riemannianChartFactor.toReal * (deRhamSignature (o := o) hRic : ℝ) :=
    hsig.symm ▸ hrhs
  exact (mul_pos_iff_of_pos_left riemannianChartFactor_toReal_pos).mp hprod

omit [SecondCountableTopology M] in
theorem halfFlat_positive_harmonic_dimension (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hplus : ∃ x, plusWeyl g x (o.frame x) ≠ 0) :
    0 < Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) := by
  have h := halfFlat_positive_signature hRic hminus hplus
  rw [deRhamSignature_hodge] at h
  push_cast at h
  have hn : (0 : ℝ) ≤ Module.finrank ℝ (smoothHarmonicNegative (o := o) hRic) :=
    Nat.cast_nonneg _
  have hp : (0 : ℝ) < Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) := by linarith
  exact_mod_cast hp

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual harmonic dimension determines the volume and Weyl energy
in the nonzero half-flat branch. Sectional pinching bounds that dimension. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour MeasureTheory
open scoped Manifold ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

omit [T3Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
  [Nonempty M] [SecondCountableTopology M] [PreconnectedSpace M] in
theorem actual_oriented_norm_pinching (hRic : RicciThree g)
    (hpositive : HasPositiveSectionalCurvature g) (x : M) :
    plusNorm o x + minusNorm o x < 2 := by
  obtain ⟨a,b,ha,hb,hab⟩ := actual_sectionalInput g hRic hpositive ⟨x,o.frame x⟩
  have hp := QuaternionFrame.normalizedBlockNorm_le_shift _
    (actual_weyl_symmetric (o.frame x)).1 (actual_weyl_traceFree (o.frame x) hRic).1 a ha
  have hm := QuaternionFrame.normalizedBlockNorm_le_shift _
    (actual_weyl_symmetric (o.frame x)).2 (actual_weyl_traceFree (o.frame x) hRic).2 b hb
  change normalizedBlockNorm _ + normalizedBlockNorm _ < 2
  linarith only [hp,hm,hab]

omit [SecondCountableTopology M] [PreconnectedSpace M] in
theorem actual_plus_energy_le_four (hRic : RicciThree g)
    (hpositive : HasPositiveSectionalCurvature g) :
    (∫ x, plusNorm o x ^ 2 ∂normalizedVolume g) ≤ 4 := by
  let : IsProbabilityMeasure (normalizedVolume g) :=
    normalizedVolume_isProbability (actual_finitePositiveVolume g)
  have hi := ((continuous_plusNorm g o).pow 2).integrable_of_hasCompactSupport
    (μ := normalizedVolume g) (HasCompactSupport.of_compactSpace _)
  calc
    _ ≤ ∫ _ : M, (4 : ℝ) ∂normalizedVolume g := integral_mono hi (integrable_const _) (by
      intro x
      change plusNorm o x ^ 2 ≤ 4
      have hp := actual_oriented_norm_pinching (o := o) hRic hpositive x
      have hn := plusNorm_nonneg o x
      have hm := minusNorm_nonneg o x
      nlinarith)
    _ = 4 := by simp

theorem halfFlat_positive_harmonic_dimension_le_two (hRic : RicciThree g)
    (hpositive : HasPositiveSectionalCurvature g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0) :
    Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) ≤ 2 := by
  obtain ⟨hv,he⟩ := halfFlat_volume_energy_counts hRic hminus
  have hV : 0 < volumeRatio g / riemannianChartFactor.toReal :=
    div_pos (volumeRatio_pos (actual_finitePositiveVolume g)) riemannianChartFactor_toReal_pos
  have hE := actual_plus_energy_le_four (o := o) hRic hpositive
  have hn : (Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) : ℝ) < 3 := by
    nlinarith
  exact Nat.le_of_lt_succ (by exact_mod_cast hn)

theorem halfFlat_positive_harmonic_dimension_cases (hRic : RicciThree g)
    (hpositive : HasPositiveSectionalCurvature g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hplus : ∃ x, plusWeyl g x (o.frame x) ≠ 0) :
    Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1 ∨
      Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 2 := by
  have hp := halfFlat_positive_harmonic_dimension hRic hminus hplus
  have hu := halfFlat_positive_harmonic_dimension_le_two hRic hpositive hminus
  omega

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_JacobiTraceProducts
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.ScalarPartition.instFintypeι _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p0 _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ordered curvature products in the lower radial determinant estimate.
No curvature matrices at different times are commuted. -/

namespace PositiveEinsteinFour.Jacobi
open Matrix
open scoped Matrix.Norms.Frobenius
noncomputable section

theorem abs_trace_mul_le_frobenius (A B : NormalMatrix) :
    |(A * B).trace| ≤ ‖A‖ * ‖B‖ := by
  have h := abs_real_inner_le_norm (matrixVector Aᵀ) (matrixVector B)
  have he : inner ℝ (matrixVector Aᵀ) (matrixVector B) = (A * B).trace := by
    change inner ℝ (WithLp.toLp 2 (fun ij : Fin 3 × Fin 3 => A ij.2 ij.1))
      (WithLp.toLp 2 (fun ij : Fin 3 × Fin 3 => B ij.1 ij.2)) = _
    simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, star_trivial,
      Fintype.sum_prod_type, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simpa only [he, matrixVector.norm_map, Matrix.frobenius_norm_transpose] using h

theorem frobenius_le_three_of_posSemidef_trace {A : NormalMatrix}
    (hA : A.PosSemidef) (htr : A.trace = 3) : ‖A‖ ≤ 3 := by
  have hs := Finset.sum_sq_le_sq_sum_of_nonneg
    (s := Finset.univ) (f := hA.isHermitian.eigenvalues)
    (fun i _ => hA.eigenvalues_nonneg i)
  have ht : (∑ i, hA.isHermitian.eigenvalues i) = 3 := by
    simpa only [RCLike.ofReal_real_eq_id, id_eq, htr] using
      hA.isHermitian.trace_eq_sum_eigenvalues.symm
  rw [ht, ← frobenius_sq_eq_sum_eigenvalues hA.isHermitian] at hs
  nlinarith [norm_nonneg A]

end
end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_JacobiKernelPowers
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.ScalarPartition.instFintypeι _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p0 _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive scalar path weights bound the noncommuting curvature kernel. -/
namespace PositiveEinsteinFour.Jacobi
open Matrix
open scoped Matrix.Norms.Frobenius
noncomputable section

theorem blockAt_curvatureKernel {N : ℕ} (G : Matrix (Fin N) (Fin N) ℝ)
    (R : Fin N → NormalMatrix) (i j : Fin N) :
    blockAt (curvatureKernel G R) i j = G i j • R j := by
  rw [curvatureKernel, blockAt_mul_diagonal, blockAt_scalarLift,
    smul_mul_assoc, Matrix.one_mul]

theorem blockAt_one {N : ℕ} (i j : Fin N) :
    blockAt (1 : Matrix (Fin 3 × Fin N) (Fin 3 × Fin N) ℝ) i j =
      if i = j then 1 else 0 := by
  rw [← scalarLift_one N, blockAt_scalarLift]
  by_cases h : i = j <;> simp [h, Matrix.one_apply]

theorem scalar_pow_entry_nonneg {N : ℕ} (G : Matrix (Fin N) (Fin N) ℝ)
    (hG : ∀ i j, 0 ≤ G i j) (k : ℕ) (i j : Fin N) : 0 ≤ (G ^ k) i j := by
  induction k generalizing i j with
  | zero => simp only [pow_zero, Matrix.one_apply]; split_ifs <;> norm_num
  | succ k ih =>
      rw [pow_succ', Matrix.mul_apply]
      exact Finset.sum_nonneg (fun l _ => mul_nonneg (hG i l) (ih l j))

/-- The initial matrix is kept outside the scalar path bound. In particular,
the zero-step bound does not lose the norm of the identity matrix. -/
theorem curvatureKernel_power_bound {N : ℕ} (G : Matrix (Fin N) (Fin N) ℝ)
    (hG : ∀ i j, 0 ≤ G i j) (R : Fin N → NormalMatrix)
    (hR : ∀ i, ‖R i‖ ≤ 3) (k : ℕ) (A : NormalMatrix) (i j : Fin N) :
    ‖A * blockAt (curvatureKernel G R ^ k) i j‖ ≤
      (3 ^ k * (G ^ k) i j) * ‖A‖ := by
  induction k generalizing A i j with
  | zero =>
      rw [pow_zero, blockAt_one, pow_zero]
      by_cases hij : i = j <;> simp [hij]
  | succ k ih =>
      rw [pow_succ', blockAt_mul, Matrix.mul_sum]
      calc
        _ ≤ ∑ l, ‖A * (blockAt (curvatureKernel G R) i l *
              blockAt (curvatureKernel G R ^ k) l j)‖ := norm_sum_le _ _
        _ = ∑ l, G i l * ‖(A * R l) *
              blockAt (curvatureKernel G R ^ k) l j‖ := by
          apply Finset.sum_congr rfl
          intro l _
          rw [blockAt_curvatureKernel, smul_mul_assoc, mul_smul_comm,
            ← Matrix.mul_assoc, norm_smul, Real.norm_eq_abs, abs_of_nonneg (hG i l)]
        _ ≤ ∑ l, G i l * ((3 ^ k * (G ^ k) l j) * (‖A‖ * 3)) := by
          apply Finset.sum_le_sum
          intro l _
          apply mul_le_mul_of_nonneg_left _ (hG i l)
          exact (ih (A * R l) l j).trans (mul_le_mul_of_nonneg_left
            ((Matrix.frobenius_norm_mul A (R l)).trans
              (mul_le_mul_of_nonneg_left (hR l) (norm_nonneg A)))
            (mul_nonneg (by positivity) (scalar_pow_entry_nonneg G hG k l j)))
        _ = (3 ^ (k + 1) * (G ^ (k + 1)) i j) * ‖A‖ := by
          rw [show G ^ (k + 1) = G * G ^ k from pow_succ' G k,
            Matrix.mul_apply, pow_succ]
          simp only [Finset.mul_sum, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro l _
          ring

end
end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_JacobiKernelTrace
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.ScalarPartition.instFintypeι _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p0 _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact endpoint expansion of the curvature-kernel trace. -/
namespace PositiveEinsteinFour.Jacobi
open Matrix
noncomputable section

theorem trace_curvatureKernel_power {N : ℕ} (G : Matrix (Fin N) (Fin N) ℝ)
    (R : Fin N → NormalMatrix) (k : ℕ) :
    (curvatureKernel G R ^ (k + 2)).trace =
      ∑ i, ∑ j, ∑ l, G i j * G l i *
        (R j * blockAt (curvatureKernel G R ^ k) j l * R i).trace := by
  have hp : curvatureKernel G R ^ (k + 2) =
      (curvatureKernel G R * curvatureKernel G R ^ k) * curvatureKernel G R := by
    rw [show k + 2 = (k + 1) + 1 from rfl, pow_succ, pow_succ']
  rw [hp, trace_eq_sum_block_traces]
  simp only [blockAt_mul, blockAt_curvatureKernel, Matrix.sum_mul, Matrix.trace_sum,
    smul_mul_assoc, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem scalar_power_trace_endpoints {N : ℕ} (G : Matrix (Fin N) (Fin N) ℝ)
    (k : ℕ) :
    (G ^ (k + 2)).trace = ∑ i, ∑ j, ∑ l, G i j * G l i * (G ^ k) j l := by
  have hp : G ^ (k + 2) = (G * G ^ k) * G := by
    rw [show k + 2 = (k + 1) + 1 from rfl, pow_succ, pow_succ']
  rw [hp]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro l _
  ring

end
end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_JacobiCyclicPowers
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Moving the square-root factors in the finite Jacobi perturbation.
Only cyclicity of trace is used; curvature matrices are never commuted. -/
namespace PositiveEinsteinFour.Jacobi
open Matrix
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem product_power_succ (A B : Matrix ι ι ℝ) (k : ℕ) :
    (A * B) ^ (k + 1) = A * (B * A) ^ k * B := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ (A * B), ih, pow_succ (B * A)]
      simp only [Matrix.mul_assoc]

theorem trace_product_powers (A B : Matrix ι ι ℝ) (k : ℕ) :
    ((A * B) ^ k).trace = ((B * A) ^ k).trace := by
  cases k with
  | zero => simp
  | succ k =>
      rw [product_power_succ, Matrix.trace_mul_cycle, ← pow_succ']

theorem trace_sandwich_powers (S D : Matrix ι ι ℝ) (k : ℕ) :
    ((S * D * S) ^ k).trace = ((S * S * D) ^ k).trace := by
  rw [trace_product_powers (S * D) S, ← Matrix.mul_assoc]

theorem det_one_sub_sandwich (S D : Matrix ι ι ℝ) :
    (1 - S * D * S).det = (1 - S * S * D).det := by
  rw [Matrix.det_one_sub_mul_comm (S * D) S, ← Matrix.mul_assoc]

end
end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_JacobiKernelAverage
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.ScalarPartition.instFintypeι _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Averaged powers of the actual noncommuting finite curvature kernel. -/
namespace PositiveEinsteinFour.Jacobi
open Matrix MeasureTheory
open scoped Matrix.Norms.Frobenius
noncomputable section
variable {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
  [CompactSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [MeasurableSpace Ω] [BorelSpace Ω] [CompactSpace Ω] in
theorem curvatureKernel_power_block_continuous {N : ℕ}
    (G : Matrix (Fin N) (Fin N) ℝ) (R : Fin N → Ω → NormalMatrix)
    (hR : ∀ i, Continuous (R i)) (k : ℕ) (i j : Fin N) :
    Continuous (fun x => blockAt (curvatureKernel G (fun l => R l x) ^ k) i j) := by
  induction k generalizing i j with
  | zero => simpa only [pow_zero, blockAt_one] using
      (continuous_const : Continuous (fun _ : Ω => if i = j then (1 : NormalMatrix) else 0))
  | succ k ih =>
      simp only [pow_succ', blockAt_mul, blockAt_curvatureKernel]
      exact continuous_finsetSum _ (fun l _ =>
        ((continuous_const : Continuous (fun _ : Ω => G i l)).smul (hR l)).mul (ih l j))

theorem integral_trace_kernel_sandwich_le {N : ℕ}
    (G : Matrix (Fin N) (Fin N) ℝ) (hG : ∀ i j, 0 ≤ G i j)
    (R : Fin N → Ω → NormalMatrix) (hR : ∀ i, Continuous (R i))
    (hbound : ∀ i x, ‖R i x‖ ≤ 3) (k : ℕ) (i j : Fin N)
    (A B : Ω → NormalMatrix) (hA : Continuous A) (hB : Continuous B)
    (hEA : (∫ x, ‖A x‖ ^ 2 ∂μ) = 15 / 2)
    (hEB : (∫ x, ‖B x‖ ^ 2 ∂μ) = 15 / 2) :
    (∫ x, (A x * blockAt (curvatureKernel G (fun l => R l x) ^ k) i j * B x).trace ∂μ) ≤
      (3 ^ k * (G ^ k) i j) * (15 / 2) := by
  let c := 3 ^ k * (G ^ k) i j
  have hc : 0 ≤ c := mul_nonneg (by positivity) (scalar_pow_entry_nonneg G hG k i j)
  have hcont := ((hA.mul (curvatureKernel_power_block_continuous G R hR k i j)).mul hB).matrix_trace
  have hi := hcont.integrable_of_hasCompactSupport (μ := μ) (HasCompactSupport.of_compactSpace _)
  have hia : Integrable (fun x => ‖A x‖ ^ 2) μ :=
    (hA.norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hib : Integrable (fun x => ‖B x‖ ^ 2) μ :=
    (hB.norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hp (x : Ω) :
      (A x * blockAt (curvatureKernel G (fun l => R l x) ^ k) i j * B x).trace ≤
        (c / 2) * (‖A x‖ ^ 2 + ‖B x‖ ^ 2) := by
    have h := (le_abs_self _).trans (abs_trace_mul_le_frobenius
      (A x * blockAt (curvatureKernel G (fun l => R l x) ^ k) i j) (B x))
    have hb := curvatureKernel_power_bound G hG (fun l => R l x)
      (fun l => hbound l x) k (A x) i j
    have h' := mul_le_mul_of_nonneg_right hb (norm_nonneg (B x))
    have ha : 2 * ‖A x‖ * ‖B x‖ ≤ ‖A x‖ ^ 2 + ‖B x‖ ^ 2 := by
      nlinarith [sq_nonneg (‖A x‖ - ‖B x‖)]
    have hm := mul_le_mul_of_nonneg_left ha hc
    change ‖A x * blockAt (curvatureKernel G (fun l => R l x) ^ k) i j‖ * ‖B x‖ ≤
      (c * ‖A x‖) * ‖B x‖ at h'
    nlinarith
  calc
    _ ≤ ∫ x, (c / 2) * (‖A x‖ ^ 2 + ‖B x‖ ^ 2) ∂μ :=
      integral_mono hi ((hia.add hib).const_mul _) hp
    _ = c * (15 / 2) := by
      rw [integral_const_mul, integral_add hia hib, hEA, hEB]
      ring

/-- At the exceptional energy three, all finite moments of order at least
two are bounded by five sixths of the scalar curvature-three moments. -/
theorem integral_trace_curvatureKernel_power_le {N : ℕ}
    (G : Matrix (Fin N) (Fin N) ℝ) (hG : ∀ i j, 0 ≤ G i j)
    (R : Fin N → Ω → NormalMatrix) (hR : ∀ i, Continuous (R i))
    (hpos : ∀ i x, (R i x).PosSemidef ∧ (R i x).trace = 3)
    (hE : ∀ i, (∫ x, ‖R i x‖ ^ 2 ∂μ) = 15 / 2) (k : ℕ) :
    (∫ x, (curvatureKernel G (fun i => R i x) ^ (k + 2)).trace ∂μ) ≤
      (5 / 6 : ℝ) * 3 ^ (k + 2) * (G ^ (k + 2)).trace := by
  let F := fun i j l x =>
    (R j x * blockAt (curvatureKernel G (fun a => R a x) ^ k) j l * R i x).trace
  have hi (i j l : Fin N) : Integrable (F i j l) μ :=
    ((((hR j).mul (curvatureKernel_power_block_continuous G R hR k j l)).mul
      (hR i)).matrix_trace).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hs (i j l : Fin N) : (∫ x, F i j l x ∂μ) ≤
      (3 ^ k * (G ^ k) j l) * (15 / 2) :=
    integral_trace_kernel_sandwich_le G hG R hR
      (fun a x => frobenius_le_three_of_posSemidef_trace (hpos a x).1 (hpos a x).2)
      k j l (R j) (R i) (hR j) (hR i) (hE j) (hE i)
  calc
    _ = ∫ x, ∑ i, ∑ j, ∑ l, (G i j * G l i) * F i j l x ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => trace_curvatureKernel_power G _ k)
    _ = ∑ i, ∑ j, ∑ l, (G i j * G l i) * ∫ x, F i j l x ∂μ := by
      rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
        integrable_finsetSum _ (fun l _ => (hi i j l).const_mul _)))]
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_finsetSum _ (fun j _ =>
        integrable_finsetSum _ (fun l _ => (hi i j l).const_mul _))]
      apply Finset.sum_congr rfl
      intro j _
      rw [integral_finsetSum _ (fun l _ => (hi i j l).const_mul _)]
      simp_rw [integral_const_mul]
    _ ≤ ∑ i, ∑ j, ∑ l, (G i j * G l i) *
        ((3 ^ k * (G ^ k) j l) * (15 / 2)) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro l _
      exact mul_le_mul_of_nonneg_left (hs i j l) (mul_nonneg (hG i j) (hG l i))
    _ = _ := by
      rw [scalar_power_trace_endpoints, pow_add]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro l _
      norm_num
      ring

end
end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_JacobiSymmetricKernel
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.ScalarPartition.instFintypeι _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Symmetric realization of the positive Green-kernel perturbation. -/
namespace PositiveEinsteinFour.Jacobi
open Matrix
noncomputable section

theorem symmetricCurvatureKernel_trace_pow {N : ℕ}
    (S G : Matrix (Fin N) (Fin N) ℝ) (hS : S * S = G)
    (R : Fin N → NormalMatrix) (k : ℕ) :
    (symmetricCurvatureKernel S R ^ k).trace = (curvatureKernel G R ^ k).trace := by
  rw [symmetricCurvatureKernel, trace_sandwich_powers, ← scalarLift_mul, hS]
  rfl

theorem symmetricCurvatureKernel_trace {N : ℕ}
    (S G : Matrix (Fin N) (Fin N) ℝ) (hS : S * S = G)
    (R : Fin N → NormalMatrix) (hR : ∀ i, (R i).trace = 3) :
    (symmetricCurvatureKernel S R).trace = 3 * G.trace := by
  have h := symmetricCurvatureKernel_trace_pow S G hS R 1
  simp only [pow_one] at h
  rw [h]
  change (scalarLift G * Matrix.blockDiagonal R).trace = _
  rw [trace_scalarLift_mul_diagonal]
  simp_rw [hR]
  simp only [Matrix.trace, Matrix.diag_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem symmetricCurvatureKernel_det {N : ℕ}
    (S G : Matrix (Fin N) (Fin N) ℝ) (hS : S * S = G)
    (R : Fin N → NormalMatrix) :
    (1 - symmetricCurvatureKernel S R).det = (1 - curvatureKernel G R).det := by
  rw [symmetricCurvatureKernel, det_one_sub_sandwich, ← scalarLift_mul, hS]
  rfl

theorem blockDiagonal_posSemidef {N : ℕ} (R : Fin N → NormalMatrix)
    (hR : ∀ i, (R i).PosSemidef) : (Matrix.blockDiagonal R).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · change (Matrix.blockDiagonal R).conjTranspose = Matrix.blockDiagonal R
    rw [Matrix.blockDiagonal_conjTranspose]
    congr 1
    funext i
    exact (hR i).isHermitian.eq
  · intro x
    rw [blockDiagonal_quadratic]
    exact Finset.sum_nonneg (fun i _ => (hR i).dotProduct_mulVec_nonneg _)

theorem scalarLift_conjTranspose {N : ℕ} (S : Matrix (Fin N) (Fin N) ℝ)
    (hS : Sᵀ = S) : (scalarLift S)ᴴ = scalarLift S := by
  ext ⟨a,i⟩ ⟨b,j⟩
  change (1 : NormalMatrix) b a * S j i = (1 : NormalMatrix) a b * S i j
  have hs : S j i = S i j := congrFun (congrFun hS i) j
  rw [hs]
  simp only [Matrix.one_apply, eq_comm]

theorem symmetricCurvatureKernel_posSemidef {N : ℕ}
    (S : Matrix (Fin N) (Fin N) ℝ) (hS : Sᵀ = S)
    (R : Fin N → NormalMatrix) (hR : ∀ i, (R i).PosSemidef) :
    (symmetricCurvatureKernel S R).PosSemidef := by
  have h := (blockDiagonal_posSemidef R hR).conjTranspose_mul_mul_same (scalarLift S)
  simpa only [scalarLift_conjTranspose S hS, symmetricCurvatureKernel] using h

end
end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_JacobiCurvatureCap
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.ScalarPartition.instFintypeι _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positivity of the curvature perturbation below the scalar conjugate
threshold. The cap three follows from positivity and trace three. -/
namespace PositiveEinsteinFour.Jacobi
open Matrix
noncomputable section

theorem three_sub_posSemidef {A : NormalMatrix} (hA : A.PosSemidef)
    (htr : A.trace = 3) : ((3 : ℝ) • (1 : NormalMatrix) - A).PosSemidef := by
  let U := hA.isHermitian.eigenvectorUnitary
  let φ := Unitary.conjStarAlgAut ℝ NormalMatrix U
  have hdiag : A = φ (diagonal hA.isHermitian.eigenvalues) := by
    simpa only [Function.comp_def, RCLike.ofReal_real_eq_id, id_eq] using
      hA.isHermitian.spectral_theorem
  have hsum : (∑ i, hA.isHermitian.eigenvalues i) = 3 := by
    simpa only [RCLike.ofReal_real_eq_id, id_eq, htr] using
      hA.isHermitian.trace_eq_sum_eigenvalues.symm
  have hb (i : Fin 3) : hA.isHermitian.eigenvalues i ≤ 3 := by
    rw [← hsum]
    exact Finset.single_le_sum (fun j _ => hA.eigenvalues_nonneg j) (Finset.mem_univ i)
  have hp : (diagonal (fun i => 3 - hA.isHermitian.eigenvalues i)).PosSemidef :=
    Matrix.posSemidef_diagonal_iff.mpr (fun i => sub_nonneg.mpr (hb i))
  have hφ : φ (diagonal (fun i => 3 - hA.isHermitian.eigenvalues i)) =
      (3 : ℝ) • (1 : NormalMatrix) - A := by
    have he : diagonal (fun i => 3 - hA.isHermitian.eigenvalues i) =
        (3 : ℝ) • (1 : NormalMatrix) - diagonal hA.isHermitian.eigenvalues := by
      ext i j
      by_cases hij : i = j <;> simp [hij]
    rw [he, map_sub, map_smul, map_one, ← hdiag]
  rw [← hφ]
  simpa only [φ, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_conjTranspose] using
    hp.conjTranspose_mul_mul_same (star (U : NormalMatrix))

theorem scalarLift_quadratic {N : ℕ} (G : Matrix (Fin N) (Fin N) ℝ)
    (x : Fin 3 × Fin N → ℝ) :
    star x ⬝ᵥ (scalarLift G *ᵥ x) =
      ∑ a : Fin 3, star (fun i => x (a,i)) ⬝ᵥ (G *ᵥ fun i => x (a,i)) := by
  simp only [dotProduct, Matrix.mulVec, Fintype.sum_prod_type, scalarLift,
    Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply, ite_mul,
    one_mul, zero_mul, star_trivial, Finset.mul_sum]
  simp

theorem scalarLift_posDef {N : ℕ} {G : Matrix (Fin N) (Fin N) ℝ}
    (hG : G.PosDef) : (scalarLift G).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · apply scalarLift_conjTranspose
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hG.isHermitian.eq
  · intro x hx
    rw [scalarLift_quadratic]
    have hn : ∃ a : Fin 3, (fun i => x (a,i)) ≠ 0 := by
      by_contra! h
      apply hx
      funext p
      exact congrFun (h p.1) p.2
    obtain ⟨a,ha⟩ := hn
    exact Finset.sum_pos' (fun b _ => hG.posSemidef.dotProduct_mulVec_nonneg _)
      ⟨a, Finset.mem_univ _, hG.dotProduct_mulVec_pos ha⟩

theorem scalarLift_sub_three {N : ℕ} (G : Matrix (Fin N) (Fin N) ℝ) :
    scalarLift (1 - (3 : ℝ) • G) = 1 - (3 : ℝ) • scalarLift G := by
  rw [← scalarLift_one N]
  ext ⟨a,i⟩ ⟨b,j⟩
  change (1 : NormalMatrix) a b * ((1 : Matrix (Fin N) (Fin N) ℝ) i j - 3 * G i j) =
    (1 : NormalMatrix) a b * (1 : Matrix (Fin N) (Fin N) ℝ) i j -
      3 * ((1 : NormalMatrix) a b * G i j)
  ring

theorem symmetricCurvatureKernel_one_sub_posDef {N : ℕ}
    (S G : Matrix (Fin N) (Fin N) ℝ) (hS : S * S = G) (hSt : Sᵀ = S)
    (hscalar : (1 - (3 : ℝ) • G).PosDef)
    (R : Fin N → NormalMatrix) (hR : ∀ i, (R i).PosSemidef ∧ (R i).trace = 3) :
    (1 - symmetricCurvatureKernel S R).PosDef := by
  have hc := blockDiagonal_posSemidef (fun i => (3 : ℝ) • (1 : NormalMatrix) - R i)
    (fun i => three_sub_posSemidef (hR i).1 (hR i).2)
  have hb : Matrix.blockDiagonal (fun i => (3 : ℝ) • (1 : NormalMatrix) - R i) =
      (3 : ℝ) • 1 - Matrix.blockDiagonal R := by
    ext ⟨a,i⟩ ⟨b,j⟩
    by_cases hij : i = j
    · subst j
      simp [Matrix.blockDiagonal_apply, Matrix.one_apply]
    · simp [Matrix.blockDiagonal_apply, hij]
  rw [hb] at hc
  have hp := hc.conjTranspose_mul_mul_same (scalarLift S)
  rw [scalarLift_conjTranspose S hSt] at hp
  have h := (scalarLift_posDef hscalar).add_posSemidef hp
  have he : scalarLift (1 - (3 : ℝ) • G) + scalarLift S *
      ((3 : ℝ) • 1 - Matrix.blockDiagonal R) * scalarLift S =
      1 - symmetricCurvatureKernel S R := by
    rw [scalarLift_sub_three, symmetricCurvatureKernel,
      Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one,
      Matrix.smul_mul, ← scalarLift_mul, hS]
    module
  rwa [he] at h

end
end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_JacobiLogDetSeries
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite-dimensional logarithmic determinant series used by the
lower radial comparison. It applies to the scalar Green matrix and its
three-dimensional curvature perturbation. -/
namespace PositiveEinsteinFour.Jacobi
open Matrix
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem trace_unitary_conjugation (U : Matrix.unitaryGroup ι ℝ)
    (A : Matrix ι ι ℝ) :
    (Unitary.conjStarAlgAut ℝ (Matrix ι ι ℝ) U A).trace = A.trace := by
  rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, one_mul]

private theorem det_unitary_conjugation (U : Matrix.unitaryGroup ι ℝ)
    (A : Matrix ι ι ℝ) :
    (Unitary.conjStarAlgAut ℝ (Matrix ι ι ℝ) U A).det = A.det := by
  have hU := congrArg Matrix.det (Unitary.coe_star_mul_self U)
  simp only [Matrix.det_mul, Matrix.det_one] at hU
  rw [Unitary.conjStarAlgAut_apply, Matrix.det_mul, Matrix.det_mul]
  calc
    _ = ((star U : Matrix ι ι ℝ).det * (U : Matrix ι ι ℝ).det) * A.det := by ring
    _ = A.det := by rw [hU, one_mul]

theorem trace_pow_eq_sum_eigenvalues {A : Matrix ι ι ℝ} (hA : A.IsHermitian)
    (k : ℕ) : (A ^ k).trace = ∑ i, hA.eigenvalues i ^ k := by
  let φ := Unitary.conjStarAlgAut ℝ (Matrix ι ι ℝ) (star hA.eigenvectorUnitary)
  have hd : φ A = diagonal hA.eigenvalues := by
    simpa only [Function.comp_def, RCLike.ofReal_real_eq_id, id_eq] using
      hA.conjStarAlgAut_star_eigenvectorUnitary
  calc
    _ = (φ (A ^ k)).trace := (trace_unitary_conjugation _ _).symm
    _ = (diagonal hA.eigenvalues ^ k).trace := by rw [map_pow, hd]
    _ = _ := by simp only [diagonal_pow, Matrix.trace_diagonal, Pi.pow_apply]

private theorem one_sub_eigenvalues_pos {A : Matrix ι ι ℝ} (hA : A.IsHermitian)
    (hI : (1 - A).PosDef) : ∀ i, 0 < 1 - hA.eigenvalues i := by
  let U := star hA.eigenvectorUnitary
  let φ := Unitary.conjStarAlgAut ℝ (Matrix ι ι ℝ) U
  have hd : φ A = diagonal hA.eigenvalues := by
    simpa only [Function.comp_def, RCLike.ofReal_real_eq_id, id_eq] using
      hA.conjStarAlgAut_star_eigenvectorUnitary
  have hunit : IsUnit (star (U : Matrix ι ι ℝ)) := (Unitary.isUnit_coe (U := U)).star
  have hp : ((star (U : Matrix ι ι ℝ))ᴴ * (1 - A) *
      star (U : Matrix ι ι ℝ)).PosDef :=
    hI.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit hunit)
  have he : φ (1 - A) = diagonal (fun i => 1 - hA.eigenvalues i) := by
    rw [map_sub, map_one, hd]
    ext i j
    by_cases hij : i = j <;> simp [hij]
  have hp' : (φ (1 - A)).PosDef := by
    simpa only [φ, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose] using hp
  rw [he, Matrix.posDef_diagonal_iff] at hp'
  exact hp'

theorem log_det_one_sub_eq_sum {A : Matrix ι ι ℝ} (hA : A.IsHermitian)
    (hI : (1 - A).PosDef) :
    Real.log (1 - A).det = ∑ i, Real.log (1 - hA.eigenvalues i) := by
  let φ := Unitary.conjStarAlgAut ℝ (Matrix ι ι ℝ) (star hA.eigenvectorUnitary)
  have hd : φ A = diagonal hA.eigenvalues := by
    simpa only [Function.comp_def, RCLike.ofReal_real_eq_id, id_eq] using
      hA.conjStarAlgAut_star_eigenvectorUnitary
  have he : φ (1 - A) = diagonal (fun i => 1 - hA.eigenvalues i) := by
    rw [map_sub, map_one, hd]
    ext i j
    by_cases hij : i = j <;> simp [hij]
  rw [← det_unitary_conjugation (star hA.eigenvectorUnitary), he, Matrix.det_diagonal]
  exact Real.log_prod (fun i _ => (one_sub_eigenvalues_pos hA hI i).ne')

/-- The full logarithmic determinant is the sum of ordered matrix moments. -/
theorem hasSum_trace_pow_neg_log_det {A : Matrix ι ι ℝ}
    (hA : A.PosSemidef) (hI : (1 - A).PosDef) :
    HasSum (fun k : ℕ => (A ^ (k + 1)).trace / (k + 1))
      (-Real.log (1 - A).det) := by
  have hs (i : ι) : HasSum
      (fun k : ℕ => hA.isHermitian.eigenvalues i ^ (k + 1) / (k + 1))
      (-Real.log (1 - hA.isHermitian.eigenvalues i)) :=
    Real.hasSum_pow_div_log_of_abs_lt_one (by
      rw [abs_of_nonneg (hA.eigenvalues_nonneg i)]
      linarith [one_sub_eigenvalues_pos hA.isHermitian hI i])
  have H := hasSum_sum (s := Finset.univ) (fun i _ => hs i)
  convert H using 1
  · ext k
    rw [trace_pow_eq_sum_eigenvalues hA.isHermitian, Finset.sum_div]
  · rw [log_det_one_sub_eq_sum hA.isHermitian hI, Finset.sum_neg_distrib]

end
end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_JacobiSeriesIntegral
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_nonempty _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Passing the finite curvature-moment bounds through the positive
logarithmic series. The dominating function is its actual pointwise sum. -/
namespace PositiveEinsteinFour.Jacobi
open MeasureTheory Filter
open scoped _root_.Topology
noncomputable section
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem integral_nonnegative_series_le
    (F : ℕ → Ω → ℝ) (S : Ω → ℝ) (g : ℕ → ℝ) (b : ℝ)
    (hF : ∀ n, Integrable (F n) μ) (hS : Integrable S μ)
    (hpos : ∀ n x, 0 ≤ F n x)
    (hs : ∀ x, HasSum (fun n => F n x) (S x))
    (hg : HasSum g b) (hbound : ∀ n, (∫ x, F n x ∂μ) ≤ g n) :
    (∫ x, S x ∂μ) ≤ b := by
  have hp (n : ℕ) (x : Ω) : ‖∑ i ∈ Finset.range n, F i x‖ ≤ S x := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg (fun i _ => hpos i x))]
    exact sum_le_hasSum (Finset.range n) (fun i _ => hpos i x) (hs x)
  have ht := tendsto_integral_of_dominated_convergence S
    (fun n => (integrable_finsetSum _ (fun i _ => hF i)).aestronglyMeasurable) hS
    (fun n => Filter.Eventually.of_forall (hp n))
    (Filter.Eventually.of_forall (fun x => (hs x).tendsto_sum_nat))
  apply le_of_tendsto_of_tendsto ht hg.tendsto_sum_nat
  apply Filter.Eventually.of_forall
  intro n
  change (∫ x, ∑ i ∈ Finset.range n, F i x ∂μ) ≤ ∑ i ∈ Finset.range n, g i
  rw [integral_finsetSum _ (fun i _ => hF i)]
  exact Finset.sum_le_sum (fun i _ => hbound i)

end
end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_JacobiExpectedLog
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The averaged logarithmic determinant estimate from the finite moments. -/
namespace PositiveEinsteinFour.Jacobi
open Matrix MeasureTheory
noncomputable section
variable {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
  [CompactSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem expected_log_det_lower
    (H : Ω → Matrix ι ι ℝ) (C : Matrix κ κ ℝ) (hH : Continuous H)
    (hp : ∀ x, (H x).PosSemidef) (hI : ∀ x, (1 - H x).PosDef)
    (hC : C.PosSemidef) (hIC : (1 - C).PosDef)
    (hfirst : (∫ x, (H x).trace ∂μ) = C.trace)
    (hmoments : ∀ k : ℕ, (∫ x, (H x ^ (k + 2)).trace ∂μ) ≤
      (5 / 6 : ℝ) * (C ^ (k + 2)).trace) :
    (5 / 6 : ℝ) * Real.log (1 - C).det - C.trace / 6 ≤
      ∫ x, Real.log (1 - H x).det ∂μ := by
  let F := fun (n : ℕ) (x : Ω) => (H x ^ (n + 1)).trace / (n + 1)
  let S := fun x => -Real.log (1 - H x).det
  let g := fun n : ℕ => (5 / 6 : ℝ) * ((C ^ (n + 1)).trace / (n + 1)) +
    if n = 0 then C.trace / 6 else 0
  have hF (n : ℕ) : Integrable (F n) μ :=
    (((hH.pow (n + 1)).matrix_trace).div_const _).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hS : Integrable S μ :=
    ((((continuous_const.sub hH).matrix_det).log
      (fun x => (hI x).det_pos.ne')).neg).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hpos (n : ℕ) (x : Ω) : 0 ≤ F n x := by
    dsimp [F]
    rw [trace_pow_eq_sum_eigenvalues (hp x).isHermitian]
    apply div_nonneg
    · exact Finset.sum_nonneg (fun i _ => pow_nonneg ((hp x).eigenvalues_nonneg i) _)
    · positivity
  have hs (x : Ω) : HasSum (fun n => F n x) (S x) :=
    hasSum_trace_pow_neg_log_det (hp x) (hI x)
  have hg : HasSum g ((5 / 6 : ℝ) * (-Real.log (1 - C).det) + C.trace / 6) := by
    exact ((hasSum_trace_pow_neg_log_det hC hIC).mul_left (5 / 6)).add
      (hasSum_ite_eq 0 (C.trace / 6))
  have hb (n : ℕ) : (∫ x, F n x ∂μ) ≤ g n := by
    cases n with
    | zero =>
        simp only [F, g, zero_add, pow_one, Nat.cast_zero, div_one, ite_true, if_true]
        rw [hfirst]
        linarith
    | succ n =>
        dsimp only [F, g]
        rw [integral_div]
        have h := div_le_div_of_nonneg_right (hmoments n)
          (show (0 : ℝ) ≤ n + 2 by positivity)
        simp only [Nat.cast_add, Nat.cast_one,
          Nat.add_assoc, Nat.reduceAdd, Nat.add_eq_zero_iff, one_ne_zero,
          and_false, ite_false, if_false, add_zero]
        first | (convert h using 1 <;> ring) | exact (le_of_eq (by ring)).trans (h.trans (le_of_eq (by ring)))
  have h := integral_nonnegative_series_le F S g _ hF hS hpos hs hg hb
  change (∫ x, -Real.log (1 - H x).det ∂μ) ≤ _ at h
  rw [integral_neg] at h
  linarith

end
end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_JacobiDeterminantJensen
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Jensen's scalar exponential step, with all logarithms and integrals
taken only for strictly positive continuous determinants. -/
namespace PositiveEinsteinFour.Jacobi
open MeasureTheory
noncomputable section
variable {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
  [CompactSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem exp_integral_log_le_integral (f : Ω → ℝ) (hf : Continuous f)
    (hpos : ∀ x, 0 < f x) : Real.exp (∫ x, Real.log (f x) ∂μ) ≤ ∫ x, f x ∂μ := by
  let m := ∫ x, Real.log (f x) ∂μ
  have hi : Integrable (fun x => Real.log (f x)) μ :=
    (hf.log (fun x => (hpos x).ne')).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hfi := hf.integrable_of_hasCompactSupport (μ := μ) (HasCompactSupport.of_compactSpace _)
  have his : Integrable (fun x => Real.log (f x) - m) μ := hi.sub (integrable_const m)
  have hb (x : Ω) : Real.exp m * (1 + (Real.log (f x) - m)) ≤ f x := by
    have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (Real.log (f x) - m))
      (Real.exp_pos m).le
    have he : Real.exp m * Real.exp (Real.log (f x) - m) = f x := by
      rw [← Real.exp_add, add_sub_cancel, Real.exp_log (hpos x)]
    rw [he] at h
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hj := integral_mono (((integrable_const 1).add his).const_mul
    (Real.exp m)) hfi hb
  rw [integral_const_mul] at hj
  change Real.exp m * (∫ x, (1 + (Real.log (f x) - m)) ∂μ) ≤ _ at hj
  rw [integral_add (integrable_const 1) his,
    integral_sub hi (integrable_const m)] at hj
  simpa [m] using hj

end
end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_JacobiFiniteLower
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.ScalarPartition.instFintypeι _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite lower determinant comparison at total Weyl energy three. -/
namespace PositiveEinsteinFour.Jacobi
open Matrix MeasureTheory
open scoped Matrix.Norms.Frobenius
noncomputable section
variable {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
  [CompactSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem finite_log_determinant_lower {N : ℕ}
    (S G : Matrix (Fin N) (Fin N) ℝ) (hS : S * S = G) (hSt : Sᵀ = S)
    (hG : G.PosSemidef) (hGentry : ∀ i j, 0 ≤ G i j)
    (R : Fin N → Ω → NormalMatrix) (hR : ∀ i, Continuous (R i))
    (hpos : ∀ i x, (R i x).PosSemidef ∧ (R i x).trace = 3)
    (hE : ∀ i, (∫ x, ‖R i x‖ ^ 2 ∂μ) = 15 / 2)
    (hscalar : (1 - (3 : ℝ) • G).PosDef)
    (hI : ∀ x, (1 - symmetricCurvatureKernel S (fun i => R i x)).PosDef) :
    (5 / 6 : ℝ) * Real.log (1 - (3 : ℝ) • G).det - G.trace / 2 ≤
      ∫ x, Real.log (1 - curvatureKernel G (fun i => R i x)).det ∂μ := by
  let H := fun x => symmetricCurvatureKernel S (fun i => R i x)
  have hH : Continuous H :=
    (continuous_const.mul ((continuous_pi hR).matrix_blockDiagonal)).mul continuous_const
  have hp : ∀ x, (H x).PosSemidef := fun x =>
    symmetricCurvatureKernel_posSemidef S hSt _ (fun i => (hpos i x).1)
  have htr (k : ℕ) : (((3 : ℝ) • G) ^ k).trace = 3 ^ k * (G ^ k).trace := by
    rw [smul_pow, Matrix.trace_smul, smul_eq_mul]
  have hfirst : (∫ x, (H x).trace ∂μ) = ((3 : ℝ) • G).trace := by
    have he (x : Ω) : (H x).trace = 3 * G.trace :=
      symmetricCurvatureKernel_trace S G hS _ (fun i => (hpos i x).2)
    simp only [he, integral_const, probReal_univ, Matrix.trace_smul, smul_eq_mul, one_mul]
  have hmoment (k : ℕ) : (∫ x, (H x ^ (k + 2)).trace ∂μ) ≤
      (5 / 6 : ℝ) * (((3 : ℝ) • G) ^ (k + 2)).trace := by
    have he (x : Ω) : (H x ^ (k + 2)).trace =
        (curvatureKernel G (fun i => R i x) ^ (k + 2)).trace :=
      symmetricCurvatureKernel_trace_pow S G hS _ _
    rw [integral_congr_ae (Filter.Eventually.of_forall he), htr]
    simpa only [mul_assoc] using integral_trace_curvatureKernel_power_le G hGentry R hR hpos hE k
  have h := expected_log_det_lower H ((3 : ℝ) • G) hH hp hI
    (hG.smul (by norm_num)) hscalar hfirst hmoment
  have he (x : Ω) : (1 - H x).det = (1 - curvatureKernel G (fun i => R i x)).det :=
    symmetricCurvatureKernel_det S G hS _
  simp only [Matrix.trace_smul, smul_eq_mul] at h
  rw [integral_congr_ae (Filter.Eventually.of_forall (fun x => congrArg Real.log (he x)))] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ring

theorem finite_determinant_lower {N : ℕ}
    (S G : Matrix (Fin N) (Fin N) ℝ) (hS : S * S = G) (hSt : Sᵀ = S)
    (hG : G.PosSemidef) (hGentry : ∀ i j, 0 ≤ G i j)
    (R : Fin N → Ω → NormalMatrix) (hR : ∀ i, Continuous (R i))
    (hpos : ∀ i x, (R i x).PosSemidef ∧ (R i x).trace = 3)
    (hE : ∀ i, (∫ x, ‖R i x‖ ^ 2 ∂μ) = 15 / 2)
    (hscalar : (1 - (3 : ℝ) • G).PosDef)
    (hI : ∀ x, (1 - symmetricCurvatureKernel S (fun i => R i x)).PosDef) :
    Real.exp ((5 / 6 : ℝ) * Real.log (1 - (3 : ℝ) • G).det - G.trace / 2) ≤
      ∫ x, (1 - curvatureKernel G (fun i => R i x)).det ∂μ := by
  have hf : Continuous (fun x => (1 - curvatureKernel G (fun i => R i x)).det) :=
    (continuous_const.sub (continuous_const.mul
      ((continuous_pi hR).matrix_blockDiagonal))).matrix_det
  have hp (x : Ω) : 0 < (1 - curvatureKernel G (fun i => R i x)).det := by
    rw [← symmetricCurvatureKernel_det S G hS]
    exact (hI x).det_pos
  exact (Real.exp_le_exp.mpr
    (finite_log_determinant_lower S G hS hSt hG hGentry R hR hpos hE hscalar hI)).trans
      (exp_integral_log_le_integral _ hf hp)

end
end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_JacobiFullCurvatureNorm
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.ScalarPartition.instFintypeι _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p0 _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The scalar curvature contribution to the normal-curvature energy. -/
namespace PositiveEinsteinFour.Jacobi
open Matrix
open scoped Matrix.Norms.Frobenius
noncomputable section

theorem frobenius_sq_eq_sum_entries (A : NormalMatrix) :
    ‖A‖ ^ 2 = ∑ i, ∑ j, A i j ^ 2 := by
  rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow]
  simp only [Real.rpow_two, Real.norm_eq_abs, sq_abs]
  exact Real.sq_sqrt (by positivity)

theorem frobenius_sq_one_add (A : NormalMatrix) :
    ‖1 + A‖ ^ 2 = 3 + 2 * A.trace + ‖A‖ ^ 2 := by
  simp only [frobenius_sq_eq_sum_entries, Matrix.trace, Matrix.diag_apply,
    Matrix.add_apply, Matrix.one_apply, Fin.sum_univ_three]
  norm_num [Fin.ext_iff]
  ring

theorem frobenius_sq_one_add_of_trace_zero (A : NormalMatrix) (hA : A.trace = 0) :
    ‖1 + A‖ ^ 2 = 3 + ‖A‖ ^ 2 := by rw [frobenius_sq_one_add, hA]; ring

end
end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_CurvatureTensors11
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.roundPolarPoint_tail _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_first _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Exact second moment of the actual full normal-curvature matrix. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix MeasureTheory Jacobi
open scoped Manifold ContDiff Matrix.Norms.Frobenius
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]

local instance instNormedAddCommGroupMat3_6_ra5163b_1 : NormedAddCommGroup Mat3 := Matrix.frobeniusNormedAddCommGroup
local instance instNormedSpaceRealMat3_4_ra5163b_1 : NormedSpace ℝ Mat3 := Matrix.frobeniusNormedSpace
omit [PreconnectedSpace M] in
theorem actualJacobiCurvature_frame_continuous (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) (t : ℝ) : Continuous (fun e => actualJacobiCurvature g e t) := by
  let d := (canonicalParallelMetricData g o hRic).toMetricGreenData
  have hp := actualParallelMetricData_reflection g (canonicalFrameMeasure g o)
    (parallelFrameFlowMap_measurePreserving g o) hRic
  let op := d.oppositeData hp hRic
  have hC : Continuous (frameCurvatureField g) := d.continuousCurvatureField op hRic
  exact continuous_const.add (hC.comp (parallelFrameFlowMap_continuous_slice g 0 t))

omit [PreconnectedSpace M] in
theorem actual_frameCurvature_mean_square (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) :
    (∫ e, ‖frameCurvatureField g e‖ ^ 2 ∂canonicalFrameMeasure g o) =
      (3 / 2) * (∫ x, plusNorm o x ^ 2 + minusNorm o x ^ 2 ∂normalizedVolume g) := by
  let : CompactSpace (FrameBundle g) := actual_compactFrameBundle g
  let d := (canonicalParallelMetricData g o hRic).toMetricGreenData
  have hp := actualParallelMetricData_reflection g (canonicalFrameMeasure g o)
    (parallelFrameFlowMap_measurePreserving g o) hRic
  let op := d.oppositeData hp hRic
  have hC : Continuous (frameCurvatureField g) := d.continuousCurvatureField op hRic
  have hi : Integrable (fun e => ‖frameCurvatureField g e‖ ^ 2)
      (canonicalFrameMeasure g o) :=
    (hC.norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  exact (canonicalFrameMeasure_energy g o).curvature_energy Angular.actual_follandMoments
    hRic (actual_orientedNormRegularity o).toPetersenInput (actual_finitePositiveVolume g) hi

omit [T3Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M] in
private theorem full_curvature_norm_square (g : SmoothMetric M) (hRic : RicciThree g)
    (e : FrameBundle g) :
    ‖1 + frameCurvatureField g e‖ ^ 2 = 3 + ‖frameCurvatureField g e‖ ^ 2 := by
  apply frobenius_sq_one_add_of_trace_zero
  have ht : (frameCurvatureField g e).trace = 0 := by
    have h := frameCurvatureField_add_one_trace g e (actual_einstein_decomposition _ hRic)
      (actual_weyl_traceFree _ hRic).1 (actual_weyl_traceFree _ hRic).2
    rw [Matrix.trace_add, Matrix.trace_one] at h
    norm_num at h
    linarith
  exact ht

omit [PreconnectedSpace M] in
private theorem full_curvature_mean_square (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) :
    (∫ e, ‖1 + frameCurvatureField g e‖ ^ 2 ∂canonicalFrameMeasure g o) =
      3 + (3 / 2) * (∫ x, plusNorm o x ^ 2 + minusNorm o x ^ 2 ∂normalizedVolume g) := by
  let : CompactSpace (FrameBundle g) := actual_compactFrameBundle g
  let d := (canonicalParallelMetricData g o hRic).toMetricGreenData
  have hp := actualParallelMetricData_reflection g (canonicalFrameMeasure g o)
    (parallelFrameFlowMap_measurePreserving g o) hRic
  let op := d.oppositeData hp hRic
  have hC : Continuous (frameCurvatureField g) := d.continuousCurvatureField op hRic
  have hi : Integrable (fun e => ‖frameCurvatureField g e‖ ^ 2)
      (canonicalFrameMeasure g o) :=
    (hC.norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  calc
    _ = ∫ e, (3 + ‖frameCurvatureField g e‖ ^ 2) ∂canonicalFrameMeasure g o := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (full_curvature_norm_square g hRic)
    _ = _ := by
      rw [integral_add (integrable_const _) hi, actual_frameCurvature_mean_square g o hRic]
      simp

omit [PreconnectedSpace M] in
theorem actualJacobiCurvature_mean_square (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) (t : ℝ) :
    (∫ e, ‖actualJacobiCurvature g e t‖ ^ 2 ∂canonicalFrameMeasure g o) =
      3 + (3 / 2) * (∫ x, plusNorm o x ^ 2 + minusNorm o x ^ 2 ∂normalizedVolume g) := by
  change (∫ e, (fun f : FrameBundle g => ‖1 + frameCurvatureField g f‖ ^ 2)
    (parallelFrameFlowMap g 0 t e) ∂canonicalFrameMeasure g o) = _
  have h := (parallelFrameFlowMap_measurePreserving g o 0 t).integral_comp
    (parallelFrameHomeomorph g 0 t).measurableEmbedding
    (fun e => ‖1 + frameCurvatureField g e‖ ^ 2)
  exact h.trans (full_curvature_mean_square g o hRic)

omit [PreconnectedSpace M] in
theorem actualJacobiCurvature_mean_square_of_energy_three
    (g : SmoothMetric M) (o : FrameOrientation g) (hRic : RicciThree g)
    (hE : (∫ x, plusNorm o x ^ 2 + minusNorm o x ^ 2 ∂normalizedVolume g) = 3)
    (t : ℝ) :
    (∫ e, ‖actualJacobiCurvature g e t‖ ^ 2 ∂canonicalFrameMeasure g o) = 15 / 2 := by
  rw [actualJacobiCurvature_mean_square g o hRic t, hE]
  norm_num

end
end PositiveEinsteinFour.Geometry
end


section

/-! The lower finite determinant estimate for the actual geodesic curvature,
with no spectral or discrete positivity hypothesis. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix MeasureTheory Jacobi Filter
open scoped Manifold ContDiff Matrix.Norms.Frobenius
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M]

theorem actual_finite_jacobi_determinant_lower (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) (hpositive : HasPositiveSectionalCurvature g)
    (hE : (∫ x, plusNorm o x ^ 2 + minusNorm o x ^ 2 ∂normalizedVolume g) = 3)
    (t : ℝ) (ht : 0 ≤ t) (htop : t < Real.pi / Real.sqrt 3) :
    ∀ᶠ N : ℕ in atTop, ∀ τ : Fin N → ℝ,
      Real.exp ((5 / 6 : ℝ) * Real.log (1 - (3 : ℝ) • scaledFlatGreen t N).det -
        (scaledFlatGreen t N).trace / 2) ≤
      ∫ e, (1 - curvatureKernel (scaledFlatGreen t N)
        (fun i => actualJacobiCurvature g e (τ i))).det ∂canonicalFrameMeasure g o := by
  let : CompactSpace (FrameBundle g) := actual_compactFrameBundle g
  filter_upwards [scaledFlatGreen_eventually_below_one ht htop] with N hN
  intro τ
  let R := fun i e => actualJacobiCurvature g e (τ i)
  have hR : ∀ i, Continuous (R i) := fun i =>
    actualJacobiCurvature_frame_continuous g o hRic (τ i)
  have hp : ∀ i e, (R i e).PosSemidef ∧ (R i e).trace = 3 := by
    intro i e
    exact ⟨actual_jacobi_posSemidef hpositive _, actualJacobiCurvature_trace g hRic e (τ i)⟩
  exact finite_determinant_lower (flatGreenRoot t N) (scaledFlatGreen t N)
    (flatGreenRoot_square t N) (flatGreenRoot_transpose t N)
    (scaledFlatGreen_posSemidef t N) (scaledFlatGreen_nonneg t N) R hR hp
    (fun i => actualJacobiCurvature_mean_square_of_energy_three g o hRic hE (τ i)) hN
    (fun e => symmetricCurvatureKernel_one_sub_posDef _ _ (flatGreenRoot_square t N)
      (flatGreenRoot_transpose t N) hN _ (fun i => hp i e))

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_DirichletVectorSequence
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.ScalarPartition.instFintypeι _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p0 _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p1 _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p2 _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p3
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Jacobi.relativeDiscretePosition_zero _root_.OAI.PositiveEinsteinFour.Jacobi.entryCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The block Dirichlet operator on an actual vector sequence. -/
namespace PositiveEinsteinFour.Jacobi
open Matrix
noncomputable section

theorem scalarLift_mulVec {N : ℕ} (G : Matrix (Fin N) (Fin N) ℝ)
    (x : Fin 3 × Fin N → ℝ) (a : Fin 3) (i : Fin N) :
    (scalarLift G *ᵥ x) (a,i) = (G *ᵥ fun j => x (a,j)) i := by
  simp [Matrix.mulVec, dotProduct, scalarLift, Matrix.kronecker, Matrix.kroneckerMap,
    Matrix.one_apply, Fintype.sum_prod_type]

theorem blockDiagonal_mulVec {N : ℕ} (D : Fin N → NormalMatrix)
    (x : Fin 3 × Fin N → ℝ) (a : Fin 3) (i : Fin N) :
    (Matrix.blockDiagonal D *ᵥ x) (a,i) = (D i *ᵥ fun b => x (b,i)) a := by
  simp [Matrix.mulVec, dotProduct, Matrix.blockDiagonal_apply, Fintype.sum_prod_type]

theorem dirichletMatrix_eq_scalarLift {N : ℕ} (D : Fin N → NormalMatrix) :
    dirichletMatrix D = scalarLift (scalarDirichlet N 2) -
      Matrix.blockDiagonal (fun i => (2 : ℝ) • (1 : NormalMatrix) - D i) := by
  have h := scalarLift_sub_diagonal (N := N) 2 1
    (fun i => (2 : ℝ) • (1 : NormalMatrix) - D i)
  simpa only [one_smul, sub_sub_cancel] using h.symm

theorem dirichlet_mulVec_sequence {N : ℕ} (D : Fin N → NormalMatrix)
    (z : ℕ → Fin 3 → ℝ) (hzero : z 0 = 0) (hend : z (N + 1) = 0)
    (a : Fin 3) (i : Fin N) :
    (dirichletMatrix D *ᵥ fun p => z (p.2.val + 1) p.1) (a,i) =
      (D i *ᵥ z (i.val + 1)) a - z i.val a - z (i.val + 2) a := by
  rw [dirichletMatrix_eq_scalarLift, Matrix.sub_mulVec, Pi.sub_apply,
    scalarLift_mulVec, blockDiagonal_mulVec]
  have h := scalarDirichlet_apply_sequence 2 (fun n => z n a)
    (by rw [hzero]; rfl) (by rw [hend]; rfl) i
  rw [h, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul]
  ring

end
end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_DirichletEndpointInvertible
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.ScalarPartition.instFintypeι _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p0 _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p1 _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p2 _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p3
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Jacobi.relativeDiscretePosition_zero _root_.OAI.PositiveEinsteinFour.Jacobi.entryCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive discrete Dirichlet forms have nonsingular Jacobi endpoints. -/
namespace PositiveEinsteinFour.Jacobi
open Matrix
noncomputable section

theorem jacobi_endpoint_isUnit_of_dirichlet_posDef
    (D Y : ℕ → NormalMatrix) (N : ℕ)
    (h0 : Y 0 = 0) (h1 : Y 1 = 1)
    (hrec : ∀ i, Y (i + 2) = D i * Y (i + 1) - Y i)
    (hpos : (dirichletMatrix (fun i : Fin N => D i.val)).PosDef) :
    IsUnit (Y (N + 1)) := by
  have hker (v : Fin 3 → ℝ) (hv : Y (N + 1) *ᵥ v = 0) : v = 0 := by
    by_cases hN : N = 0
    · simpa [hN, h1] using hv
    have hNpos : 0 < N := Nat.pos_of_ne_zero hN
    let z : ℕ → Fin 3 → ℝ := fun i => Y i *ᵥ v
    let x : Fin 3 × Fin N → ℝ := fun p => z (p.2.val + 1) p.1
    have hz0 : z 0 = 0 := by simp [z,h0]
    have hzN : z (N + 1) = 0 := hv
    have hxzero : dirichletMatrix (fun i : Fin N => D i.val) *ᵥ x = 0 := by
      ext ⟨a,i⟩
      rw [show x = (fun p => z (p.2.val + 1) p.1) from rfl,
        dirichlet_mulVec_sequence _ z hz0 hzN]
      dsimp [z]
      rw [hrec, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, Pi.sub_apply]
      ring
    have hx : x = 0 := by
      by_contra hx
      have h := hpos.dotProduct_mulVec_pos hx
      rw [hxzero, dotProduct_zero] at h
      exact (lt_irrefl 0) h
    funext a
    have h := congrFun hx (a,⟨0,hNpos⟩)
    simpa [x,z,h1] using h
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro v w hvw
  have h : Y (N + 1) *ᵥ (v - w) = 0 := by
    rw [Matrix.mulVec_sub, hvw, sub_self]
  exact sub_eq_zero.mp (hker (v - w) h)

end
end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_DirichletLeadingPositive
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.ScalarPartition.instFintypeι _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p0 _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p1 _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p2 _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p3
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Jacobi.relativeDiscretePosition_zero _root_.OAI.PositiveEinsteinFour.Jacobi.entryCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positivity of the full discrete form controls every Jacobi endpoint. -/
namespace PositiveEinsteinFour.Jacobi
open Matrix
noncomputable section

theorem dirichlet_leading_posDef (D : ℕ → NormalMatrix) {n N : ℕ} (hn : n ≤ N)
    (hpos : (dirichletMatrix (fun i : Fin N => D i.val)).PosDef) :
    (dirichletMatrix (fun i : Fin n => D i.val)).PosDef := by
  let f : Fin 3 × Fin n → Fin 3 × Fin N := fun p => (p.1, Fin.castLE hn p.2)
  have hf : Function.Injective f := by
    intro p q h
    apply Prod.ext
    · exact congrArg (fun z : Fin 3 × Fin N => z.1) h
    · apply Fin.ext
      exact congrArg (fun z => z.2.val) h
  convert hpos.submatrix hf using 1
  all_goals try with_reducible_and_instances rfl
  ext ⟨a,i⟩ ⟨b,j⟩
  simp [dirichletMatrix, Matrix.submatrix, f]

theorem jacobi_prefix_isUnit_of_dirichlet_posDef
    (D Y : ℕ → NormalMatrix) (N : ℕ)
    (h0 : Y 0 = 0) (h1 : Y 1 = 1)
    (hrec : ∀ i, Y (i + 2) = D i * Y (i + 1) - Y i)
    (hpos : (dirichletMatrix (fun i : Fin N => D i.val)).PosDef)
    (i : ℕ) (hi : 1 ≤ i) (hiN : i ≤ N + 1) : IsUnit (Y i) := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
  exact jacobi_endpoint_isUnit_of_dirichlet_posDef D Y n h0 h1 hrec
    (dirichlet_leading_posDef D (by omega) hpos)

theorem curvatureDirichlet_determinant_of_posDef {N : ℕ} {t : ℝ} (ht : t ≠ 0)
    (R : ℕ → NormalMatrix) (hsym : ∀ i, (R i)ᵀ = R i)
    (hpos : (curvatureDirichlet t (fun i : Fin N => R (i.val + 1) - 1)).PosDef) :
    (curvatureDirichlet t (fun i : Fin N => R (i.val + 1) - 1)).det =
      (normalizedDiscrete R (t / (N + 1)) (N + 1)).det := by
  let D := fun i => (2 : ℝ) • (1 : NormalMatrix) - (t / (N + 1)) ^ 2 • R (i + 1)
  have hD : (dirichletMatrix (fun i : Fin N => D i.val)).PosDef := by
    simpa only [curvatureDirichlet_eq, add_sub_cancel] using hpos
  have hh : t / ((N : ℝ) + 1) ≠ 0 := div_ne_zero ht (by positivity)
  apply curvatureDirichlet_determinant ht R hsym
  intro i hi hiN
  exact (Matrix.isUnit_iff_isUnit_det _).mp
    (jacobi_prefix_isUnit_of_dirichlet_posDef D (normalizedDiscrete R (t / (N + 1))) N
      (normalizedDiscrete_zero _ _) (normalizedDiscrete_one _ hh)
      (normalizedDiscrete_recurrence R _) hD i hi hiN)

end
end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_FlatCurvatureDirichlet
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.ScalarPartition.instFintypeι _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual flat Green normalization of the curvature Dirichlet form. -/
namespace PositiveEinsteinFour.Jacobi
open Matrix Filter
noncomputable section

theorem scalarLift_smul {N : ℕ} (c : ℝ) (G : Matrix (Fin N) (Fin N) ℝ) :
    scalarLift (c • G) = c • scalarLift G := by
  ext ⟨a,i⟩ ⟨b,j⟩
  change (1 : NormalMatrix) a b * (c * G i j) = c * ((1 : NormalMatrix) a b * G i j)
  ring

theorem flat_curvatureDirichlet_eq {N : ℕ} (t : ℝ) (R : Fin N → NormalMatrix) :
    curvatureDirichlet t (fun i => R i - 1) =
      scalarLift (scalarDirichlet N 2) - (t / (N + 1)) ^ 2 • Matrix.blockDiagonal R := by
  rw [curvatureDirichlet_eq, scalarLift_sub_diagonal]
  simp only [add_sub_cancel]

theorem flat_curvatureDirichlet_normalized {N : ℕ} (t : ℝ) (R : Fin N → NormalMatrix) :
    scalarLift (scalarNormalizer (scalarDirichlet N 2)) *
      curvatureDirichlet t (fun i => R i - 1) *
      scalarLift (scalarNormalizer (scalarDirichlet N 2)) =
        1 - symmetricCurvatureKernel (flatGreenRoot t N) R := by
  rw [flat_curvatureDirichlet_eq, Matrix.mul_sub, Matrix.sub_mul,
    ← scalarLift_mul, ← scalarLift_mul,
    scalarNormalizer_normalizes (flatDirichlet_posDef N), scalarLift_one,
    Matrix.mul_smul, Matrix.smul_mul, symmetricCurvatureKernel,
    flatGreenRoot, scalarLift_smul, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.smul_mul, smul_smul]
  rw [pow_two]

theorem flat_curvatureDirichlet_posDef {N : ℕ} (t : ℝ) (R : Fin N → NormalMatrix)
    (hR : ∀ i, (R i).PosSemidef ∧ (R i).trace = 3)
    (hscalar : (1 - (3 : ℝ) • scaledFlatGreen t N).PosDef) :
    (curvatureDirichlet t (fun i => R i - 1)).PosDef := by
  let U := scalarNormalizer (scalarDirichlet N 2)
  have hn : U * scalarDirichlet N 2 * U = 1 :=
    scalarNormalizer_normalizes (flatDirichlet_posDef N)
  have hu : IsUnit (scalarLift U) := by
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    rw [det_scalarLift]
    exact (Matrix.isUnit_det_of_left_inverse hn).pow 3
  have hUt : Uᵀ = U := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (scalarNormalizer_posSemidef (scalarDirichlet N 2)).isHermitian.eq
  apply hu.posDef_star_left_conjugate_iff.mp
  rw [Matrix.star_eq_conjTranspose, scalarLift_conjTranspose U hUt,
    flat_curvatureDirichlet_normalized]
  exact symmetricCurvatureKernel_one_sub_posDef _ _ (flatGreenRoot_square t N)
    (flatGreenRoot_transpose t N) hscalar R hR

end
end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_FlatDirichletDeterminant
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.ScalarPartition.instFintypeι _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p0 _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p1 _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p2 _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p3
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Jacobi.relativeDiscretePosition_zero _root_.OAI.PositiveEinsteinFour.Jacobi.entryCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact normalization of the flat discrete determinant. -/
namespace PositiveEinsteinFour.Jacobi
open Matrix
noncomputable section

theorem flatDirichlet_det (N : ℕ) : (scalarDirichlet N 2).det = N + 1 := by
  let D := fun _ : ℕ => (2 : ℝ) • (1 : NormalMatrix)
  let Y := fun n : ℕ => (n : ℝ) • (1 : NormalMatrix)
  have hrec (i : ℕ) : Y (i + 2) = D i * Y (i + 1) - Y i := by
    dsimp [D,Y]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul]
    push_cast
    module
  have hu (i : ℕ) (hi : 1 ≤ i) (_ : i ≤ N + 1) : IsUnit (Y i).det := by
    simp only [Y, Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one]
    apply isUnit_iff_ne_zero.mpr
    positivity
  have h := dirichlet_determinant_eq_jacobi D Y N
    (fun _ => by simp [D]) (by simp [Y]) (by simp [Y]) hrec hu
  have he : dirichletMatrix (fun i : Fin N => D i.val) =
      scalarLift (scalarDirichlet N 2) := by
    simpa only [D, smul_zero, zero_smul, sub_zero] using
      (scalarLift_sub_diagonal (N := N) 2 0 (fun _ => (0 : NormalMatrix))).symm
  rw [he, det_scalarLift] at h
  simp only [Y, Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one,
    Nat.cast_add, Nat.cast_one] at h
  exact (Odd.pow_injective (by decide : Odd 3)) h

end
end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_FlatGreenDeterminant
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.ScalarPartition.instFintypeι _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact determinant normalization by the flat discrete Green matrix. -/
namespace PositiveEinsteinFour.Jacobi
open Matrix
noncomputable section

theorem flatGreen_curvature_factorization {N : ℕ} (t : ℝ) (R : Fin N → NormalMatrix) :
    1 - curvatureKernel (scaledFlatGreen t N) R =
      scalarLift (flatGreen N) * curvatureDirichlet t (fun i => R i - 1) := by
  have hflat : flatGreen N * scalarDirichlet N 2 = 1 := by
    rw [flatGreen_eq_inverse]
    exact Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp
      (flatDirichlet_posDef N).isUnit)
  rw [flat_curvatureDirichlet_eq, Matrix.mul_sub, ← scalarLift_mul, hflat,
    scalarLift_one, curvatureKernel, scaledFlatGreen, scalarLift_smul,
    Matrix.smul_mul, Matrix.mul_smul]

theorem flatGreen_curvature_det {N : ℕ} (t : ℝ) (R : Fin N → NormalMatrix) :
    ((N : ℝ) + 1) ^ 3 * (1 - curvatureKernel (scaledFlatGreen t N) R).det =
      (curvatureDirichlet t (fun i => R i - 1)).det := by
  rw [flatGreen_curvature_factorization, Matrix.det_mul, det_scalarLift,
    flatGreen_eq_inverse, Matrix.det_nonsing_inv, flatDirichlet_det, Ring.inverse_eq_inv]
  field_simp

theorem flatGreen_endpoint_det {N : ℕ} {t : ℝ} (ht : t ≠ 0)
    (R : ℕ → NormalMatrix) (hsym : ∀ i, (R i)ᵀ = R i)
    (hpos : (curvatureDirichlet t (fun i : Fin N => R (i.val + 1) - 1)).PosDef) :
    t ^ 3 * (1 - curvatureKernel (scaledFlatGreen t N)
      (fun i => R (i.val + 1))).det =
        (discretePosition R (t / (N + 1)) (N + 1)).det := by
  have hd := flatGreen_curvature_det t (fun i : Fin N => R (i.val + 1))
  rw [curvatureDirichlet_determinant_of_posDef ht R hsym hpos] at hd
  have hh : t / ((N : ℝ) + 1) ≠ 0 := div_ne_zero ht (by positivity)
  have he : (t / ((N : ℝ) + 1)) • normalizedDiscrete R (t / (N + 1)) (N + 1) =
      discretePosition R (t / (N + 1)) (N + 1) := by
    simp only [normalizedDiscrete, smul_smul, mul_inv_cancel₀ hh, one_smul]
  rw [← he, Matrix.det_smul, Fintype.card_fin, ← hd]
  field_simp

end
end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_FlatJacobiLimit
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.ScalarPartition.instFintypeι _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The flat-kernel determinants converge without a preconjugacy premise. -/
namespace PositiveEinsteinFour.Jacobi
open Matrix Filter
open scoped Matrix.Norms.L2Operator
noncomputable section

namespace RegularJacobi
variable {t : ℝ} (d : RegularJacobi t)

theorem flat_kernel_determinant_tendsto (ht : 0 < t)
    (htop : t < Real.pi / Real.sqrt 3)
    (hR : ∀ s, (d.R s).PosSemidef ∧ (d.R s).trace = 3) :
    Tendsto (fun N : ℕ => (1 - curvatureKernel (scaledFlatGreen t N)
      (fun i => d.R (((i.val + 1 : ℕ) : ℝ) * meshStep t N))).det)
      atTop (nhds ((d.J t).det / t ^ 3)) := by
  have hx := (continuous_id.matrix_det.tendsto (d.J t)).comp
    (d.endpoint_position_tendsto ht)
  apply (hx.div_const (t ^ 3)).congr'
  filter_upwards [scaledFlatGreen_eventually_below_one ht.le htop] with N hN
  have hp := flat_curvatureDirichlet_posDef t
    (fun i : Fin N => d.R (((i.val + 1 : ℕ) : ℝ) * meshStep t N))
    (fun i => hR _) hN
  have he := flatGreen_endpoint_det ht.ne' (meshCurvature d.R t N)
    (fun i => d.symmetric _) hp
  change (discretePosition (meshCurvature d.R t N) (meshStep t N) (N + 1)).det / t ^ 3 = _
  simp only [meshStep, meshCurvature] at he ⊢
  rw [← he]
  field_simp

end RegularJacobi
end
end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_JacobiKernelBound
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.ScalarPartition.instFintypeι _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed integrable bound for every positive normalized discrete determinant. -/
namespace PositiveEinsteinFour.Jacobi
open Matrix
noncomputable section

theorem flat_kernel_det_mem_Ioc {N : ℕ} (t : ℝ) (R : Fin N → NormalMatrix)
    (hR : ∀ i, (R i).PosSemidef ∧ (R i).trace = 3)
    (hscalar : (1 - (3 : ℝ) • scaledFlatGreen t N).PosDef) :
    (1 - curvatureKernel (scaledFlatGreen t N) R).det ∈ Set.Ioc (0 : ℝ) 1 := by
  let H := symmetricCurvatureKernel (flatGreenRoot t N) R
  have hp : (1 - H).PosDef := symmetricCurvatureKernel_one_sub_posDef _ _
    (flatGreenRoot_square t N) (flatGreenRoot_transpose t N) hscalar R hR
  have hH : H.PosSemidef := symmetricCurvatureKernel_posSemidef _
    (flatGreenRoot_transpose t N) R (fun i => (hR i).1)
  have he : (1 - H).det = (1 - curvatureKernel (scaledFlatGreen t N) R).det :=
    symmetricCurvatureKernel_det _ _ (flatGreenRoot_square t N) R
  rw [← he]
  refine ⟨hp.det_pos, det_le_one_of_trace_le_card hp.posSemidef ?_⟩
  rw [Matrix.trace_sub, Matrix.trace_one]
  linarith [hH.trace_nonneg]

end
end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_PositiveDeterminantOrder
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Determinant monotonicity for the positive matrices in radial comparison. -/
namespace PositiveEinsteinFour.Jacobi
open Matrix
open scoped MatrixOrder
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem one_le_det_one_add_posSemidef {P : Matrix ι ι ℝ} (hP : P.PosSemidef) :
    1 ≤ (1 + P).det := by
  let U := star hP.isHermitian.eigenvectorUnitary
  let φ := Unitary.conjStarAlgAut ℝ (Matrix ι ι ℝ) U
  have hd : φ P = diagonal hP.isHermitian.eigenvalues := by
    simpa only [Function.comp_def, RCLike.ofReal_real_eq_id, id_eq] using
      hP.isHermitian.conjStarAlgAut_star_eigenvectorUnitary
  have he : φ (1 + P) = diagonal (fun i => 1 + hP.isHermitian.eigenvalues i) := by
    rw [map_add, map_one, hd]
    ext i j
    by_cases hij : i = j <;> simp [hij]
  have hdet : (φ (1 + P)).det = (1 + P).det := by
    have hu := congrArg Matrix.det (Unitary.coe_star_mul_self U)
    simp only [Matrix.det_mul, Matrix.det_one] at hu
    dsimp only [φ]
    rw [Unitary.conjStarAlgAut_apply, Matrix.det_mul, Matrix.det_mul]
    calc
      _ = ((star U : Matrix ι ι ℝ).det * (U : Matrix ι ι ℝ).det) * (1 + P).det := by ring
      _ = _ := by rw [hu, one_mul]
  rw [← hdet, he, Matrix.det_diagonal]
  exact Finset.one_le_prod (fun i _ => by linarith [hP.eigenvalues_nonneg i])

theorem det_le_det_of_posDef_sub_posSemidef {A B : Matrix ι ι ℝ}
    (hA : A.PosDef) (hBA : (B - A).PosSemidef) : A.det ≤ B.det := by
  let U := CFC.sqrt A⁻¹
  have hU : Uᴴ = U := (CFC.sqrt_nonneg A⁻¹).posSemidef.isHermitian.eq
  have hsq : U * U = A⁻¹ := CFC.sqrt_mul_sqrt_self A⁻¹ hA.inv.posSemidef.nonneg
  have hn : U * A * U = 1 := by
    apply mul_eq_one_comm.mp
    rw [← Matrix.mul_assoc, hsq,
      Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hA.isUnit)]
  have hp : (U * (B - A) * U).PosSemidef := by
    simpa only [hU] using hBA.conjTranspose_mul_mul_same U
  have he : U * B * U = 1 + U * (B - A) * U := by
    rw [Matrix.mul_sub, Matrix.sub_mul, hn]
    abel
  have hd := one_le_det_one_add_posSemidef hp
  rw [← he, Matrix.det_mul, Matrix.det_mul] at hd
  have hn' := congrArg Matrix.det hn
  simp only [Matrix.det_mul, Matrix.det_one] at hn'
  calc
    A.det ≤ A.det * (U.det * B.det * U.det) := le_mul_of_one_le_right hA.det_pos.le hd
    _ = (U.det * A.det * U.det) * B.det := by ring
    _ = B.det := by rw [hn', one_mul]

end
end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_JacobiKernelLowerCap
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.ScalarPartition.instFintypeι _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The pointwise lower comparison with the scalar curvature cap three. -/
namespace PositiveEinsteinFour.Jacobi
open Matrix
noncomputable section

theorem symmetricCurvatureKernel_cap_posSemidef {N : ℕ}
    (S G : Matrix (Fin N) (Fin N) ℝ) (hS : S * S = G) (hSt : Sᵀ = S)
    (R : Fin N → NormalMatrix) (hR : ∀ i, (R i).PosSemidef ∧ (R i).trace = 3) :
    ((3 : ℝ) • scalarLift G - symmetricCurvatureKernel S R).PosSemidef := by
  have hc := blockDiagonal_posSemidef (fun i => (3 : ℝ) • (1 : NormalMatrix) - R i)
    (fun i => three_sub_posSemidef (hR i).1 (hR i).2)
  have he : Matrix.blockDiagonal (fun i => (3 : ℝ) • (1 : NormalMatrix) - R i) =
      (3 : ℝ) • 1 - Matrix.blockDiagonal R := by
    ext ⟨a,i⟩ ⟨b,j⟩
    by_cases hij : i = j
    · subst j
      simp [Matrix.blockDiagonal_apply, Matrix.one_apply]
    · simp [Matrix.blockDiagonal_apply, hij]
  rw [he] at hc
  have hp := hc.conjTranspose_mul_mul_same (scalarLift S)
  simpa only [scalarLift_conjTranspose S hSt, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, ← scalarLift_mul, hS,
    symmetricCurvatureKernel] using hp

theorem curvatureKernel_determinant_lower_cap {N : ℕ}
    (S G : Matrix (Fin N) (Fin N) ℝ) (hS : S * S = G) (hSt : Sᵀ = S)
    (R : Fin N → NormalMatrix) (hR : ∀ i, (R i).PosSemidef ∧ (R i).trace = 3)
    (hscalar : (1 - (3 : ℝ) • G).PosDef) :
    (1 - (3 : ℝ) • G).det ^ 3 ≤ (1 - curvatureKernel G R).det := by
  have hp : ((1 - symmetricCurvatureKernel S R) - scalarLift (1 - (3 : ℝ) • G)).PosSemidef := by
    rw [scalarLift_sub_three]
    convert symmetricCurvatureKernel_cap_posSemidef S G hS hSt R hR using 1
    all_goals try with_reducible_and_instances rfl
    abel
  have h := det_le_det_of_posDef_sub_posSemidef (scalarLift_posDef hscalar) hp
  rwa [det_scalarLift, symmetricCurvatureKernel_det S G hS R] at h

end
end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_LowerVolumeIntegral
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact integral of the refined lower-volume comparison kernel. -/
namespace PositiveEinsteinFour.VolumeConstants
open MeasureTheory
noncomputable section

theorem integral_square_sine :
    (∫ u in (0 : ℝ)..1, u ^ 2 * Real.sin (Real.pi * u)) =
      (Real.pi ^ 2 - 4) / Real.pi ^ 3 := by
  let F := fun u : ℝ => -u ^ 2 * Real.cos (Real.pi * u) / Real.pi +
    2 * u * Real.sin (Real.pi * u) / Real.pi ^ 2 +
    2 * Real.cos (Real.pi * u) / Real.pi ^ 3
  have hd (u : ℝ) : HasDerivAt F (u ^ 2 * Real.sin (Real.pi * u)) u := by
    have hs := (Real.hasDerivAt_sin (Real.pi * u)).comp u ((hasDerivAt_id u).const_mul Real.pi)
    have hc := (Real.hasDerivAt_cos (Real.pi * u)).comp u ((hasDerivAt_id u).const_mul Real.pi)
    refine ((((((hasDerivAt_id u).pow 2).neg.mul hc).div_const Real.pi).add
      (((((hasDerivAt_id u).const_mul 2).mul hs).div_const (Real.pi ^ 2)))).add
      ((hc.const_mul 2).div_const (Real.pi ^ 3))).congr_deriv ?_
    · simp only [Function.comp_apply, Pi.neg_apply, Pi.pow_apply, id_eq]
      field_simp [Real.pi_ne_zero]
      ring
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u)
    ((by fun_prop : Continuous (fun u : ℝ => u ^ 2 * Real.sin (Real.pi * u))).intervalIntegrable 0 1)
  rw [h]
  dsimp [F]
  simp only [one_pow, mul_one, Real.cos_pi, Real.sin_pi, mul_zero, zero_mul, Real.cos_zero,
    zero_pow (by decide : 2 ≠ 0), zero_div]
  field_simp
  ring

theorem integral_lowerVolumeKernel :
    (∫ u in (0 : ℝ)..1, lowerVolumeKernel u) =
      2 * (Real.pi ^ 2 - 4) / 9 + ∫ u in (0 : ℝ)..1, lowerKernel u := by
  have h1 : IntervalIntegrable (fun u : ℝ => (2 * Real.pi ^ 3 / 9) * u ^ 2 *
      Real.sin (Real.pi * u)) volume 0 1 := (by fun_prop : Continuous _).intervalIntegrable _ _
  have h2 : IntervalIntegrable lowerKernel volume 0 1 :=
    (by unfold lowerKernel; fun_prop : Continuous _).intervalIntegrable _ _
  change (∫ u in (0 : ℝ)..1, ((2 * Real.pi ^ 3 / 9) * u ^ 2 * Real.sin (Real.pi * u) +
    lowerKernel u)) = _
  rw [intervalIntegral.integral_add h1 h2]
  congr 1
  simp_rw [mul_assoc]
  rw [intervalIntegral.integral_const_mul, integral_square_sine]
  field_simp

theorem integral_lowerVolumeKernel_gt :
    (4 / 3 : ℝ) < ∫ u in (0 : ℝ)..1, lowerVolumeKernel u := by
  rw [integral_lowerVolumeKernel]
  exact analytic_lower_margin

end
end PositiveEinsteinFour.VolumeConstants

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarGreenLimit
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.ScalarPartition.instFintypeι _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The scalar flat-kernel determinant converges to sin(theta)/theta. -/
namespace PositiveEinsteinFour.Jacobi
open Matrix Filter
noncomputable section

theorem tendsto_of_cube_tendsto {α : Type*} {l : Filter α} {f : α → ℝ} {a : ℝ}
    (h : Tendsto (fun x => f x ^ 3) l (nhds (a ^ 3))) : Tendsto f l (nhds a) := by
  have ho : Odd 3 := by decide
  apply tendsto_order.mpr
  constructor
  · intro b hb
    filter_upwards [(tendsto_order.mp h).1 (b ^ 3) (ho.pow_lt_pow.mpr hb)] with x hx
    exact ho.pow_lt_pow.mp hx
  · intro b hb
    filter_upwards [(tendsto_order.mp h).2 (b ^ 3) (ho.pow_lt_pow.mpr hb)] with x hx
    exact ho.pow_lt_pow.mp hx

theorem scalarGreen_reference_factorization (t : ℝ) (N : ℕ) :
    1 - (3 : ℝ) • scaledFlatGreen t N =
      flatGreen N * referenceMatrix (Real.sqrt 3 * t) N := by
  have hf : flatGreen N * scalarDirichlet N 2 = 1 := by
    rw [flatGreen_eq_inverse]
    exact Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp
      (flatDirichlet_posDef N).isUnit)
  rw [referenceMatrix_sqrt_three, Matrix.mul_sub, hf, Matrix.mul_smul,
    Matrix.mul_one, scaledFlatGreen, smul_smul]

theorem scalarGreen_reference_det (t : ℝ) (N : ℕ) :
    (1 - (3 : ℝ) • scaledFlatGreen t N).det =
      (referenceMatrix (Real.sqrt 3 * t) N).det / ((N : ℝ) + 1) := by
  rw [scalarGreen_reference_factorization, Matrix.det_mul, flatGreen_eq_inverse,
    Matrix.det_nonsing_inv, flatDirichlet_det, Ring.inverse_eq_inv]
  ring

theorem scalarGreen_determinant_tendsto {t : ℝ} (ht : 0 < t)
    (htop : t < Real.pi / Real.sqrt 3) :
    Tendsto (fun N : ℕ => (1 - (3 : ℝ) • scaledFlatGreen t N).det) atTop
      (nhds (Real.sin (Real.sqrt 3 * t) / (Real.sqrt 3 * t))) := by
  have hθ : 0 < Real.sqrt 3 * t := mul_pos (Real.sqrt_pos.mpr (by norm_num)) ht
  have hθπ : Real.sqrt 3 * t < Real.pi := by
    have h := (lt_div_iff₀ (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3))).mp htop
    nlinarith
  have hc : Tendsto (fun N : ℕ =>
      ((Real.sqrt 3 * t / (N + 1)) * (referenceMatrix (Real.sqrt 3 * t) N).det) ^ 3)
      atTop (nhds (Real.sin (Real.sqrt 3 * t) ^ 3)) := by
    simpa only [mul_pow] using reference_determinant_tendsto hθ hθπ
  have h := (tendsto_of_cube_tendsto hc).div_const (Real.sqrt 3 * t)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ext N
  rw [scalarGreen_reference_det]
  field_simp

end
end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_SineLogPolynomial
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An explicit comparison function for the lower-volume sine remainder. -/
namespace PositiveEinsteinFour.Jacobi
noncomputable section

theorem sineLogPolynomial_hasDerivAt (x : ℝ) :
    HasDerivAt sineLogPolynomial (sineLogRate x) x := by
  convert (((hasDerivAt_id x).pow 2).div_const 6 |>.add
    (((hasDerivAt_id x).pow 4).div_const 180)).add
    (((hasDerivAt_id x).pow 6).div_const 2835) using 1
  all_goals try with_reducible_and_instances rfl
  all_goals first | rfl | (dsimp [sineLogRate]; ring)

theorem sineCotPolynomial_hasDerivAt (x : ℝ) :
    HasDerivAt sineCotPolynomial (-2 * x / 3 - 4 * x ^ 3 / 45 - 12 * x ^ 5 / 945) x := by
  convert (((hasDerivAt_const x (1 : ℝ)).sub
    (((hasDerivAt_id x).pow 2).div_const 3)).sub
    (((hasDerivAt_id x).pow 4).div_const 45)).sub
    ((((hasDerivAt_id x).pow 6).const_mul 2).div_const 945) using 1
  all_goals try with_reducible_and_instances rfl
  all_goals first | rfl | (dsimp; ring)

theorem sineLogWronskian_hasDerivAt (x : ℝ) :
    HasDerivAt sineLogWronskian
      (Real.exp (-sineLogPolynomial x) * sineLogResidual x * Real.sin x) x := by
  have he := ((sineLogPolynomial_hasDerivAt x).neg).exp
  have hw := ((sineCotPolynomial_hasDerivAt x).mul (Real.hasDerivAt_sin x)).sub
    ((hasDerivAt_id x).mul (Real.hasDerivAt_cos x))
  refine (he.mul hw).congr_deriv ?_
  · dsimp [sineCotPolynomial, sineLogRate, sineLogResidual]
    ring

theorem sineLogWronskian_nonneg {x : ℝ} (hx : 0 ≤ x) (hxπ : x ≤ Real.pi) :
    0 ≤ sineLogWronskian x := by
  have hm : MonotoneOn sineLogWronskian (Set.Icc 0 Real.pi) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
    · exact (continuous_iff_continuousAt.mpr
        (fun s => (sineLogWronskian_hasDerivAt s).continuousAt)).continuousOn
    · intro s hs
      exact (sineLogWronskian_hasDerivAt s).hasDerivWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      have hs0 : 0 ≤ s := hs.1.le
      have hr : 0 ≤ sineLogResidual s := by unfold sineLogResidual; positivity
      exact mul_nonneg (mul_nonneg (Real.exp_pos _).le hr)
        (Real.sin_nonneg_of_nonneg_of_le_pi hs.1.le hs.2.le)
  have h := hm (by simp [Real.pi_pos.le]) ⟨hx,hxπ⟩ hx
  simpa [sineLogWronskian, sineLogPolynomial, sineCotPolynomial] using h

end
end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_SineLogRemainder
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A logarithmic sine bound supplying the strict volume correction. -/
namespace PositiveEinsteinFour.Jacobi
open Filter Set
open scoped _root_.Topology
noncomputable section

private theorem weightedSinc_hasDerivAt {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt weightedSinc
      (-(Real.exp (sineLogPolynomial x) *
        (sineCotPolynomial x * Real.sin x - x * Real.cos x)) / x ^ 2) x := by
  have h := ((sineLogPolynomial_hasDerivAt x).exp).mul
    ((Real.hasDerivAt_sin x).div (hasDerivAt_id x) hx)
  have he : weightedSinc =ᶠ[𝓝 x] (fun y => Real.exp (sineLogPolynomial y) * (Real.sin y / y)) := by
    filter_upwards [isClosed_singleton.isOpen_compl.mem_nhds hx] with y hy
    exact congrArg (fun r => Real.exp (sineLogPolynomial y) * r) (Real.sinc_of_ne_zero hy)
  convert h.congr_of_eventuallyEq he using 1
  all_goals try with_reducible_and_instances rfl
  dsimp [sineLogRate, sineCotPolynomial]
  field_simp
  ring

theorem sineLogPolynomial_le_neg_log {x : ℝ} (hx : 0 < x) (hxπ : x < Real.pi) :
    sineLogPolynomial x ≤ -Real.log (Real.sin x / x) := by
  have hcontinuous : Continuous weightedSinc :=
    (Real.continuous_exp.comp (continuous_iff_continuousAt.mpr
      (fun s => (sineLogPolynomial_hasDerivAt s).continuousAt))).mul Real.continuous_sinc
  have hm : AntitoneOn weightedSinc (Icc 0 x) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _) hcontinuous.continuousOn
    · intro s hs
      rw [interior_Icc] at hs
      exact (weightedSinc_hasDerivAt hs.1.ne').hasDerivWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      have hW := sineLogWronskian_nonneg hs.1.le (hs.2.trans hxπ).le
      have hB : 0 ≤ sineCotPolynomial s * Real.sin s - s * Real.cos s := by
        exact (mul_nonneg_iff_of_pos_left (Real.exp_pos _)).mp hW
      exact div_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr (mul_nonneg (Real.exp_pos _).le hB)) (sq_nonneg s)
  have hq := hm (by simp [hx.le]) (by simp [hx.le]) hx.le
  have hs : 0 < Real.sin x / x := div_pos (Real.sin_pos_of_pos_of_lt_pi hx hxπ) hx
  have hle : Real.sin x / x ≤ Real.exp (-sineLogPolynomial x) := by
    have h' : Real.exp (sineLogPolynomial x) * (Real.sin x / x) ≤ 1 := by
      simpa [weightedSinc, sineLogPolynomial, Real.sinc_of_ne_zero hx.ne'] using hq
    calc
      _ ≤ 1 / Real.exp (sineLogPolynomial x) :=
        (le_div_iff₀ (Real.exp_pos _)).mpr (by simpa only [mul_comm] using h')
      _ = _ := by rw [Real.exp_neg, one_div]
  have hl := (Real.log_le_iff_le_exp hs).mpr hle
  linarith

theorem sine_log_remainder_lower {x : ℝ} (hx : 0 < x) (hxπ : x < Real.pi) :
    (x / Real.pi) ^ 4 / 2 + (x / Real.pi) ^ 6 / 3 ≤
      -Real.log (Real.sin x / x) - x ^ 2 / 6 := by
  have hp : (157 / 50 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d2]
  have hp4 : 90 ≤ Real.pi ^ 4 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 157 / 50) hp 4
    norm_num at h
    linarith
  have hp6 : 945 ≤ Real.pi ^ 6 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 157 / 50) hp 6
    norm_num at h
    linarith
  have h4 : (x / Real.pi) ^ 4 / 2 ≤ x ^ 4 / 180 := by
    rw [div_pow, div_div]
    exact div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)
  have h6 : (x / Real.pi) ^ 6 / 3 ≤ x ^ 6 / 2835 := by
    rw [div_pow, div_div]
    exact div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)
  have h := sineLogPolynomial_le_neg_log hx hxπ
  unfold sineLogPolynomial at h
  linarith

end
end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_WeylEstimates06
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.ScalarPartition.instFintypeι _root_.OAI.PositiveEinsteinFour.Geometry.oneFormC0_complete _root_.OAI.PositiveEinsteinFour.Geometry.oneFormCoexactSpectralFinite _root_.OAI.PositiveEinsteinFour.Geometry.oneFormEigenIndex_countable _root_.OAI.PositiveEinsteinFour.Geometry.scalarBaseEigenIndex_countable _root_.OAI.PositiveEinsteinFour.Geometry.scalarBaseSpectralSpaceFinite _root_.OAI.PositiveEinsteinFour.Geometry.smoothHarmonicNegative_finite _root_.OAI.PositiveEinsteinFour.Geometry.smoothHarmonicPositive_finite _root_.OAI.PositiveEinsteinFour.Geometry.twoFormEigenIndexCountable _root_.OAI.PositiveEinsteinFour.Geometry.twoFormSmoothEigenFinite _root_.OAI.PositiveEinsteinFour.Geometry.twoFormSpectralSpaceFinite _root_.OAI.PositiveEinsteinFour.Geometry.twoFormWeitzenbockKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Averaging the lower polar integral over the actual frame probability. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Matrix MeasureTheory Set Metric
open scoped Manifold ContDiff _root_.Topology ENNReal
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem measurable_actualBallRadialMass (g : SmoothMetric M) (hRic : RicciThree g) (R : ℝ) :
    Measurable (actualBallRadialMass g hRic R) := by
  have h := ENNReal.measurable_ofReal.comp
    (actualJacobiJ_joint_continuous g hRic).matrix_det.abs.measurable
  exact (h.comp measurable_swap).lintegral_prod_right'

theorem actualBallRadialMass_subtype (g : SmoothMetric M) (hRic : RicciThree g)
    (R : ℝ) (e : FrameBundle g) :
    (∫⁻ r : Ioi (0 : ℝ),
      (if r.val < R then ENNReal.ofReal |((actualJacobiSolution g hRic e).J r.val).det| else 0)
      ∂((volume : Measure ℝ).comap Subtype.val)) = actualBallRadialMass g hRic R e := by
  let F : ℝ → ℝ≥0∞ := fun r =>
    if r < R then ENNReal.ofReal |((actualJacobiSolution g hRic e).J r).det| else 0
  change (∫⁻ r : Ioi (0 : ℝ), F r.val ∂((volume : Measure ℝ).comap Subtype.val)) = _
  rw [lintegral_subtype_comap measurableSet_Ioi F, ← lintegral_indicator measurableSet_Ioi]
  rw [actualBallRadialMass, ← lintegral_indicator measurableSet_Ioo]
  apply lintegral_congr
  intro r
  by_cases h0 : 0 < r
  · rw [Set.indicator_of_mem (show r ∈ Ioi (0 : ℝ) from h0)]
    by_cases hR : r < R
    · rw [Set.indicator_of_mem (show r ∈ Ioo (0 : ℝ) R from ⟨h0,hR⟩)]
      exact ite_eq_left hR
    · rw [Set.indicator_of_notMem (fun h => hR h.2)]
      exact ite_eq_right hR
  · rw [Set.indicator_of_notMem (show r ∉ Ioi (0 : ℝ) from h0),
      Set.indicator_of_notMem (fun h => h0 h.1)]

theorem exponential_ball_integral_radial_mass (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) (e : FrameBundle g)
    (he : e ∈ o.positive) (R : ℝ) :
    (∫⁻ v in ball 0 R, ENNReal.ofReal (frameExponentialJacobian g o e v)) =
      polarAngularMass * ∫⁻ q : Directions,
        actualBallRadialMass g hRic R
          (e.rotate (orientedToOrthogonal (directionOrientedMatrix q))) ∂sphereMeasure := by
  rw [exponential_ball_integral_radial g o hRic e he]
  simp_rw [actualBallRadialMass_subtype]

variable [MeasurableSpace M] [BorelSpace M] [Nonempty M] [SecondCountableTopology M]

theorem lower_canonical_radial_mass_le_volume (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) (R : ℝ)
    (hinj : ∀ e ∈ o.positive, InjOn (frameExponential g o e) (ball 0 R)) :
    (riemannianChartFactor * polarAngularMass) *
      (∫⁻ e, actualBallRadialMass g hRic R e ∂canonicalFrameMeasure g o) ≤ volumeMeasure g univ := by
  have hc : riemannianChartFactor * polarAngularMass ≠ ⊤ := by
    apply ENNReal.mul_ne_top _ polarAngularMass_ne_top
    unfold riemannianChartFactor
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.coe_ne_top
  have hs (e : FrameBundle g) (he : e ∈ o.positive) :
      (riemannianChartFactor * polarAngularMass) *
        (∫⁻ q : Directions, actualBallRadialMass g hRic R
          (e.rotate (orientedToOrthogonal (directionOrientedMatrix q))) ∂sphereMeasure) ≤
      volumeMeasure g univ := by
    have h := exponential_ball_integral_le_volume g o e R (hinj e he)
    rw [exponential_ball_integral_radial_mass g o hRic e he R, ← mul_assoc] at h
    exact h
  have h := lintegral_mono_ae ((canonicalFrameMeasure_supported g o).mono hs)
  rw [lintegral_const_mul' _ _ hc, canonicalFrame_lintegral_sphere_rotations g o _
    (measurable_actualBallRadialMass g hRic R), lintegral_const,
    show canonicalFrameMeasure g o univ = 1 from measure_univ, mul_one] at h
  exact h

end
end PositiveEinsteinFour.Geometry
end

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GeodesicGeometry12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Dominated convergence for the actual averaged lower Jacobi comparison. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix MeasureTheory Jacobi Filter
open scoped Manifold ContDiff Matrix.Norms.Frobenius
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M]

theorem actualFlatKernelDeterminant_continuous (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) (t : ℝ) (N : ℕ) :
    Continuous (actualFlatKernelDeterminant g t N) := by
  have hR (i : Fin N) : Continuous (fun e : FrameBundle g =>
      actualJacobiCurvature g e (((i.val + 1 : ℕ) : ℝ) * meshStep t N)) :=
    actualJacobiCurvature_frame_continuous g o hRic _
  exact (continuous_const.sub (continuous_const.mul
    ((continuous_pi hR).matrix_blockDiagonal))).matrix_det

omit [MeasurableSpace M] [BorelSpace M] [Nonempty M] [SecondCountableTopology M] in
theorem actualFlatKernelDeterminant_tendsto (g : SmoothMetric M) (hRic : RicciThree g)
    (hpositive : HasPositiveSectionalCurvature g) (e : FrameBundle g)
    {t : ℝ} (ht : 0 < t) (htop : t < Real.pi / Real.sqrt 3) :
    Tendsto (fun N => actualFlatKernelDeterminant g t N e) atTop
      (nhds (((actualJacobiSolution g hRic e).J t).det / t ^ 3)) := by
  have hR : ∀ s, ((actualRegularJacobi g hRic e t).R s).PosSemidef ∧
      ((actualRegularJacobi g hRic e t).R s).trace = 3 := by
    intro s
    rw [actualRegularJacobi_R]
    exact ⟨actual_jacobi_posSemidef hpositive _, actualJacobiCurvature_trace g hRic e s⟩
  simpa only [actualFlatKernelDeterminant, actualRegularJacobi_R, actualRegularJacobi_J] using
    (actualRegularJacobi g hRic e t).flat_kernel_determinant_tendsto ht htop hR

theorem actualFlatKernelDeterminant_integral_tendsto (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g)
    (hpositive : HasPositiveSectionalCurvature g)
    {t : ℝ} (ht : 0 < t) (htop : t < Real.pi / Real.sqrt 3) :
    Tendsto (fun N => ∫ e, actualFlatKernelDeterminant g t N e ∂canonicalFrameMeasure g o)
      atTop (nhds (∫ e, ((actualJacobiSolution g hRic e).J t).det / t ^ 3
        ∂canonicalFrameMeasure g o)) := by
  have hbound : ∀ᶠ N : ℕ in atTop, ∀ᵐ e ∂canonicalFrameMeasure g o,
      ‖actualFlatKernelDeterminant g t N e‖ ≤ 1 := by
    filter_upwards [scaledFlatGreen_eventually_below_one ht.le htop] with N hN
    refine Eventually.of_forall fun e => ?_
    have hb := flat_kernel_det_mem_Ioc t
      (fun i : Fin N => actualJacobiCurvature g e (((i.val + 1 : ℕ) : ℝ) * meshStep t N))
      (fun i => ⟨actual_jacobi_posSemidef hpositive _,
        actualJacobiCurvature_trace g hRic e _⟩) hN
    simpa only [actualFlatKernelDeterminant, Real.norm_eq_abs, abs_of_pos hb.1] using hb.2
  exact tendsto_integral_filter_of_dominated_convergence (fun _ : FrameBundle g => (1 : ℝ))
    (Eventually.of_forall fun N => (actualFlatKernelDeterminant_continuous g o hRic t N).aestronglyMeasurable)
    hbound (integrable_const 1)
    (Eventually.of_forall fun e => actualFlatKernelDeterminant_tendsto g hRic hpositive e ht htop)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Constant-curvature Jacobi fields for the round branch of model
identification. All coefficients are the actual metric curvature. -/

namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Jacobi Angular
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.L2Operator
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem actualFirstConjugateTime_eq_pi_of_weyl_zero (hRic : RicciThree g)
    (hplus : ∀ c, plusWeyl g c (o.frame c) = 0)
    (hminus : ∀ c, minusWeyl g c (o.frame c) = 0)
    (e : FrameBundle g) (he : e ∈ o.positive) :
    actualFirstConjugateTime g hRic e = Real.pi := by
  apply le_antisymm (actualFirstConjugateTime_le_pi g hRic e)
  by_contra hnot
  have hlt : actualFirstConjugateTime g hRic e < Real.pi := lt_of_not_ge hnot
  apply actualFirstConjugateTime_singular g hRic e
  rw [(actualJacobi_eq_sine_of_weyl_zero hRic hplus hminus e he _).1]
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
  exact isUnit_iff_ne_zero.mpr (pow_ne_zero _
    (Real.sin_pos_of_pos_of_lt_pi (actualFirstConjugateTime_pos g hRic e) hlt).ne')

end
end PositiveEinsteinFour.Geometry
end


section

/-! No actual conjugate point occurs below pi/sqrt(3). -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Jacobi Matrix Filter
open scoped Manifold ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem actualJacobi_determinant_lower_cap (g : SmoothMetric M) (hRic : RicciThree g)
    (hpositive : HasPositiveSectionalCurvature g) (e : FrameBundle g)
    {t : ℝ} (ht : 0 < t) (htop : t < Real.pi / Real.sqrt 3) :
    (Real.sin (Real.sqrt 3 * t) / (Real.sqrt 3 * t)) ^ 3 ≤
      ((actualJacobiSolution g hRic e).J t).det / t ^ 3 := by
  apply le_of_tendsto_of_tendsto ((scalarGreen_determinant_tendsto ht htop).pow 3)
    (actualFlatKernelDeterminant_tendsto g hRic hpositive e ht htop)
  filter_upwards [scaledFlatGreen_eventually_below_one ht.le htop] with N hN
  exact curvatureKernel_determinant_lower_cap _ _ (flatGreenRoot_square t N)
    (flatGreenRoot_transpose t N) _
    (fun i => ⟨actual_jacobi_posSemidef hpositive _, actualJacobiCurvature_trace g hRic e _⟩) hN

theorem actualJacobi_determinant_pos_below_sqrt_three (g : SmoothMetric M)
    (hRic : RicciThree g) (hpositive : HasPositiveSectionalCurvature g) (e : FrameBundle g)
    {t : ℝ} (ht : 0 < t) (htop : t < Real.pi / Real.sqrt 3) :
    0 < ((actualJacobiSolution g hRic e).J t).det := by
  have hθ : 0 < Real.sqrt 3 * t := mul_pos (Real.sqrt_pos.mpr (by norm_num)) ht
  have hθπ : Real.sqrt 3 * t < Real.pi := by
    have h := (lt_div_iff₀ (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3))).mp htop
    nlinarith
  have hp := pow_pos (div_pos (Real.sin_pos_of_pos_of_lt_pi hθ hθπ) hθ) 3
  have hd := hp.trans_le (actualJacobi_determinant_lower_cap g hRic hpositive e ht htop)
  have h := (lt_div_iff₀ (pow_pos ht 3)).mp hd
  simpa only [zero_mul] using h

theorem actualJacobi_isUnit_below_sqrt_three (g : SmoothMetric M) (hRic : RicciThree g)
    (hpositive : HasPositiveSectionalCurvature g) (e : FrameBundle g)
    {t : ℝ} (ht : 0 < t) (htop : t < Real.pi / Real.sqrt 3) :
    IsUnit ((actualJacobiSolution g hRic e).J t) :=
  (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr
    (actualJacobi_determinant_pos_below_sqrt_three g hRic hpositive e ht htop).ne')

end
end PositiveEinsteinFour.Geometry
end


section

/-! The continuous lower Jacobi determinant comparison at total Weyl energy three. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix MeasureTheory Jacobi Filter
open scoped Manifold ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M]

theorem actual_jacobi_average_lower_normalized (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) (hpositive : HasPositiveSectionalCurvature g)
    (hE : (∫ x, plusNorm o x ^ 2 + minusNorm o x ^ 2 ∂normalizedVolume g) = 3)
    {t : ℝ} (ht : 0 < t) (htop : t < Real.pi / Real.sqrt 3) :
    Real.exp ((5 / 6 : ℝ) * Real.log (Real.sin (Real.sqrt 3 * t) / (Real.sqrt 3 * t)) -
      t ^ 2 / 12) ≤
        ∫ e, ((actualJacobiSolution g hRic e).J t).det / t ^ 3 ∂canonicalFrameMeasure g o := by
  have hθ : 0 < Real.sqrt 3 * t := mul_pos (Real.sqrt_pos.mpr (by norm_num)) ht
  have hθπ : Real.sqrt 3 * t < Real.pi := by
    have h := (lt_div_iff₀ (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3))).mp htop
    nlinarith
  have hs : 0 < Real.sin (Real.sqrt 3 * t) / (Real.sqrt 3 * t) :=
    div_pos (Real.sin_pos_of_pos_of_lt_pi hθ hθπ) hθ
  have hlog := (scalarGreen_determinant_tendsto ht htop).log hs.ne'
  have htrace := (scaledFlatGreen_trace_tendsto t).div_const 2
  have hleft : Tendsto (fun N : ℕ => Real.exp ((5 / 6 : ℝ) *
      Real.log (1 - (3 : ℝ) • scaledFlatGreen t N).det -
        (scaledFlatGreen t N).trace / 2)) atTop
      (nhds (Real.exp ((5 / 6 : ℝ) *
        Real.log (Real.sin (Real.sqrt 3 * t) / (Real.sqrt 3 * t)) - t ^ 2 / 12))) := by
    have ha := (hlog.const_mul (5 / 6 : ℝ)).sub htrace
    convert (Real.continuous_exp.tendsto _).comp ha using 1
    all_goals try with_reducible_and_instances rfl
    congr 2
    ring_nf
  apply le_of_tendsto_of_tendsto hleft
    (actualFlatKernelDeterminant_integral_tendsto g o hRic hpositive ht htop)
  filter_upwards [actual_finite_jacobi_determinant_lower g o hRic hpositive hE t ht.le htop]
    with N hN
  exact hN (fun i => ((i.val + 1 : ℕ) : ℝ) * meshStep t N)

theorem actual_jacobi_average_lower (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) (hpositive : HasPositiveSectionalCurvature g)
    (hE : (∫ x, plusNorm o x ^ 2 + minusNorm o x ^ 2 ∂normalizedVolume g) = 3)
    {t : ℝ} (ht : 0 < t) (htop : t < Real.pi / Real.sqrt 3) :
    t ^ 3 * Real.exp ((5 / 6 : ℝ) *
      Real.log (Real.sin (Real.sqrt 3 * t) / (Real.sqrt 3 * t)) - t ^ 2 / 12) ≤
        ∫ e, ((actualJacobiSolution g hRic e).J t).det ∂canonicalFrameMeasure g o := by
  have h := actual_jacobi_average_lower_normalized g o hRic hpositive hE ht htop
  rw [integral_div] at h
  simpa only [mul_comm] using (le_div_iff₀ (pow_pos ht 3)).mp h

end
end PositiveEinsteinFour.Geometry
end


section

/-! All points of the open round normal ball have genuine local exponential
charts, including its center. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Set
open scoped Manifold ContDiff _root_.Topology
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem frameExponential_round_localChart (hRic : RicciThree g)
    (hplus : ∀ c, plusWeyl g c (o.frame c) = 0)
    (hminus : ∀ c, minusWeyl g c (o.frame c) = 0)
    (e : FrameBundle g) (he : e ∈ o.positive) (v : FourSpace)
    (hv : ‖v‖ < Real.pi) :
    ∃ C : OpenPartialHomeomorph FourSpace M,
      v ∈ C.source ∧ EqOn C (frameExponential g o e) C.source := by
  by_cases hz : v = 0
  · subst v
    exact frameExponential_localChart g o e
  let q : Directions := ⟨‖v‖⁻¹ • v, by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)]⟩
  have hrad : ‖v‖ • q.val = v := by
    change ‖v‖ • (‖v‖⁻¹ • v) = v
    rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hz), one_smul]
  have hf : e.rotate (orientedToOrthogonal (directionOrientedMatrix q)) ∈ o.positive :=
    frameRotate_oriented_positive o e he (directionOrientedMatrix q)
  have hp : (q, ‖v‖) ∈ framePolarDomain g hRic e := by
    refine ⟨norm_pos_iff.mpr hz, ?_⟩
    rw [actualFirstConjugateTime_eq_pi_of_weyl_zero hRic hplus hminus _ hf]
    exact hv
  obtain ⟨C, hC, heq⟩ := frameExponential_polar_localChart g o hRic e he q ‖v‖ hp
  exact ⟨C, hrad ▸ hC, heq⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! The genuine exponential pullback metric in the round branch. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Jacobi
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g}

private theorem round_jacobi_gram (a : ℝ) :
    (jacobiBlockMatrix 1 (a • (1 : NormalMatrix)))ᵀ *
      jacobiBlockMatrix 1 (a • (1 : NormalMatrix)) =
      jacobiBlockMatrix 1 (a ^ 2 • (1 : NormalMatrix)) := by
  have hblock (b : ℝ) : jacobiBlockMatrix 1 (b • (1 : NormalMatrix)) =
      Matrix.diagonal (Fin.cons 1 (fun _ : Fin 3 => b)) := by
    ext i j
    refine Fin.cases ?_ (fun i => ?_) i
    · refine Fin.cases ?_ (fun j => ?_) j
      · simp [jacobiBlockMatrix, Matrix.diagonal]
      · simp [jacobiBlockMatrix, Matrix.diagonal, Ne.symm (Fin.succ_ne_zero j)]
    · refine Fin.cases ?_ (fun j => ?_) j
      · simp [jacobiBlockMatrix, Matrix.diagonal]
      · simp [jacobiBlockMatrix, Matrix.diagonal, Matrix.one_apply]
  rw [hblock, Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, hblock]
  congr 1
  funext i
  refine Fin.cases ?_ (fun i => ?_) i <;> simp [pow_two]

theorem heatNormalMetric_first_of_weyl_zero (hRic : RicciThree g)
    (hplus : ∀ c, plusWeyl g c (o.frame c) = 0)
    (hminus : ∀ c, minusWeyl g c (o.frame c) = 0)
    (e : FrameBundle g) (he : e ∈ o.positive) (t : ℝ) (ht : 0 < t) :
    heatNormalMetric g o e (t • coordinateVector 0) =
      jacobiBlockMatrix 1 ((Real.sin t / t) ^ 2 • (1 : NormalMatrix)) := by
  let f := parallelFrameFlowMap g 0 t e
  let c := f.base
  have hf : f.base ∈ (chartAt FourSpace c).source := mem_chart_source FourSpace c
  have hx : frameExponential g o e (t • coordinateVector 0) = f.base :=
    frameExponential_first_ray g o e he t ht
  let E := frameChartMatrix g c f
  let H := metricInChart g c (chartAt FourSpace c f.base)
  let B := jacobiBlockMatrix 1 (t⁻¹ • (actualJacobiSolution g hRic e).J t)
  have hN : Eᵀ * H * E = 1 := frameChartMatrix_normalizes g c f hf
  have hD := (frameExponential_hasFDerivAt g o hRic c e he t ht hf).fderiv
  have hcol (i : Fin 4) :
      WithLp.ofLp (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) (E * B)
        (coordinateVector i)) = fun k => (E * B) k i := by
    change (E * B) *ᵥ Pi.single i 1 = _
    exact Matrix.mulVec_single_one _ _
  have hGram : heatNormalMetric g o e (t • coordinateVector 0) = Bᵀ * B := by
    ext i j
    rw [heatNormalMetric_chart_pairing g o e c _ (hx ▸ hf), hD]
    rw [hcol, hcol]
    rw [hx, ← heat_matrix_congruence_pairing]
    change ((E * B)ᵀ * H * (E * B)) i j = (Bᵀ * B) i j
    have hmat : (E * B)ᵀ * H * (E * B) = Bᵀ * B := by
      rw [Matrix.transpose_mul]
      calc
        _ = Bᵀ * (Eᵀ * H * E) * B := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hN, Matrix.mul_one]
    exact congrArg (fun A : Mat4 => A i j) hmat
  rw [hGram]
  have hB : B = jacobiBlockMatrix 1 ((Real.sin t / t) • (1 : NormalMatrix)) := by
    dsimp only [B]
    rw [(actualJacobi_eq_sine_of_weyl_zero hRic hplus hminus e he t).1, smul_smul]
    congr 2
    ring
  rw [hB, round_jacobi_gram]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The explicit positive correction to the continuous lower radial bound. -/
namespace PositiveEinsteinFour.Jacobi
noncomputable section

theorem sine_exponential_lower_refined {x : ℝ} (hx : 0 < x) (hxπ : x < Real.pi) :
    (Real.sin x / x) * (1 + ((x / Real.pi) ^ 4 / 2 + (x / Real.pi) ^ 6 / 3) / 6) ≤
      Real.exp ((5 / 6 : ℝ) * Real.log (Real.sin x / x) - x ^ 2 / 36) := by
  have hs : 0 < Real.sin x / x := div_pos (Real.sin_pos_of_pos_of_lt_pi hx hxπ) hx
  have hr := sine_log_remainder_lower hx hxπ
  have he : (5 / 6 : ℝ) * Real.log (Real.sin x / x) - x ^ 2 / 36 =
      Real.log (Real.sin x / x) + (-Real.log (Real.sin x / x) - x ^ 2 / 6) / 6 := by ring
  rw [he, Real.exp_add, Real.exp_log hs]
  apply mul_le_mul_of_nonneg_left _ hs.le
  have h := Real.add_one_le_exp ((-Real.log (Real.sin x / x) - x ^ 2 / 6) / 6)
  linarith

end
end PositiveEinsteinFour.Jacobi

namespace PositiveEinsteinFour.Geometry
open EinsteinFour Jacobi Matrix MeasureTheory
open scoped Manifold ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M]

theorem actual_jacobi_average_lower_refined (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) (hpositive : HasPositiveSectionalCurvature g)
    (hE : (∫ x, plusNorm o x ^ 2 + minusNorm o x ^ 2 ∂normalizedVolume g) = 3)
    {t : ℝ} (ht : 0 < t) (htop : t < Real.pi / Real.sqrt 3) :
    t ^ 3 * (Real.sin (Real.sqrt 3 * t) / (Real.sqrt 3 * t)) *
      (1 + ((Real.sqrt 3 * t / Real.pi) ^ 4 / 2 +
        (Real.sqrt 3 * t / Real.pi) ^ 6 / 3) / 6) ≤
      ∫ e, ((actualJacobiSolution g hRic e).J t).det ∂canonicalFrameMeasure g o := by
  have hθ : 0 < Real.sqrt 3 * t := mul_pos (Real.sqrt_pos.mpr (by norm_num)) ht
  have hθπ : Real.sqrt 3 * t < Real.pi := by
    have h := (lt_div_iff₀ (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3))).mp htop
    nlinarith
  have h := mul_le_mul_of_nonneg_left (sine_exponential_lower_refined hθ hθπ)
    (pow_nonneg ht.le 3)
  have he : (Real.sqrt 3 * t) ^ 2 / 36 = t ^ 2 / 12 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num)]
    ring
  rw [he, ← mul_assoc] at h
  exact h.trans (actual_jacobi_average_lower g o hRic hpositive hE ht htop)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Real-valued lower polar integration with the actual normalization factor. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Matrix MeasureTheory Set Filter Metric
open scoped Manifold ContDiff _root_.Topology ENNReal
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem actualJacobi_truncated_eq_det_below_sqrt_three (g : SmoothMetric M)
    (hRic : RicciThree g) (hpositive : HasPositiveSectionalCurvature g)
    (e : FrameBundle g) {r : ℝ} (hr : 0 < r) (htop : r < Real.pi / Real.sqrt 3) :
    (actualRegularJacobi g hRic e r).truncatedDensity =
      ((actualJacobiSolution g hRic e).J r).det := by
  rw [← actualJacobi_abs_det_eq_truncatedDensity g hRic e r hr
    (fun s hs hsr => actualJacobi_isUnit_below_sqrt_three g hRic hpositive e hs (hsr.trans_lt htop)),
    abs_of_pos (actualJacobi_determinant_pos_below_sqrt_three g hRic hpositive e hr htop)]

variable [MeasurableSpace M] [BorelSpace M] [Nonempty M]

theorem canonical_actualBallRadialMass_eq (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) (hpositive : HasPositiveSectionalCurvature g)
    {R : ℝ} (hR : 0 ≤ R) (hRtop : R ≤ Real.pi / Real.sqrt 3) :
    (∫⁻ e, actualBallRadialMass g hRic R e ∂canonicalFrameMeasure g o) =
      ENNReal.ofReal (∫ r in (0 : ℝ)..R, ∫ e,
        (actualRegularJacobi g hRic e r).truncatedDensity ∂canonicalFrameMeasure g o) := by
  have hmeas := ENNReal.measurable_ofReal.comp
    (actualJacobiJ_joint_continuous g hRic).matrix_det.abs.measurable
  have hswap : (∫⁻ e, actualBallRadialMass g hRic R e ∂canonicalFrameMeasure g o) =
      ∫⁻ r in Ioo (0 : ℝ) R, ∫⁻ e, ENNReal.ofReal
        |((actualJacobiSolution g hRic e).J r).det| ∂canonicalFrameMeasure g o :=
    lintegral_lintegral_swap (hmeas.comp measurable_swap).aemeasurable
  rw [hswap, intervalIntegral.integral_of_le hR, integral_Ioc_eq_integral_Ioo]
  have hi := (actualJacobi_average_integrableOn g o hRic 0 R).mono_set Ioo_subset_Icc_self
  have hn : ∀ᵐ r ∂volume.restrict (Ioo (0 : ℝ) R),
      0 ≤ ∫ e, (actualRegularJacobi g hRic e r).truncatedDensity ∂canonicalFrameMeasure g o := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    exact actualJacobi_average_nonneg g o hRic r hr.1.le
  rw [ofReal_integral_eq_lintegral_ofReal hi hn]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
  have he (e : FrameBundle g) : |((actualJacobiSolution g hRic e).J r).det| =
      (actualRegularJacobi g hRic e r).truncatedDensity :=
    actualJacobi_abs_det_eq_truncatedDensity g hRic e r hr.1
      (fun s hs hsr => actualJacobi_isUnit_below_sqrt_three g hRic hpositive e hs
        (hsr.trans_lt (hr.2.trans_le hRtop)))
  simp_rw [he]
  exact (ofReal_integral_eq_lintegral_ofReal (actualJacobiDensity_integrable g o hRic r)
    (Eventually.of_forall fun e => (actualRegularJacobi g hRic e r).truncatedDensity_nonneg hr.1.le)).symm

variable [SecondCountableTopology M]

theorem lower_polar_volume_of_injective_ball (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) (hpositive : HasPositiveSectionalCurvature g)
    {R : ℝ} (hR : 0 ≤ R) (hRtop : R ≤ Real.pi / Real.sqrt 3)
    (hinj : ∀ e ∈ o.positive, InjOn (frameExponential g o e) (ball 0 R)) :
    riemannianChartFactor.toReal * (2 * Real.pi ^ 2) *
      (∫ r in (0 : ℝ)..R, ∫ e, (actualRegularJacobi g hRic e r).truncatedDensity
        ∂canonicalFrameMeasure g o) ≤ totalVolume g := by
  have h := lower_canonical_radial_mass_le_volume g o hRic R hinj
  rw [canonical_actualBallRadialMass_eq g o hRic hpositive hR hRtop, polarAngularMass_eq] at h
  have hfin : volumeMeasure g univ ≠ ⊤ := ne_of_lt (actual_finitePositiveVolume g).finite
  have hb := ENNReal.toReal_mono hfin h
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 2 * Real.pi ^ 2),
    ENNReal.toReal_ofReal (intervalIntegral.integral_nonneg hR (fun r hr =>
      actualJacobi_average_nonneg g o hRic r hr.1)), totalVolume] using hb

end
end PositiveEinsteinFour.Geometry
end


section

/-! Elementary metric identities for the actual unit sphere. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Set
open scoped RealInnerProductSpace
noncomputable section

theorem roundDistance_eq_angle (p q : RoundSphere4) :
    roundDistance p q = InnerProductGeometry.angle p.val q.val := by
  simp only [roundDistance, InnerProductGeometry.angle, p.property, q.property,
    one_mul, div_one]

theorem roundDistance_nonneg (p q : RoundSphere4) : 0 ≤ roundDistance p q :=
  Real.arccos_nonneg _

theorem roundDistance_le_pi (p q : RoundSphere4) : roundDistance p q ≤ Real.pi :=
  Real.arccos_le_pi _

theorem roundDistance_comm (p q : RoundSphere4) : roundDistance p q = roundDistance q p := by
  simp only [roundDistance, real_inner_comm]

theorem roundDistance_self (p : RoundSphere4) : roundDistance p p = 0 := by
  simp [roundDistance, p.property]

theorem roundDistance_eq_zero_iff (p q : RoundSphere4) : roundDistance p q = 0 ↔ p = q := by
  constructor
  · intro h
    apply Subtype.ext
    exact InnerProductGeometry.eq_of_angle_eq_zero_of_norm_eq
      ((roundDistance_eq_angle p q).symm.trans h) (p.property.trans q.property.symm)
  · rintro rfl
    exact roundDistance_self _

theorem round_inner_bounds (p q : RoundSphere4) : inner ℝ p.val q.val ∈ Icc (-1 : ℝ) 1 := by
  have h := abs_real_inner_le_norm p.val q.val
  rw [p.property, q.property, one_mul] at h
  exact abs_le.mp h

theorem cos_roundDistance (p q : RoundSphere4) :
    Real.cos (roundDistance p q) = inner ℝ p.val q.val :=
  Real.cos_arccos (round_inner_bounds p q).1 (round_inner_bounds p q).2

theorem round_tangent_pairing_bound (p q : RoundSphere4)
    (w : EuclideanSpace ℝ (Fin 5)) (hw : inner ℝ q.val w = 0) :
    |inner ℝ p.val w| ≤ Real.sin (roundDistance p q) * ‖w‖ := by
  let v := p.val - (inner ℝ p.val q.val) • q.val
  have hi : inner ℝ v w = inner ℝ p.val w := by
    simp [v, inner_sub_left, real_inner_smul_left, hw]
  have hn : ‖v‖ = Real.sin (roundDistance p q) := by
    apply (sq_eq_sq₀ (norm_nonneg _) (Real.sin_nonneg_of_nonneg_of_le_pi
      (roundDistance_nonneg p q) (roundDistance_le_pi p q))).mp
    rw [Real.sin_sq, cos_roundDistance]
    dsimp [v]
    rw [norm_sub_pow_two_real, norm_smul, Real.norm_eq_abs, q.property,
      mul_one, sq_abs, p.property, real_inner_smul_right]
    ring
  have h := abs_real_inner_le_norm v w
  rwa [hi, hn] at h

end
end PositiveEinsteinFour.Geometry
end


section

/-! The refined radial estimate in the manuscript's unit-interval variable. -/
namespace PositiveEinsteinFour.VolumeConstants
noncomputable section

theorem lowerVolumeKernel_rescale {u : ℝ} (hu : u ≠ 0) :
    lowerVolumeKernel u =
      (2 * (Real.pi / Real.sqrt 3)) *
        (((Real.pi / Real.sqrt 3) * u) ^ 3 *
          (Real.sin (Real.pi * u) / (Real.pi * u)) *
          (1 + (u ^ 4 / 2 + u ^ 6 / 3) / 6)) := by
  have hs : Real.sqrt 3 ^ 4 = 9 := by
    rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul, Real.sq_sqrt (by norm_num)]
    norm_num
  unfold lowerVolumeKernel lowerKernel
  field_simp [hu, Real.pi_ne_zero, ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3))]
  rw [hs]
  ring

end
end PositiveEinsteinFour.VolumeConstants

namespace PositiveEinsteinFour.Geometry
open EinsteinFour Jacobi Matrix MeasureTheory VolumeConstants
open scoped Manifold ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M] [SecondCountableTopology M]

theorem actual_scaled_jacobi_lower (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) (hpositive : HasPositiveSectionalCurvature g)
    (hE : (∫ x, plusNorm o x ^ 2 + minusNorm o x ^ 2 ∂normalizedVolume g) = 3)
    {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    lowerVolumeKernel u ≤ (2 * (Real.pi / Real.sqrt 3)) *
      ∫ e, (actualRegularJacobi g hRic e ((Real.pi / Real.sqrt 3) * u)).truncatedDensity
        ∂canonicalFrameMeasure g o := by
  have hR : 0 < Real.pi / Real.sqrt 3 := div_pos Real.pi_pos (Real.sqrt_pos.mpr (by norm_num))
  have ht : 0 < (Real.pi / Real.sqrt 3) * u := mul_pos hR hu
  have htop : (Real.pi / Real.sqrt 3) * u < Real.pi / Real.sqrt 3 := by
    nlinarith
  have heθ : Real.sqrt 3 * ((Real.pi / Real.sqrt 3) * u) = Real.pi * u := by
    field_simp
  have hediv : (Real.pi * u) / Real.pi = u := by field_simp
  have h := mul_le_mul_of_nonneg_left
    (actual_jacobi_average_lower_refined g o hRic hpositive hE ht htop)
    (by positivity : 0 ≤ 2 * (Real.pi / Real.sqrt 3))
  rw [heθ, hediv, ← lowerVolumeKernel_rescale hu.ne'] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun e =>
    actualJacobi_truncated_eq_det_below_sqrt_three g hRic hpositive e ht htop

end
end PositiveEinsteinFour.Geometry
end


section

/-! The full radial/tangential metric formula of the actual exponential
in the constant-curvature branch. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Jacobi Angular
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise
noncomputable section
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

private theorem round_block_pairing (a : ℝ) (w z : FourSpace) :
    WithLp.ofLp w ⬝ᵥ (jacobiBlockMatrix 1 (a ^ 2 • (1 : NormalMatrix)) *ᵥ WithLp.ofLp z) =
      a ^ 2 * inner ℝ w z + (1 - a ^ 2) * w 0 * z 0 := by
  rw [jacobiBlockMatrix_mulVec]
  simp only [Matrix.smul_mulVec, Matrix.one_mulVec, one_mul]
  simp only [dotProduct, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
    Pi.smul_apply, smul_eq_mul, PiLp.inner_apply, RCLike.inner_apply,
    conj_trivial]
  simp only [Finset.univ_eq_empty, Finset.sum_empty]
  ring

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem frameExponential_round_first_pairing (hRic : RicciThree g)
    (hplus : ∀ c, plusWeyl g c (o.frame c) = 0)
    (hminus : ∀ c, minusWeyl g c (o.frame c) = 0)
    (e : FrameBundle g) (he : e ∈ o.positive) (t : ℝ) (ht : 0 < t) (w z : FourSpace) :
    g.inner (frameExponential g o e (t • coordinateVector 0))
      (mfderiv I4 I4 (frameExponential g o e) (t • coordinateVector 0) w)
      (mfderiv I4 I4 (frameExponential g o e) (t • coordinateVector 0) z) =
        (Real.sin t / t) ^ 2 * inner ℝ w z +
          (1 - (Real.sin t / t) ^ 2) * w 0 * z 0 := by
  have hp := heatNormalMetric_pairing g o e (t • coordinateVector 0)
    (WithLp.ofLp w) (WithLp.ofLp z)
  simp only [WithLp.toLp_ofLp] at hp
  rw [← hp, heatNormalMetric_first_of_weyl_zero hRic hplus hminus e he t ht]
  exact round_block_pairing _ w z

theorem frameExponential_round_pairing (hRic : RicciThree g)
    (hplus : ∀ c, plusWeyl g c (o.frame c) = 0)
    (hminus : ∀ c, minusWeyl g c (o.frame c) = 0)
    (e : FrameBundle g) (he : e ∈ o.positive) (q : Directions)
    (t : ℝ) (ht : 0 < t) (w z : FourSpace) :
    g.inner (frameExponential g o e (t • q.val))
      (mfderiv I4 I4 (frameExponential g o e) (t • q.val) w)
      (mfderiv I4 I4 (frameExponential g o e) (t • q.val) z) =
        (Real.sin t / t) ^ 2 * inner ℝ w z +
          (1 - (Real.sin t / t) ^ 2) * inner ℝ q.val w * inner ℝ q.val z := by
  let Q := directionOrientedMatrix q
  let L := orthogonalEuclideanIsometry (orientedToOrthogonal Q).val
    (orientedToOrthogonal Q).property
  let f := e.rotate (orientedToOrthogonal Q)
  have hf : f ∈ o.positive := frameRotate_oriented_positive o e he Q
  have hfirst : L (coordinateVector 0) = q.val := directionRotation_first q
  have hpoint : L (t • coordinateVector 0) = t • q.val := by rw [map_smul, hfirst]
  have hbase : frameExponential g o f (t • coordinateVector 0) =
      frameExponential g o e (t • q.val) := by
    rw [frameExponential_rotate]
    exact congrArg (frameExponential g o e) hpoint
  have hD (u : FourSpace) :
      mfderiv I4 I4 (frameExponential g o f) (t • coordinateVector 0) u =
        mfderiv I4 I4 (frameExponential g o e) (t • q.val) (L u) := by
    have h := frameExponential_rotate_mfderiv g o e Q (t • coordinateVector 0) u
    change _ = mfderiv I4 I4 (frameExponential g o e) (L (t • coordinateVector 0)) (L u) at h
    rwa [hpoint] at h
  have hzero (u : FourSpace) : (L.symm u) 0 = inner ℝ q.val u := by
    have h := L.inner_map_map (coordinateVector 0) (L.symm u)
    rw [hfirst, L.apply_symm_apply] at h
    simpa [PiLp.inner_apply, coordinateVector] using h.symm
  have hinner : inner ℝ (L.symm w) (L.symm z) = inner ℝ w z := by
    simpa only [L.apply_symm_apply] using
      (L.inner_map_map (L.symm w) (L.symm z)).symm
  have h := frameExponential_round_first_pairing hRic hplus hminus f hf t ht
    (L.symm w) (L.symm z)
  let B₁ : FourSpace →L[ℝ] FourSpace →L[ℝ] ℝ :=
    g.inner (frameExponential g o f (t • coordinateVector 0))
  let B₂ : FourSpace →L[ℝ] FourSpace →L[ℝ] ℝ :=
    g.inner (frameExponential g o e (t • q.val))
  let D₁ : FourSpace →L[ℝ] FourSpace :=
    mfderiv I4 I4 (frameExponential g o f) (t • coordinateVector 0)
  let D₂ : FourSpace →L[ℝ] FourSpace :=
    mfderiv I4 I4 (frameExponential g o e) (t • q.val)
  have hB : B₁ = B₂ := by
    dsimp only [B₁, B₂]
    rw [hbase]
  have hD' (u : FourSpace) : D₁ u = D₂ (L u) := hD u
  change B₁ (D₁ (L.symm w)) (D₁ (L.symm z)) = _ at h
  change B₂ (D₂ w) (D₂ z) = _
  rw [hB, hD', hD', L.apply_symm_apply, L.apply_symm_apply, hinner,
    hzero, hzero] at h
  exact h

end
end PositiveEinsteinFour.Geometry
end


section

/-! The differential bound for angular distance along a genuine sphere
curve. The two singular values are explicit. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Set
open scoped RealInnerProductSpace
noncomputable section

theorem round_inner_ne_endpoints (p q : RoundSphere4) (hpq : q ≠ p)
    (hanti : q ≠ antipode p) :
    inner ℝ p.val q.val ≠ -1 ∧ inner ℝ p.val q.val ≠ 1 := by
  constructor
  · intro h
    have heq := (inner_eq_neg_one_iff_of_norm_eq_one p.property q.property).mp h
    apply hanti
    apply Subtype.ext
    change q.val = -p.val
    simpa using congrArg Neg.neg heq.symm
  · intro h
    have heq := (inner_eq_one_iff_of_norm_eq_one p.property q.property).mp h
    exact hpq (Subtype.ext heq.symm)

theorem round_curve_tangent {u : ℝ → RoundSphere4} {t : ℝ}
    {w : EuclideanSpace ℝ (Fin 5)}
    (hu : HasDerivAt (fun s => (u s).val) w t) :
    inner ℝ (u t).val w = 0 := by
  have h := hu.inner ℝ hu
  have heq : (fun s => inner ℝ (u s).val (u s).val) = fun _ : ℝ => (1 : ℝ) := by
    funext s
    simp [(u s).property]
  rw [heq] at h
  have hz := h.unique (hasDerivAt_const t (1 : ℝ))
  rw [real_inner_comm (u t).val w] at hz
  linarith

theorem roundDistance_derivative_bound (p : RoundSphere4) {u : ℝ → RoundSphere4}
    {t : ℝ} {w : EuclideanSpace ℝ (Fin 5)}
    (hu : HasDerivAt (fun s => (u s).val) w t)
    (hpq : u t ≠ p) (hanti : u t ≠ antipode p) :
    DifferentiableAt ℝ (fun s => roundDistance p (u s)) t ∧
      |deriv (fun s => roundDistance p (u s)) t| ≤ ‖w‖ := by
  obtain ⟨hm, hp⟩ := round_inner_ne_endpoints p (u t) hpq hanti
  have hd := (Real.hasDerivAt_arccos hm hp).comp t
    ((hasDerivAt_const t p.val).inner ℝ hu)
  have hsin : 0 < Real.sin (roundDistance p (u t)) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · exact lt_of_le_of_ne (roundDistance_nonneg _ _)
        (fun h => hpq ((roundDistance_eq_zero_iff _ _).mp h.symm).symm)
    · apply lt_of_le_of_ne (roundDistance_le_pi _ _)
      intro h
      have hc := cos_roundDistance p (u t)
      rw [h, Real.cos_pi] at hc
      exact hm hc.symm
  have hsqrt : Real.sqrt (1 - inner ℝ p.val (u t).val ^ 2) =
      Real.sin (roundDistance p (u t)) := by
    rw [roundDistance, Real.sin_arccos]
  have hform : deriv (fun s => roundDistance p (u s)) t =
      -(inner ℝ p.val w / Real.sin (roundDistance p (u t))) := by
    change deriv (fun s => Real.arccos (inner ℝ p.val (u s).val)) t = _
    change deriv (Real.arccos ∘ fun s => inner ℝ p.val (u s).val) t = _
    rw [hd.deriv]
    simp only [inner_zero_left, hsqrt]
    ring
  refine ⟨hd.differentiableAt, ?_⟩
  rw [hform, abs_neg, abs_div, abs_of_pos hsin]
  exact (div_le_iff₀ hsin).mpr (by
    simpa only [mul_comm] using round_tangent_pairing_bound p (u t) w (round_curve_tangent hu))

end
end PositiveEinsteinFour.Geometry
end


section

/-! Angular distance is bounded by the parameter length of a unit-speed
sphere curve, allowing finitely many exceptional parameters. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Set
noncomputable section

private theorem roundDistance_curve_continuous (p : RoundSphere4) (u : ℝ → RoundSphere4)
    {a b : ℝ} (hu : ContinuousOn u (Icc a b)) :
    ContinuousOn (fun t => roundDistance p (u t)) (Icc a b) := by
  have hv : ContinuousOn (fun t => (u t).val) (Icc a b) :=
    continuous_subtype_val.comp_continuousOn hu
  have hi : ContinuousOn (fun t => inner ℝ p.val (u t).val) (Icc a b) :=
    continuousOn_const.inner hv
  change ContinuousOn (fun t => Real.arccos (inner ℝ p.val (u t).val)) (Icc a b)
  exact Real.continuous_arccos.comp_continuousOn hi

private theorem roundDistance_curve_deriv_bound (p : RoundSphere4) (u : ℝ → RoundSphere4)
    (t : ℝ) (hd : ∃ w : EuclideanSpace ℝ (Fin 5),
      HasDerivAt (fun s => (u s).val) w t ∧ ‖w‖ ≤ 1)
    (hregular : u t ≠ p ∧ u t ≠ antipode p) :
    DifferentiableAt ℝ (fun s => roundDistance p (u s)) t ∧
      deriv (fun s => roundDistance p (u s)) t ≤ 1 := by
  obtain ⟨w, hw, hn⟩ := hd
  obtain ⟨hD, hbound⟩ := roundDistance_derivative_bound p hw hregular.1 hregular.2
  exact ⟨hD, (le_abs_self _).trans (hbound.trans hn)⟩

theorem roundDistance_curve_sub_le (p : RoundSphere4) (u : ℝ → RoundSphere4)
    (a b : ℝ) (hab : a ≤ b) (E : Finset ℝ)
    (hu : ContinuousOn u (Icc a b))
    (hd : ∀ t ∈ Ioo a b, t ∉ E → ∃ w : EuclideanSpace ℝ (Fin 5),
      HasDerivAt (fun s => (u s).val) w t ∧ ‖w‖ ≤ 1)
    (hregular : ∀ t ∈ Ioo a b, t ∉ E → u t ≠ p ∧ u t ≠ antipode p) :
    roundDistance p (u b) - roundDistance p (u a) ≤ b - a := by
  have hc := roundDistance_curve_continuous p u hu
  have hD := fun t ht he => roundDistance_curve_deriv_bound p u t (hd t ht he)
    (hregular t ht he)
  have h := image_sub_le_mul_sub_of_deriv_le_off_finite E hab hc
    (fun t ht he => (hD t ht he).1) (fun t ht he => (hD t ht he).2)
  rwa [one_mul] at h

theorem roundDistance_curve_le (u : ℝ → RoundSphere4)
    (a b : ℝ) (hab : a ≤ b) (E : Finset ℝ)
    (hu : ContinuousOn u (Icc a b))
    (hd : ∀ t ∈ Ioo a b, t ∉ E → ∃ w : EuclideanSpace ℝ (Fin 5),
      HasDerivAt (fun s => (u s).val) w t ∧ ‖w‖ ≤ 1)
    (hregular : ∀ t ∈ Ioo a b, t ∉ E → u t ≠ u a ∧ u t ≠ antipode (u a)) :
    roundDistance (u a) (u b) ≤ b - a := by
  simpa only [roundDistance_self, sub_zero] using
    roundDistance_curve_sub_le (u a) u a b hab E hu hd hregular

end
end PositiveEinsteinFour.Geometry
end


section

/-! The energy-three strict volume refinement, with only the geometric
injectivity bound still explicit. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Jacobi Matrix MeasureTheory VolumeConstants Set Metric Filter
open scoped Manifold ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M] [SecondCountableTopology M]

theorem strict_lower_volume_of_injective_ball (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) (hpositive : HasPositiveSectionalCurvature g)
    (hE : (∫ x, plusNorm o x ^ 2 + minusNorm o x ^ 2 ∂normalizedVolume g) = 3)
    (hinj : ∀ e ∈ o.positive,
      InjOn (frameExponential g o e) (ball 0 (Real.pi / Real.sqrt 3))) :
    (1 / 2 : ℝ) < volumeRatio g / riemannianChartFactor.toReal := by
  let R : ℝ := Real.pi / Real.sqrt 3
  let F : ℝ → ℝ := fun r => ∫ e, (actualRegularJacobi g hRic e r).truncatedDensity
    ∂canonicalFrameMeasure g o
  have hR : 0 < R := div_pos Real.pi_pos (Real.sqrt_pos.mpr (by norm_num))
  have hFi : IntervalIntegrable F volume 0 R :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hR.le).mpr
      (actualJacobi_average_integrableOn g o hRic 0 R)
  have hFscaled : IntervalIntegrable (fun u => F (R * u)) volume 0 1 := by
    convert hFi.comp_mul_left (c := R) using 1 <;> first | (with_reducible_and_instances rfl) | (simp [hR.ne'])
  have hkernel : IntervalIntegrable lowerVolumeKernel volume 0 1 := by
    apply Continuous.intervalIntegrable
    unfold lowerVolumeKernel lowerKernel
    fun_prop
  have hae : ∀ᵐ u ∂volume.restrict (Icc (0 : ℝ) 1),
      lowerVolumeKernel u ≤ (2 * R) * F (R * u) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc,
      ae_restrict_of_ae (volume.ae_ne 0), ae_restrict_of_ae (volume.ae_ne 1)] with u hu h0 h1
    exact actual_scaled_jacobi_lower g o hRic hpositive hE
      (lt_of_le_of_ne hu.1 (Ne.symm h0)) (lt_of_le_of_ne hu.2 h1)
  have hi := intervalIntegral.integral_mono_ae_restrict (by norm_num : (0 : ℝ) ≤ 1)
    hkernel (hFscaled.const_mul (2 * R)) hae
  rw [intervalIntegral.integral_const_mul] at hi
  have hchange : (∫ r in (0 : ℝ)..R, F r) = R * ∫ u in (0 : ℝ)..1, F (R * u) := by
    simpa only [smul_eq_mul, mul_zero, mul_one] using
      (intervalIntegral.smul_integral_comp_mul_left (a := (0 : ℝ)) (b := 1) F R).symm
  have hstrict : (4 / 3 : ℝ) < 2 * ∫ r in (0 : ℝ)..R, F r := by
    rw [hchange]
    nlinarith [integral_lowerVolumeKernel_gt]
  have hvol := lower_polar_volume_of_injective_ball g o hRic hpositive hR.le le_rfl hinj
  have hk := riemannianChartFactor_toReal_pos
  have hpi := Real.pi_pos
  have hp2 : 0 < Real.pi ^ 2 := sq_pos_of_pos hpi
  have hnorm : (3 / 4 : ℝ) * (∫ r in (0 : ℝ)..R, F r) ≤
      volumeRatio g / riemannianChartFactor.toReal := by
    rw [volumeRatio, div_div]
    apply (le_div_iff₀ (mul_pos (by positivity : 0 < 8 * Real.pi ^ 2 / 3) hk)).mpr
    convert hvol using 1
    all_goals try with_reducible_and_instances rfl
    ring
  linarith

end
end PositiveEinsteinFour.Geometry
end


section

/-! The dimension-two branch reduces to the geometric injectivity bound. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix MeasureTheory Set Metric
open scoped Manifold ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem halfFlat_dimension_two_impossible_of_injective_ball (hRic : RicciThree g)
    (hpositive : HasPositiveSectionalCurvature g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hinj : ∀ e ∈ o.positive,
      InjOn (frameExponential g o e) (ball 0 (Real.pi / Real.sqrt 3))) :
    Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) ≠ 2 := by
  intro hdim
  obtain ⟨hV,hE⟩ := halfFlat_volume_energy_counts hRic hminus
  rw [hdim] at hV hE
  norm_num at hV hE
  have hplus : (∫ x, plusNorm o x ^ 2 ∂normalizedVolume g) = 3 := by
    rw [hV] at hE
    linarith
  have htotal : (∫ x, plusNorm o x ^ 2 + minusNorm o x ^ 2 ∂normalizedVolume g) = 3 := by
    have hz : ∀ x, minusNorm o x = 0 := fun x => (minusNorm_eq_zero_iff o x).mpr (hminus x)
    simpa only [hz, zero_pow (by decide : 2 ≠ 0), add_zero] using hplus
  have hstrict := strict_lower_volume_of_injective_ball g o hRic hpositive htotal hinj
  rw [hV] at hstrict
  norm_num at hstrict

theorem halfFlat_positive_harmonic_dimension_one_of_injective_ball (hRic : RicciThree g)
    (hpositive : HasPositiveSectionalCurvature g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hplus : ∃ x, plusWeyl g x (o.frame x) ≠ 0)
    (hinj : ∀ e ∈ o.positive,
      InjOn (frameExponential g o e) (ball 0 (Real.pi / Real.sqrt 3))) :
    Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1 :=
  (halfFlat_positive_harmonic_dimension_cases hRic hpositive hminus hplus).resolve_right
    (halfFlat_dimension_two_impossible_of_injective_ball hRic hpositive hminus hinj)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual sphere exponential and its continuous ambient formula.
This fixes the topology at the center of polar coordinates. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Set
open scoped _root_.Topology
noncomputable section

theorem roundSphereExponential_vector (v : FourSpace) :
    (roundSphereExponential v).val =
      WithLp.toLp 2 (Fin.cons (Real.cos ‖v‖) (fun i => Real.sinc ‖v‖ * v i)) := by
  by_cases hz : v = 0
  · subst v
    rw [roundSphereExponential_zero]
    ext i
    refine Fin.cases ?_ (fun i => ?_) i <;> simp [roundNorth]
  · rw [roundSphereExponential, dite_eq_right hz]
    ext i
    refine Fin.cases ?_ (fun i => ?_) i
    · rfl
    · change Real.sin ‖v‖ * (‖v‖⁻¹ * v i) = Real.sinc ‖v‖ * v i
      rw [Real.sinc_of_ne_zero (norm_ne_zero_iff.mpr hz)]
      ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The differential of the standard sphere exponential away from zero,
with the radial norm derivative justified from its squared norm. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Filter Set
open scoped _root_.Topology InnerProductSpace
noncomputable section

theorem round_norm_fderiv (v : FourSpace) (hv : v ≠ 0) (w : FourSpace) :
    fderiv ℝ (fun x : FourSpace => ‖x‖) v w = inner ℝ (‖v‖⁻¹ • v) w := by
  have hd : DifferentiableAt ℝ (fun x : FourSpace => ‖x‖) v :=
    (contDiffAt_norm ℝ hv : ContDiffAt ℝ 1 (fun x : FourSpace => ‖x‖) v).differentiableAt one_ne_zero
  have h := congrArg (fun D : FourSpace →L[ℝ] ℝ => D w)
    ((hd.hasFDerivAt.pow 2).unique (hasStrictFDerivAt_norm_sq v).hasFDerivAt)
  simp only [Nat.reduceSub, pow_one, _root_.smul_apply, smul_eq_mul,
    two_smul, add_apply, innerSL_apply_apply] at h
  rw [real_inner_smul_left]
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  apply (mul_left_cancel₀ hn)
  rw [← mul_assoc, mul_inv_cancel₀ hn, one_mul]
  linarith

theorem roundSphereExponential_differentiableAt (v : FourSpace) (hv : v ≠ 0) :
    DifferentiableAt ℝ (fun x : FourSpace => (roundSphereExponential x).val) v := by
  have hn : DifferentiableAt ℝ (fun x : FourSpace => ‖x‖) v :=
    (contDiffAt_norm ℝ hv : ContDiffAt ℝ 1 (fun x : FourSpace => ‖x‖) v).differentiableAt one_ne_zero
  have hs : DifferentiableAt ℝ (fun x : FourSpace => Real.sin ‖x‖ / ‖x‖) v := by
    simpa only [div_eq_mul_inv] using! hn.sin.mul (hn.inv (norm_ne_zero_iff.mpr hv))
  have htail : DifferentiableAt ℝ (fun x : FourSpace => (Real.sin ‖x‖ / ‖x‖) • x) v :=
    hs.smul differentiableAt_id
  have hF := roundSphereLinearInclusion.differentiableAt.comp v (hn.cos.prodMk htail)
  apply hF.congr_of_eventuallyEq
  filter_upwards [isOpen_compl_singleton.mem_nhds hv] with x hx
  rw [roundSphereExponential_vector, Real.sinc_of_ne_zero (norm_ne_zero_iff.mpr hx)]
  rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! The polar differential of the standard round exponential. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Filter Set
open scoped _root_.Topology InnerProductSpace
noncomputable section

theorem roundSphereExponential_fderiv (v : FourSpace) (hv : v ≠ 0) (w : FourSpace) :
    fderiv ℝ (fun x : FourSpace => (roundSphereExponential x).val) v w =
      roundSphereLinearInclusion
        (-Real.sin ‖v‖ * inner ℝ (‖v‖⁻¹ • v) w,
          ((Real.cos ‖v‖ - Real.sin ‖v‖ / ‖v‖) * inner ℝ (‖v‖⁻¹ • v) w) • (‖v‖⁻¹ • v) +
            (Real.sin ‖v‖ / ‖v‖) • w) := by
  have hn : HasFDerivAt (fun x : FourSpace => ‖x‖)
      (fderiv ℝ (fun x : FourSpace => ‖x‖) v) v :=
    ((contDiffAt_norm ℝ hv : ContDiffAt ℝ 1 (fun x : FourSpace => ‖x‖) v).differentiableAt one_ne_zero).hasFDerivAt
  have hi := (hasDerivAt_inv (norm_ne_zero_iff.mpr hv)).comp_hasFDerivAt v hn
  have hs := (hn.sin.mul hi).smul (hasFDerivAt_id v)
  have hF := roundSphereLinearInclusion.hasFDerivAt.comp v (hn.cos.prodMk hs)
  have heq : (fun x : FourSpace => (roundSphereExponential x).val) =ᶠ[𝓝 v]
      (fun x : FourSpace => roundSphereLinearInclusion
        (Real.cos ‖x‖, (Real.sin ‖x‖ * ‖x‖⁻¹) • x)) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hv] with x hx
    rw [roundSphereExponential_vector, Real.sinc_of_ne_zero (norm_ne_zero_iff.mpr hx)]
    simp only [roundSphereLinearInclusion, div_eq_mul_inv]
    rfl
  have hA := hF.congr_of_eventuallyEq heq
  rw [hA.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    add_apply, Function.comp_apply, Pi.mul_apply, id_eq,
    ContinuousLinearMap.smulRight_apply, _root_.smul_apply,
    smul_eq_mul, ContinuousLinearMap.id_apply]
  rw [round_norm_fderiv v hv w]
  congr 1
  apply Prod.ext
  · rfl
  · ext i
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    field_simp [norm_ne_zero_iff.mpr hv]
    ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The standard sphere's radial differential has exactly the metric
pairing supplied by the round Jacobi equation. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular
open scoped BigOperators InnerProductSpace
noncomputable section

theorem roundSphereLinearInclusion_inner (p r : ℝ × FourSpace) :
    inner ℝ (roundSphereLinearInclusion p) (roundSphereLinearInclusion r) =
      p.1 * r.1 + inner ℝ p.2 r.2 := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  rw [Fin.sum_univ_succ]
  change r.1 * p.1 + (∑ i : Fin 4, r.2 i * p.2 i) =
    p.1 * r.1 + (∑ i : Fin 4, r.2 i * p.2 i)
  ring

theorem roundSphere_radial_pairing (q : Directions) (t : ℝ) (w z : FourSpace) :
    inner ℝ
      (roundSphereLinearInclusion
        (-Real.sin t * inner ℝ q.val w,
          ((Real.cos t - Real.sin t / t) * inner ℝ q.val w) • q.val +
            (Real.sin t / t) • w))
      (roundSphereLinearInclusion
        (-Real.sin t * inner ℝ q.val z,
          ((Real.cos t - Real.sin t / t) * inner ℝ q.val z) • q.val +
            (Real.sin t / t) • z)) =
      (Real.sin t / t) ^ 2 * inner ℝ w z +
        (1 - (Real.sin t / t) ^ 2) * inner ℝ q.val w * inner ℝ q.val z := by
  rw [roundSphereLinearInclusion_inner]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
  have hq : inner ℝ q.val q.val = 1 := by
    rw [real_inner_self_eq_norm_sq, q.property, one_pow]
  rw [hq, real_inner_comm w q.val]
  have htrig := Real.sin_sq_add_cos_sq t
  linear_combination (inner ℝ w q.val * inner ℝ q.val z) * htrig

end
end PositiveEinsteinFour.Geometry
end


section

/-! Equality of the genuine manifold and standard sphere metrics in
normal coordinates. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Set
open scoped Manifold ContDiff _root_.Topology InnerProductSpace
noncomputable section
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem roundSphereMap_exponential (hRic : RicciThree g)
    (hplus : ∀ c, plusWeyl g c (o.frame c) = 0)
    (hminus : ∀ c, minusWeyl g c (o.frame c) = 0)
    (e : FrameBundle g) (he : e ∈ o.positive) (v : FourSpace)
    (hv : ‖v‖ ≤ Real.pi) :
    roundSphereMap g o e (roundSphereExponential v) = frameExponential g o e v := by
  by_cases hz : v = 0
  · subst v
    rw [roundSphereExponential_zero, roundSphereMap_north, frameExponential_zero]
  let q : Directions := ⟨‖v‖⁻¹ • v, by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)]⟩
  have hrad : ‖v‖ • q.val = v := by
    change ‖v‖ • (‖v‖⁻¹ • v) = v
    rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hz), one_smul]
  rw [← hrad, roundSphereExponential_radial _ (norm_nonneg _),
    roundSphereMap_polar hRic hplus hminus e he _ ⟨norm_nonneg _, hv⟩]

theorem frameExponential_round_metric_eq_sphere (hRic : RicciThree g)
    (hplus : ∀ c, plusWeyl g c (o.frame c) = 0)
    (hminus : ∀ c, minusWeyl g c (o.frame c) = 0)
    (e : FrameBundle g) (he : e ∈ o.positive) (v : FourSpace) (hv : v ≠ 0)
    (w z : FourSpace) :
    g.inner (frameExponential g o e v)
      (mfderiv I4 I4 (frameExponential g o e) v w)
      (mfderiv I4 I4 (frameExponential g o e) v z) =
      inner ℝ (fderiv ℝ (fun x : FourSpace => (roundSphereExponential x).val) v w)
        (fderiv ℝ (fun x : FourSpace => (roundSphereExponential x).val) v z) := by
  let q : Directions := ⟨‖v‖⁻¹ • v, by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]⟩
  have hrad : ‖v‖ • q.val = v := by
    change ‖v‖ • (‖v‖⁻¹ • v) = v
    rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv), one_smul]
  rw [roundSphereExponential_fderiv v hv w, roundSphereExponential_fderiv v hv z]
  change _ = inner ℝ
    (roundSphereLinearInclusion (-Real.sin ‖v‖ * inner ℝ q.val w,
      ((Real.cos ‖v‖ - Real.sin ‖v‖ / ‖v‖) * inner ℝ q.val w) • q.val +
        (Real.sin ‖v‖ / ‖v‖) • w))
    (roundSphereLinearInclusion (-Real.sin ‖v‖ * inner ℝ q.val z,
      ((Real.cos ‖v‖ - Real.sin ‖v‖ / ‖v‖) * inner ℝ q.val z) • q.val +
        (Real.sin ‖v‖ / ‖v‖) • z))
  rw [roundSphere_radial_pairing]
  have h := frameExponential_round_pairing hRic hplus hminus e he q ‖v‖
    (norm_pos_iff.mpr hv) w z
  rw [hrad] at h
  exact h

end
end PositiveEinsteinFour.Geometry
end


section

/-! The pointwise speed identity in the actual round exponential chart. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Set Filter Bundle
open scoped Manifold ContDiff _root_.Topology
noncomputable section
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem frameExponential_round_curve_speed (hRic : RicciThree g)
    (hplus : ∀ c, plusWeyl g c (o.frame c) = 0)
    (hminus : ∀ c, minusWeyl g c (o.frame c) = 0)
    (e : FrameBundle g) (he : e ∈ o.positive)
    {α : ℝ → FourSpace} {t : ℝ} (ha : DifferentiableAt ℝ α t)
    (hz : α t ≠ 0) :
    ‖deriv (fun s => (roundSphereExponential (α s)).val) t‖ =
      metricTangentNorm g (frameExponential g o e (α t))
        (mfderiv 𝓘(ℝ, ℝ) I4 (fun s => frameExponential g o e (α s)) t 1) := by
  have hsp := (roundSphereExponential_differentiableAt (α t) hz).hasFDerivAt.comp_hasDerivAt t
    ha.hasDerivAt
  dsimp only [Function.comp_def] at hsp
  have hm := mfderiv_comp t
    ((frameExponential_contMDiff g o e).mdifferentiable one_ne_zero (α t))
    ha.mdifferentiableAt
  have hDa : mfderiv 𝓘(ℝ, ℝ) I4 α t 1 = deriv α t := by
    have h : (fderiv ℝ α t) (1 : ℝ) = deriv α t := fderiv_apply_one_eq_deriv
    simpa only [mfderiv_eq_fderiv] using! h
  have hD : mfderiv 𝓘(ℝ, ℝ) I4 (fun s => frameExponential g o e (α s)) t 1 =
      mfderiv I4 I4 (frameExponential g o e) (α t) (deriv α t) := by
    have h := congrArg (fun D : ℝ →L[ℝ] FourSpace => D 1) hm
    exact h.trans (congrArg (mfderiv I4 I4 (frameExponential g o e) (α t)) hDa)
  let w : FourSpace := deriv α t
  have hh := frameExponential_round_metric_eq_sphere hRic hplus hminus e he (α t) hz w w
  have hn : ‖fderiv ℝ (fun x : FourSpace => (roundSphereExponential x).val) (α t) w‖ =
      metricTangentNorm g (frameExponential g o e (α t))
        (mfderiv I4 I4 (frameExponential g o e) (α t) w) := by
    rw [metricTangentNorm_eq_sqrt, hh]
    exact norm_eq_sqrt_real_inner _
  exact (congrArg norm hsp.deriv).trans (hn.trans
    (congrArg (metricTangentNorm g (frameExponential g o e (α t))) hD).symm)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Every point in the round branch lies on a minimizing segment from a
point to its unique antipodal endpoint. The resulting distance sum turns
one distance inequality for the sphere homeomorphism into equality. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Set Bundle
open scoped Manifold ContDiff _root_.Topology ENNReal
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

omit [T3Space M] [PreconnectedSpace M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [Nonempty M]
    [SecondCountableTopology M] in
theorem metricDistance_symm (g : SmoothMetric M) (x y : M) :
    metricDistance g x y = metricDistance g y x := by
  let : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩
  change (Manifold.riemannianEDist I4 x y).toReal = (Manifold.riemannianEDist I4 y x).toReal
  rw [Manifold.riemannianEDist_comm]

theorem round_antipodal_distance (hRic : RicciThree g)
    (hpositive : HasPositiveSectionalCurvature g)
    (hplus : ∀ c, plusWeyl g c (o.frame c) = 0)
    (hminus : ∀ c, minusWeyl g c (o.frame c) = 0)
    (e : FrameBundle g) (he : e ∈ o.positive) :
    metricDistance g e.base (roundAntipodalPoint g o e) = Real.pi := by
  have h := roundSphereMap_radial_distance hRic hpositive hplus hminus e he
    (antipode roundNorth)
  rw [roundSphereMap_south] at h
  simpa [antipode, roundNorth] using h

theorem round_antipodal_distance_sum (hRic : RicciThree g)
    (hpositive : HasPositiveSectionalCurvature g)
    (hplus : ∀ c, plusWeyl g c (o.frame c) = 0)
    (hminus : ∀ c, minusWeyl g c (o.frame c) = 0)
    (e : FrameBundle g) (he : e ∈ o.positive) (x : M) :
    metricDistance g e.base x + metricDistance g (roundAntipodalPoint g o e) x = Real.pi := by
  obtain ⟨p, rfl⟩ := roundSphereMap_surjective hRic hplus hminus e he x
  have hbase := roundSphereMap_radial_distance hRic hpositive hplus hminus e he p
  have hu := roundSphereMap_distance_south hRic hplus hminus e he p
  have hr : metricDistance g (roundAntipodalPoint g o e) (roundSphereMap g o e p) ≤
      Real.pi - Real.arccos (p.val 0) := by
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hu
    simpa only [metricDistance, ENNReal.toReal_ofReal
      (sub_nonneg.mpr (Real.arccos_le_pi _))] using hh
  have hl := metricDistance_triangle g e.base (roundSphereMap g o e p)
    (roundAntipodalPoint g o e)
  rw [round_antipodal_distance hRic hpositive hplus hminus e he,
    metricDistance_symm g (roundSphereMap g o e p) (roundAntipodalPoint g o e)] at hl
  linarith

omit [TopologicalSpace M] [ChartedSpace FourSpace M] [IsManifold I4 ∞ M]
    [T3Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [Nonempty M]
    [SecondCountableTopology M] [PreconnectedSpace M] in
theorem roundDistance_antipode_left (p q : RoundSphere4) :
    roundDistance (antipode p) q = Real.pi - roundDistance p q := by
  simp only [roundDistance, antipode, inner_neg_left, Real.arccos_neg]

omit [TopologicalSpace M] [ChartedSpace FourSpace M] [IsManifold I4 ∞ M]
    [T3Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [Nonempty M]
    [SecondCountableTopology M] [PreconnectedSpace M] in
theorem roundDistance_antipodal (p : RoundSphere4) :
    roundDistance p (antipode p) = Real.pi := by
  rw [roundDistance_comm, roundDistance_antipode_left, roundDistance_self, sub_zero]

theorem roundSphereMap_distance_eq_of_le (hRic : RicciThree g)
    (hpositive : HasPositiveSectionalCurvature g)
    (hplus : ∀ c, plusWeyl g c (o.frame c) = 0)
    (hminus : ∀ c, minusWeyl g c (o.frame c) = 0)
    (e : FrameBundle g) (he : e ∈ o.positive)
    (hle : ∀ p q : RoundSphere4, roundDistance p q ≤
      metricDistance g (roundSphereMap g o e p) (roundSphereMap g o e q)) :
    ∀ p q : RoundSphere4, metricDistance g (roundSphereMap g o e p)
      (roundSphereMap g o e q) = roundDistance p q := by
  intro p q
  let H := actualRoundHomeomorph hRic hpositive hplus hminus e he
  let f : FrameBundle g := ⟨H p, o.frame (H p)⟩
  have hf : f ∈ o.positive := o.frame_positive (H p)
  let r := H.symm (roundAntipodalPoint g o f)
  have hHr : H r = roundAntipodalPoint g o f := H.apply_symm_apply _
  have hs (x : RoundSphere4) : metricDistance g (H p) (H x) +
      metricDistance g (H r) (H x) = Real.pi := by
    rw [hHr]
    exact round_antipodal_distance_sum hRic hpositive hplus hminus f hf (H x)
  have hranti : r = antipode p := by
    have hsum := hs (antipode p)
    have hp := hle p (antipode p)
    have hr := hle r (antipode p)
    rw [roundDistance_antipodal] at hp
    have hz : roundDistance r (antipode p) = 0 := by
      have hn := roundDistance_nonneg r (antipode p)
      change Real.pi ≤ metricDistance g (H p) (H (antipode p)) at hp
      change roundDistance r (antipode p) ≤ metricDistance g (H r) (H (antipode p)) at hr
      linarith
    exact (roundDistance_eq_zero_iff _ _).mp hz
  have hsum := hs q
  rw [hranti] at hsum
  have hq := hle (antipode p) q
  rw [roundDistance_antipode_left] at hq
  have hl := hle p q
  change metricDistance g (H p) (H q) = roundDistance p q
  change Real.pi - roundDistance p q ≤ metricDistance g (H (antipode p)) (H q) at hq
  change roundDistance p q ≤ metricDistance g (H p) (H q) at hl
  linarith

end
end PositiveEinsteinFour.Geometry
end


section

/-! The genuine exponential inverse in the open round normal ball is C1.
The invertible derivative is derived from the actual Jacobi solution. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Set
open scoped Manifold ContDiff _root_.Topology
noncomputable section
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem frameExponential_round_mfderiv_isUnit (hRic : RicciThree g)
    (hplus : ∀ c, plusWeyl g c (o.frame c) = 0)
    (hminus : ∀ c, minusWeyl g c (o.frame c) = 0)
    (e : FrameBundle g) (he : e ∈ o.positive) (v : FourSpace)
    (hv : v ≠ 0) (hpi : ‖v‖ < Real.pi) :
    IsUnit (show FourSpace →L[ℝ] FourSpace from mfderiv I4 I4 (frameExponential g o e) v) := by
  let q : Directions := ⟨‖v‖⁻¹ • v, by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]⟩
  let Q := directionOrientedMatrix q
  let L := (orthogonalEuclideanIsometry (orientedToOrthogonal Q).val
    (orientedToOrthogonal Q).property).toContinuousLinearEquiv
  let f := e.rotate (orientedToOrthogonal Q)
  let x := ‖v‖ • coordinateVector 0
  have hf : f ∈ o.positive := frameRotate_oriented_positive o e he Q
  have hrad : ‖v‖ • q.val = v := by
    change ‖v‖ • (‖v‖⁻¹ • v) = v
    rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv), one_smul]
  have hpoint : L x = v := by
    change L (‖v‖ • coordinateVector 0) = v
    rw [map_smul]
    exact (congrArg (fun z => ‖v‖ • z) (directionRotation_first q)).trans hrad
  let d := (parallelFrameFlowMap g 0 ‖v‖ f).base
  have hd : d ∈ (chartAt FourSpace d).source := mem_chart_source FourSpace d
  have hexp : frameExponential g o f x = d :=
    frameExponential_first_ray g o f hf ‖v‖ (norm_pos_iff.mpr hv)
  have hunit : IsUnit (show FourSpace →L[ℝ] FourSpace from mfderiv I4 I4 (frameExponential g o f) x) := by
    rw [← frameExponential_center_fderiv, hexp,
      (frameExponential_hasFDerivAt g o hRic d f hf ‖v‖ (norm_pos_iff.mpr hv) hd).fderiv]
    apply frameExponential_preconjugate_isUnit g hRic d f ‖v‖ (norm_pos_iff.mpr hv)
    · rw [actualFirstConjugateTime_eq_pi_of_weyl_zero hRic hplus hminus f hf]
      exact hpi
    · exact hd
  have hD : (show FourSpace →L[ℝ] FourSpace from mfderiv I4 I4 (frameExponential g o e) v) =
      (show FourSpace →L[ℝ] FourSpace from mfderiv I4 I4 (frameExponential g o f) x) *
        (L.symm : FourSpace →L[ℝ] FourSpace) := by
    apply ContinuousLinearMap.ext
    intro w
    have h := frameExponential_rotate_mfderiv g o e Q x (L.symm w)
    change _ = mfderiv I4 I4 (frameExponential g o e) (L x) (L (L.symm w)) at h
    rw [hpoint, L.apply_symm_apply] at h
    exact h.symm
  rw [hD]
  exact hunit.mul L.symm.toUnit.isUnit

theorem frameExponential_round_inverse_contMDiffAt (hRic : RicciThree g)
    (hplus : ∀ c, plusWeyl g c (o.frame c) = 0)
    (hminus : ∀ c, minusWeyl g c (o.frame c) = 0)
    (e : FrameBundle g) (he : e ∈ o.positive) (v : FourSpace)
    (hv : v ≠ 0) (hpi : ‖v‖ < Real.pi)
    (C : OpenPartialHomeomorph FourSpace M) (hCv : v ∈ C.source)
    (hC : EqOn C (frameExponential g o e) C.source) :
    ContMDiffAt I4 I4 1 C.symm (frameExponential g o e v) := by
  apply frameExponential_local_inverse_contMDiffAt g o e v C hCv hC
  rw [frameExponential_center_fderiv]
  exact frameExponential_round_mfderiv_isUnit hRic hplus hminus e he v hv hpi

end
end PositiveEinsteinFour.Geometry
end


section

/-! A smooth manifold curve lifts through the actual sphere homeomorphism
with the same speed away from the two polar values. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Set Filter Bundle
open scoped Manifold ContDiff _root_.Topology
noncomputable section
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem round_inverse_curve_speed (hRic : RicciThree g)
    (hpositive : HasPositiveSectionalCurvature g)
    (hplus : ∀ c, plusWeyl g c (o.frame c) = 0)
    (hminus : ∀ c, minusWeyl g c (o.frame c) = 0)
    (e : FrameBundle g) (he : e ∈ o.positive)
    {γ : ℝ → M} {t : ℝ} (hγ : ContMDiffAt 𝓘(ℝ, ℝ) I4 1 γ t)
    (hnorth : (actualRoundHomeomorph hRic hpositive hplus hminus e he).symm (γ t) ≠ roundNorth)
    (hsouth : (actualRoundHomeomorph hRic hpositive hplus hminus e he).symm (γ t) ≠
      antipode roundNorth) :
    ∃ w : EuclideanSpace ℝ (Fin 5),
      HasDerivAt (fun s => ((actualRoundHomeomorph hRic hpositive hplus hminus e he).symm
        (γ s)).val) w t ∧
      ‖w‖ = metricTangentNorm g (γ t) (mfderiv 𝓘(ℝ, ℝ) I4 γ t 1) := by
  let H := actualRoundHomeomorph hRic hpositive hplus hminus e he
  let p := H.symm (γ t)
  let v := roundLog p
  have hp : roundSphereExponential v = p := roundSphereExponential_log p
  have hv : v ≠ 0 := by
    intro hz
    have hpn : p = roundNorth := by rw [← hp, hz, roundSphereExponential_zero]
    exact hnorth hpn
  have hvpi : ‖v‖ < Real.pi := roundLog_norm_lt_pi hsouth
  have hpoint : frameExponential g o e v = γ t := by
    change H p = γ t
    exact H.apply_symm_apply (γ t)
  obtain ⟨C, hCv, hC⟩ := frameExponential_round_localChart hRic hplus hminus e he v hvpi
  have hCt : C v = γ t := (hC hCv).trans hpoint
  have hy : γ t ∈ C.target := hCt ▸ C.map_source hCv
  let α : ℝ → FourSpace := fun s => C.symm (γ s)
  have hαt : α t = v := by
    change C.symm (γ t) = v
    rw [← hCt]
    exact C.left_inv hCv
  have hα : ContDiffAt ℝ 1 α t := by
    have hi := frameExponential_round_inverse_contMDiffAt hRic hplus hminus e he v hv hvpi C hCv hC
    rw [hpoint] at hi
    exact (hi.comp t hγ).contDiffAt
  have hn : ∀ᶠ s in 𝓝 t, γ s ∈ C.target :=
    hγ.continuousAt.preimage_mem_nhds (C.open_target.mem_nhds hy)
  have hEq : (fun s => frameExponential g o e (α s)) =ᶠ[𝓝 t] γ := by
    filter_upwards [hn] with s hs
    exact (hC (C.map_target hs)).symm.trans (C.right_inv hs)
  have hnorm : ∀ᶠ s in 𝓝 t, ‖α s‖ < Real.pi :=
    hα.continuousAt.norm.eventually_lt continuousAt_const (by rw [hαt]; exact hvpi)
  have hLift : (fun s => H.symm (γ s)) =ᶠ[𝓝 t]
      (fun s => roundSphereExponential (α s)) := by
    filter_upwards [hEq, hnorm] with s hs hsn
    apply H.injective
    rw [H.apply_symm_apply]
    change γ s = roundSphereMap g o e (roundSphereExponential (α s))
    rw [roundSphereMap_exponential hRic hplus hminus e he _ hsn.le, hs]
  have hdα := hα.differentiableAt one_ne_zero
  have hzα : α t ≠ 0 := by rwa [hαt]
  have hdsp := (roundSphereExponential_differentiableAt (α t) hzα).comp t hdα
  refine ⟨deriv (fun s => (roundSphereExponential (α s)).val) t,
    hdsp.hasDerivAt.congr_of_eventuallyEq ?_, ?_⟩
  · exact hLift.mono (fun _ h => congrArg Subtype.val h)
  · rw [frameExponential_round_curve_speed hRic hplus hminus e he hdα hzα]
    exact metric_curve_speed_congr hEq

end
end PositiveEinsteinFour.Geometry
end


section

/-! The inverse sphere homeomorphism does not increase the distance
between the endpoints of an actual unit geodesic of length at most pi. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Set
open scoped Manifold ContDiff _root_.Topology ENNReal
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem round_frameGeodesic_radial_distance (hRic : RicciThree g)
    (hpositive : HasPositiveSectionalCurvature g)
    (hplus : ∀ c, plusWeyl g c (o.frame c) = 0)
    (hminus : ∀ c, minusWeyl g c (o.frame c) = 0)
    (f : FrameBundle g) (hf : f ∈ o.positive) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) Real.pi) :
    metricDistance g f.base (frameGeodesic g 0 f t) = t := by
  have hn : ‖t • (coordinateVector 0 : FourSpace)‖ = t := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    simp [coordinateVector]
  have hm := frameExponential_round_minimizing hRic hpositive hplus hminus f hf
    (t • coordinateVector 0) (by rw [hn]; exact ht.2)
  rwa [frameExponential_first_ray_all g o f hf t, hn] at hm

theorem round_frameGeodesic_injOn (hRic : RicciThree g)
    (hpositive : HasPositiveSectionalCurvature g)
    (hplus : ∀ c, plusWeyl g c (o.frame c) = 0)
    (hminus : ∀ c, minusWeyl g c (o.frame c) = 0)
    (f : FrameBundle g) (hf : f ∈ o.positive) :
    InjOn (frameGeodesic g 0 f) (Icc (0 : ℝ) Real.pi) := by
  intro s hs t ht heq
  have h := congrArg (metricDistance g f.base) heq
  rwa [round_frameGeodesic_radial_distance hRic hpositive hplus hminus f hf s hs,
    round_frameGeodesic_radial_distance hRic hpositive hplus hminus f hf t ht] at h

theorem round_inverse_geodesic_distance_le (hRic : RicciThree g)
    (hpositive : HasPositiveSectionalCurvature g)
    (hplus : ∀ c, plusWeyl g c (o.frame c) = 0)
    (hminus : ∀ c, minusWeyl g c (o.frame c) = 0)
    (e : FrameBundle g) (he : e ∈ o.positive)
    (f : FrameBundle g) (hf : f ∈ o.positive) (d : ℝ) (hd : d ∈ Icc (0 : ℝ) Real.pi) :
    roundDistance
      ((actualRoundHomeomorph hRic hpositive hplus hminus e he).symm (frameGeodesic g 0 f 0))
      ((actualRoundHomeomorph hRic hpositive hplus hminus e he).symm (frameGeodesic g 0 f d)) ≤ d := by
  classical
  let H := actualRoundHomeomorph hRic hpositive hplus hminus e he
  let u : ℝ → RoundSphere4 := fun t => H.symm (frameGeodesic g 0 f t)
  have hu : Continuous u := H.symm.continuous.comp (frameGeodesic_contMDiff g 0 f).continuous
  have hi : InjOn u (Icc (0 : ℝ) Real.pi) := by
    intro s hs t ht heq
    exact round_frameGeodesic_injOn hRic hpositive hplus hminus f hf hs ht
      (H.symm.injective heq)
  let S : Set RoundSphere4 := {roundNorth, antipode roundNorth, u 0, antipode (u 0)}
  let B : Set ℝ := Ioo 0 d ∩ u ⁻¹' S
  have hS : S.Finite := by
    simp only [S, Set.finite_insert, Set.finite_singleton]
  have hmap : MapsTo u B S := fun _ ht => ht.2
  have hbi : InjOn u B := hi.mono (show B ⊆ Icc 0 Real.pi from
    fun _ ht => ⟨ht.1.1.le, ht.1.2.le.trans hd.2⟩)
  have hB : B.Finite := hS.of_injOn hmap hbi
  have hgood (t : ℝ) (ht : t ∈ Ioo 0 d) (hexc : t ∉ hB.toFinset) : u t ∉ S := by
    intro hs
    exact hexc (hB.mem_toFinset.mpr ⟨ht, hs⟩)
  have hder (t : ℝ) (ht : t ∈ Ioo 0 d) (hexc : t ∉ hB.toFinset) :
      ∃ w : EuclideanSpace ℝ (Fin 5), HasDerivAt (fun s => (u s).val) w t ∧ ‖w‖ ≤ 1 := by
    have hg := hgood t ht hexc
    have hn : u t ≠ roundNorth := fun h => hg (by simp [S, h])
    have hs : u t ≠ antipode roundNorth := fun h => hg (by simp [S, h])
    obtain ⟨w, hw, hnorm⟩ := round_inverse_curve_speed hRic hpositive hplus hminus e he
      ((frameGeodesic_contMDiff g 0 f).contMDiffAt) hn hs
    exact ⟨w, hw, (hnorm.trans (round_frameGeodesic_real_speed f t)).le⟩
  have hr (t : ℝ) (ht : t ∈ Ioo 0 d) (hexc : t ∉ hB.toFinset) :
      u t ≠ u 0 ∧ u t ≠ antipode (u 0) := by
    have hg := hgood t ht hexc
    exact ⟨fun h => hg (by simp [S, h]), fun h => hg (by simp [S, h])⟩
  have hh := roundDistance_curve_le u 0 d hd.1 hB.toFinset hu.continuousOn hder hr
  simpa only [sub_zero] using hh

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual unit-speed frame geodesic is globally distance nonincreasing in time. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set
open scoped Manifold ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M}

theorem frameGeodesic_metricDistance_le (f : FrameBundle g) (s t : ℝ) :
    metricDistance g (frameGeodesic g 0 f s) (frameGeodesic g 0 f t) ≤ |t-s| := by
  have hordered (a b : ℝ) (hab : a ≤ b) :
      metricDistance g (frameGeodesic g 0 f a) (frameGeodesic g 0 f b) ≤ b-a := by
    have hh := metricDistance_le_of_interior_speed_bound g hab zero_le_one
      (frameGeodesic_contMDiff g 0 f).continuous
      (fun _ _ => (frameGeodesic_contMDiff g 0 f).contMDiffAt)
      (fun x _ => (round_frameGeodesic_real_speed f x).le)
    simpa only [one_mul] using hh
  rcases le_total s t with hst | hts
  · simpa only [abs_of_nonneg (sub_nonneg.mpr hst)] using hordered s t hst
  · rw [metricDistance_symm,abs_of_nonpos (sub_nonpos.mpr hts),neg_sub]
    exact hordered t s hts

end
end PositiveEinsteinFour.Geometry
end


section

/-! The global distance comparison for the actual round sphere map. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Set
open scoped Manifold ContDiff _root_.Topology ENNReal
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem roundSphereMap_distance_ge (hRic : RicciThree g)
    (hpositive : HasPositiveSectionalCurvature g)
    (hplus : ∀ c, plusWeyl g c (o.frame c) = 0)
    (hminus : ∀ c, minusWeyl g c (o.frame c) = 0)
    (e : FrameBundle g) (he : e ∈ o.positive) (p q : RoundSphere4) :
    roundDistance p q ≤ metricDistance g (roundSphereMap g o e p) (roundSphereMap g o e q) := by
  let H := actualRoundHomeomorph hRic hpositive hplus hminus e he
  let f : FrameBundle g := ⟨H p, o.frame (H p)⟩
  have hf : f ∈ o.positive := o.frame_positive (H p)
  let F := actualRoundHomeomorph hRic hpositive hplus hminus f hf
  let r := F.symm (H q)
  let v := roundLog r
  have hend : frameExponential g o f v = H q := F.apply_symm_apply (H q)
  have hd : ‖v‖ = metricDistance g (H p) (H q) := by
    have hh := roundSphereMap_radial_distance hRic hpositive hplus hminus f hf r
    change metricDistance g (H p) (F r) = Real.arccos (r.val 0) at hh
    rw [F.apply_symm_apply] at hh
    rw [show ‖v‖ = Real.arccos (r.val 0) from roundLog_norm r]
    exact hh.symm
  have hpi : ‖v‖ ≤ Real.pi := by
    change ‖roundLog r‖ ≤ Real.pi
    rw [roundLog_norm]
    exact Real.arccos_le_pi _
  by_cases hz : v = 0
  · have hpq : p = q := by
      apply H.injective
      have hh := hend
      rw [hz, frameExponential_zero] at hh
      exact hh
    subst q
    rw [roundDistance_self]
    exact metricDistance_nonneg _ _ _
  let w : Directions := ⟨‖v‖⁻¹ • v, by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)]⟩
  let f' := f.rotate (orientedToOrthogonal (directionOrientedMatrix w))
  have hf' : f' ∈ o.positive := frameRotate_oriented_positive o f hf _
  have hrad : ‖v‖ • w.val = v := by
    change ‖v‖ • (‖v‖⁻¹ • v) = v
    rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hz), one_smul]
  have hstart : frameGeodesic g 0 f' 0 = H p := by
    simp only [frameGeodesic, parallelFrameFlowMap_zero]
    rfl
  have hfinish : frameGeodesic g 0 f' ‖v‖ = H q := by
    rw [← frameExponential_direction_ray g o f hf w ‖v‖, hrad, hend]
  have hh := round_inverse_geodesic_distance_le hRic hpositive hplus hminus e he f' hf'
    ‖v‖ ⟨norm_nonneg _, hpi⟩
  change roundDistance (H.symm (frameGeodesic g 0 f' 0))
    (H.symm (frameGeodesic g 0 f' ‖v‖)) ≤ ‖v‖ at hh
  rw [hstart, hfinish, H.symm_apply_apply, H.symm_apply_apply, hd] at hh
  exact hh

theorem roundSphereMap_distance_eq (hRic : RicciThree g)
    (hpositive : HasPositiveSectionalCurvature g)
    (hplus : ∀ c, plusWeyl g c (o.frame c) = 0)
    (hminus : ∀ c, minusWeyl g c (o.frame c) = 0)
    (e : FrameBundle g) (he : e ∈ o.positive) (p q : RoundSphere4) :
    metricDistance g (roundSphereMap g o e p) (roundSphereMap g o e q) = roundDistance p q :=
  roundSphereMap_distance_eq_of_le hRic hpositive hplus hminus e he
    (roundSphereMap_distance_ge hRic hpositive hplus hminus e he) p q

end
end PositiveEinsteinFour.Geometry
end


section

/-! The metric round-model identification in the vanishing-Weyl branch. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Set
open scoped Manifold ContDiff _root_.Topology ENNReal
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem actual_round_model (hRic : RicciThree g)
    (hpositive : HasPositiveSectionalCurvature g)
    (hplus : ∀ c, plusWeyl g c (o.frame c) = 0)
    (hminus : ∀ c, minusWeyl g c (o.frame c) = 0) :
    ScaledIsometricTo g 1 roundDistance := by
  let x : M := Classical.choice inferInstance
  let e : FrameBundle g := ⟨x, o.frame x⟩
  have he : e ∈ o.positive := o.frame_positive x
  let H := actualRoundHomeomorph hRic hpositive hplus hminus e he
  refine ⟨H.symm.toEquiv, ?_⟩
  intro p q
  have h := roundSphereMap_distance_eq hRic hpositive hplus hminus e he (H.symm p) (H.symm q)
  change metricDistance g (H (H.symm p)) (H (H.symm q)) =
    roundDistance (H.symm p) (H.symm q) at h
  rw [H.apply_symm_apply, H.apply_symm_apply] at h
  change ENNReal.ofReal (roundDistance (H.symm p) (H.symm q)) = scaledEDistance g 1 p q
  rw [← h, ofReal_metricDistance]
  simp only [scaledEDistance, Real.sqrt_one, ENNReal.ofReal_one, one_mul]
  rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! A unit self-dual form admits a positively oriented standard frame,
constructed with the existing quaternion lifts. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix TraceHessian QuaternionFrame
open scoped BigOperators
noncomputable section

theorem selfDual_matrix_eq_imaginary (a : TwoFormFour) (ha : twoFormHodge a = a) :
    twoFormMatrix a = -imaginaryCombination quaternionMatrix ![a 0,a 1,a 2] := by
  have h3 : a 3 = a 2 := congrArg (fun b : TwoFormFour => b 2) ha
  have h4 : a 4 = -a 1 := by
    have h := congrArg (fun b : TwoFormFour => b 1) ha
    change -a 4 = a 1 at h
    linarith
  have h5 : a 5 = a 0 := congrArg (fun b : TwoFormFour => b 0) ha
  ext i j
  simp only [imaginaryCombination, Matrix.neg_apply, Matrix.sum_apply, Matrix.smul_apply]
  fin_cases i <;> fin_cases j <;>
    simp [twoFormMatrix, quaternionMatrix, Fin.sum_univ_succ, h3,h4,h5]

theorem standardSelfDualForm_matrix : twoFormMatrix standardSelfDualForm = -quaternionMatrix 0 := by
  ext i j
  simp only [Matrix.neg_apply]
  fin_cases i <;> fin_cases j <;>
    simp [standardSelfDualForm, twoFormMatrix, quaternionMatrix]

theorem unitSelfDual_exists_oriented_frame (a : TwoFormFour)
    (ha : twoFormHodge a = a) (hn : ‖a‖ ^ 2 = 2) :
    ∃ c : ℝ, c ^ 2 = 1 ∧ ∃ Q : OrientedOrthogonalFour,
      twoFormFrameAction Q.val a = c • standardSelfDualForm := by
  let v : ThreeSpace := WithLp.toLp 2 ![a 0,a 1,a 2]
  let e0 : ThreeSpace := EuclideanSpace.basisFun (Fin 3) ℝ 0
  have hv : ‖v‖ = 1 := by
    have h := selfDual_firstThree_unit a ha hn
    have hs : ‖v‖ ^ 2 = 1 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      simpa only [v, pow_two, dotProduct] using h
    nlinarith [norm_nonneg v]
  have he0 : ‖e0‖ = 1 := (EuclideanSpace.basisFun (Fin 3) ℝ).norm_eq_one 0
  let φ : ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace := Submodule.reflection (ℝ ∙ (e0 - v))ᗮ
  have hφ : φ e0 = v := Submodule.reflection_sub (he0.trans hv.symm)
  obtain ⟨c,hc,⟨P⟩⟩ := exists_signed_left_lift φ
  have hAv : (c • frameMatrix φ) *ᵥ (Pi.single 0 1 : Fin 3 → ℝ) = c • (v : Fin 3 → ℝ) := by
    rw [Matrix.smul_mulVec, Matrix.mulVec_single_one]
    ext i
    change c * frameMatrix φ i 0 = c * v i
    rw [frameMatrix_apply]
    exact congrArg (fun x : ThreeSpace => c * x i) hφ
  have hbasic : imaginaryCombination quaternionMatrix (Pi.single 0 1) = quaternionMatrix 0 := by
    simp [imaginaryCombination, Pi.single_apply]
  have hsmul : imaginaryCombination quaternionMatrix (c • (v : Fin 3 → ℝ)) =
      c • imaginaryCombination quaternionMatrix v := by
    simp only [imaginaryCombination, Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]
  have hi := intertwines_combination quaternionMatrix (c • frameMatrix φ) P.matrix
    P.intertwines (Pi.single 0 1)
  rw [hAv,hbasic,hsmul] at hi
  have hj := congrArg (fun B : Mat4 => P.matrixᵀ * B) hi
  have hj' : quaternionMatrix 0 = c •
      (P.matrixᵀ * imaginaryCombination quaternionMatrix v * P.matrix) := by
    simpa only [← Matrix.mul_assoc, P.orthogonal, Matrix.one_mul,
      Matrix.mul_smul, Matrix.smul_mul] using hj
  have hjc := congrArg (fun B : Mat4 => c • B) hj'
  rw [smul_smul, ← pow_two, hc, one_smul] at hjc
  refine ⟨c,hc,⟨P.matrix,Matrix.mem_specialOrthogonalGroup_iff.mpr
    ⟨by rw [Matrix.mem_orthogonalGroup_iff']; exact P.orthogonal, P.orientation⟩⟩,?_⟩
  apply twoFormMatrix_injective
  rw [twoFormMatrix_frameAction, selfDual_matrix_eq_imaginary a ha,
    Matrix.mul_neg, Matrix.neg_mul, ← hjc, twoFormMatrix_smul,
    standardSelfDualForm_matrix, smul_neg]

end
end PositiveEinsteinFour.Geometry
end


section

/-! An actual positive frame and a global parallel form with the standard
complex matrix, with no choice of complex structure assumed as input. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Matrix
open scoped Manifold ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem halfFlat_dimension_one_standard_frame (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1) (x : M) :
    ∃ w : smoothTwoForms o,
      (∀ y, twoFormHodge (w.val y) = w.val y) ∧
      (∀ y, ‖w.val y‖ ^ 2 = 2) ∧
      (∀ e : FrameBundle g, twoFormFramedCovariantDerivative o w.val e = 0) ∧
      ∃ e : FrameBundle g, e.base = x ∧ e ∈ o.positive ∧
        twoFormFrameValue o w.val e = standardSelfDualForm := by
  obtain ⟨w,hs,hn,hz⟩ := halfFlat_dimension_one_parallel_unit_form hRic hminus hdim
  let f : FrameBundle g := ⟨x,o.frame x⟩
  have hf : f ∈ o.positive := o.frame_positive x
  have hfs : twoFormHodge (twoFormFrameValue o w.val f) = twoFormFrameValue o w.val f := by
    rw [← twoFormFrameValue_hodge o w.val f hf]
    congr 1
    exact funext hs
  have hfn : ‖twoFormFrameValue o w.val f‖ ^ 2 = 2 := by
    rw [twoFormFrameValue_norm, hn]
  obtain ⟨c,hc,Q,hQ⟩ := unitSelfDual_exists_oriented_frame _ hfs hfn
  let e := f.rotate (orientedToOrthogonal Q)
  refine ⟨c • w, ?_, ?_, ?_, e, rfl, frameRotate_oriented_positive o f hf Q, ?_⟩
  · intro y
    change twoFormHodge (c • w.val y) = c • w.val y
    rw [map_smul,hs]
  · intro y
    change ‖c • w.val y‖ ^ 2 = 2
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hc,hn,one_mul]
  · intro E
    change twoFormFramedCovariantDerivative o (c • w.val) E = 0
    rw [twoFormFramedCovariantDerivative_smul,hz,smul_zero]
  · change twoFormFrameValue o (c • w.val) e = standardSelfDualForm
    rw [twoFormFrameValue_smul, twoFormFrameValue_rotate]
    change c • twoFormFrameAction Q.val (twoFormFrameValue o w.val f) = _
    rw [hQ,smul_smul,← pow_two,hc,one_smul]

end
end PositiveEinsteinFour.Geometry
end

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_WeylEstimates14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Density and continuous extension of the distance bound across the thin chart sets. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Filter
open scoped _root_.Topology NNReal ENNReal
noncomputable section

theorem complexParametrizedImage_compl_dense (p : Fin 2 → ℂ → FourSpace) (U : Fin 2 → Set ℂ)
    (hp : ∀ i z, z ∈ U i → ∃ K : ℝ≥0, ∃ V ∈ 𝓝 z, LipschitzOnWith K (p i) V) :
    Dense (⋃ i, p i '' U i)ᶜ := by
  have hdim : dimH (⋃ i, p i '' U i) ≤ 3 := by
    rw [dimH_iUnion]
    apply iSup_le
    intro i
    apply le_trans (dimH_mono ?_) (complexParametrizedCone_dimH_le 0 (p i) (U i) (hp i))
    rintro x ⟨z,hz,rfl⟩
    refine ⟨(z,1),⟨hz,mem_univ _⟩,?_⟩
    simp
  intro x
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨y,hy,hnot⟩ := exists_not_mem_of_dimH_le_three _ hdim x (Metric.ball x ε)
    (Metric.ball_mem_nhds x hε)
  exact ⟨y,hnot,by simpa only [Metric.mem_ball,dist_comm] using hy⟩

theorem dist_le_on_open_of_dense {Y : Type*} [PseudoMetricSpace Y]
    (D : Set FourSpace) (hD : Dense D) (V : Set FourSpace) (hV : IsOpen V)
    (f : FourSpace → Y) (hf : ContinuousOn f V) (K : ℝ)
    (hbound : ∀ x ∈ V, x ∈ D → ∀ y ∈ V, y ∈ D → dist (f x) (f y) ≤ K*dist x y)
    (x y : FourSpace) (hx : x ∈ V) (hy : y ∈ V) :
    dist (f x) (f y) ≤ K * dist x y := by
  obtain ⟨u,hu,hux⟩ := mem_closure_iff_seq_limit.mp (hD x)
  obtain ⟨v,hv,hvy⟩ := mem_closure_iff_seq_limit.mp (hD y)
  have huV : ∀ᶠ n in atTop, u n ∈ V := hux (hV.mem_nhds hx)
  have hvV : ∀ᶠ n in atTop, v n ∈ V := hvy (hV.mem_nhds hy)
  have huf : Tendsto (fun n => f (u n)) atTop (𝓝 (f x)) :=
    (show Tendsto f (𝓝[V] x) (𝓝 (f x)) from hf x hx).comp
      (tendsto_nhdsWithin_iff.mpr ⟨hux,huV⟩)
  have hvf : Tendsto (fun n => f (v n)) atTop (𝓝 (f y)) :=
    (show Tendsto f (𝓝[V] y) (𝓝 (f y)) from hf y hy).comp
      (tendsto_nhdsWithin_iff.mpr ⟨hvy,hvV⟩)
  apply le_of_tendsto_of_tendsto
    (continuous_dist.continuousAt.tendsto.comp (huf.prodMk_nhds hvf))
    (tendsto_const_nhds.mul (continuous_dist.continuousAt.tendsto.comp (hux.prodMk_nhds hvy)))
  filter_upwards [huV,hvV] with n hun hvn
  exact hbound (u n) hun (hu n) (v n) hvn (hv n)

end
end PositiveEinsteinFour.Geometry
end

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GeodesicGeometry14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Continuous inverse chart bounds hold at the cut locus as well. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Set Filter Bundle
open scoped Manifold ContDiff _root_.Topology ENNReal NNReal
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

attribute [local instance] complexProjectiveMetric

theorem actualComplexProjective_section_chart_all_distance_le (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1)
    (W : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (W.val x) = W.val x)
    (hw : ∀ x, ‖W.val x‖ ^ 2 = 2)
    (hz : ∀ f : FrameBundle g, twoFormFramedCovariantDerivative o W.val f = 0)
    (e : FrameBundle g) (he : e ∈ o.positive)
    (hstd : twoFormFrameValue o W.val e = standardSelfDualForm)
    (S : M → ComplexProjective2) (hS : Function.RightInverse S (actualComplexProjectiveMap g o e))
    (hSc : Continuous S) (c : M) (A : FourSpace ≃L[ℝ] FourSpace) (V : Set FourSpace)
    (hV : IsOpen V) (hconv : Convex ℝ V) (hVT : ∀ x ∈ V, A x ∈ (chartAt FourSpace c).target)
    (K : ℝ) (hK : 0 ≤ K)
    (hbound : ∀ x ∈ V, ∀ y ∈ V,
      metricDistance g ((chartAt FourSpace c).symm (A x)) ((chartAt FourSpace c).symm (A y)) ≤ K*dist x y)
    (x y : FourSpace) (hx : x ∈ V) (hy : y ∈ V) :
    fubiniStudyDistance (S ((chartAt FourSpace c).symm (A x)))
      (S ((chartAt FourSpace c).symm (A y))) ≤ (Real.sqrt 2)⁻¹*K*dist x y := by
  let T : FourSpace → M := fun z => (chartAt FourSpace c).symm (A z)
  let p := complexCutChartMap g o e c A.symm.toContinuousLinearMap
  let U := complexCutChartDomain g o e c
  let D := (⋃ i, p i '' U i)ᶜ
  have hp := fun i => complexCutChartMap_locallyLipschitz hRic hminus hdim W hstar hw hz e he hstd c A.symm.toContinuousLinearMap i
  have hD : Dense D := complexParametrizedImage_compl_dense p U hp
  have hT : ContinuousOn T V :=
    (chartAt FourSpace c).symm.continuousOn.comp A.continuous.continuousOn hVT
  have hcont : ContinuousOn (S ∘ T) V := hSc.comp_continuousOn hT
  have hgood (z : FourSpace) (hzV : z ∈ V) (hzD : z ∈ D) :
      metricDistance g e.base (T z) < complexJacobiRadius := by
    apply lt_of_le_of_ne (actual_complex_distance_le_radius hRic hminus hdim W hstar hw hz e he hstd (T z))
    intro heq
    exact hzD ((complexCutChartImage_iff hRic hminus hdim W hstar hw hz e he hstd c A z (hVT z hzV)).mpr heq)
  exact dist_le_on_open_of_dense D hD V hV (S ∘ T) hcont ((Real.sqrt 2)⁻¹*K)
    (fun z hzV hzD w hwV hwD => actualComplexProjective_section_chart_distance_le
      hRic hminus hdim W hstar hw hz e he hstd S hS c A V hV hconv hVT K hK hbound
      z w hzV hwV (hgood z hzV hzD) (hgood w hwV hwD)) x y hx hy

end
end PositiveEinsteinFour.Geometry
end


section

/-! Arbitrarily sharp inverse metric bounds on neighborhoods of every actual point. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Set Filter Bundle
open scoped Manifold ContDiff _root_.Topology ENNReal NNReal
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

attribute [local instance] complexProjectiveMetric

theorem actualComplexProjective_inverse_local_bound (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1)
    (W : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (W.val x) = W.val x)
    (hw : ∀ x, ‖W.val x‖ ^ 2 = 2)
    (hz : ∀ f : FrameBundle g, twoFormFramedCovariantDerivative o W.val f = 0)
    (e : FrameBundle g) (he : e ∈ o.positive)
    (hstd : twoFormFrameValue o W.val e = standardSelfDualForm)
    (S : M → ComplexProjective2) (hS : Function.RightInverse S (actualComplexProjectiveMap g o e))
    (hSc : Continuous S) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) (c : M) :
    ∃ N ∈ 𝓝 c, ∀ x ∈ N, ∀ y ∈ N,
      fubiniStudyDistance (S x) (S y) ≤ complexInverseDistortion δ * metricDistance g x y := by
  obtain ⟨A,V,hV,hconv,hcenter,hVT,hup,hlo⟩ := exists_sharp_linear_chart_neighborhood g c δ hδ hδ1
  let Z := chartAt FourSpace c
  let k : M → FourSpace := fun x => A.symm (Z x)
  let N := Z.source ∩ k ⁻¹' V
  have hk : ContinuousAt k c := A.symm.continuous.continuousAt.comp
    (Z.continuousAt (mem_chart_source FourSpace c))
  have hN : N ∈ 𝓝 c := inter_mem (Z.open_source.mem_nhds (mem_chart_source FourSpace c))
    (hk (hV.mem_nhds hcenter))
  refine ⟨N,hN,?_⟩
  intro x hx y hy
  have hxinv : Z.symm (A (k x)) = x := by rw [A.apply_symm_apply,Z.left_inv hx.1]
  have hyinv : Z.symm (A (k y)) = y := by rw [A.apply_symm_apply,Z.left_inv hy.1]
  have h1 := actualComplexProjective_section_chart_all_distance_le hRic hminus hdim W hstar hw hz e he hstd
    S hS hSc c A V hV hconv hVT (Real.sqrt (1+δ)) (Real.sqrt_nonneg _) hup
    (k x) (k y) hx.2 hy.2
  change fubiniStudyDistance (S (Z.symm (A (k x)))) (S (Z.symm (A (k y)))) ≤ _ at h1
  rw [hxinv,hyinv] at h1
  have h2 := hlo (k x) hx.2 (k y) hy.2
  change dist (k x) (k y) ≤ (1 / Real.sqrt (1-δ))*metricDistance g (Z.symm (A (k x))) (Z.symm (A (k y))) at h2
  rw [hxinv,hyinv] at h2
  calc
    _ ≤ ((Real.sqrt 2)⁻¹*Real.sqrt (1+δ))*dist (k x) (k y) := h1
    _ ≤ ((Real.sqrt 2)⁻¹*Real.sqrt (1+δ))*((1 / Real.sqrt (1-δ))*metricDistance g x y) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = _ := by unfold complexInverseDistortion; ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The continuous actual inverse preserves the length bound along every unit geodesic. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Set Filter Bundle
open scoped Manifold ContDiff _root_.Topology ENNReal NNReal
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

attribute [local instance] complexProjectiveMetric

theorem actualComplexProjective_inverse_geodesic_le (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1)
    (W : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (W.val x) = W.val x)
    (hw : ∀ x, ‖W.val x‖ ^ 2 = 2)
    (hz : ∀ f : FrameBundle g, twoFormFramedCovariantDerivative o W.val f = 0)
    (e : FrameBundle g) (he : e ∈ o.positive)
    (hstd : twoFormFrameValue o W.val e = standardSelfDualForm)
    (S : M → ComplexProjective2) (hS : Function.RightInverse S (actualComplexProjectiveMap g o e))
    (hSc : Continuous S) (f : FrameBundle g) (d : ℝ) (hd : 0 ≤ d) :
    fubiniStudyDistance (S (frameGeodesic g 0 f 0)) (S (frameGeodesic g 0 f d)) ≤ (Real.sqrt 2)⁻¹*d := by
  let γ := frameGeodesic g 0 f
  have hγ : Continuous γ := (frameGeodesic_contMDiff g 0 f).continuous
  let q : ℝ → ℝ := fun t => fubiniStudyDistance (S (γ 0)) (S (γ t))
  have hq : Continuous q := continuous_dist.comp (continuous_const.prodMk (hSc.comp hγ))
  have hδbound (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) : q d ≤ complexInverseDistortion δ*d := by
    have hC : 0 ≤ complexInverseDistortion δ := by unfold complexInverseDistortion; positivity
    have hinc (t : ℝ) (_ht : t ∈ Ico (0 : ℝ) d) :
        ∀ᶠ s in 𝓝[>] t, q s-q t ≤ complexInverseDistortion δ*(s-t) := by
      obtain ⟨N,hN,hbound⟩ := actualComplexProjective_inverse_local_bound hRic hminus hdim
        W hstar hw hz e he hstd S hS hSc δ hδ hδ1 (γ t)
      have htN : γ t ∈ N := mem_of_mem_nhds hN
      have hev : ∀ᶠ s in 𝓝[>] t, γ s ∈ N :=
        (hγ.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) hN
      filter_upwards [hev,self_mem_nhdsWithin] with s hs hts
      have htri : q s-q t ≤ fubiniStudyDistance (S (γ t)) (S (γ s)) := by
        dsimp [q]
        linarith [fubiniStudyDistance_triangle (S (γ 0)) (S (γ t)) (S (γ s))]
      have hg : metricDistance g (γ t) (γ s) ≤ s-t := by
        simpa only [γ,abs_of_nonneg (sub_nonneg.mpr (show t ≤ s from le_of_lt hts))] using frameGeodesic_metricDistance_le f t s
      exact htri.trans ((hbound _ htN _ hs).trans (mul_le_mul_of_nonneg_left hg hC))
    have hh := sub_le_of_local_increment q 0 d (complexInverseDistortion δ) hd hq.continuousOn hinc
    simpa only [q,fubiniStudyDistance_self,sub_zero] using hh
  have hc : ContinuousAt complexInverseDistortion 0 := by
    unfold complexInverseDistortion
    fun_prop (disch := norm_num)
  have hlim : Tendsto (fun δ => complexInverseDistortion δ*d) (𝓝[>] (0 : ℝ))
      (𝓝 ((Real.sqrt 2)⁻¹*d)) := by
    have hh := (hc.tendsto.mono_left (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)).mul_const d
    simpa [complexInverseDistortion] using hh
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))] with δ hδ hδ1
  exact hδbound δ hδ hδ1

end
end PositiveEinsteinFour.Geometry
end


section

/-! Global distance preservation of the actual complex projective parametrization. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Set Filter Bundle
open scoped Manifold ContDiff _root_.Topology ENNReal NNReal
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

attribute [local instance] complexProjectiveMetric

theorem actualComplexProjectiveMap_distance_ge (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1)
    (W : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (W.val x) = W.val x)
    (hw : ∀ x, ‖W.val x‖ ^ 2 = 2)
    (hz : ∀ f : FrameBundle g, twoFormFramedCovariantDerivative o W.val f = 0)
    (e : FrameBundle g) (he : e ∈ o.positive)
    (hstd : twoFormFrameValue o W.val e = standardSelfDualForm)
    (P Q : ComplexProjective2) :
    fubiniStudyDistance P Q ≤ (Real.sqrt 2)⁻¹ *
      metricDistance g (actualComplexProjectiveMap g o e P) (actualComplexProjectiveMap g o e Q) := by
  let H := actualComplexHomeomorph hRic hminus hdim W hstar hw hz e he hstd
  let f : FrameBundle g := ⟨H P,o.frame (H P)⟩
  have hf : f ∈ o.positive := o.frame_positive (H P)
  have hcover := frameExponential_complex_closedBall_image hRic hminus hdim f hf
  have hmem : H Q ∈ frameExponential g o f '' Metric.closedBall 0 complexJacobiRadius := by
    rw [hcover]
    trivial
  obtain ⟨v,hv,hend⟩ := hmem
  have hvR : ‖v‖ ≤ complexJacobiRadius := by simpa only [Metric.mem_closedBall,dist_zero_right] using hv
  have hdist : ‖v‖ = metricDistance g (H P) (H Q) := by
    have hh := frameExponential_complex_minimizing hRic hminus hdim f hf v hvR
    rw [hend] at hh
    exact hh.symm
  by_cases hv0 : v = 0
  · have hPQ : P = Q := by
      apply H.injective
      simpa only [hv0,frameExponential_zero] using hend
    subst Q
    rw [fubiniStudyDistance_self]
    exact mul_nonneg (by positivity) (metricDistance_nonneg g _ _)
  let q : Directions := ⟨‖v‖⁻¹ • v,by
    rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_nonneg (norm_nonneg _),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv0)]⟩
  let f' := f.rotate (orientedToOrthogonal (directionOrientedMatrix q))
  have hrad : ‖v‖ • q.val = v := by
    change ‖v‖ • (‖v‖⁻¹ • v) = v
    rw [smul_smul,mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv0),one_smul]
  have hstart : frameGeodesic g 0 f' 0 = H P := by
    simp only [frameGeodesic,parallelFrameFlowMap_zero]
    rfl
  have hfinish : frameGeodesic g 0 f' ‖v‖ = H Q := by
    rw [← frameExponential_direction_ray g o f hf q ‖v‖,hrad,hend]
  have hS : Function.RightInverse H.symm (actualComplexProjectiveMap g o e) :=
    fun x => H.apply_symm_apply x
  have hh := actualComplexProjective_inverse_geodesic_le hRic hminus hdim W hstar hw hz e he hstd
    H.symm hS H.symm.continuous f' ‖v‖ (norm_nonneg _)
  rw [hstart,hfinish,H.symm_apply_apply,H.symm_apply_apply,hdist] at hh
  exact hh

theorem actualComplexProjectiveMap_distance_eq (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1)
    (W : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (W.val x) = W.val x)
    (hw : ∀ x, ‖W.val x‖ ^ 2 = 2)
    (hz : ∀ f : FrameBundle g, twoFormFramedCovariantDerivative o W.val f = 0)
    (e : FrameBundle g) (he : e ∈ o.positive)
    (hstd : twoFormFrameValue o W.val e = standardSelfDualForm)
    (P Q : ComplexProjective2) :
    metricDistance g (actualComplexProjectiveMap g o e P) (actualComplexProjectiveMap g o e Q) =
      Real.sqrt 2 * fubiniStudyDistance P Q := by
  apply le_antisymm (actualComplexProjectiveMap_distance_le hRic hminus hdim W hstar hw hz e he hstd P Q)
  have h := mul_le_mul_of_nonneg_left
    (actualComplexProjectiveMap_distance_ge hRic hminus hdim W hstar hw hz e he hstd P Q)
    (Real.sqrt_nonneg 2)
  simpa only [← mul_assoc,mul_inv_cancel₀ (by positivity : Real.sqrt 2 ≠ 0),one_mul] using h

end
end PositiveEinsteinFour.Geometry
end


section

/-! The dimension-one branch is the actual Fubini--Study model after scaling by one half. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Set Filter Bundle
open scoped Manifold ContDiff _root_.Topology ENNReal NNReal
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

attribute [local instance] complexProjectiveMetric

theorem actual_complex_projective_model (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1) :
    ScaledIsometricTo g (1/2) fubiniStudyDistance := by
  let x : M := Classical.choice inferInstance
  obtain ⟨W,hstar,hw,hz,e,_,he,hstd⟩ := halfFlat_dimension_one_standard_frame hRic hminus hdim x
  let H := actualComplexHomeomorph hRic hminus hdim W hstar hw hz e he hstd
  refine ⟨H.symm.toEquiv,?_⟩
  intro p q
  have hdist := actualComplexProjectiveMap_distance_eq hRic hminus hdim W hstar hw hz e he hstd
    (H.symm p) (H.symm q)
  change metricDistance g (H (H.symm p)) (H (H.symm q)) =
    Real.sqrt 2 * fubiniStudyDistance (H.symm p) (H.symm q) at hdist
  rw [H.apply_symm_apply,H.apply_symm_apply] at hdist
  have hsqrt : Real.sqrt (1/2 : ℝ) * Real.sqrt 2 = 1 := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 1/2)]
    norm_num
  change ENNReal.ofReal (fubiniStudyDistance (H.symm p) (H.symm q)) = scaledEDistance g (1/2) p q
  rw [scaledEDistance]
  change ENNReal.ofReal (fubiniStudyDistance (H.symm p) (H.symm q)) =
    ENNReal.ofReal (Real.sqrt (1/2 : ℝ)) * metricEDistance g p q
  rw [← ofReal_metricDistance g,← ENNReal.ofReal_mul (Real.sqrt_nonneg _),hdist]
  congr 1
  rw [← mul_assoc,hsqrt,one_mul]

end
end PositiveEinsteinFour.Geometry
end

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ActualModelIdentification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual half-conformally-flat model identification. All analytic,
index, injectivity, and metric-model inputs are supplied by proved geometry. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour
open scoped Manifold ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem actual_halfFlat_positive_harmonic_dimension_one (hRic : RicciThree g)
    (hpositive : HasPositiveSectionalCurvature g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hplus : ∃ x, plusWeyl g x (o.frame x) ≠ 0) :
    Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1 :=
  halfFlat_positive_harmonic_dimension_one_of_injective_ball hRic hpositive hminus hplus
    (actual_frameExponential_injOn_sqrt_three g o hRic hpositive)

theorem actual_halfFlat_models (hRic : RicciThree g)
    (hpositive : HasPositiveSectionalCurvature g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0) :
    ∃ a : ℝ, 0 < a ∧ (ScaledIsometricTo g a roundDistance ∨
      ScaledIsometricTo g a fubiniStudyDistance) := by
  by_cases hp : ∀ x, plusWeyl g x (o.frame x) = 0
  · exact ⟨1,by norm_num,Or.inl (actual_round_model hRic hpositive hp hminus)⟩
  · have hn : ∃ x, plusWeyl g x (o.frame x) ≠ 0 := not_forall.mp hp
    exact ⟨1/2,by norm_num,Or.inr (actual_complex_projective_model hRic hminus
      (actual_halfFlat_positive_harmonic_dimension_one hRic hpositive hminus hn))⟩

variable [ConnectedSpace M]

omit [CompactSpace M] [SecondCountableTopology M] [ConnectedSpace M] [PreconnectedSpace M] in
theorem actual_derdzinski_hitchin_oai (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) : DerdzinskiHitchinInput g o := by
  intro _ _ _ _ _ hpositive hblock
  rcases hblock with hplus | hminus
  · have hminus : ∀ x, minusWeyl g x (o.reversed.frame x) = 0 := by
      intro x
      apply (minusNorm_eq_zero_iff o.reversed x).mp
      rw [minusNorm_reversed]
      exact (plusNorm_eq_zero_iff o x).mpr (hplus x)
    exact actual_halfFlat_models hRic hpositive hminus
  · exact actual_halfFlat_models hRic hpositive hminus

end
end PositiveEinsteinFour.Geometry

end OAI
end

theorem solution.{u_1} : type_of% @OAI.PositiveEinsteinFour.Geometry.actual_derdzinski_hitchin_oai.{u_1} := @OAI.PositiveEinsteinFour.Geometry.actual_derdzinski_hitchin_oai.{u_1}
