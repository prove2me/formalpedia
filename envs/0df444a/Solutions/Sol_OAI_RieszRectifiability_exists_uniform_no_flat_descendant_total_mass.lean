-- Prove2me | solution 1 for OAI.RieszRectifiability.exists_uniform_no_flat_descendant_total_mass
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:25:52.934225+00:00
-- url     : https://prove2.me/submissions/d604cec9-f1c7-44cd-a838-233478cfffd2

import Mathlib
import Definitions.Def_RieszQuantitative
import Definitions.Def_OAIQ231Rr000
import Theorems.Thm_OAI_RieszRectifiability_exists_uniform_cell_flat_annular_alternative

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Packing_OrthogonalNormalFrame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open Function

theorem exists_isometry_onto_subspace {q d : ℕ} (S : Submodule ℝ (Ambient d))
    (hdim : Module.finrank ℝ S = q) :
    ∃ N : Ambient q →ₗᵢ[ℝ] Ambient d, N.toLinearMap.range = S := by
  let b : OrthonormalBasis (Fin q) ℝ S :=
    (stdOrthonormalBasis ℝ S).reindex (finCongr hdim)
  let E : Ambient q ≃ₗᵢ[ℝ] S := b.repr.symm
  let N : Ambient q →ₗᵢ[ℝ] Ambient d :=
    { toLinearMap := S.subtype.comp E.toLinearEquiv.toLinearMap
      norm_map' := fun x => E.norm_map x }
  refine ⟨N, ?_⟩
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact (b.repr.symm y).property
  · intro hx
    refine ⟨b.repr ⟨x, hx⟩, ?_⟩
    change ((b.repr.symm (b.repr ⟨x, hx⟩) : S) : Ambient d) = x
    simp

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Packing_AffinePlaneNormalFrame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Normal coordinates for affine planes

Isometric tangent and normal frames express affine orthogonal projection and distance
to a plane in Euclidean coordinates. The frame construction chooses the point of the
plane nearest the origin as its base point.
-/

namespace RieszRectifiability

noncomputable section

open Metric Set EuclideanGeometry

theorem exists_euclidean_isometric_embedding {n d : ℕ} (hnd : n ≤ d) :
    Nonempty (Ambient n →ₗᵢ[ℝ] Ambient d) := by
  have hdim : n ≤ Module.finrank ℝ (Ambient d) := by
    simpa only [finrank_euclideanSpace_fin] using! hnd
  obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_finrank hdim
  have hspan : Module.finrank ℝ (Submodule.span ℝ (range v)) = n := by
    simpa only [Fintype.card_fin] using! finrank_span_eq_card hv
  obtain ⟨L, _hL⟩ := exists_isometry_onto_subspace (Submodule.span ℝ (range v)) hspan
  exact ⟨L⟩

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Flatness_ApproximatePlaneFits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology

theorem exists_affine_n_plane {n d : ℕ} (hnd : n ≤ d) :
    ∃ S : AffineSubspace ℝ (Ambient d), IsAffineNPlane n S := by
  obtain ⟨L⟩ := exists_euclidean_isometric_embedding hnd
  refine ⟨L.toLinearMap.range.toAffineSubspace, ⟨0, ?_⟩, ?_⟩
  · exact L.toLinearMap.range.zero_mem
  · rw [Submodule.toAffineSubspace_direction, LinearMap.finrank_range_of_inj L.injective]
    exact finrank_euclideanSpace_fin

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Flatness_BilateralBeta
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem directedBallDeviation_bddAbove {d : ℕ} (s t : Set (Ambient d)) (ht : t.Nonempty)
    (a : Ambient d) (r : ℝ) : BddAbove ((fun x => infDist x t) '' (ball a r ∩ s)) := by
  obtain ⟨y, hy⟩ := ht
  refine ⟨r + dist a y, ?_⟩
  rintro v ⟨x, hx, rfl⟩
  have hx' : dist x a ≤ r := hx.1.le
  exact (infDist_le_dist_of_mem hy).trans ((dist_triangle x a y).trans (by linarith))

theorem directedBallDeviation_nonneg {d : ℕ} (s t : Set (Ambient d))
    (a : Ambient d) (r : ℝ) : 0 ≤ directedBallDeviation s t a r := by
  apply Real.sSup_nonneg
  rintro v ⟨x, _, rfl⟩
  exact infDist_nonneg

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Flatness_BilateralBetaWitnesses
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem exists_bilateral_plane_error_lt {n d : ℕ} (hnd : n ≤ d)
    (μ : Measure (Ambient d)) (a : Ambient d) (r ε : ℝ)
    (hbeta : bilateralBeta n μ a r < ε) :
    ∃ S : AffineSubspace ℝ (Ambient d), IsAffineNPlane n S ∧ bilateralPlaneError μ a r S < ε := by
  obtain ⟨S, hS⟩ := exists_affine_n_plane hnd
  have hne : {t : ℝ | ∃ T : AffineSubspace ℝ (Ambient d),
      IsAffineNPlane n T ∧ t = bilateralPlaneError μ a r T}.Nonempty :=
    ⟨bilateralPlaneError μ a r S, S, hS, rfl⟩
  obtain ⟨t, ⟨T, hT, ht⟩, hlt⟩ := exists_lt_of_csInf_lt hne hbeta
  exact ⟨T, hT, ht ▸ hlt⟩

theorem bilateralPlaneError_lt_pointwise {n d : ℕ}
    (μ : Measure (Ambient d)) (hμ : μ.support.Nonempty) (a : Ambient d)
    (r ε : ℝ) (hr : 0 < r) (S : AffineSubspace ℝ (Ambient d)) (hS : IsAffineNPlane n S)
    (he : bilateralPlaneError μ a r S < ε) :
    (∀ x ∈ ball a r, x ∈ μ.support → infDist x (S : Set (Ambient d)) < ε * r) ∧
    (∀ x ∈ ball a r, x ∈ S → infDist x μ.support < ε * r) := by
  have he' : directedBallDeviation μ.support (S : Set (Ambient d)) a r +
      directedBallDeviation (S : Set (Ambient d)) μ.support a r < ε * r :=
    (div_lt_iff₀ hr).mp he
  have h1 := directedBallDeviation_nonneg μ.support (S : Set (Ambient d)) a r
  have h2 := directedBallDeviation_nonneg (S : Set (Ambient d)) μ.support a r
  constructor
  · intro x hx hxs
    have hv : infDist x (S : Set (Ambient d)) ≤
        directedBallDeviation μ.support (S : Set (Ambient d)) a r :=
      le_csSup (directedBallDeviation_bddAbove μ.support (S : Set (Ambient d)) hS.1 a r)
        ⟨x, ⟨hx, hxs⟩, rfl⟩
    linarith
  · intro x hx hxs
    have hv : infDist x μ.support ≤ directedBallDeviation (S : Set (Ambient d)) μ.support a r :=
      le_csSup (directedBallDeviation_bddAbove (S : Set (Ambient d)) μ.support hμ a r)
        ⟨x, ⟨hx, hxs⟩, rfl⟩
    linarith

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_KernelBasic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Elementary measurability and inverse-distance bounds for the Euclidean Riesz kernel.
Global upper growth records the ball-mass estimate used in kernel integration.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

theorem kernel_measurable_right {d : ℕ} (n : ℕ) (x : Ambient d) :
    Measurable (kernel n x) := by
  have : IsBoundedSMul ℝ (Ambient d) := NormedSpace.toIsBoundedSMul
  have : ContinuousSMul ℝ (Ambient d) := IsBoundedSMul.continuousSMul
  have : MeasurableSMul₂ ℝ (Ambient d) := ContinuousSMul.measurableSMul₂
  unfold kernel
  fun_prop

theorem kernel_norm_of_ne {d : ℕ} (n : ℕ) (x y : Ambient d) (hxy : x ≠ y) :
    ‖kernel n x y‖ = (dist x y ^ n)⁻¹ := by
  have hnorm : ‖x - y‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy)
  have hnonneg : 0 ≤ (‖x - y‖ ^ (n + 1))⁻¹ := by positivity
  rw [kernel, norm_smul, Real.norm_eq_abs, abs_of_nonneg hnonneg, dist_eq_norm, pow_succ]
  field_simp

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_PlanarPullbackMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Pullback along the adjoint of an isometric embedding transports a measure supported on
its range to Euclidean coordinates, preserving ball masses and upper growth bounds.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

theorem globalGrowth_finite_on_compacts {n d : ℕ} (C : ℝ)
    (ν : Measure (Ambient d)) (hg : GlobalUpperGrowth n C ν) : IsFiniteMeasureOnCompacts ν := by
  let : IsLocallyFiniteMeasure ν := ⟨fun x => ⟨ball x 1, ball_mem_nhds x zero_lt_one,
    (hg.2 x 1 zero_lt_one).trans_lt ENNReal.ofReal_lt_top⟩⟩
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_MomentRepair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Filter Topology

variable {X : Type*} [MeasurableSpace X]

theorem integral_squared_difference (μ : Measure X) (w v : X → ℝ)
    (hww : Integrable (fun x => w x ^ 2) μ)
    (hwv : Integrable (fun x => w x * v x) μ)
    (hvv : Integrable (fun x => v x ^ 2) μ) :
    (∫ x, (w x - v x) ^ 2 ∂μ) =
      (∫ x, w x ^ 2 ∂μ) - 2 * (∫ x, w x * v x ∂μ) + (∫ x, v x ^ 2 ∂μ) := by
  have h : (fun x => (w x - v x) ^ 2) =
      (fun x => w x ^ 2 - 2 * (w x * v x) + v x ^ 2) := by
    funext x
    ring
  have hadd := integral_add (hww.sub (hwv.const_mul 2)) hvv
  have hsub := integral_sub hww (hwv.const_mul 2)
  simp only [Pi.sub_apply] at hadd hsub
  rw [h, hadd, hsub, integral_const_mul]

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_CellVariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set

variable {X : Type*} [MeasurableSpace X]

theorem integral_sq_sub_const (μ : Measure X) [IsFiniteMeasure μ]
    (w : X → ℝ) (hw : MemLp w 2 μ) (a : ℝ) :
    (∫ x, (w x - a) ^ 2 ∂μ) = (∫ x, w x ^ 2 ∂μ) -
      2 * (∫ x, w x ∂μ) * a + μ.real univ * a ^ 2 := by
  have h := integral_squared_difference μ w (fun _ => a) hw.integrable_sq
    ((hw.integrable (by norm_num)).mul_const a) (integrable_const _)
  simpa only [integral_mul_const, integral_const, smul_eq_mul, mul_assoc] using! h

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_CellMeanBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set

variable {X : Type*} [MeasurableSpace X]

theorem cellMean_mul_mass (μ : Measure X) (w : X → ℝ) (hμ : μ.real univ ≠ 0) :
    μ.real univ * cellMean μ w = ∫ x, w x ∂μ := by
  unfold cellMean
  field_simp

theorem cellMean_sq_mass_le (μ : Measure X) [IsFiniteMeasure μ]
    (w : X → ℝ) (hw : MemLp w 2 μ) (hμ : μ.real univ ≠ 0) :
    μ.real univ * (cellMean μ w) ^ 2 ≤ ∫ x, w x ^ 2 ∂μ := by
  have hv := integral_sq_sub_const μ w hw (cellMean μ w)
  rw [← cellMean_mul_mass μ w hμ] at hv
  have hpos : 0 ≤ ∫ x, (w x - cellMean μ w) ^ 2 ∂μ :=
    integral_nonneg fun x => sq_nonneg _
  nlinarith

theorem cellMean_abs_bound (μ : Measure X) [IsFiniteMeasure μ]
    (w : X → ℝ) (hw : MemLp w 2 μ)
    (c B : ℝ) (hc : 0 < c) (hmass : c ≤ μ.real univ)
    (hB : (∫ x, w x ^ 2 ∂μ) ≤ B) :
    |cellMean μ w| ≤ B / c + 1 := by
  have hμ : 0 < μ.real univ := lt_of_lt_of_le hc hmass
  have hs : (cellMean μ w) ^ 2 ≤ B / c := by
    apply (le_div_iff₀ hc).2
    calc
      _ = c * (cellMean μ w) ^ 2 := mul_comm _ _
      _ ≤ μ.real univ * (cellMean μ w) ^ 2 :=
        mul_le_mul_of_nonneg_right hmass (sq_nonneg _)
      _ ≤ _ := (cellMean_sq_mass_le μ w hw hμ.ne').trans hB
  have hsmall : |cellMean μ w| ≤ (cellMean μ w) ^ 2 + 1 := by
    nlinarith [sq_nonneg (|cellMean μ w| - 1), sq_abs (cellMean μ w), sq_nonneg (cellMean μ w)]
  linarith

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_FiniteStepLp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite-step functions in L²

Finite-step functions on finite measures belong to L². Products are represented on
intersections of cells, expressing squared distances through cell masses and mixed moments.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Function Filter Topology

variable {X ι κ : Type*} [MeasurableSpace X] [Fintype ι] [Fintype κ]

theorem toLp_norm_sq_eq_integral (μ : Measure X) (f : X → ℝ) (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ ^ 2 = ∫ x, f x ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  simp only [hx, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_L2Pairings
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Integral pairings of real L² functions

The L² inner product agrees with integration of pointwise products. Subtraction and
Cauchy–Schwarz then bound differences of pairings by squared L² errors.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Function Filter Topology

variable {X : Type*} [MeasurableSpace X]

theorem real_scalar_inner_mul (a b : ℝ) : inner ℝ a b = a * b := by
  rw [real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two]
  simp only [← pow_two, Real.norm_eq_abs, sq_abs]
  ring

theorem toLp_inner_eq_integral (μ : Measure X) (f g : X → ℝ)
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    inner ℝ (hf.toLp f) (hg.toLp g) = ∫ x, f x * g x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
  rw [hx, hy, real_scalar_inner_mul]

theorem integral_mul_sub_eq (μ : Measure X) (f g ψ : X → ℝ)
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) (hψ : MemLp ψ 2 μ) :
    (∫ x, (f x - g x) * ψ x ∂μ) =
      (∫ x, f x * ψ x ∂μ) - (∫ x, g x * ψ x ∂μ) := by
  have hfp : MemLp (fun x => f x * ψ x) 1 μ := MeasureTheory.MemLp.mul (hφ := hf) (hf := hψ)
  have hgp : MemLp (fun x => g x * ψ x) 1 μ := MeasureTheory.MemLp.mul (hφ := hg) (hf := hψ)
  simp_rw [sub_mul]
  exact integral_sub (memLp_one_iff_integrable.mp hfp) (memLp_one_iff_integrable.mp hgp)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Packing_FiniteWeightedSchur
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

theorem weighted_young_real (x y u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
    2 * x * y ≤ x ^ 2 * v / u + y ^ 2 * u / v := by
  have heq : (x ^ 2 * v / u + y ^ 2 * u / v - 2 * x * y) * (u * v) =
      (v * x - u * y) ^ 2 := by
    field_simp
    ring
  have hp := sq_nonneg (v * x - u * y)
  rw [← heq] at hp
  have hnonneg : 0 ≤ x ^ 2 * v / u + y ^ 2 * u / v - 2 * x * y :=
    nonneg_of_mul_nonneg_left hp (mul_pos hu hv)
  linarith

theorem finite_weighted_schur_quadratic {ι : Type*} (s : Finset ι)
    (k : ι → ι → ℝ) (w a : ι → ℝ) (C : ℝ)
    (hw : ∀ i ∈ s, 0 < w i) (hk : ∀ i ∈ s, ∀ j ∈ s, 0 ≤ k i j)
    (hsymm : ∀ i ∈ s, ∀ j ∈ s, k j i = k i j)
    (hrow : ∀ i ∈ s, ∑ j ∈ s, k i j * w j ≤ C * w i) :
    (∑ i ∈ s, ∑ j ∈ s, |a i| * |a j| * k i j) ≤ C * ∑ i ∈ s, a i ^ 2 := by
  have hpoint (i : ι) (hi : i ∈ s) (j : ι) (hj : j ∈ s) :
      2 * (|a i| * |a j| * k i j) ≤
        a i ^ 2 * k i j * w j / w i + a j ^ 2 * k i j * w i / w j := by
    have hy := weighted_young_real |a i| |a j| (w i) (w j) (hw i hi) (hw j hj)
    simp only [sq_abs] at hy
    calc
      _ = (2 * |a i| * |a j|) * k i j := by ring
      _ ≤ (a i ^ 2 * w j / w i + a j ^ 2 * w i / w j) * k i j :=
        mul_le_mul_of_nonneg_right hy (hk i hi j hj)
      _ = _ := by ring
  let A : ℝ := ∑ i ∈ s, ∑ j ∈ s, a i ^ 2 * k i j * w j / w i
  let B : ℝ := ∑ i ∈ s, ∑ j ∈ s, a j ^ 2 * k i j * w i / w j
  have hA : A ≤ C * ∑ i ∈ s, a i ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    calc
      _ = (a i ^ 2 / w i) * (∑ j ∈ s, k i j * w j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ ≤ (a i ^ 2 / w i) * (C * w i) :=
        mul_le_mul_of_nonneg_left (hrow i hi) (div_nonneg (sq_nonneg _) (hw i hi).le)
      _ = C * a i ^ 2 := by field_simp [(hw i hi).ne']
  have hBA : B = A := by
    dsimp only [A, B]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hsymm i hi j hj]
  have hh := Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun j hj => hpoint i hi j hj))
  have htwo : 2 * (∑ i ∈ s, ∑ j ∈ s, |a i| * |a j| * k i j) ≤ A + B := by
    simpa only [A, B, Finset.sum_add_distrib, Finset.mul_sum] using! hh
  rw [hBA] at htwo
  linarith

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Packing_WeightedGramBessel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory

theorem finite_synthesis_sq_le_weighted_gram {ι E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (s : Finset ι) (h : ι → E) (w a : ι → ℝ) (C : ℝ)
    (hw : ∀ i ∈ s, 0 < w i)
    (hrow : ∀ i ∈ s, ∑ j ∈ s, |inner ℝ (h i) (h j)| * w j ≤ C * w i) :
    ‖∑ i ∈ s, a i • h i‖ ^ 2 ≤ C * ∑ i ∈ s, a i ^ 2 := by
  have heq : ‖∑ i ∈ s, a i • h i‖ ^ 2 =
      ∑ i ∈ s, ∑ j ∈ s, a i * a j * inner ℝ (h i) (h j) := by
    rw [← real_inner_self_eq_norm_sq]
    simp_rw [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [heq]
  calc
    _ ≤ ∑ i ∈ s, ∑ j ∈ s, |a i| * |a j| * |inner ℝ (h i) (h j)| := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      simpa only [abs_mul] using! le_abs_self (a i * a j * inner ℝ (h i) (h j))
    _ ≤ _ := finite_weighted_schur_quadratic s (fun i j => |inner ℝ (h i) (h j)|) w a C hw
      (fun _ _ _ _ => abs_nonneg _) (fun i _ j _ => by rw [real_inner_comm]) hrow

theorem finite_bessel_of_weighted_gram {ι E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (s : Finset ι) (h : ι → E) (w : ι → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hw : ∀ i ∈ s, 0 < w i)
    (hrow : ∀ i ∈ s, ∑ j ∈ s, |inner ℝ (h i) (h j)| * w j ≤ C * w i) (u : E) :
    ∑ i ∈ s, (inner ℝ (h i) u) ^ 2 ≤ C * ‖u‖ ^ 2 := by
  let a := fun i => inner ℝ (h i) u
  let S : ℝ := ∑ i ∈ s, a i ^ 2
  let v := ∑ i ∈ s, a i • h i
  have hSv : inner ℝ v u = S := by
    simp only [v, S, a, sum_inner, real_inner_smul_left, pow_two]
  have hv : ‖v‖ ^ 2 ≤ C * S := finite_synthesis_sq_le_weighted_gram s h w a C hw hrow
  have hcs := real_inner_mul_inner_self_le v u
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hSv] at hcs
  have hcs' : S ^ 2 ≤ ‖v‖ ^ 2 * ‖u‖ ^ 2 := by simpa only [pow_two] using! hcs
  have hsq : S ^ 2 ≤ C * S * ‖u‖ ^ 2 := by
    exact hcs'.trans (mul_le_mul_of_nonneg_right hv (sq_nonneg ‖u‖))
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  change S ≤ C * ‖u‖ ^ 2
  by_cases hzero : S = 0
  · rw [hzero]
    exact mul_nonneg hC (sq_nonneg _)
  · have hpos : 0 < S := lt_of_le_of_ne hS (Ne.symm hzero)
    nlinarith

theorem finite_L2_bessel_of_weighted_pairings {ι X : Type*} [MeasurableSpace X]
    (μ : Measure X) (s : Finset ι) (f : ι → X → ℝ) (hf : ∀ i, MemLp (f i) 2 μ)
    (w : ι → ℝ) (C : ℝ) (hC : 0 ≤ C) (hw : ∀ i ∈ s, 0 < w i)
    (hrow : ∀ i ∈ s, ∑ j ∈ s, |∫ x, f i x * f j x ∂μ| * w j ≤ C * w i)
    (u : X → ℝ) (hu : MemLp u 2 μ) :
    ∑ i ∈ s, (∫ x, f i x * u x ∂μ) ^ 2 ≤ C * ∫ x, u x ^ 2 ∂μ := by
  have hGram : ∀ i ∈ s, ∑ j ∈ s, |inner ℝ ((hf i).toLp (f i)) ((hf j).toLp (f j))| * w j ≤ C * w i := by
    simpa only [toLp_inner_eq_integral] using! hrow
  have hb := finite_bessel_of_weighted_gram s (fun i => (hf i).toLp (f i)) w C hC hw hGram (hu.toLp u)
  simpa only [toLp_inner_eq_integral, toLp_norm_sq_eq_integral] using! hb

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_SeparatedSupportNets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Maximal separated extensions give covering nets. Positive separation also gives discreteness,
countability in separable spaces, and finiteness on compact sets.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set TopologicalSpace

theorem separated_set_countable {X : Type*} [MetricSpace X] [SeparableSpace X]
    (N : Set X) (r : ℝ) (hr : 0 < r)
    (hsep : N.Pairwise fun x y => r ≤ dist x y) : N.Countable := by
  have hd : N.PairwiseDisjoint (fun x => ball x (r / 2)) := by
    intro x hx y hy hxy
    apply ball_disjoint_ball
    linarith [hsep hx hy hxy]
  exact hd.countable_of_isOpen (fun _ _ => isOpen_ball)
    (fun x _ => ⟨x, mem_ball_self (by positivity)⟩)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_AnnularLatticeScales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open Filter Topology

theorem annularLatticeDepth_radius_upper (R : ℝ) (k : ℕ) (r : ℝ) (hr : 0 < r) :
    latticeRadius R (k + annularLatticeDepth R k r hr) ≤ r / 8 := by
  classical
  exact Nat.find_spec (exists_annular_lattice_depth R k r hr)

theorem annularLatticeDepth_minimal (R : ℝ) (k : ℕ) (r : ℝ) (hr : 0 < r)
    (t : ℕ) (ht : latticeRadius R (k + t) ≤ r / 8) :
    annularLatticeDepth R k r hr ≤ t := by
  classical
  exact Nat.find_min' (exists_annular_lattice_depth R k r hr) ht

theorem annularLatticeDepth_antitone (R : ℝ) (k : ℕ) (r s : ℝ)
    (hr : 0 < r) (hs : 0 < s) (hrs : r ≤ s) :
    annularLatticeDepth R k s hs ≤ annularLatticeDepth R k r hr :=
  annularLatticeDepth_minimal R k s hs _
    ((annularLatticeDepth_radius_upper R k r hr).trans (by linarith))

theorem annularLatticeDepth_radius_lower (R : ℝ) (hR : 0 < R) (k : ℕ)
    (r : ℝ) (hr : 0 < r) (hrtop : r ≤ 8 * latticeRadius R k) :
    r ≤ 512 * latticeRadius R (k + annularLatticeDepth R k r hr) := by
  generalize hd : annularLatticeDepth R k r hr = t
  cases t with
  | zero =>
    simp only [Nat.add_zero]
    have hp := latticeRadius_pos R hR k
    linarith
  | succ t =>
    have hp : r / 8 < latticeRadius R (k + t) := by
      by_contra hbad
      have hm := annularLatticeDepth_minimal R k r hr t (le_of_not_gt hbad)
      rw [hd] at hm
      omega
    rw [← Nat.add_assoc, latticeRadius_succ]
    linarith

theorem annularLatticeDepth_pos (R : ℝ) (k : ℕ) (r : ℝ) (hr : 0 < r)
    (hrtop : r < 8 * latticeRadius R k) : 0 < annularLatticeDepth R k r hr := by
  have hu := annularLatticeDepth_radius_upper R k r hr
  by_contra ht
  have hz : annularLatticeDepth R k r hr = 0 := by omega
  rw [hz, Nat.add_zero] at hu
  linarith

theorem exists_uniform_annular_lattice_depth (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ I : ℕ, 0 < I ∧ ∀ (R : ℝ), 0 < R → ∀ (k : ℕ) (r : ℝ) (hr : 0 < r),
      ρ * latticeRadius R k ≤ r → annularLatticeDepth R k r hr ≤ I := by
  obtain ⟨j, hj⟩ := exists_annular_lattice_depth 1 0 ρ hρ
  refine ⟨j + 1, by omega, ?_⟩
  intro R hR k r hr hmin
  apply annularLatticeDepth_minimal R k r hr (j + 1)
  have hi : latticeRadius 1 (j + 1) ≤ ρ / 8 :=
    (latticeRadius_antitone 1 (by norm_num) (Nat.le_succ j)).trans (by simpa using! hj)
  have hp := latticeRadius_pos R hR k
  calc
    _ = latticeRadius R k * latticeRadius 1 (j + 1) := by rw [latticeRadius_add]; simp [latticeRadius]
    _ ≤ latticeRadius R k * (ρ / 8) := mul_le_mul_of_nonneg_left hi hp.le
    _ ≤ r / 8 := by linarith

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_ADHoleDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
AD lower bounds and global upper growth quantify the density lost to a ball-shaped hole.
Persistent holes at vanishing scales force a measurable set to have zero measure.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal NNReal

theorem ballHoleDensityDefect_pos (n : ℕ) (C G : ℝ) (hC : 0 < C) (hG : 0 < G) :
    0 < ballHoleDensityDefect n C G := by
  unfold ballHoleDensityDefect
  positivity

theorem ad_ball_hole_density_bound {n d : ℕ} (μ : Measure (Ambient d)) (C G : ℝ)
    (hC : 0 < C) (hG : 0 < G) (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ z ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball z r))
    (A : Set (Ambient d)) (x z : Ambient d) (r : ℝ) (hr : 0 < r)
    (hz : z ∈ μ.support) (hnear : dist x z ≤ r) (hcore : AdmissibleRadius μ (r / 4))
    (hhole : Disjoint A (ball z (r / 4))) :
    0 < μ.real (closedBall x (2 * r)) ∧
      μ.real (A ∩ closedBall x (2 * r)) / μ.real (closedBall x (2 * r)) ≤
        1 - ballHoleDensityDefect n C G := by
  have hsub : ball z (r / 4) ⊆ closedBall x (2 * r) := by
    intro y hy
    change dist y x ≤ 2 * r
    have ht := dist_triangle y z x
    rw [dist_comm z x] at ht
    change dist y z < r / 4 at hy
    linarith
  have hbig : μ (closedBall x (2 * r)) ≤ ENNReal.ofReal (G * (3 * r) ^ n) :=
    (measure_mono (closedBall_subset_ball (by linarith : 2 * r < 3 * r))).trans
      (hg.2 x (3 * r) (by positivity))
  have hfin : μ (closedBall x (2 * r)) ≠ ∞ := (hbig.trans_lt ENNReal.ofReal_lt_top).ne
  have hholefin := measure_ne_top_of_subset hsub hfin
  have hsmall : (r / 4) ^ n / C ≤ μ.real (ball z (r / 4)) := by
    have h := ENNReal.toReal_mono hholefin (hlower z hz (r / 4) hcore)
    simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ (r / 4) ^ n / C), Measure.real] using! h
  have hpos : 0 < μ.real (closedBall x (2 * r)) :=
    (by positivity : 0 < (r / 4) ^ n / C).trans_le
      (hsmall.trans (measureReal_mono hsub hfin))
  refine ⟨hpos, ?_⟩
  have hsum : μ.real (A ∩ closedBall x (2 * r)) + μ.real (ball z (r / 4)) ≤
      μ.real (closedBall x (2 * r)) := by
    rw [← measureReal_union (hhole.mono_left inter_subset_left) measurableSet_ball
      (measure_ne_top_of_subset inter_subset_right hfin) hholefin]
    exact measureReal_mono (union_subset inter_subset_right hsub) hfin
  have hupper : μ.real (closedBall x (2 * r)) ≤ G * (3 * r) ^ n :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) hbig
  have hidentity : ballHoleDensityDefect n C G * (G * (3 * r) ^ n) = (r / 4) ^ n / C := by
    unfold ballHoleDensityDefect
    simp only [mul_pow, div_pow]
    field_simp
  have hdef : ballHoleDensityDefect n C G * μ.real (closedBall x (2 * r)) ≤
      μ.real (ball z (r / 4)) := by
    calc
      _ ≤ ballHoleDensityDefect n C G * (G * (3 * r) ^ n) :=
        mul_le_mul_of_nonneg_left hupper (ballHoleDensityDefect_pos n C G hC hG).le
      _ = _ := hidentity
      _ ≤ _ := hsmall
  apply (div_le_iff₀ hpos).mpr
  linarith

theorem measurable_set_null_of_uniform_ball_holes {n d : ℕ}
    (μ : Measure (Ambient d)) (C G : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ z ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball z r))
    (A : Set (Ambient d)) (hA : MeasurableSet A)
    (r : ℕ → ℝ) (hr : ∀ k, 0 < r k) (ht : Tendsto r atTop (𝓝 0))
    (hcore : ∀ k, AdmissibleRadius μ (r k / 4))
    (hhole : ∀ x ∈ A, ∀ k, ∃ z ∈ μ.support, dist x z ≤ r k ∧ Disjoint A (ball z (r k / 4))) :
    μ A = 0 := by
  let : IsFiniteMeasureOnCompacts μ := globalGrowth_finite_on_compacts G μ hg
  have hrt : Tendsto (fun k => 2 * r k) atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, Filter.Eventually.of_forall (fun k => ?_)⟩
    · simpa only [mul_zero] using! ht.const_mul 2
    · change 0 < 2 * r k
      exact mul_pos (by norm_num) (hr k)
  have hzero : ∀ᵐ x ∂μ.restrict A, False := by
    filter_upwards [Besicovitch.ae_tendsto_measure_inter_div μ A, ae_restrict_mem hA] with x hx hxA
    have hd := hx.comp hrt
    have hdreal : Tendsto (fun k => μ.real (A ∩ closedBall x (2 * r k)) /
        μ.real (closedBall x (2 * r k))) atTop (𝓝 (1 : ℝ)) := by
      simpa only [Function.comp_def, ENNReal.toReal_div, ENNReal.toReal_one, Measure.real] using!
        (ENNReal.continuousAt_toReal (by norm_num : (1 : ℝ≥0∞) ≠ ∞)).tendsto.comp hd
    have hb : (1 : ℝ) ≤ 1 - ballHoleDensityDefect n C G := by
      apply le_of_tendsto hdreal
      apply Filter.Eventually.of_forall
      intro k
      obtain ⟨z, hz, hnear, hh⟩ := hhole x hxA k
      exact (ad_ball_hole_density_bound μ C G hC hG hg hlower A x z (r k) (hr k)
        hz hnear (hcore k) hh).2
    have hp := ballHoleDensityDefect_pos n C G hC hG
    linarith
  simpa using! (ae_iff.mp hzero)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_NetDescendantCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open Metric Set

theorem netDescendants_subset {X : Type*} [MetricSpace X] {E : Set X} {r : ℕ → ℝ}
    (N : (k : ℕ) → SeparatedCover E (r k)) (k : ℕ) (z : E) : netDescendants N k z ⊆ E := by
  rintro x ⟨t, hx, _, _⟩
  exact hx

theorem closedNetCell_isClosed {X : Type*} [MetricSpace X] {E : Set X} {r : ℕ → ℝ}
    (N : (k : ℕ) → SeparatedCover E (r k)) (k : ℕ) (z : E) : IsClosed (closedNetCell N k z) :=
  isClosed_closure

theorem closedNetCell_subset {X : Type*} [MetricSpace X] {E : Set X} {r : ℕ → ℝ}
    (N : (k : ℕ) → SeparatedCover E (r k)) (hE : IsClosed E) (k : ℕ) (z : E) :
    closedNetCell N k z ⊆ E :=
  hE.closure_subset_iff.mpr (netDescendants_subset N k z)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_ClosedNetCellCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Covering by closed net cells

The geometric decay of lattice radii lets fine net points approximate every point of the
underlying set. Ancestor forcing places relative balls inside their closed cells, while
properness reduces nearby ancestors to finitely many choices and yields a closed-cell cover.
-/

namespace RieszRectifiability

noncomputable section

open Metric Set Filter Topology

theorem exists_closedNetCell_containing {X : Type*} [MetricSpace X] [ProperSpace X]
    {E : Set X} (R : ℝ) (hR : 0 < R)
    (N : (k : ℕ) → SeparatedCover E (latticeRadius R k)) (k : ℕ) (y : E) :
    ∃ z : E, (z : X) ∈ (N k).points ∧ (y : X) ∈ closedNetCell N k z := by
  classical
  let S := (N k).points ∩ closedBall (y : X) (3 * latticeRadius R k)
  have hS : S.Finite := separated_set_finite_inter_compact _ _ (latticeRadius R k)
    (latticeRadius_pos R hR k) (N k).separated (isCompact_closedBall _ _)
  let : Fintype S := hS.fintype
  let center : S → E := fun z => ⟨z, (N k).subset z.property.1⟩
  have hclosure : (y : X) ∈ closure (⋃ z : S, netDescendants N k (center z)) := by
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨t, ht⟩ := exists_latticeRadius_tail_lt R hR k ε hε
    obtain ⟨x, hxN, hyx⟩ := (N (k + t + 1)).covers y y.property
    have hxE := (N (k + t + 1)).subset hxN
    let z := netAncestor N k (t + 1) ⟨x, hxE⟩
    have hzN : (z : X) ∈ (N k).points := netAncestor_mem N k t _
    have hzy : dist (z : X) (y : X) ≤ 3 * latticeRadius R k := by
      have hd := dist_triangle (z : X) x (y : X)
      rw [dist_comm (z : X) x, dist_comm x (y : X)] at hd
      have ha := netAncestor_dist_le_latticeRadius R hR N k (t + 1) ⟨x, hxE⟩
      have hs := latticeRadius_antitone R hR.le (show k ≤ k + t + 1 by omega)
      change dist x (z : X) ≤ _ at ha
      linarith
    let w : S := ⟨z, ⟨hzN, hzy⟩⟩
    refine ⟨x, mem_iUnion.mpr ⟨w, ?_⟩, hyx.trans ht⟩
    refine ⟨t + 1, hxE, ?_, ?_⟩
    · simpa only [Nat.add_succ] using! hxN
    · rfl
  rw [closure_iUnion_of_finite] at hclosure
  obtain ⟨z, hz⟩ := mem_iUnion.mp hclosure
  exact ⟨center z, z.property.1, hz⟩

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_ConstructedSupportCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

theorem supportLatticeNets_countable {d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R)
    (k : ℕ) : (supportLatticeNets μ R hR k).points.Countable :=
  separated_set_countable _ _ (latticeRadius_pos R hR k) (supportLatticeNets μ R hR k).separated

theorem supportLatticeCell_closed {d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R)
    (k : ℕ) (z : (supportLatticeNets μ R hR k).points) : IsClosed (supportLatticeCell μ R hR k z) :=
  closedNetCell_isClosed _ _ _

theorem supportLatticeCell_subset_support {d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R)
    (k : ℕ) (z : (supportLatticeNets μ R hR k).points) : supportLatticeCell μ R hR k z ⊆ μ.support :=
  closedNetCell_subset _ μ.isClosed_support _ _

theorem supportLatticeCell_cover {d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R)
    (k : ℕ) (x : Ambient d) (hx : x ∈ μ.support) :
    ∃ z : (supportLatticeNets μ R hR k).points, x ∈ supportLatticeCell μ R hR k z := by
  obtain ⟨z, hz, hcell⟩ := exists_closedNetCell_containing R hR (supportLatticeNets μ R hR) k ⟨x, hx⟩
  exact ⟨⟨z, hz⟩, hcell⟩

theorem supportLatticeCell_compact {d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R)
    (k : ℕ) (z : (supportLatticeNets μ R hR k).points) : IsCompact (supportLatticeCell μ R hR k z) :=
  (isCompact_closedBall (z : Ambient d) (2 * latticeRadius R k)).of_isClosed_subset
    (supportLatticeCell_closed μ R hR k z) (supportLatticeCell_bounds μ R hR k z).2

theorem supportLatticeCell_measure_bounds {n d : ℕ} (μ : Measure (Ambient d)) (C G : ℝ)
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (hcore : AdmissibleRadius μ (latticeRadius R k / 8))
    (z : (supportLatticeNets μ R hR k).points) :
    ENNReal.ofReal ((latticeRadius R k / 8) ^ n / C) ≤ μ (supportLatticeCell μ R hR k z) ∧
      μ (supportLatticeCell μ R hR k z) ≤ ENNReal.ofReal (G * (3 * latticeRadius R k) ^ n) := by
  have hball : μ (μ.support ∩ ball (z : Ambient d) (latticeRadius R k / 8)) =
      μ (ball (z : Ambient d) (latticeRadius R k / 8)) := by
    apply measure_congr
    filter_upwards [μ.support_mem_ae] with x hx
    apply propext
    change (x ∈ μ.support ∧ x ∈ ball (z : Ambient d) (latticeRadius R k / 8)) ↔
      x ∈ ball (z : Ambient d) (latticeRadius R k / 8)
    simp only [hx, true_and]
  constructor
  · calc
      _ ≤ μ (ball (z : Ambient d) (latticeRadius R k / 8)) :=
        hlower z ((supportLatticeNets μ R hR k).subset z.property) _ hcore
      _ = _ := hball.symm
      _ ≤ _ := measure_mono (supportLatticeCell_bounds μ R hR k z).1
  · have hsub : closedBall (z : Ambient d) (2 * latticeRadius R k) ⊆
        ball (z : Ambient d) (3 * latticeRadius R k) :=
      closedBall_subset_ball (by have hp := latticeRadius_pos R hR k; linarith)
    apply (measure_mono ((supportLatticeCell_bounds μ R hR k z).2.trans hsub)).trans
    exact hg.2 z _ (mul_pos (by norm_num) (latticeRadius_pos R hR k))

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_SupportCellOverlaps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Null overlaps of support lattice cells

The countable union of intersections of distinct closed cells is measurable and avoids
every deep core ball. Upper growth and lower AD bounds turn these holes into nullity;
when a core radius exceeds the support diameter, separation makes the overlap empty.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal NNReal

theorem supportLatticeOverlap_measurable {d : ℕ} (μ : Measure (Ambient d)) (R : ℝ)
    (hR : 0 < R) (k : ℕ) : MeasurableSet (supportLatticeOverlap μ R hR k) := by
  classical
  let : Countable (supportLatticeNets μ R hR k).points :=
    (supportLatticeNets_countable μ R hR k).to_subtype
  apply MeasurableSet.iUnion
  intro z
  apply MeasurableSet.iUnion
  intro w
  split_ifs
  · exact MeasurableSet.empty
  · exact (supportLatticeCell_closed μ R hR k z).measurableSet.inter
      (supportLatticeCell_closed μ R hR k w).measurableSet

theorem supportLatticeOverlap_subset_support {d : ℕ} (μ : Measure (Ambient d)) (R : ℝ)
    (hR : 0 < R) (k : ℕ) : supportLatticeOverlap μ R hR k ⊆ μ.support := by
  intro x hx
  obtain ⟨z, _, _, hz, _⟩ := (mem_supportLatticeOverlap μ R hR k x).mp hx
  exact supportLatticeCell_subset_support μ R hR k z hz

theorem supportLatticeOverlap_null_of_admissible_core {n d : ℕ}
    (μ : Measure (Ambient d)) (C G : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ z ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball z r))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (hcore : AdmissibleRadius μ (latticeRadius R k / 4)) :
    μ (supportLatticeOverlap μ R hR k) = 0 := by
  apply measurable_set_null_of_uniform_ball_holes μ C G hC hG hg hlower
    (supportLatticeOverlap μ R hR k) (supportLatticeOverlap_measurable μ R hR k)
    (fun q => latticeRadius R (k + q)) (fun q => latticeRadius_pos R hR (k + q))
  · simpa only [latticeRadius_add, mul_zero] using!
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 64)
        (by norm_num : (1 / 64 : ℝ) < 1)).const_mul (latticeRadius R k)
  · intro q
    refine ⟨div_pos (latticeRadius_pos R hR (k + q)) (by norm_num), ?_⟩
    exact (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right
      (latticeRadius_antitone R hR.le (Nat.le_add_right k q)) (by norm_num))).trans hcore.2
  · intro x hx q
    have hxE := supportLatticeOverlap_subset_support μ R hR k hx
    obtain ⟨z, hz, hnear⟩ := (supportLatticeNets μ R hR (k + q)).covers x hxE
    exact ⟨z, (supportLatticeNets μ R hR (k + q)).subset hz, hnear.le,
      supportLatticeOverlap_disjoint_deep_core μ R hR k q ⟨z, hz⟩⟩

theorem supportLatticeOverlap_null {n d : ℕ}
    (μ : Measure (Ambient d)) (C G : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ z ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball z r))
    (R : ℝ) (hR : 0 < R) (k : ℕ) : μ (supportLatticeOverlap μ R hR k) = 0 := by
  by_cases hcore : ENNReal.ofReal (latticeRadius R k / 4) ≤ ediam μ.support
  · exact supportLatticeOverlap_null_of_admissible_core μ C G hC hG hg hlower R hR k
      ⟨div_pos (latticeRadius_pos R hR k) (by norm_num), hcore⟩
  · have hempty : supportLatticeOverlap μ R hR k = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      obtain ⟨z, w, hne, _, _⟩ := (mem_supportLatticeOverlap μ R hR k x).mp hx
      have hsep := (supportLatticeNets μ R hR k).separated z.property w.property
        (fun h => hne (Subtype.ext h))
      have hdiam := edist_le_ediam_of_mem
        ((supportLatticeNets μ R hR k).subset z.property)
        ((supportLatticeNets μ R hR k).subset w.property)
      apply hcore
      have hp := latticeRadius_pos R hR k
      have hd : latticeRadius R k / 4 ≤ dist (z : Ambient d) (w : Ambient d) := by linarith
      exact (ENNReal.ofReal_le_ofReal hd).trans (by simpa only [edist_dist] using! hdiam)
    rw [hempty, measure_empty]

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_CleanSupportPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Cleaning the support lattice partition

Removing the union of all cell overlaps produces nested, disjoint measurable cells that
cover the support outside one exceptional set. Net centers avoid that set, so cleaning
preserves the closed cells as closures. Under the growth bounds, it also preserves cell
mass and gives a unique cell at every scale almost everywhere.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal NNReal

theorem supportLatticeExceptional_measurable {d : ℕ} (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) : MeasurableSet (supportLatticeExceptional μ R hR) :=
  MeasurableSet.iUnion (supportLatticeOverlap_measurable μ R hR)

theorem supportLatticeExceptional_null {n d : ℕ}
    (μ : Measure (Ambient d)) (C G : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ z ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball z r))
    (R : ℝ) (hR : 0 < R) : μ (supportLatticeExceptional μ R hR) = 0 :=
  measure_iUnion_null (fun k => supportLatticeOverlap_null μ C G hC hG hg hlower R hR k)

theorem cleanSupportCell_measurable {d : ℕ} (μ : Measure (Ambient d)) (R : ℝ)
    (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points) :
    MeasurableSet (cleanSupportCell μ R hR k z) :=
  (supportLatticeCell_closed μ R hR k z).measurableSet.diff
    (supportLatticeExceptional_measurable μ R hR)

theorem cleanSupportCell_measure_eq {n d : ℕ}
    (μ : Measure (Ambient d)) (C G : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ z ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball z r))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points) :
    μ (cleanSupportCell μ R hR k z) = μ (supportLatticeCell μ R hR k z) :=
  measure_sdiff_null (supportLatticeExceptional_null μ C G hC hG hg hlower R hR)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_FiniteSupportRefinements
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

theorem cleanSupportCell_measure_bounds {n d : ℕ}
    (μ : Measure (Ambient d)) (C G : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ z ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball z r))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (hcore : AdmissibleRadius μ (latticeRadius R k / 8))
    (z : (supportLatticeNets μ R hR k).points) :
    ENNReal.ofReal ((latticeRadius R k / 8) ^ n / C) ≤ μ (cleanSupportCell μ R hR k z) ∧
      μ (cleanSupportCell μ R hR k z) ≤ ENNReal.ofReal (G * (3 * latticeRadius R k) ^ n) := by
  rw [cleanSupportCell_measure_eq μ C G hC hG hg hlower R hR k z]
  exact supportLatticeCell_measure_bounds μ C G hg hlower R hR k hcore z

theorem cleanSupportCell_measure_pos_finite {n d : ℕ}
    (μ : Measure (Ambient d)) (C G : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ z ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball z r))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (hcore : AdmissibleRadius μ (latticeRadius R k / 8))
    (z : (supportLatticeNets μ R hR k).points) :
    0 < μ (cleanSupportCell μ R hR k z) ∧ μ (cleanSupportCell μ R hR k z) < ∞ := by
  have hb := cleanSupportCell_measure_bounds μ C G hC hG hg hlower R hR k hcore z
  exact ⟨(ENNReal.ofReal_pos.mpr (div_pos (pow_pos hcore.1 n) hC)).trans_le hb.1,
    hb.2.trans_lt ENNReal.ofReal_lt_top⟩

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_NormalizedSetIndicators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Normalized indicators weight a measurable set by the reciprocal of its real mass.
Finite set mass gives integrability and L² membership for these averaging functions.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

variable {X : Type*} [MeasurableSpace X]

theorem normalizedSetIndicator_of_mem (μ : Measure X) (A : Set X) (x : X) (hx : x ∈ A) :
    normalizedSetIndicator μ A x = (μ.real A)⁻¹ := indicator_of_mem hx _

theorem normalizedSetIndicator_of_notMem (μ : Measure X) (A : Set X) (x : X) (hx : x ∉ A) :
    normalizedSetIndicator μ A x = 0 := indicator_of_notMem hx _

theorem normalizedSetIndicator_memLp (μ : Measure X) (A : Set X)
    (hA : MeasurableSet A) (hfin : μ A < ∞) : MemLp (normalizedSetIndicator μ A) 2 μ := by
  let : IsFiniteMeasure (μ.restrict A) := ⟨by simpa only [Measure.restrict_apply_univ] using! hfin⟩
  exact (memLp_indicator_iff_restrict hA).mpr (memLp_const _)

theorem normalizedSetIndicator_integrable (μ : Measure X) (A : Set X)
    (hA : MeasurableSet A) (hfin : μ A < ∞) : Integrable (normalizedSetIndicator μ A) μ :=
  (integrable_indicator_iff hA).mpr (integrableOn_const hfin.ne)

theorem normalizedSetIndicator_integral (μ : Measure X) (A : Set X)
    (hA : MeasurableSet A) (hpos : 0 < μ.real A) :
    (∫ x, normalizedSetIndicator μ A x ∂μ) = 1 := by
  rw [normalizedSetIndicator, integral_indicator hA, setIntegral_const, smul_eq_mul]
  exact mul_inv_cancel₀ hpos.ne'

theorem normalizedSetIndicator_pairing (μ : Measure X) (A : Set X)
    (hA : MeasurableSet A) (f : X → ℝ) :
    (∫ x, normalizedSetIndicator μ A x * f x ∂μ) = cellMean (μ.restrict A) f := by
  have heq : (fun x => normalizedSetIndicator μ A x * f x) =
      A.indicator (fun x => (μ.real A)⁻¹ * f x) := by
    funext x
    by_cases hx : x ∈ A <;> simp [normalizedSetIndicator, hx]
  rw [heq, integral_indicator hA, integral_const_mul]
  simp only [cellMean, Measure.real, Measure.restrict_apply_univ, div_eq_mul_inv, mul_comm]

theorem normalizedSetIndicator_sq_integral (μ : Measure X) (A : Set X)
    (hA : MeasurableSet A) (hpos : 0 < μ.real A) :
    (∫ x, normalizedSetIndicator μ A x ^ 2 ∂μ) = (μ.real A)⁻¹ := by
  have heq : (fun x => normalizedSetIndicator μ A x ^ 2) =
      A.indicator (fun _ => ((μ.real A)⁻¹) ^ 2) := by
    funext x
    by_cases hx : x ∈ A <;> simp [normalizedSetIndicator, hx]
  rw [heq, integral_indicator hA, setIntegral_const, smul_eq_mul]
  field_simp

theorem normalizedSetIndicator_nested_product_integral (μ : Measure X) (A B : Set X)
    (hA : MeasurableSet A) (hAB : A ⊆ B) (hpos : 0 < μ.real A) :
    (∫ x, normalizedSetIndicator μ A x * normalizedSetIndicator μ B x ∂μ) = (μ.real B)⁻¹ := by
  have heq : (fun x => normalizedSetIndicator μ A x * normalizedSetIndicator μ B x) =
      A.indicator (fun _ => (μ.real A)⁻¹ * (μ.real B)⁻¹) := by
    funext x
    by_cases hx : x ∈ A
    · simp only [normalizedSetIndicator_of_mem μ A x hx,
        normalizedSetIndicator_of_mem μ B x (hAB hx), indicator_of_mem hx]
    · simp only [normalizedSetIndicator_of_notMem μ A x hx, zero_mul, indicator_of_notMem hx]
  rw [heq, integral_indicator hA, setIntegral_const, smul_eq_mul, ← mul_assoc,
    mul_inv_cancel₀ hpos.ne', one_mul]

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_NestedCellIndicators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem cleanSupportCell_nested_or_disjoint {d : ℕ} (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) (k l : ℕ) (hkl : k ≤ l)
    (z : (supportLatticeNets μ R hR k).points) (w : (supportLatticeNets μ R hR l).points) :
    cleanSupportCell μ R hR l w ⊆ cleanSupportCell μ R hR k z ∨
      Disjoint (cleanSupportCell μ R hR l w) (cleanSupportCell μ R hR k z) := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hkl
  by_cases h : supportLatticeAncestor μ R hR k t w = z
  · left
    simpa only [h] using! cleanSupportCell_nested μ R hR k t w
  · right
    exact (cleanSupportCell_disjoint μ R hR k _ z h).mono_left
      (cleanSupportCell_nested μ R hR k t w)

theorem normalizedSetIndicator_const_of_nested_or_disjoint {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (A B : Set X) (h : B ⊆ A ∨ Disjoint B A) :
    ∃ c : ℝ, ∀ x ∈ B, normalizedSetIndicator μ A x = c := by
  rcases h with h | h
  · exact ⟨(μ.real A)⁻¹, fun x hx => normalizedSetIndicator_of_mem μ A x (h hx)⟩
  · exact ⟨0, fun x hx => normalizedSetIndicator_of_notMem μ A x
      (fun hy => Set.disjoint_left.mp h hx hy)⟩

theorem normalizedCellIndicator_const_on_finer {d : ℕ} (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) (k l : ℕ) (hkl : k ≤ l)
    (z : (supportLatticeNets μ R hR k).points) (w : (supportLatticeNets μ R hR l).points) :
    ∃ c : ℝ, ∀ x ∈ cleanSupportCell μ R hR l w,
      normalizedSetIndicator μ (cleanSupportCell μ R hR k z) x = c :=
  normalizedSetIndicator_const_of_nested_or_disjoint μ _ _
    (cleanSupportCell_nested_or_disjoint μ R hR k l hkl z w)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Packing_CellHaarFunctions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Haar functions for nested cells

The difference of normalized indicators, scaled by the square root of the smaller cell's
mass, has mean zero. Its squared integral is the complementary mass ratio, and pairing
with an `L²` function recovers the difference of the two cell means.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

variable {X : Type*} [MeasurableSpace X]

theorem cellHaar_memLp (μ : Measure X) (A B : Set X)
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hAf : μ A < ∞) (hBf : μ B < ∞) :
    MemLp (cellHaar μ A B) 2 μ :=
  ((normalizedSetIndicator_memLp μ A hA hAf).sub
    (normalizedSetIndicator_memLp μ B hB hBf)).const_mul (Real.sqrt (μ.real A))

theorem cellHaar_zero_of_notMem (μ : Measure X) (A B : Set X) (hAB : A ⊆ B)
    (x : X) (hx : x ∉ B) : cellHaar μ A B x = 0 := by
  rw [cellHaar, normalizedSetIndicator_of_notMem μ A x (fun h => hx (hAB h)),
    normalizedSetIndicator_of_notMem μ B x hx, sub_self, mul_zero]

theorem cellHaar_mean_zero (μ : Measure X) (A B : Set X)
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hAf : μ A < ∞) (hBf : μ B < ∞)
    (hAB : A ⊆ B) (hpos : 0 < μ.real A) : (∫ x, cellHaar μ A B x ∂μ) = 0 := by
  have hBpos : 0 < μ.real B := hpos.trans_le (measureReal_mono hAB hBf.ne)
  simp only [cellHaar]
  rw [integral_const_mul,
    integral_sub (normalizedSetIndicator_integrable μ A hA hAf)
      (normalizedSetIndicator_integrable μ B hB hBf),
    normalizedSetIndicator_integral μ A hA hpos,
    normalizedSetIndicator_integral μ B hB hBpos, sub_self, mul_zero]

theorem cellHaar_sq_integral (μ : Measure X) (A B : Set X)
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hAf : μ A < ∞) (hBf : μ B < ∞)
    (hAB : A ⊆ B) (hpos : 0 < μ.real A) :
    (∫ x, cellHaar μ A B x ^ 2 ∂μ) = 1 - μ.real A / μ.real B := by
  have hBpos : 0 < μ.real B := hpos.trans_le (measureReal_mono hAB hBf.ne)
  have ha := normalizedSetIndicator_memLp μ A hA hAf
  have hb := normalizedSetIndicator_memLp μ B hB hBf
  have hp : MemLp (fun x => normalizedSetIndicator μ A x * normalizedSetIndicator μ B x) 1 μ :=
    MemLp.mul' (hφ := ha) (hf := hb)
  simp only [cellHaar, mul_pow]
  rw [integral_const_mul, Real.sq_sqrt hpos.le,
    integral_squared_difference μ (normalizedSetIndicator μ A) (normalizedSetIndicator μ B)
      ha.integrable_sq (memLp_one_iff_integrable.mp hp) hb.integrable_sq,
    normalizedSetIndicator_sq_integral μ A hA hpos,
    normalizedSetIndicator_sq_integral μ B hB hBpos,
    normalizedSetIndicator_nested_product_integral μ A B hA hAB hpos]
  calc
    _ = μ.real A * (μ.real A)⁻¹ - μ.real A * (μ.real B)⁻¹ := by ring
    _ = _ := by rw [mul_inv_cancel₀ hpos.ne', div_eq_mul_inv]

theorem cellHaar_sq_integral_le_one (μ : Measure X) (A B : Set X)
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hAf : μ A < ∞) (hBf : μ B < ∞)
    (hAB : A ⊆ B) (hpos : 0 < μ.real A) : (∫ x, cellHaar μ A B x ^ 2 ∂μ) ≤ 1 := by
  rw [cellHaar_sq_integral μ A B hA hB hAf hBf hAB hpos]
  exact sub_le_self _ (div_nonneg measureReal_nonneg measureReal_nonneg)

theorem cellHaar_pairing (μ : Measure X) (A B : Set X)
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hAf : μ A < ∞) (hBf : μ B < ∞)
    (u : X → ℝ) (hu : MemLp u 2 μ) :
    (∫ x, cellHaar μ A B x * u x ∂μ) =
      Real.sqrt (μ.real A) * (cellMean (μ.restrict A) u - cellMean (μ.restrict B) u) := by
  simp only [cellHaar, mul_assoc]
  rw [integral_const_mul, integral_mul_sub_eq μ (normalizedSetIndicator μ A)
    (normalizedSetIndicator μ B) u (normalizedSetIndicator_memLp μ A hA hAf)
      (normalizedSetIndicator_memLp μ B hB hBf) hu,
    normalizedSetIndicator_pairing μ A hA u, normalizedSetIndicator_pairing μ B hB u]

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Packing_CellHaarPairGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

variable {d : ℕ} {μ : Measure (Ambient d)} {R : ℝ} {hR : 0 < R} {k I : ℕ}
  {z : (supportLatticeNets μ R hR k).points}

theorem CellHaarPair.outer_subset_parent (P : CellHaarPair μ R hR k z I) :
    P.outerCell ⊆ cleanSupportCell μ R hR k z := by
  have h := cleanSupportCell_nested μ R hR k P.outerOffset P.outerCenter
  rw [P.outer_ancestor] at h
  exact h

theorem CellHaarPair.inner_subset_outer (P : CellHaarPair μ R hR k z I) :
    P.innerCell ⊆ P.outerCell := by
  have h := cleanSupportCell_nested μ R hR (k + P.outerOffset) P.innerOffset P.innerCenter
  rw [P.inner_ancestor] at h
  exact h

theorem CellHaarPair.outer_measurable (P : CellHaarPair μ R hR k z I) : MeasurableSet P.outerCell :=
  cleanSupportCell_measurable μ R hR (k + P.outerOffset) P.outerCenter

theorem CellHaarPair.inner_measurable (P : CellHaarPair μ R hR k z I) : MeasurableSet P.innerCell :=
  cleanSupportCell_measurable μ R hR (k + P.outerOffset + P.innerOffset) P.innerCenter

theorem CellHaarPair.test_zero_outside_parent (P : CellHaarPair μ R hR k z I)
    (x : Ambient d) (hx : x ∉ cleanSupportCell μ R hR k z) : P.test x = 0 :=
  cellHaar_zero_of_notMem μ P.innerCell P.outerCell P.inner_subset_outer x
    (fun h => hx (P.outer_subset_parent h))

theorem CellHaarPair.test_constant_on_finer (P : CellHaarPair μ R hR k z I)
    (l : ℕ) (hl : k + I ≤ l) (w : (supportLatticeNets μ R hR l).points) :
    ∃ c : ℝ, ∀ x ∈ cleanSupportCell μ R hR l w, P.test x = c := by
  have ho : k + P.outerOffset ≤ l := by have h := P.depth_bound; omega
  have hi : k + P.outerOffset + P.innerOffset ≤ l := by have h := P.depth_bound; omega
  obtain ⟨co, hco⟩ := normalizedCellIndicator_const_on_finer μ R hR (k + P.outerOffset) l ho P.outerCenter w
  obtain ⟨ci, hci⟩ := normalizedCellIndicator_const_on_finer μ R hR
    (k + P.outerOffset + P.innerOffset) l hi P.innerCenter w
  refine ⟨Real.sqrt (μ.real P.innerCell) * (ci - co), ?_⟩
  intro x hx
  change Real.sqrt (μ.real P.innerCell) *
    (normalizedSetIndicator μ P.innerCell x - normalizedSetIndicator μ P.outerCell x) = _
  have hix : normalizedSetIndicator μ P.innerCell x = ci := hci x hx
  have hox : normalizedSetIndicator μ P.outerCell x = co := hco x hx
  rw [hix, hox]

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Packing_LatticeMassPacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Mass bounds for lattice descendants

Each descendant cell is contained in a ball with controlled radius. Global
upper growth therefore bounds its mass by a constant times the corresponding
power of its radius, both in extended and real-valued form.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

theorem cleanSupportCell_real_measure_bounds {n d : ℕ}
    (μ : Measure (Ambient d)) (C G : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (hcore : AdmissibleRadius μ (latticeRadius R k / 8))
    (z : (supportLatticeNets μ R hR k).points) :
    (latticeRadius R k / 8) ^ n / C ≤ μ.real (cleanSupportCell μ R hR k z) ∧
      μ.real (cleanSupportCell μ R hR k z) ≤ (G * 3 ^ n) * latticeRadius R k ^ n := by
  have hr := latticeRadius_pos R hR k
  have hb := cleanSupportCell_measure_bounds μ C G hC hG hg hlower R hR k hcore z
  have hf : μ (cleanSupportCell μ R hR k z) ≠ ∞ := (hb.2.trans_lt ENNReal.ofReal_lt_top).ne
  constructor
  · simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ (latticeRadius R k / 8) ^ n / C),
      Measure.real] using! ENNReal.toReal_mono hf hb.1
  · have hu := ENNReal.toReal_le_of_le_ofReal
      (by positivity : 0 ≤ G * (3 * latticeRadius R k) ^ n) hb.2
    simpa only [mul_pow, mul_assoc, Measure.real] using! hu

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Packing_ADCellHaarPairs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Haar tests on AD-regular lattice cells

Admissible core radii remain admissible at later lattice levels. Global upper
growth makes the clean cells finite, while the lower AD estimate gives positive
inner-cell mass. These facts yield mean-zero, L²-normalized Haar tests and the
exact pairing formula in terms of the inner and outer cell means.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

theorem lattice_core_admissible_at_later_level {d : ℕ} (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) (k l : ℕ) (hkl : k ≤ l)
    (hcore : AdmissibleRadius μ (latticeRadius R k / 8)) :
    AdmissibleRadius μ (latticeRadius R l / 8) := by
  refine ⟨div_pos (latticeRadius_pos R hR l) (by norm_num), ?_⟩
  exact (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right
    (latticeRadius_antitone R hR.le hkl) (by norm_num))).trans hcore.2

theorem cleanSupportCell_finite_of_growth {n d : ℕ} (μ : Measure (Ambient d))
    (G : ℝ) (hg : GlobalUpperGrowth n G μ) (R : ℝ) (hR : 0 < R)
    (k : ℕ) (z : (supportLatticeNets μ R hR k).points) :
    μ (cleanSupportCell μ R hR k z) < ∞ := by
  let : IsFiniteMeasureOnCompacts μ := globalGrowth_finite_on_compacts G μ hg
  exact (measure_mono sdiff_subset).trans_lt (supportLatticeCell_compact μ R hR k z).measure_lt_top

theorem CellHaarPair.cells_finite {n d : ℕ} {μ : Measure (Ambient d)}
    {R : ℝ} {hR : 0 < R} {k I : ℕ} {z : (supportLatticeNets μ R hR k).points}
    (P : CellHaarPair μ R hR k z I) (G : ℝ) (hg : GlobalUpperGrowth n G μ) :
    μ P.innerCell < ∞ ∧ μ P.outerCell < ∞ :=
  ⟨cleanSupportCell_finite_of_growth μ G hg R hR (k + P.outerOffset + P.innerOffset) P.innerCenter,
    cleanSupportCell_finite_of_growth μ G hg R hR (k + P.outerOffset) P.outerCenter⟩

theorem CellHaarPair.inner_real_pos {n d : ℕ} {μ : Measure (Ambient d)}
    {R : ℝ} {hR : 0 < R} {k I : ℕ} {z : (supportLatticeNets μ R hR k).points}
    (P : CellHaarPair μ R hR k z I) (C G : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
    (hcore : AdmissibleRadius μ (latticeRadius R k / 8)) : 0 < μ.real P.innerCell := by
  have ha := lattice_core_admissible_at_later_level μ R hR k
    (k + P.outerOffset + P.innerOffset) (by omega) hcore
  have hp := cleanSupportCell_measure_pos_finite μ C G hC hG hg hlower R hR
    (k + P.outerOffset + P.innerOffset) ha P.innerCenter
  exact ENNReal.toReal_pos hp.1.ne' hp.2.ne

theorem CellHaarPair.test_properties {n d : ℕ} {μ : Measure (Ambient d)}
    {R : ℝ} {hR : 0 < R} {k I : ℕ} {z : (supportLatticeNets μ R hR k).points}
    (P : CellHaarPair μ R hR k z I) (C G : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
    (hcore : AdmissibleRadius μ (latticeRadius R k / 8)) :
    MemLp P.test 2 μ ∧ (∫ x, P.test x ∂μ) = 0 ∧ (∫ x, P.test x ^ 2 ∂μ) ≤ 1 ∧
      ∀ u : Ambient d → ℝ, MemLp u 2 μ →
        (∫ x, P.test x * u x ∂μ) = Real.sqrt (μ.real P.innerCell) *
          (cellMean (μ.restrict P.innerCell) u - cellMean (μ.restrict P.outerCell) u) := by
  have hf := P.cells_finite G hg
  have hp := P.inner_real_pos C G hC hG hg hlower hcore
  exact ⟨cellHaar_memLp μ P.innerCell P.outerCell P.inner_measurable P.outer_measurable hf.1 hf.2,
    cellHaar_mean_zero μ P.innerCell P.outerCell P.inner_measurable P.outer_measurable
      hf.1 hf.2 P.inner_subset_outer hp,
    cellHaar_sq_integral_le_one μ P.innerCell P.outerCell P.inner_measurable P.outer_measurable
      hf.1 hf.2 P.inner_subset_outer hp,
    fun u hu => cellHaar_pairing μ P.innerCell P.outerCell P.inner_measurable P.outer_measurable
      hf.1 hf.2 u hu⟩

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_BoundaryCellGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

theorem clean_cell_dist_to_closed_point {d : ℕ} (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points)
    (a : Ambient d) (ha : a ∈ supportLatticeCell μ R hR k z)
    (x : Ambient d) (hx : x ∈ cleanSupportCell μ R hR k z) :
    dist x a ≤ 4 * latticeRadius R k := by
  have hb := (supportLatticeCell_bounds μ R hR k z).2
  have hxa : dist x (z : Ambient d) ≤ 2 * latticeRadius R k := hb hx.1
  have haa : dist a (z : Ambient d) ≤ 2 * latticeRadius R k := hb ha
  have ht := dist_triangle x (z : Ambient d) a
  rw [dist_comm (z : Ambient d) a] at ht
  linarith

theorem supportLatticeAncestor_forced_near_center {d : ℕ} (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) (k t : ℕ) (ht : 0 < t)
    (z : (supportLatticeNets μ R hR k).points)
    (w : (supportLatticeNets μ R hR (k + t)).points)
    (hnear : dist (w : Ambient d) (z : Ambient d) < latticeRadius R k / 4) :
    supportLatticeAncestor μ R hR k t w = z := by
  cases t with
  | zero => omega
  | succ t =>
    apply Subtype.ext
    exact congrArg (fun u : μ.support => (u : Ambient d))
      (netAncestor_forced_near_center R hR (supportLatticeNets μ R hR)
      k t (supportLatticeCenter μ R hR (k + (t + 1)) w)
      (supportLatticeCenter μ R hR k z) z.property hnear)

theorem closed_cell_ancestor_eq_of_interior_point {d : ℕ} (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) (k t : ℕ) (ht : 0 < t)
    (z : (supportLatticeNets μ R hR k).points)
    (w : (supportLatticeNets μ R hR (k + t)).points)
    (a : Ambient d) (ha : a ∈ supportLatticeCell μ R hR (k + t) w)
    (hnear : dist a (z : Ambient d) ≤ latticeRadius R k / 8)
    (hscale : latticeRadius R (k + t) ≤ latticeRadius R k / 64) :
    supportLatticeAncestor μ R hR k t w = z := by
  apply supportLatticeAncestor_forced_near_center μ R hR k t ht z w
  have haW : dist a (w : Ambient d) ≤ 2 * latticeRadius R (k + t) :=
    (supportLatticeCell_bounds μ R hR (k + t) w).2 ha
  have htri := dist_triangle (w : Ambient d) a (z : Ambient d)
  rw [dist_comm (w : Ambient d) a] at htri
  have hp := latticeRadius_pos R hR k
  linarith

theorem annularCellMassConstant_pos (n : ℕ) (C : ℝ) (hC : 0 < C) :
    0 < annularCellMassConstant n C := by unfold annularCellMassConstant; positivity

theorem clean_cell_annular_mass_bound {n d : ℕ}
    (μ : Measure (Ambient d)) (C G : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points)
    (hcore : AdmissibleRadius μ (latticeRadius R k / 8))
    (r : ℝ) (hr : 0 ≤ r) (hscale : r ≤ 512 * latticeRadius R k) :
    r ^ n ≤ annularCellMassConstant n C * μ.real (cleanSupportCell μ R hR k z) := by
  have hl := (cleanSupportCell_real_measure_bounds μ C G hC hG hg hlower R hR k hcore z).1
  have hK := annularCellMassConstant_pos n C hC
  calc
    _ ≤ (512 * latticeRadius R k) ^ n := pow_le_pow_left₀ hr hscale n
    _ = annularCellMassConstant n C * ((latticeRadius R k / 8) ^ n / C) := by
      unfold annularCellMassConstant
      simp only [mul_pow, div_pow]
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hl hK.le

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Flatness_FlatCellGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem exists_flat_ball_descendant_geometry {d : ℕ} (μ : Measure (Ambient d))
    (R₀ : ℝ) (hR₀ : 0 < R₀) (k : ℕ) (z : (supportLatticeNets μ R₀ hR₀ k).points)
    (a : Ambient d) (ha : a ∈ μ.support)
    (hnear : dist a (z : Ambient d) < latticeRadius R₀ k / 16)
    (r A : ℝ) (hr : 0 < r) (hrtop : r < latticeRadius R₀ k / 16) (hA : 1 ≤ A)
    (I : ℕ) (hdepth : annularLatticeDepth R₀ k (r / (A + 2)) (by positivity) ≤ I) :
    ∃ i : SupportCellDescendant μ R₀ hR₀ k z,
      0 < i.depth ∧ i.depth ≤ I ∧ r ≤ (512 * (A + 2)) * i.radius ∧
        A * i.radius ≤ latticeRadius R₀ k / 8 ∧
        ball i.center (A * i.radius) ⊆ ball a r := by
  have hp := latticeRadius_pos R₀ hR₀ k
  have hAp : 0 < A + 2 := by linarith
  have hq : 0 < r / (A + 2) := div_pos hr hAp
  have hqr : r / (A + 2) ≤ r := (div_le_iff₀ hAp).mpr (by nlinarith)
  let t := annularLatticeDepth R₀ k (r / (A + 2)) hq
  have ht : 0 < t := annularLatticeDepth_pos R₀ k (r / (A + 2)) hq (by linarith)
  have hu : latticeRadius R₀ (k + t) ≤ (r / (A + 2)) / 8 :=
    annularLatticeDepth_radius_upper R₀ k (r / (A + 2)) hq
  have hl : r / (A + 2) ≤ 512 * latticeRadius R₀ (k + t) :=
    annularLatticeDepth_radius_lower R₀ hR₀ k (r / (A + 2)) hq (by linarith)
  have hmul : (A + 2) * latticeRadius R₀ (k + t) ≤ r / 8 := by
    have hv := mul_le_mul_of_nonneg_left hu hAp.le
    calc
      _ ≤ (A + 2) * ((r / (A + 2)) / 8) := hv
      _ = r / 8 := by field_simp
  have hu64 : latticeRadius R₀ (k + t) ≤ latticeRadius R₀ k / 64 := by
    have hup := latticeRadius_pos R₀ hR₀ (k + t)
    nlinarith
  obtain ⟨w, haw⟩ := supportLatticeCell_cover μ R₀ hR₀ (k + t) a ha
  have hwz := closed_cell_ancestor_eq_of_interior_point μ R₀ hR₀ k t ht z w a haw
    (by linarith) hu64
  let i : SupportCellDescendant μ R₀ hR₀ k z :=
    { depth := t, center := w, mem_net := w.property, ancestor := hwz }
  refine ⟨i, ht, hdepth, ?_, ?_, ?_⟩
  · change r ≤ (512 * (A + 2)) * latticeRadius R₀ (k + t)
    have hv := (div_le_iff₀ hAp).mp hl
    nlinarith
  · change A * latticeRadius R₀ (k + t) ≤ latticeRadius R₀ k / 8
    have hup := latticeRadius_pos R₀ hR₀ (k + t)
    nlinarith
  · intro x hx
    have hxa : dist x (w : Ambient d) < A * latticeRadius R₀ (k + t) := hx
    have hwa : dist (w : Ambient d) a ≤ 2 * latticeRadius R₀ (k + t) := by
      rw [dist_comm]
      exact (supportLatticeCell_bounds μ R₀ hR₀ (k + t) w).2 haw
    have htri := dist_triangle x (w : Ambient d) a
    change dist x a < r
    nlinarith

theorem exists_uniform_flat_ball_descendant_geometry (ρ A : ℝ) (hρ : 0 < ρ) (hA : 1 ≤ A) :
    ∃ I : ℕ, 0 < I ∧ ∀ {d : ℕ} (μ : Measure (Ambient d))
      (R₀ : ℝ) (hR₀ : 0 < R₀) (k : ℕ) (z : (supportLatticeNets μ R₀ hR₀ k).points),
      ∀ a ∈ μ.support, dist a (z : Ambient d) < latticeRadius R₀ k / 16 →
      ∀ r : ℝ, 0 < r → ρ * latticeRadius R₀ k ≤ r → r < latticeRadius R₀ k / 16 →
      ∃ i : SupportCellDescendant μ R₀ hR₀ k z,
        0 < i.depth ∧ i.depth ≤ I ∧ r ≤ (512 * (A + 2)) * i.radius ∧
          A * i.radius ≤ latticeRadius R₀ k / 8 ∧
          ball i.center (A * i.radius) ⊆ ball a r := by
  obtain ⟨I, hI, hchoose⟩ := exists_uniform_annular_lattice_depth (ρ / (A + 2)) (by positivity)
  refine ⟨I, hI, ?_⟩
  intro d μ R₀ hR₀ k z a ha hnear r hr hfloor hcap
  apply exists_flat_ball_descendant_geometry μ R₀ hR₀ k z a ha hnear r A hr hcap hA I
  apply hchoose R₀ hR₀ k (r / (A + 2)) (by positivity)
  calc
    _ = (ρ * latticeRadius R₀ k) / (A + 2) := by ring
    _ ≤ r / (A + 2) := div_le_div_of_nonneg_right hfloor (by positivity)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_TruncationIntegrability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Integrability of hard Riesz truncations

Global upper growth makes the Riesz kernel square-integrable outside each positive-radius
ball. Pairing this exterior estimate with an L² input proves integrability of the hard
truncation. For finite measures, integrability instead follows from the bounded exterior
kernel and the inclusion of L² in L¹.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

theorem kernel_sq_norm_le_tail_weight {d : ℕ} (n : ℕ) (hn : 1 ≤ n)
    (x y : Ambient d) (ε : ℝ) (hε : 0 < ε) (hy : ε ≤ dist x y) :
    ‖kernel n x y‖ ^ 2 ≤ (ε ^ (n - 1))⁻¹ * inverseDistancePow (n + 1) x y := by
  have hd : 0 < dist x y := lt_of_lt_of_le hε hy
  rw [kernel_norm_of_ne n x y (dist_pos.mp hd), inv_pow, ← pow_mul,
    show n * 2 = (n - 1) + (n + 1) by omega, pow_add, mul_inv]
  apply mul_le_mul_of_nonneg_right
  · simpa only [one_div] using! one_div_le_one_div_of_le
      (pow_pos hε (n - 1)) (pow_le_pow_left₀ hε.le hy (n - 1))
  · positivity

theorem kernel_memLp_two_on_exterior {d : ℕ} (n : ℕ) (hn : 1 ≤ n) (C : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth n C μ)
    (x : Ambient d) (ε : ℝ) (hε : 0 < ε) :
    MemLp (kernel n x) 2 (μ.restrict {y | ε < dist x y}) := by
  have hmeas : AEStronglyMeasurable (kernel n x) (μ.restrict {y | ε < dist x y}) :=
    (kernel_measurable_right n x).aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq_norm hmeas).2
  have hi := (inverseDistancePow_integrableOn_exterior n C μ hg x ε hε).const_mul
    ((ε ^ (n - 1))⁻¹)
  apply hi.mono' ((kernel_measurable_right n x).norm.pow_const 2).aestronglyMeasurable
  filter_upwards [ae_restrict_mem
    (measurableSet_lt measurable_const (continuous_const.dist continuous_id).measurable)] with y hy
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact kernel_sq_norm_le_tail_weight n hn x y ε hε hy.le

theorem truncation_integrable_of_globalGrowth {d : ℕ} (n : ℕ) (hn : 1 ≤ n) (C : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth n C μ)
    (f : Ambient d → ℝ) (hf : MemLp f 2 μ)
    (x : Ambient d) (ε : ℝ) (hε : 0 < ε) :
    IntegrableOn (fun y => f y • kernel n x y) {y | ε < dist x y} μ := by
  apply memLp_one_iff_integrable.mp
  exact MemLp.smul (hf := kernel_memLp_two_on_exterior n hn C μ hg x ε hε) (hφ := hf.restrict _)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_BoundedSupportEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Energy of bounded functions with finite-measure support

Comparison with a constant indicator gives square integrability and an explicit
energy bound in terms of the uniform bound and the measure of the support set.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

theorem bounded_support_memLp_energy {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) (hfm : Measurable f)
    (S : Set X) (hS : MeasurableSet S) (hfin : μ S < ∞)
    (M : ℝ) (hM : 0 ≤ M) (hfM : ∀ x, |f x| ≤ M) (hs : ∀ x, x ∉ S → f x = 0) :
    MemLp f 2 μ ∧ (∫ x, f x ^ 2 ∂μ) ≤ M ^ 2 * μ.real S := by
  let g : X → ℝ := S.indicator (fun _ => M)
  let : IsFiniteMeasure (μ.restrict S) := ⟨by simpa only [Measure.restrict_apply_univ] using! hfin⟩
  have hg : MemLp g 2 μ := (memLp_indicator_iff_restrict hS).mpr (memLp_const M)
  have hpoint (x : X) : |f x| ≤ |g x| := by
    by_cases hx : x ∈ S
    · simpa only [g, indicator_of_mem hx, abs_of_nonneg hM] using! hfM x
    · simp only [hs x hx, g, indicator_of_notMem hx, abs_zero, le_refl]
  have hf : MemLp f 2 μ := hg.of_le hfm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using! hpoint x)
  refine ⟨hf, ?_⟩
  calc
    _ ≤ ∫ x, g x ^ 2 ∂μ := integral_mono hf.integrable_sq hg.integrable_sq (fun x => by
      have hb := mul_self_le_mul_self (abs_nonneg (f x)) (hpoint x)
      simpa only [← pow_two, sq_abs] using! hb)
    _ = M ^ 2 * μ.real S := by
      have heq : (fun x => g x ^ 2) = S.indicator (fun _ => M ^ 2) := by
        funext x
        by_cases hx : x ∈ S <;> simp [g, hx]
      rw [heq, integral_indicator hS, setIntegral_const, smul_eq_mul, mul_comm]

theorem bounded_ball_support_energy {d : ℕ} (n : ℕ) (G : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth n G μ)
    (f : Ambient d → ℝ) (hfm : Measurable f) (a : Ambient d) (r M : ℝ)
    (hr : 0 < r) (hM : 0 ≤ M) (hfM : ∀ x, |f x| ≤ M)
    (hs : ∀ x, r ≤ dist x a → f x = 0) :
    MemLp f 2 μ ∧ (∫ x, f x ^ 2 ∂μ) ≤ M ^ 2 * (G * r ^ n) := by
  have hm := hg.2 a r hr
  have hfin := lt_of_le_of_lt hm ENNReal.ofReal_lt_top
  have hf := bounded_support_memLp_energy μ f hfm (ball a r) measurableSet_ball hfin M hM hfM
    (fun x hx => hs x (le_of_not_gt hx))
  refine ⟨hf.1, hf.2.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg M)
  exact ENNReal.toReal_le_of_le_ofReal (by positivity [hg.1]) hm

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_SmoothAnnularWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Smooth annular and exterior weights

Differences of smooth ball cutoffs localize functions to annular regions.
Subtracting a cutoff from a finite-measure set indicator gives an exterior
weight with controlled size, square integrability, and distance from the center.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

theorem annularSmoothBallCutoff_energy {d : ℕ} (n : ℕ) (G : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth n G μ)
    (a : Ambient d) (r : ℝ) (hr : 0 < r) :
    MemLp (annularSmoothBallCutoff a r hr) 2 μ ∧
      (∫ x, annularSmoothBallCutoff a r hr x ^ 2 ∂μ) ≤ G * (2 * r) ^ n := by
  have hb := annularSmoothBallCutoff_basic a r hr
  simpa only [one_pow, one_mul] using! bounded_ball_support_energy n G μ hg _ hb.1
    a (2 * r) 1 (by positivity) (by norm_num) hb.2.1 hb.2.2.2

theorem smoothAnnularWeight_properties {d : ℕ} (n : ℕ) (G : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth n G μ)
    (a : Ambient d) (r R : ℝ) (hr : 0 < r) (hrR : r ≤ R) :
    MemLp (smoothAnnularWeight a r R hr (hr.trans_le hrR)) 2 μ ∧
    (∀ x, |smoothAnnularWeight a r R hr (hr.trans_le hrR) x| ≤ 1) ∧
    (∀ x, smoothAnnularWeight a r R hr (hr.trans_le hrR) x ≠ 0 → r ≤ dist a x) ∧
    (∫ x, smoothAnnularWeight a r R hr (hr.trans_le hrR) x ^ 2 ∂μ) ≤ G * (2 * R) ^ n := by
  have hR := hr.trans_le hrR
  have hb := annularSmoothBallCutoff_basic a r hr
  have hB := annularSmoothBallCutoff_basic a R hR
  have hm : Measurable (smoothAnnularWeight a r R hr hR) := hB.1.sub hb.1
  have hbound (x : Ambient d) : |smoothAnnularWeight a r R hr hR x| ≤ 1 := by
    have hl := (annularSmoothBallCutoff a r hr).nonneg (x := x)
    have hu := (annularSmoothBallCutoff a r hr).le_one (x := x)
    have hL := (annularSmoothBallCutoff a R hR).nonneg (x := x)
    have hU := (annularSmoothBallCutoff a R hR).le_one (x := x)
    unfold smoothAnnularWeight
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hs (x : Ambient d) (hx : 2 * R ≤ dist x a) : smoothAnnularWeight a r R hr hR x = 0 := by
    rw [smoothAnnularWeight, hB.2.2.2 x hx, hb.2.2.2 x (by linarith), sub_self]
  have he := bounded_ball_support_energy n G μ hg _ hm a (2 * R) 1 (by positivity)
    (by norm_num) hbound hs
  refine ⟨he.1, hbound, ?_, by simpa only [one_pow, one_mul] using! he.2⟩
  intro x hx
  by_contra hdist
  have hd : dist x a ≤ r := by rw [dist_comm]; exact (lt_of_not_ge hdist).le
  apply hx
  rw [smoothAnnularWeight, hB.2.2.1 x (hd.trans hrR), hb.2.2.1 x hd, sub_self]

theorem smoothExteriorWeight_properties {d : ℕ} (n : ℕ) (G : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth n G μ)
    (a : Ambient d) (R : ℝ) (hR : 0 < R)
    (S : Set (Ambient d)) (hS : MeasurableSet S) (hfin : μ S < ∞)
    (hcontains : ball a (2 * R) ⊆ S) :
    MemLp (smoothExteriorWeight a R hR S) 2 μ ∧
    (∀ x, |smoothExteriorWeight a R hR S x| ≤ 1) ∧
    (∀ x, smoothExteriorWeight a R hR S x ≠ 0 → R ≤ dist a x) := by
  let : IsFiniteMeasure (μ.restrict S) := ⟨by simpa only [Measure.restrict_apply_univ] using! hfin⟩
  have hi : MemLp (S.indicator (fun _ : Ambient d => (1 : ℝ))) 2 μ :=
    (memLp_indicator_iff_restrict hS).mpr (memLp_const 1)
  have hb := annularSmoothBallCutoff_basic a R hR
  refine ⟨hi.sub (annularSmoothBallCutoff_energy n G μ hg a R hR).1, ?_, ?_⟩
  · intro x
    unfold smoothExteriorWeight
    by_cases hx : x ∈ S
    · rw [indicator_of_mem hx]
      have hl := (annularSmoothBallCutoff a R hR).nonneg (x := x)
      have hu := (annularSmoothBallCutoff a R hR).le_one (x := x)
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    · have hd : 2 * R ≤ dist x a := le_of_not_gt (fun h => hx (hcontains h))
      rw [indicator_of_notMem hx, hb.2.2.2 x hd]
      norm_num
  · intro x hx
    by_contra hdist
    have hd : dist x a < R := by rw [dist_comm]; exact lt_of_not_ge hdist
    have hxS : x ∈ S := hcontains (by change dist x a < 2 * R; linarith)
    apply hx
    rw [smoothExteriorWeight, indicator_of_mem hxS, hb.2.2.1 x hd.le, sub_self]

theorem smoothAnnularWeights_sum {d : ℕ} (a : Ambient d) (r R : ℝ)
    (hr : 0 < r) (hR : 0 < R) (S : Set (Ambient d)) (x : Ambient d) :
    annularSmoothBallCutoff a r hr x + smoothAnnularWeight a r R hr hR x +
      smoothExteriorWeight a R hR S x = S.indicator (fun _ => 1) x := by
  unfold smoothAnnularWeight smoothExteriorWeight
  ring

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Packing_VectorBesselTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Transferring scalar Bessel bounds to vector fields

Scalar-vector pairings commute with the Bochner integral, and the squared native
`L²` norm agrees with the integral of the squared pointwise norm. Expanding in an
orthonormal basis transfers a finite scalar Bessel bound to pairings of a vector
field against test vectors of norm at most one, with the same Bessel constant.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory
open scoped NNReal ENNReal

theorem memLp_inner_const_of_vector {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (μ : Measure X) (u : X → E) (hu : MemLp u 2 μ) (e : E) :
    MemLp (fun x => inner ℝ e (u x)) 2 μ :=
  hu.of_le_mul (aestronglyMeasurable_const.inner hu.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x => norm_inner_le_norm (𝕜 := ℝ) e (u x))

theorem integral_scalar_vector_pairing {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (μ : Measure X) (f : X → ℝ) (u : X → E)
    (hf : MemLp f 2 μ) (hu : MemLp u 2 μ) (e : E) :
    (∫ x, f x * inner ℝ e (u x) ∂μ) = inner ℝ e (∫ x, f x • u x ∂μ) := by
  have hi : Integrable (fun x => f x • u x) μ := memLp_one_iff_integrable.mp (MemLp.smul (hf := hu) (hφ := hf))
  simpa only [real_inner_smul_right] using! (integral_inner (𝕜 := ℝ) hi e)

theorem toLp_vector_norm_sq_eq_integral {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (μ : Measure X) (u : X → E) (hu : MemLp u 2 μ) :
    ‖hu.toLp u‖ ^ 2 = ∫ x, ‖u x‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hu.coeFn_toLp] with x hx
  rw [hx, real_inner_self_eq_norm_sq]

theorem vector_sq_integral_of_native_norm_bound {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (μ : Measure X) (f : X → ℝ) (u : X → E)
    (hf : MemLp f 2 μ) (hu : MemLp u 2 μ) (D : ℝ≥0)
    (hN : eLpNorm u 2 μ ≤ (D : ℝ≥0∞) * eLpNorm f 2 μ) :
    (∫ x, ‖u x‖ ^ 2 ∂μ) ≤ (D : ℝ) ^ 2 * ∫ x, f x ^ 2 ∂μ := by
  have hfin : (D : ℝ≥0∞) * eLpNorm f 2 μ ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top hf.eLpNorm_ne_top
  have hnorm : ‖hu.toLp u‖ ≤ (D : ℝ) * ‖hf.toLp f‖ := by
    simpa only [Lp.norm_toLp, ENNReal.toReal_mul, ENNReal.coe_toReal] using!
      ENNReal.toReal_mono hfin hN
  rw [← toLp_vector_norm_sq_eq_integral μ u hu, ← toLp_norm_sq_eq_integral μ f hf]
  have hh := mul_self_le_mul_self (norm_nonneg (hu.toLp u)) hnorm
  nlinarith

theorem finite_vector_bessel_of_scalar {ι κ X E : Type*} [Fintype κ]
    [MeasurableSpace X] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (b : OrthonormalBasis κ ℝ E) (μ : Measure X) (s : Finset ι)
    (f : ι → X → ℝ) (hf : ∀ i, MemLp (f i) 2 μ) (B : ℝ)
    (hb : ∀ v : X → ℝ, MemLp v 2 μ →
      ∑ i ∈ s, (∫ x, f i x * v x ∂μ) ^ 2 ≤ B * ∫ x, v x ^ 2 ∂μ)
    (u : X → E) (hu : MemLp u 2 μ) (e : ι → E)
    (he : ∀ i ∈ s, ‖e i‖ ≤ 1) :
    ∑ i ∈ s, (∫ x, f i x * inner ℝ (e i) (u x) ∂μ) ^ 2 ≤
      B * ∫ x, ‖u x‖ ^ 2 ∂μ := by
  classical
  let v : ι → E := fun i => ∫ x, f i x • u x ∂μ
  have hv (i : ι) (hi : i ∈ s) :
      (∫ x, f i x * inner ℝ (e i) (u x) ∂μ) ^ 2 ≤ ‖v i‖ ^ 2 := by
    rw [integral_scalar_vector_pairing μ (f i) u (hf i) hu (e i)]
    have hnorm : |inner ℝ (e i) (v i)| ≤ ‖v i‖ := by
      calc
        _ ≤ ‖e i‖ * ‖v i‖ := by
          simpa only [Real.norm_eq_abs] using! norm_inner_le_norm (𝕜 := ℝ) (e i) (v i)
        _ ≤ 1 * ‖v i‖ := mul_le_mul_of_nonneg_right (he i hi) (norm_nonneg _)
        _ = _ := one_mul _
    have hh := mul_self_le_mul_self (abs_nonneg _) hnorm
    simpa only [← pow_two, sq_abs] using! hh
  have hcoord (k : κ) := memLp_inner_const_of_vector μ u hu (b k)
  calc
    _ ≤ ∑ i ∈ s, ‖v i‖ ^ 2 := Finset.sum_le_sum hv
    _ = ∑ k : κ, ∑ i ∈ s, (∫ x, f i x * inner ℝ (b k) (u x) ∂μ) ^ 2 := by
      dsimp only [v]
      simp_rw [← b.sum_sq_inner_right, ← integral_scalar_vector_pairing μ _ u (hf _) hu]
      exact Finset.sum_comm
    _ ≤ ∑ k : κ, B * ∫ x, (inner ℝ (b k) (u x)) ^ 2 ∂μ :=
      Finset.sum_le_sum (fun k _ => hb _ (hcoord k))
    _ = B * ∫ x, ‖u x‖ ^ 2 ∂μ := by
      rw [← Finset.mul_sum, ← integral_finsetSum _ (fun k _ => (hcoord k).integrable_sq)]
      congr 1
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => b.sum_sq_inner_right (u x)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_NativeCellMeanBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Cell means from native vector norm bounds

Cell means respect addition, subtraction, and constants, and inherit almost-everywhere
uniform bounds. For a vector field controlled in `L²` by a scalar input, its components
along vectors of norm at most one have bounded means on sets of finite positive mass.
The estimate combines the squared norm bound with the scalar input's local energy budget.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

variable {X : Type*} [MeasurableSpace X]

theorem cellMean_add (μ : Measure X) (f g : X → ℝ)
    (hf : Integrable f μ) (hg : Integrable g μ) :
    cellMean μ (fun x => f x + g x) = cellMean μ f + cellMean μ g := by
  simp only [cellMean, integral_add hf hg, add_div]

theorem cellMean_sub (μ : Measure X) (f g : X → ℝ)
    (hf : Integrable f μ) (hg : Integrable g μ) :
    cellMean μ (fun x => f x - g x) = cellMean μ f - cellMean μ g := by
  simp only [cellMean, integral_sub hf hg, sub_div]

theorem cellMean_const (μ : Measure X) (c : ℝ) (hμ : μ.real univ ≠ 0) :
    cellMean μ (fun _ => c) = c := by
  simp only [cellMean, integral_const, smul_eq_mul]
  exact mul_div_cancel_left₀ c hμ

theorem cellMean_abs_le_ae_bound (μ : Measure X) [IsFiniteMeasure μ]
    (f : X → ℝ) (hμ : 0 < μ.real univ) (B : ℝ)
    (hb : ∀ᵐ x ∂μ, |f x| ≤ B) : |cellMean μ f| ≤ B := by
  have hn : ‖∫ x, f x ∂μ‖ ≤ B * μ.real univ :=
    norm_integral_le_of_norm_le_const (by simpa only [Real.norm_eq_abs] using! hb)
  rw [cellMean, abs_div, abs_of_pos hμ]
  exact (div_le_iff₀ hμ).mpr (by simpa only [Real.norm_eq_abs] using! hn)

theorem cellMean_near_constant (μ : Measure X) [IsFiniteMeasure μ]
    (f : X → ℝ) (hf : Integrable f μ) (hμ : 0 < μ.real univ) (c B : ℝ)
    (hb : ∀ᵐ x ∂μ, |f x - c| ≤ B) : |cellMean μ f - c| ≤ B := by
  have h := cellMean_abs_le_ae_bound μ (fun x => f x - c) hμ B hb
  rwa [cellMean_sub μ f (fun _ => c) hf (integrable_const c), cellMean_const μ c hμ.ne'] at h

theorem native_vector_cellMean_bound {d : ℕ}
    (μ : Measure X) (A : Set X) (hfin : μ A < ∞) (hpos : 0 < μ.real A)
    (f : X → ℝ) (u : X → Ambient d) (hf : MemLp f 2 μ) (hu : MemLp u 2 μ)
    (D : ℝ≥0) (hN : eLpNorm u 2 μ ≤ (D : ℝ≥0∞) * eLpNorm f 2 μ)
    (e : Ambient d) (he : ‖e‖ ≤ 1) (B : ℝ)
    (henergy : (∫ x, f x ^ 2 ∂μ) ≤ B * μ.real A) :
    |cellMean (μ.restrict A) (fun x => inner ℝ e (u x))| ≤ (D : ℝ) ^ 2 * B + 1 := by
  let : IsFiniteMeasure (μ.restrict A) := ⟨by simpa only [Measure.restrict_apply_univ] using! hfin⟩
  let v := fun x => inner ℝ e (u x)
  have hv := memLp_inner_const_of_vector μ u hu e
  have hpoint (x : X) : (v x) ^ 2 ≤ ‖u x‖ ^ 2 := by
    have hb : |v x| ≤ ‖u x‖ := by
      calc
        _ ≤ ‖e‖ * ‖u x‖ := by
          simpa only [Real.norm_eq_abs] using! norm_inner_le_norm (𝕜 := ℝ) e (u x)
        _ ≤ 1 * ‖u x‖ := mul_le_mul_of_nonneg_right he (norm_nonneg _)
        _ = _ := one_mul _
    have hs := mul_self_le_mul_self (abs_nonneg (v x)) hb
    simpa only [← pow_two, sq_abs] using! hs
  have hbound : (∫ x, v x ^ 2 ∂μ.restrict A) ≤
      ((D : ℝ) ^ 2 * B) * μ.real A := by
    calc
      _ ≤ ∫ x, v x ^ 2 ∂μ :=
        integral_mono_measure Measure.restrict_le_self
          (Filter.Eventually.of_forall fun x => sq_nonneg _) hv.integrable_sq
      _ ≤ ∫ x, ‖u x‖ ^ 2 ∂μ :=
        integral_mono hv.integrable_sq hu.norm.integrable_sq hpoint
      _ ≤ (D : ℝ) ^ 2 * ∫ x, f x ^ 2 ∂μ :=
        vector_sq_integral_of_native_norm_bound μ f u hf hu D hN
      _ ≤ (D : ℝ) ^ 2 * (B * μ.real A) :=
        mul_le_mul_of_nonneg_left henergy (sq_nonneg _)
      _ = _ := by ring
  have h := cellMean_abs_bound (μ.restrict A) v (hv.restrict A) (μ.real A)
    (((D : ℝ) ^ 2 * B) * μ.real A) hpos (by simp [Measure.real]) hbound
  simpa only [mul_div_cancel_right₀ _ hpos.ne'] using! h

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_NativeTruncationDecomposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Decomposition of native truncations

Global upper growth makes hard-truncated kernels integrable against square-integrable
inputs, so truncation respects addition. On cells of finite mass, the same decomposition
passes to means of scalar components of the resulting vector-valued transforms.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

theorem truncated_add_of_globalGrowth {d : ℕ} (n : ℕ) (hn : 1 ≤ n)
    (G : ℝ) (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth n G μ)
    (ε : ℝ) (hε : 0 < ε) (f g : Ambient d → ℝ)
    (hf : MemLp f 2 μ) (hh : MemLp g 2 μ) (x : Ambient d) :
    truncated n μ ε (fun y => f y + g y) x =
      truncated n μ ε f x + truncated n μ ε g x := by
  unfold truncated
  simp only [add_smul]
  exact integral_add (truncation_integrable_of_globalGrowth n hn G μ hg f hf x ε hε)
    (truncation_integrable_of_globalGrowth n hn G μ hg g hh x ε hε)

theorem three_part_truncated_cellMean {d : ℕ} (n : ℕ) (hn : 1 ≤ n)
    (G : ℝ) (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth n G μ)
    (ε : ℝ) (hε : 0 < ε) (f g h : Ambient d → ℝ)
    (hf : MemLp f 2 μ) (hhg : MemLp g 2 μ) (hh : MemLp h 2 μ)
    (huf : MemLp (truncated n μ ε f) 2 μ) (hug : MemLp (truncated n μ ε g) 2 μ)
    (huh : MemLp (truncated n μ ε h) 2 μ)
    (A : Set (Ambient d)) (hfin : μ A < ∞) (e : Ambient d) :
    cellMean (μ.restrict A) (fun x => inner ℝ e
      (truncated n μ ε (fun y => f y + g y + h y) x)) =
    cellMean (μ.restrict A) (fun x => inner ℝ e (truncated n μ ε f x)) +
    cellMean (μ.restrict A) (fun x => inner ℝ e (truncated n μ ε g x)) +
    cellMean (μ.restrict A) (fun x => inner ℝ e (truncated n μ ε h x)) := by
  let : IsFiniteMeasure (μ.restrict A) := ⟨by simpa only [Measure.restrict_apply_univ] using! hfin⟩
  have hif := ((memLp_inner_const_of_vector μ _ huf e).restrict A).integrable (by norm_num)
  have hig := ((memLp_inner_const_of_vector μ _ hug e).restrict A).integrable (by norm_num)
  have hih := ((memLp_inner_const_of_vector μ _ huh e).restrict A).integrable (by norm_num)
  have heq : (fun x => inner ℝ e (truncated n μ ε (fun y => f y + g y + h y) x)) =
      (fun x => inner ℝ e (truncated n μ ε f x) + inner ℝ e (truncated n μ ε g x) +
        inner ℝ e (truncated n μ ε h x)) := by
    funext x
    rw [truncated_add_of_globalGrowth n hn G μ hg ε hε (fun y => f y + g y) h (hf.add hhg) hh x,
      truncated_add_of_globalGrowth n hn G μ hg ε hε f g hf hhg x,
      inner_add_right, inner_add_right]
  rw [heq]
  rw [cellMean_add (μ.restrict A)
    (fun x => inner ℝ e (truncated n μ ε f x) + inner ℝ e (truncated n μ ε g x))
    (fun x => inner ℝ e (truncated n μ ε h x)) (hif.add hig) hih,
    cellMean_add (μ.restrict A) (fun x => inner ℝ e (truncated n μ ε f x))
      (fun x => inner ℝ e (truncated n μ ε g x)) hif hig]

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_FarKernelDifference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem inverseDistancePow_far_difference {d : ℕ} (m : ℕ) (a x y : Ambient d)
    (hy : 0 < dist a y) (hfar : 2 * dist x a ≤ dist a y) :
    |inverseDistancePow (m + 1) x y - inverseDistancePow (m + 1) a y| ≤
      (m + 1 : ℝ) * 2 ^ (m + 2) * dist x a * inverseDistancePow (m + 2) a y := by
  have hhalf : dist a y / 2 ≤ dist x y := by
    have ht := dist_triangle a x y
    rw [dist_comm a x] at ht
    linarith
  have h := inverse_pow_difference_le m (dist x y) (dist a y) (dist a y / 2)
    (by positivity) hhalf (by linarith)
  have hdist := abs_dist_sub_le x a y
  unfold inverseDistancePow
  calc
    _ ≤ (m + 1 : ℝ) * |dist x y - dist a y| * ((dist a y / 2) ^ (m + 2))⁻¹ := h
    _ ≤ (m + 1 : ℝ) * dist x a * ((dist a y / 2) ^ (m + 2))⁻¹ := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdist (by positivity))
        (by positivity)
    _ = _ := by
      rw [div_pow, inv_div]
      ring

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_ClosedTailBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function

theorem closedExterior_measurable {d : ℕ} (a : Ambient d) (R : ℝ) :
    MeasurableSet (closedExterior a R) :=
  measurableSet_le measurable_const (continuous_const.dist continuous_id).measurable

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_RenormalizedFarPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function

theorem inverseDistancePow_far_le {d : ℕ} (p : ℕ) (a x y : Ambient d)
    (hy : 0 < dist a y) (hfar : 2 * dist x a ≤ dist a y) :
    inverseDistancePow p x y ≤ 2 ^ p * inverseDistancePow p a y := by
  have hhalf : dist a y / 2 ≤ dist x y := by
    have ht := dist_triangle a x y
    rw [dist_comm a x] at ht
    linarith
  calc
    _ ≤ ((dist a y / 2) ^ p)⁻¹ := by
      simpa only [inverseDistancePow, one_div] using!
        one_div_le_one_div_of_le (pow_pos (by positivity : 0 < dist a y / 2) p)
          (pow_le_pow_left₀ (by positivity) hhalf p)
    _ = _ := by unfold inverseDistancePow; rw [div_pow, inv_div]; ring

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_VectorKernelFarDifference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem vectorKernelFarConstant_pos (n : ℕ) : 0 < vectorKernelFarConstant n := by
  unfold vectorKernelFarConstant
  positivity

theorem vector_kernel_difference_identity {d : ℕ} (n : ℕ) (a x y : Ambient d) :
    kernel n x y - kernel n a y =
      (inverseDistancePow (n + 1) x y - inverseDistancePow (n + 1) a y) • (a - y) +
        inverseDistancePow (n + 1) x y • (x - a) := by
  simp only [kernel, inverseDistancePow, dist_eq_norm]
  module

theorem vector_kernel_far_difference {d : ℕ} (n : ℕ) (a x y : Ambient d)
    (hy : 0 < dist a y) (hfar : 2 * dist x a ≤ dist a y) :
    ‖kernel n x y - kernel n a y‖ ≤
      vectorKernelFarConstant n * dist x a * inverseDistancePow (n + 1) a y := by
  have hd := inverseDistancePow_far_difference n a x y hy hfar
  have hi := inverseDistancePow_far_le (n + 1) a x y hy hfar
  rw [vector_kernel_difference_identity]
  calc
    _ ≤ ‖(inverseDistancePow (n + 1) x y - inverseDistancePow (n + 1) a y) • (a - y)‖ +
        ‖inverseDistancePow (n + 1) x y • (x - a)‖ := norm_add_le _ _
    _ = |inverseDistancePow (n + 1) x y - inverseDistancePow (n + 1) a y| * dist a y +
        inverseDistancePow (n + 1) x y * dist x a := by
      simp only [norm_smul, Real.norm_eq_abs, ← dist_eq_norm,
        abs_of_nonneg (inverseDistancePow_nonneg _ _ _), Real.dist_eq]
    _ ≤ ((n + 1 : ℝ) * 2 ^ (n + 2) * dist x a * inverseDistancePow (n + 2) a y) * dist a y +
        (2 ^ (n + 1) * inverseDistancePow (n + 1) a y) * dist x a :=
      add_le_add (mul_le_mul_of_nonneg_right hd (dist_nonneg))
        (mul_le_mul_of_nonneg_right hi (dist_nonneg))
    _ = _ := by
      unfold vectorKernelFarConstant inverseDistancePow
      rw [show n + 2 = (n + 1) + 1 by omega, pow_succ]
      field_simp <;> ring

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_HardExteriorOscillation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exterior oscillation of hard truncations

Global upper growth controls the integral of a bounded density times a far-field
kernel difference. For an L² density supported outside a ball, this gives the
corresponding oscillation estimate for the exact hard-truncated transform.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem bounded_exterior_kernel_difference {d : ℕ} (n : ℕ) (G M : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth n G μ)
    (f : Ambient d → ℝ) (hfm : AEStronglyMeasurable f μ) (hM : 0 ≤ M)
    (a x : Ambient d) (R : ℝ) (hR : 0 < R) (hx : 2 * dist x a ≤ R)
    (hfM : ∀ y ∈ closedExterior a R, |f y| ≤ M) :
    IntegrableOn (fun y => f y • (kernel n x y - kernel n a y)) (closedExterior a R) μ ∧
      ‖∫ y in closedExterior a R, f y • (kernel n x y - kernel n a y) ∂μ‖ ≤
        (M * vectorKernelFarConstant n * dist x a) * (2 * (G * 2 ^ n / R)) := by
  let : ContinuousSMul ℝ (Ambient d) := IsBoundedSMul.continuousSMul
  have ht := inverseDistancePow_closedExterior_integrable_and_bound n G μ hg a R hR
  let K := M * vectorKernelFarConstant n * dist x a
  have hK : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg (mul_nonneg hM (vectorKernelFarConstant_pos n).le) dist_nonneg
  have hmeas : AEStronglyMeasurable
      (fun y => f y • (kernel n x y - kernel n a y)) (μ.restrict (closedExterior a R)) :=
    hfm.restrict.smul ((kernel_measurable_right n x).aestronglyMeasurable.sub
      (kernel_measurable_right n a).aestronglyMeasurable)
  have hpoint : ∀ᵐ y ∂μ.restrict (closedExterior a R),
      ‖f y • (kernel n x y - kernel n a y)‖ ≤ K * inverseDistancePow (n + 1) a y := by
    filter_upwards [ae_restrict_mem (closedExterior_measurable a R)] with y hy
    have hdist : R ≤ dist a y := hy
    rw [norm_smul, Real.norm_eq_abs]
    calc
      _ ≤ M * (vectorKernelFarConstant n * dist x a * inverseDistancePow (n + 1) a y) :=
        mul_le_mul (hfM y hy)
          (vector_kernel_far_difference n a x y (hR.trans_le hdist) (hx.trans hdist))
          (norm_nonneg _) hM
      _ = _ := by dsimp [K] <;> ring
  have hi := (ht.1.const_mul K).mono' hmeas hpoint
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ y in closedExterior a R, K * inverseDistancePow (n + 1) a y ∂μ :=
      norm_integral_le_of_norm_le (ht.1.const_mul K) hpoint
    _ = K * ∫ y in closedExterior a R, inverseDistancePow (n + 1) a y ∂μ :=
      integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left ht.2 hK

theorem truncated_eq_exterior_integral_of_support {d : ℕ} (n : ℕ)
    (μ : Measure (Ambient d)) (f : Ambient d → ℝ) (a x : Ambient d)
    (R ε : ℝ) (hx : 2 * dist x a ≤ R) (hε : ε < R / 2)
    (hs : ∀ y, f y ≠ 0 → R ≤ dist a y) :
    truncated n μ ε f x = ∫ y in closedExterior a R, f y • kernel n x y ∂μ := by
  have hzero (y : Ambient d) (hy : ¬ ε < dist x y) : f y = 0 := by
    by_contra hfy
    have hd := hs y hfy
    have htri := dist_triangle a x y
    rw [dist_comm a x] at htri
    linarith
  unfold truncated
  calc
    _ = ∫ y, f y • kernel n x y ∂μ :=
      setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by rw [hzero y hy, zero_smul])
    _ = _ := (setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by
      have hf : f y = 0 := by
        by_contra hfy
        exact hy (hs y hfy)
      rw [hf, zero_smul])).symm

theorem hard_truncated_exterior_difference_bound {d : ℕ} (n : ℕ) (hn : 1 ≤ n)
    (G M : ℝ) (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth n G μ)
    (f : Ambient d → ℝ) (hf : MemLp f 2 μ) (hM : 0 ≤ M)
    (hfM : ∀ y, |f y| ≤ M) (a x : Ambient d) (R ε : ℝ)
    (hR : 0 < R) (hε : 0 < ε) (hεR : ε < R / 2) (hx : 2 * dist x a ≤ R)
    (hs : ∀ y, f y ≠ 0 → R ≤ dist a y) :
    ‖truncated n μ ε f x - truncated n μ ε f a‖ ≤
      (M * vectorKernelFarConstant n * dist x a) * (2 * (G * 2 ^ n / R)) := by
  have hsep (b : Ambient d) (hb : 2 * dist b a ≤ R) :
      closedExterior a R ⊆ {y | ε < dist b y} := by
    intro y hy
    have hd : R ≤ dist a y := hy
    have ht := dist_triangle a b y
    rw [dist_comm a b] at ht
    change ε < dist b y
    linarith
  have hia : IntegrableOn (fun y => f y • kernel n a y) (closedExterior a R) μ :=
    (truncation_integrable_of_globalGrowth n hn G μ hg f hf a ε hε).mono_set
      (hsep a (by simp <;> positivity))
  have hix : IntegrableOn (fun y => f y • kernel n x y) (closedExterior a R) μ :=
    (truncation_integrable_of_globalGrowth n hn G μ hg f hf x ε hε).mono_set (hsep x hx)
  rw [truncated_eq_exterior_integral_of_support n μ f a x R ε hx hεR hs,
    truncated_eq_exterior_integral_of_support n μ f a a R ε (by simp <;> positivity) hεR hs,
    ← integral_sub hix hia]
  simp only [← smul_sub]
  exact (bounded_exterior_kernel_difference n G M μ hg f hf.aestronglyMeasurable hM
    a x R hR hx (fun y _ => hfM y)).2

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_ExteriorCellMeans
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Means of exterior hard-truncated fields

For bounded data supported outside a ball, the far-kernel estimate controls the
directional oscillation of the hard-truncated transform near the ball's center.
Averaging this estimate over a measurable set of finite positive mass gives the
same bound for the difference between its cell mean and the central value.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

theorem hard_exterior_directional_difference {d : ℕ} (n : ℕ) (hn : 1 ≤ n)
    (G M : ℝ) (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth n G μ)
    (f : Ambient d → ℝ) (hf : MemLp f 2 μ) (hM : 0 ≤ M) (hfM : ∀ y, |f y| ≤ M)
    (a x e : Ambient d) (he : ‖e‖ ≤ 1) (R ε : ℝ)
    (hR : 0 < R) (hε : 0 < ε) (hεR : ε < R / 2) (hx : 2 * dist x a ≤ R)
    (hs : ∀ y, f y ≠ 0 → R ≤ dist a y) :
    |inner ℝ e (truncated n μ ε f x) - inner ℝ e (truncated n μ ε f a)| ≤
      exteriorCellMeanConstant n G M := by
  have hb := hard_truncated_exterior_difference_bound n hn G M μ hg f hf hM hfM
    a x R ε hR hε hεR hx hs
  have hK : 0 ≤ M * vectorKernelFarConstant n :=
    mul_nonneg hM (vectorKernelFarConstant_pos n).le
  have htail : 0 ≤ 2 * (G * 2 ^ n / R) := by positivity [hg.1]
  calc
    _ = |inner ℝ e (truncated n μ ε f x - truncated n μ ε f a)| := by rw [inner_sub_right]
    _ ≤ ‖truncated n μ ε f x - truncated n μ ε f a‖ := by
      have ht := norm_inner_le_norm (𝕜 := ℝ) e (truncated n μ ε f x - truncated n μ ε f a)
      simpa only [Real.norm_eq_abs, one_mul] using!
        ht.trans (mul_le_mul_of_nonneg_right he (norm_nonneg _))
    _ ≤ (M * vectorKernelFarConstant n * dist x a) * (2 * (G * 2 ^ n / R)) := hb
    _ ≤ (M * vectorKernelFarConstant n * (R / 2)) * (2 * (G * 2 ^ n / R)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hK) htail
    _ = _ := by unfold exteriorCellMeanConstant; field_simp

theorem hard_exterior_cellMean_near_center {d : ℕ} {ε : ℝ} (n : ℕ) (hn : 1 ≤ n)
    (G M : ℝ) (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth n G μ)
    (f : Ambient d → ℝ) (hf : MemLp f 2 μ) (hu : MemLp (truncated n μ ε f) 2 μ)
    (hM : 0 ≤ M) (hfM : ∀ y, |f y| ≤ M)
    (a e : Ambient d) (he : ‖e‖ ≤ 1) (R : ℝ)
    (hR : 0 < R) (hε : 0 < ε) (hεR : ε < R / 2)
    (hs : ∀ y, f y ≠ 0 → R ≤ dist a y)
    (A : Set (Ambient d)) (hA : MeasurableSet A) (hfin : μ A < ∞) (hpos : 0 < μ.real A)
    (hnear : ∀ x ∈ A, 2 * dist x a ≤ R) :
    |cellMean (μ.restrict A) (fun x => inner ℝ e (truncated n μ ε f x)) -
      inner ℝ e (truncated n μ ε f a)| ≤ exteriorCellMeanConstant n G M := by
  let : IsFiniteMeasure (μ.restrict A) := ⟨by simpa only [Measure.restrict_apply_univ] using! hfin⟩
  have hi := ((memLp_inner_const_of_vector μ _ hu e).restrict A).integrable (by norm_num)
  apply cellMean_near_constant (μ.restrict A) _ hi (by simpa only [Measure.real,
    Measure.restrict_apply_univ] using! hpos)
  filter_upwards [ae_restrict_mem hA] with x hx
  exact hard_exterior_directional_difference n hn G M μ hg f hf hM hfM a x e he
    R ε hR hε hεR (hnear x hx) hs

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_AnnularAverageComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

theorem annular_cell_average_comparison {d : ℕ} (n : ℕ) (hn : 1 ≤ n)
    (G M B : ℝ) (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth n G μ)
    (ε r R : ℝ) (hε : 0 < ε) (hr : 0 < r) (hrR : r ≤ R) (hεr : ε < r / 2)
    (f g h : Ambient d → ℝ) (hf : MemLp f 2 μ) (hhg : MemLp g 2 μ) (hh : MemLp h 2 μ)
    (hM : 0 ≤ M) (hgM : ∀ y, |g y| ≤ M) (hhM : ∀ y, |h y| ≤ M)
    (a e : Ambient d) (he : ‖e‖ ≤ 1)
    (hgs : ∀ y, g y ≠ 0 → r ≤ dist a y) (hhs : ∀ y, h y ≠ 0 → R ≤ dist a y)
    (A Q : Set (Ambient d)) (hA : MeasurableSet A) (hQ : MeasurableSet Q)
    (hAfin : μ A < ∞) (hQfin : μ Q < ∞) (hApos : 0 < μ.real A) (hQpos : 0 < μ.real Q)
    (hAnear : ∀ x ∈ A, 2 * dist x a ≤ r) (hQnear : ∀ x ∈ Q, 2 * dist x a ≤ R)
    (hfA : (∫ y, f y ^ 2 ∂μ) ≤ B * μ.real A)
    (hfQ : (∫ y, f y ^ 2 ∂μ) ≤ B * μ.real Q)
    (hgQ : (∫ y, g y ^ 2 ∂μ) ≤ B * μ.real Q)
    (D : ℝ≥0)
    (hRiesz : ∀ u : Ambient d → ℝ, MemLp u 2 μ →
      MemLp (truncated n μ ε u) 2 μ ∧
        eLpNorm (truncated n μ ε u) 2 μ ≤ (D : ℝ≥0∞) * eLpNorm u 2 μ) :
    |inner ℝ e (truncated n μ ε g a)| ≤
      |cellMean (μ.restrict A) (fun x => inner ℝ e
          (truncated n μ ε (fun y => f y + g y + h y) x)) -
        cellMean (μ.restrict Q) (fun x => inner ℝ e
          (truncated n μ ε (fun y => f y + g y + h y) x))| +
      3 * ((D : ℝ) ^ 2 * B + 1) + 3 * exteriorCellMeanConstant n G M := by
  have huf := hRiesz f hf
  have hug := hRiesz g hhg
  have huh := hRiesz h hh
  have hfAb := native_vector_cellMean_bound μ A hAfin hApos f _ hf huf.1 D huf.2 e he B hfA
  have hfQb := native_vector_cellMean_bound μ Q hQfin hQpos f _ hf huf.1 D huf.2 e he B hfQ
  have hgQb := native_vector_cellMean_bound μ Q hQfin hQpos g _ hhg hug.1 D hug.2 e he B hgQ
  have hgAb := hard_exterior_cellMean_near_center n hn G M μ hg g hhg hug.1 hM hgM
    a e he r hr hε hεr hgs A hA hAfin hApos hAnear
  have hhAb := hard_exterior_cellMean_near_center n hn G M μ hg h hh huh.1 hM hhM
    a e he R (hr.trans_le hrR) hε (by linarith) hhs A hA hAfin hApos
    (fun x hx => (hAnear x hx).trans hrR)
  have hhQb := hard_exterior_cellMean_near_center n hn G M μ hg h hh huh.1 hM hhM
    a e he R (hr.trans_le hrR) hε (by linarith) hhs Q hQ hQfin hQpos hQnear
  have hsumA := three_part_truncated_cellMean n hn G μ hg ε hε f g h hf hhg hh
    huf.1 hug.1 huh.1 A hAfin e
  have hsumQ := three_part_truncated_cellMean n hn G μ hg ε hε f g h hf hhg hh
    huf.1 hug.1 huh.1 Q hQfin e
  rw [hsumA, hsumQ]
  rcases abs_le.mp hfAb with ⟨hfAl, hfAu⟩
  rcases abs_le.mp hfQb with ⟨hfQl, hfQu⟩
  rcases abs_le.mp hgQb with ⟨hgQl, hgQu⟩
  rcases abs_le.mp hgAb with ⟨hgAl, hgAu⟩
  rcases abs_le.mp hhAb with ⟨hhAl, hhAu⟩
  rcases abs_le.mp hhQb with ⟨hhQl, hhQu⟩
  apply abs_le.mpr
  constructor
  · linarith [neg_le_abs
      (cellMean (μ.restrict A) (fun x => inner ℝ e (truncated n μ ε f x)) +
        cellMean (μ.restrict A) (fun x => inner ℝ e (truncated n μ ε g x)) +
        cellMean (μ.restrict A) (fun x => inner ℝ e (truncated n μ ε h x)) -
        (cellMean (μ.restrict Q) (fun x => inner ℝ e (truncated n μ ε f x)) +
        cellMean (μ.restrict Q) (fun x => inner ℝ e (truncated n μ ε g x)) +
        cellMean (μ.restrict Q) (fun x => inner ℝ e (truncated n μ ε h x))))]
  · linarith [le_abs_self
      (cellMean (μ.restrict A) (fun x => inner ℝ e (truncated n μ ε f x)) +
        cellMean (μ.restrict A) (fun x => inner ℝ e (truncated n μ ε g x)) +
        cellMean (μ.restrict A) (fun x => inner ℝ e (truncated n μ ε h x)) -
        (cellMean (μ.restrict Q) (fun x => inner ℝ e (truncated n μ ε f x)) +
        cellMean (μ.restrict Q) (fun x => inner ℝ e (truncated n μ ε g x)) +
        cellMean (μ.restrict Q) (fun x => inner ℝ e (truncated n μ ε h x))))]

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_SmoothAnnularCellComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

theorem truncated_smoothAnnular_at_center {d : ℕ} (n : ℕ) (G : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth n G μ)
    (a : Ambient d) (r R ε : ℝ) (hr : 0 < r) (hrR : r ≤ R) (hε : ε < r) :
    truncated n μ ε (smoothAnnularWeight a r R hr (hr.trans_le hrR)) a =
      smoothAnnularTransform n μ a r R hr (hr.trans_le hrR) := by
  have hs := (smoothAnnularWeight_properties n G μ hg a r R hr hrR).2.2.1
  unfold truncated smoothAnnularTransform
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro y hy
  have hzero : smoothAnnularWeight a r R hr (hr.trans_le hrR) y = 0 := by
    by_contra hne
    have hd := hs y hne
    exact hy (hε.trans_le hd)
  rw [hzero, zero_smul]

theorem smooth_annular_indicator_cell_comparison {d : ℕ} (n : ℕ) (hn : 1 ≤ n)
    (G L : ℝ) (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth n G μ)
    (a e : Ambient d) (he : ‖e‖ ≤ 1)
    (r R ε : ℝ) (hr : 0 < r) (hrR : r ≤ R) (hε : 0 < ε) (hεr : ε < r / 2)
    (S : Set (Ambient d)) (hS : MeasurableSet S) (hSfin : μ S < ∞)
    (hcontains : ball a (2 * R) ⊆ S)
    (A Q : Set (Ambient d)) (hA : MeasurableSet A) (hQ : MeasurableSet Q)
    (hAfin : μ A < ∞) (hQfin : μ Q < ∞) (hApos : 0 < μ.real A) (hQpos : 0 < μ.real Q)
    (hAnear : ∀ x ∈ A, 2 * dist x a ≤ r) (hQnear : ∀ x ∈ Q, 2 * dist x a ≤ R)
    (hAmass : r ^ n ≤ L * μ.real A) (hQmass : R ^ n ≤ L * μ.real Q)
    (D : ℝ≥0)
    (hRiesz : ∀ u : Ambient d → ℝ, MemLp u 2 μ →
      MemLp (truncated n μ ε u) 2 μ ∧
        eLpNorm (truncated n μ ε u) 2 μ ≤ (D : ℝ≥0∞) * eLpNorm u 2 μ) :
    |inner ℝ e (smoothAnnularTransform n μ a r R hr (hr.trans_le hrR))| ≤
      |cellMean (μ.restrict A) (fun x => inner ℝ e
          (truncated n μ ε (S.indicator (fun _ => 1)) x)) -
        cellMean (μ.restrict Q) (fun x => inner ℝ e
          (truncated n μ ε (S.indicator (fun _ => 1)) x))| +
      3 * ((D : ℝ) ^ 2 * (G * 2 ^ n * L) + 1) + 3 * exteriorCellMeanConstant n G 1 := by
  let f : Ambient d → ℝ := annularSmoothBallCutoff a r hr
  let g := smoothAnnularWeight a r R hr (hr.trans_le hrR)
  let h := smoothExteriorWeight a R (hr.trans_le hrR) S
  have hf := annularSmoothBallCutoff_energy n G μ hg a r hr
  have hg' := smoothAnnularWeight_properties n G μ hg a r R hr hrR
  have hh := smoothExteriorWeight_properties n G μ hg a R (hr.trans_le hrR) S hS hSfin hcontains
  have hGN : 0 ≤ G * (2 : ℝ) ^ n := mul_nonneg hg.1 (by positivity)
  have hlocal (t : ℝ) (B : Set (Ambient d)) (ht : t ^ n ≤ L * μ.real B) :
      G * (2 * t) ^ n ≤ (G * 2 ^ n * L) * μ.real B := by
    calc
      _ = (G * 2 ^ n) * t ^ n := by rw [mul_pow]; ring
      _ ≤ (G * 2 ^ n) * (L * μ.real B) := mul_le_mul_of_nonneg_left ht hGN
      _ = _ := by ring
  have hfA : (∫ y, f y ^ 2 ∂μ) ≤ (G * 2 ^ n * L) * μ.real A :=
    hf.2.trans (hlocal r A hAmass)
  have hfQ : (∫ y, f y ^ 2 ∂μ) ≤ (G * 2 ^ n * L) * μ.real Q :=
    hf.2.trans (hlocal r Q ((pow_le_pow_left₀ hr.le hrR n).trans hQmass))
  have hgQ : (∫ y, g y ^ 2 ∂μ) ≤ (G * 2 ^ n * L) * μ.real Q :=
    hg'.2.2.2.trans (hlocal R Q hQmass)
  have hb := annular_cell_average_comparison n hn G 1 (G * 2 ^ n * L) μ hg ε r R
    hε hr hrR hεr f g h hf.1 hg'.1 hh.1 (by norm_num) hg'.2.1 hh.2.1
    a e he hg'.2.2.1 hh.2.2 A Q hA hQ hAfin hQfin hApos hQpos hAnear hQnear
    hfA hfQ hgQ D hRiesz
  have heq : (fun y => f y + g y + h y) = S.indicator (fun _ => 1) :=
    funext (smoothAnnularWeights_sum a r R hr (hr.trans_le hrR) S)
  rw [heq] at hb
  change |inner ℝ e (truncated n μ ε (smoothAnnularWeight a r R hr (hr.trans_le hrR)) a)| ≤ _ at hb
  rwa [truncated_smoothAnnular_at_center n G μ hg a r R ε hr hrR (by linarith)] at hb

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_SmoothAnnularIntegrability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

theorem exists_unit_bounded_norm_direction {d : ℕ} (v : Ambient d) :
    ∃ e : Ambient d, ‖e‖ ≤ 1 ∧ inner ℝ e v = ‖v‖ := by
  by_cases hv : v = 0
  · refine ⟨0, by simp, ?_⟩
    simp [hv]
  · have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    refine ⟨‖v‖⁻¹ • v, ?_, ?_⟩
    · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg v)),
        inv_mul_cancel₀ hn]
    · rw [real_inner_smul_left, real_inner_self_eq_norm_sq, pow_two]
      field_simp

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_BallLocalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Localization to balls

Restricting a measure preserves its global upper growth bound and gives finite mass on
positive-radius balls. The diameter estimate controls pairs of points in a ball, while
the Lipschitz height estimate supplies the boundedness needed for local `MemLp` control.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal

theorem finiteMeasure_restrict_ball_of_globalGrowth {d : ℕ} (m : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth m C μ)
    (a : Ambient d) (R : ℝ) (hR : 0 < R) : IsFiniteMeasure (μ.restrict (ball a R)) := by
  constructor
  simpa only [Measure.restrict_apply_univ] using! (hg.2 a R hR).trans_lt ENNReal.ofReal_lt_top

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Flatness_FlatCellSeeds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem exists_uniform_flat_ball_to_cell {n d : ℕ} (hnd : n ≤ d)
    (ρ A α : ℝ) (hρ : 0 < ρ) (hA : 1 ≤ A) (hα : 0 < α) :
    ∃ I : ℕ, 0 < I ∧ ∀ (μ : Measure (Ambient d))
      (R₀ : ℝ) (hR₀ : 0 < R₀) (k : ℕ) (z : (supportLatticeNets μ R₀ hR₀ k).points),
      HasFlatBallAbove n μ (ball (z : Ambient d) (latticeRadius R₀ k / 16))
        (ρ * latticeRadius R₀ k) (latticeRadius R₀ k / 16) (α / (1024 * (A + 2))) →
      HasFlatDescendant n μ R₀ hR₀ k z I A α := by
  obtain ⟨I, hI, hchoose⟩ := exists_uniform_flat_ball_descendant_geometry ρ A hρ hA
  refine ⟨I, hI, ?_⟩
  intro μ R₀ hR₀ k z hflat
  obtain ⟨a, ha, hnear, r, hr, hfloor, hcap, hbeta⟩ := hflat
  obtain ⟨i, hip, hiI, hscale, hisize, hsub⟩ :=
    hchoose μ R₀ hR₀ k z a ha hnear r hr hfloor hcap
  obtain ⟨S, hS, he⟩ := exists_bilateral_plane_error_lt hnd μ a r _ hbeta
  obtain ⟨hf, hb⟩ := bilateralPlaneError_lt_pointwise μ ⟨a, ha⟩ a r _ hr S hS he
  have hAp : 0 < A + 2 := by linarith
  have hbound : (α / (1024 * (A + 2))) * r ≤ α * i.radius := by
    calc
      _ ≤ (α / (1024 * (A + 2))) * ((512 * (A + 2)) * i.radius) :=
        mul_le_mul_of_nonneg_left hscale (by positivity)
      _ = α * i.radius / 2 := by field_simp <;> ring
      _ ≤ α * i.radius := by nlinarith [mul_pos hα i.radius_pos]
  refine ⟨i, hip, hiI, hisize, S, hS, ?_, ?_⟩
  · intro x hx hsupp
    exact (hf x (hsub hx) hsupp).le.trans hbound
  · intro x hx hs
    exact (hb x (hsub hx) hs).le.trans hbound

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_SmoothAnnularGapWitness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

theorem exists_uniform_smooth_annular_gap_direction {d : ℕ} (n : ℕ) (hn : 1 ≤ n)
    (G L : ℝ) (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth n G μ)
    (a : Ambient d) (r R : ℝ) (hr : 0 < r) (hrR : r ≤ R)
    (S : Set (Ambient d)) (hS : MeasurableSet S) (hSfin : μ S < ∞)
    (hcontains : ball a (2 * R) ⊆ S)
    (A Q : Set (Ambient d)) (hA : MeasurableSet A) (hQ : MeasurableSet Q)
    (hAfin : μ A < ∞) (hQfin : μ Q < ∞) (hApos : 0 < μ.real A) (hQpos : 0 < μ.real Q)
    (hAnear : ∀ x ∈ A, 2 * dist x a ≤ r) (hQnear : ∀ x ∈ Q, 2 * dist x a ≤ R)
    (hAmass : r ^ n ≤ L * μ.real A) (hQmass : R ^ n ≤ L * μ.real Q)
    (D : ℝ≥0)
    (hRiesz : ∀ ε : ℝ, 0 < ε → ∀ u : Ambient d → ℝ, MemLp u 2 μ →
      MemLp (truncated n μ ε u) 2 μ ∧
        eLpNorm (truncated n μ ε u) 2 μ ≤ (D : ℝ≥0∞) * eLpNorm u 2 μ) :
    ∃ e : Ambient d, ‖e‖ ≤ 1 ∧ ∀ ε : ℝ, 0 < ε → ε < r / 2 →
      ‖smoothAnnularTransform n μ a r R hr (hr.trans_le hrR)‖ -
        (3 * ((D : ℝ) ^ 2 * (G * 2 ^ n * L) + 1) + 3 * exteriorCellMeanConstant n G 1) ≤
      |cellMean (μ.restrict A) (fun x => inner ℝ e
          (truncated n μ ε (S.indicator (fun _ => 1)) x)) -
        cellMean (μ.restrict Q) (fun x => inner ℝ e
          (truncated n μ ε (S.indicator (fun _ => 1)) x))| := by
  obtain ⟨e, he, hev⟩ := exists_unit_bounded_norm_direction
    (smoothAnnularTransform n μ a r R hr (hr.trans_le hrR))
  refine ⟨e, he, ?_⟩
  intro ε hε hεr
  have hb := smooth_annular_indicator_cell_comparison n hn G L μ hg a e he r R ε hr hrR hε hεr
    S hS hSfin hcontains A Q hA hQ hAfin hQfin hApos hQpos hAnear hQnear
    hAmass hQmass D (hRiesz ε hε)
  rw [hev, abs_of_nonneg (norm_nonneg _)] at hb
  linarith

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_AnnularCellPairSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

theorem exists_annular_cell_pair {d : ℕ} (μ : Measure (Ambient d))
    (R₀ : ℝ) (hR₀ : 0 < R₀) (k : ℕ) (z : (supportLatticeNets μ R₀ hR₀ k).points)
    (a : Ambient d) (ha : a ∈ μ.support) (hnear : dist a (z : Ambient d) ≤ latticeRadius R₀ k / 8)
    (r R : ℝ) (hr : 0 < r) (hrR : r ≤ R) (hRtop : R ≤ latticeRadius R₀ k / 8)
    (I : ℕ) (hdepth : annularLatticeDepth R₀ k r hr ≤ I) :
    ∃ P : CellHaarPair μ R₀ hR₀ k z I,
      (∀ x ∈ P.innerCell, 2 * dist x a ≤ r) ∧
      (∀ x ∈ P.outerCell, 2 * dist x a ≤ R) ∧
      r ≤ 512 * latticeRadius R₀ (k + P.outerOffset + P.innerOffset) ∧
      R ≤ 512 * latticeRadius R₀ (k + P.outerOffset) := by
  have hR := hr.trans_le hrR
  have hp := latticeRadius_pos R₀ hR₀ k
  let t := annularLatticeDepth R₀ k R hR
  have htpos : 0 < t := annularLatticeDepth_pos R₀ k R hR (by linarith)
  have htu : t ≤ annularLatticeDepth R₀ k r hr :=
    annularLatticeDepth_antitone R₀ k r R hr hR hrR
  obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le htu
  have htj : t + j ≤ I := by rw [← hj]; exact hdepth
  have huOuter : latticeRadius R₀ (k + t) ≤ R / 8 :=
    annularLatticeDepth_radius_upper R₀ k R hR
  have huInner : latticeRadius R₀ (k + t + j) ≤ r / 8 := by
    rw [Nat.add_assoc, ← hj]
    exact annularLatticeDepth_radius_upper R₀ k r hr
  have hlOuter : R ≤ 512 * latticeRadius R₀ (k + t) :=
    annularLatticeDepth_radius_lower R₀ hR₀ k R hR (by linarith)
  have hlInner : r ≤ 512 * latticeRadius R₀ (k + t + j) := by
    rw [Nat.add_assoc, ← hj]
    exact annularLatticeDepth_radius_lower R₀ hR₀ k r hr (by linarith)
  obtain ⟨w, haw⟩ := supportLatticeCell_cover μ R₀ hR₀ (k + t + j) a ha
  let v := supportLatticeAncestor μ R₀ hR₀ (k + t) j w
  have hav : a ∈ supportLatticeCell μ R₀ hR₀ (k + t) v :=
    supportLatticeCell_nested μ R₀ hR₀ (k + t) j w haw
  have hvz : supportLatticeAncestor μ R₀ hR₀ k t v = z :=
    closed_cell_ancestor_eq_of_interior_point μ R₀ hR₀ k t htpos z v a hav hnear (by linarith)
  let P : CellHaarPair μ R₀ hR₀ k z I :=
    { outerOffset := t, innerOffset := j, depth_bound := htj,
      outerCenter := v, innerCenter := w, outer_ancestor := hvz, inner_ancestor := rfl }
  refine ⟨P, ?_, ?_, hlInner, hlOuter⟩
  · intro x hx
    have hd := clean_cell_dist_to_closed_point μ R₀ hR₀ (k + t + j) w a haw x hx
    linarith
  · intro x hx
    have hd := clean_cell_dist_to_closed_point μ R₀ hR₀ (k + t) v a hav x hx
    linarith

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_AnnularCellPairMasses
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

theorem CellHaarPair.outer_real_pos {n d : ℕ} {μ : Measure (Ambient d)}
    {R : ℝ} {hR : 0 < R} {k I : ℕ} {z : (supportLatticeNets μ R hR k).points}
    (P : CellHaarPair μ R hR k z I) (C G : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
    (hcore : AdmissibleRadius μ (latticeRadius R k / 8)) : 0 < μ.real P.outerCell := by
  have ha := lattice_core_admissible_at_later_level μ R hR k (k + P.outerOffset) (by omega) hcore
  have hp := cleanSupportCell_measure_pos_finite μ C G hC hG hg hlower R hR
    (k + P.outerOffset) ha P.outerCenter
  exact ENNReal.toReal_pos hp.1.ne' hp.2.ne

theorem exists_annular_cell_pair_with_masses {n d : ℕ}
    (μ : Measure (Ambient d)) (C G : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
    (R₀ : ℝ) (hR₀ : 0 < R₀) (k : ℕ) (z : (supportLatticeNets μ R₀ hR₀ k).points)
    (hcore : AdmissibleRadius μ (latticeRadius R₀ k / 8))
    (a : Ambient d) (ha : a ∈ μ.support) (hnear : dist a (z : Ambient d) ≤ latticeRadius R₀ k / 8)
    (r R : ℝ) (hr : 0 < r) (hrR : r ≤ R) (hRtop : R ≤ latticeRadius R₀ k / 8)
    (I : ℕ) (hdepth : annularLatticeDepth R₀ k r hr ≤ I) :
    ∃ P : CellHaarPair μ R₀ hR₀ k z I,
      (∀ x ∈ P.innerCell, 2 * dist x a ≤ r) ∧
      (∀ x ∈ P.outerCell, 2 * dist x a ≤ R) ∧
      r ^ n ≤ annularCellMassConstant n C * μ.real P.innerCell ∧
      R ^ n ≤ annularCellMassConstant n C * μ.real P.outerCell := by
  obtain ⟨P, hPi, hPo, hri, hRo⟩ := exists_annular_cell_pair μ R₀ hR₀ k z a ha hnear r R hr hrR hRtop I hdepth
  refine ⟨P, hPi, hPo, ?_, ?_⟩
  · exact clean_cell_annular_mass_bound μ C G hC hG hg hlower R₀ hR₀
      (k + P.outerOffset + P.innerOffset) P.innerCenter
      (lattice_core_admissible_at_later_level μ R₀ hR₀ k _ (by omega) hcore) r hr.le hri
  · exact clean_cell_annular_mass_bound μ C G hC hG hg hlower R₀ hR₀
      (k + P.outerOffset) P.outerCenter
      (lattice_core_admissible_at_later_level μ R₀ hR₀ k _ (by omega) hcore) R (hr.trans_le hrR).le hRo

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_AnnularCellGap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

theorem exists_annular_cell_gap {n d : ℕ} (hn : 1 ≤ n)
    (μ : Measure (Ambient d)) (C G : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
    (R₀ : ℝ) (hR₀ : 0 < R₀) (k : ℕ) (z : (supportLatticeNets μ R₀ hR₀ k).points)
    (hcore : AdmissibleRadius μ (latticeRadius R₀ k / 8))
    (a : Ambient d) (ha : a ∈ μ.support) (hnear : dist a (z : Ambient d) ≤ latticeRadius R₀ k / 8)
    (r R : ℝ) (hr : 0 < r) (hrR : r ≤ R) (hRtop : R ≤ latticeRadius R₀ k / 8)
    (I : ℕ) (hdepth : annularLatticeDepth R₀ k r hr ≤ I)
    (S : Set (Ambient d)) (hS : MeasurableSet S) (hSfin : μ S < ∞) (hcontains : ball a (2 * R) ⊆ S)
    (D : ℝ≥0)
    (hRiesz : ∀ ε : ℝ, 0 < ε → ∀ f : Ambient d → ℝ, MemLp f 2 μ →
      MemLp (truncated n μ ε f) 2 μ ∧
        eLpNorm (truncated n μ ε f) 2 μ ≤ (D : ℝ≥0∞) * eLpNorm f 2 μ) :
    ∃ (P : CellHaarPair μ R₀ hR₀ k z I) (e : Ambient d), ‖e‖ ≤ 1 ∧
      ∀ ε : ℝ, 0 < ε → ε < r / 2 →
        ‖smoothAnnularTransform n μ a r R hr (hr.trans_le hrR)‖ - annularCellComparisonError n C G D ≤
        |cellMean (μ.restrict P.innerCell) (fun x => inner ℝ e
            (truncated n μ ε (S.indicator (fun _ => 1)) x)) -
          cellMean (μ.restrict P.outerCell) (fun x => inner ℝ e
            (truncated n μ ε (S.indicator (fun _ => 1)) x))| := by
  obtain ⟨P, hPi, hPo, hmi, hmo⟩ := exists_annular_cell_pair_with_masses μ C G hC hG hg hlower
    R₀ hR₀ k z hcore a ha hnear r R hr hrR hRtop I hdepth
  have hfin := P.cells_finite G hg
  obtain ⟨e, he, hgap⟩ := exists_uniform_smooth_annular_gap_direction n hn G
    (annularCellMassConstant n C) μ hg a r R hr hrR S hS hSfin hcontains
    P.innerCell P.outerCell P.inner_measurable P.outer_measurable hfin.1 hfin.2
    (P.inner_real_pos C G hC hG hg hlower hcore) (P.outer_real_pos C G hC hG hg hlower hcore)
    hPi hPo hmi hmo D hRiesz
  exact ⟨P, e, he, hgap⟩

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_CellAnnularWitnesses
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

theorem CellAnnulus.top_ball_contains {d : ℕ} {μ : Measure (Ambient d)}
    {R₀ : ℝ} {hR₀ : 0 < R₀} {k : ℕ} {z : (supportLatticeNets μ R₀ hR₀ k).points} {ρ : ℝ}
    (i : SupportCellDescendant μ R₀ hR₀ k z)
    (W : CellAnnulus μ R₀ hR₀ (k + i.depth) ⟨i.center, i.mem_net⟩ ρ) :
    ball W.center (2 * W.outerRadius) ⊆ ball (z : Ambient d) (4 * latticeRadius R₀ k) := by
  intro x hx
  have hxW : dist x W.center < 2 * W.outerRadius := hx
  have hW : dist W.center i.center ≤ i.radius / 8 := W.center_dist
  have hR : W.outerRadius ≤ i.radius / 8 := W.outer_upper
  have hi := i.center_dist_top
  have hr : i.radius ≤ latticeRadius R₀ k := latticeRadius_antitone R₀ hR₀.le (by omega)
  have ht1 := dist_triangle x W.center i.center
  have ht2 := dist_triangle x i.center (z : Ambient d)
  have hp := latticeRadius_pos R₀ hR₀ k
  change dist x (z : Ambient d) < 4 * latticeRadius R₀ k
  linarith

theorem exists_uniform_depth_for_cell_annuli (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ I : ℕ, 0 < I ∧ ∀ (d : ℕ) (μ : Measure (Ambient d)) (R₀ : ℝ) (hR₀ : 0 < R₀)
      (k : ℕ) (z : (supportLatticeNets μ R₀ hR₀ k).points) (W : CellAnnulus μ R₀ hR₀ k z ρ),
      annularLatticeDepth R₀ k W.innerRadius W.inner_pos ≤ I := by
  obtain ⟨I, hI, hb⟩ := exists_uniform_annular_lattice_depth ρ hρ
  exact ⟨I, hI, fun _ _ R₀ hR₀ k _ W => hb R₀ hR₀ k W.innerRadius W.inner_pos W.inner_lower⟩

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Flatness_FlatDescendantAlternative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem exists_uniform_flat_descendant_annular_alternative {n d : ℕ}
    (hn : 1 ≤ n) (hnd : n ≤ d) (C G B A α : ℝ)
    (hC : 0 < C) (hA : 1 ≤ A) (hα : 0 < α) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 / 16 ∧ ∃ I : ℕ, 0 < I ∧
      ∀ μ : Measure (Ambient d), GlobalUpperGrowth n G μ →
      (∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
        ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r)) →
      ∀ (R₀ : ℝ) (hR₀ : 0 < R₀) (k : ℕ) (z : (supportLatticeNets μ R₀ hR₀ k).points),
      AdmissibleRadius μ (latticeRadius R₀ k / 8) →
      HasFlatDescendant n μ R₀ hR₀ k z I A α ∨
        HasLargeCellAnnulus n μ R₀ hR₀ k z ρ B := by
  obtain ⟨ρ, hρ, hρcap, hchoose⟩ := exists_uniform_cell_flat_annular_alternative hn hnd C G B
    (α / (1024 * (A + 2))) hC (by positivity)
  obtain ⟨I, hI, hflat⟩ := exists_uniform_flat_ball_to_cell hnd ρ A α hρ hA hα
  refine ⟨ρ, hρ, hρcap, I, hI, ?_⟩
  intro μ hg hlower R₀ hR₀ k z hcore
  rcases hchoose μ hg hlower R₀ hR₀ k z hcore with hf | ha
  · exact Or.inl (hflat μ R₀ hR₀ k z hf)
  · exact Or.inr ha

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_CommonFiniteTruncation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

theorem exists_positive_below_finset {ι : Type*} (s : Finset ι) (r : ι → ℝ)
    (hr : ∀ i ∈ s, 0 < r i) : ∃ ε : ℝ, 0 < ε ∧ ∀ i ∈ s, ε < r i := by
  classical
  revert hr
  induction s using Finset.induction_on with
  | empty =>
    intro _
    exact ⟨1, by norm_num, by simp⟩
  | @insert a s _ ih =>
    intro hr
    have ha := hr a (Finset.mem_insert_self a s)
    obtain ⟨δ, hδ, hsmall⟩ := ih (fun i hi => hr i (Finset.mem_insert_of_mem hi))
    have hm : 0 < min δ (r a) := lt_min hδ ha
    refine ⟨min δ (r a) / 2, by positivity, ?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · have hh := min_le_right δ (r i)
      linarith
    · have hh := min_le_left δ (r a)
      have hsi := hsmall i hi
      linarith

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_FixedCutoffPairingLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Fixed-cutoff limits of hard-truncated pairings

Restricting a globally growing measure to the outer ball gives a finite measure.
Mean-zero Lipschitz tests then identify the limit of dyadic hard truncations
with the scalar Riesz pairing on that restriction. The ball indicator also has
finite squared integral equal to the real mass of the ball.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

theorem ball_indicator_one_memLp_and_sq_integral {d : ℕ} (n : ℕ) (G : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth n G μ)
    (a : Ambient d) (T : ℝ) (hT : 0 < T) :
    MemLp ((ball a T).indicator (fun _ => (1 : ℝ))) 2 μ ∧
      (∫ x, ((ball a T).indicator (fun _ => (1 : ℝ)) x) ^ 2 ∂μ) = μ.real (ball a T) := by
  let : IsFiniteMeasure (μ.restrict (ball a T)) :=
    finiteMeasure_restrict_ball_of_globalGrowth n G μ hg a T hT
  refine ⟨(memLp_indicator_iff_restrict measurableSet_ball).mpr (memLp_const (1 : ℝ)), ?_⟩
  have heq : (fun x => ((ball a T).indicator (fun _ => (1 : ℝ)) x) ^ 2) =
      (ball a T).indicator (fun _ => (1 : ℝ)) := by
    funext x
    by_cases hx : x ∈ ball a T <;> simp only [indicator_of_mem, indicator_of_notMem, hx,
      not_false_eq_true, one_pow, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
  rw [heq, integral_indicator measurableSet_ball, integral_const]
  simp only [Measure.real, Measure.restrict_apply_univ, smul_eq_mul, mul_one]

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Packing_CoarseLevelPacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

theorem finite_sum_of_bounded_level_slices {ι : Type*}
    (s : Finset ι) (level : ι → ℕ) (mass : ι → ℝ) (N : ℕ) (B : ℝ)
    (hlevel : ∀ i ∈ s, level i < N)
    (hslice : ∀ k < N, ∑ i ∈ s with level i = k, mass i ≤ B) :
    ∑ i ∈ s, mass i ≤ (N : ℝ) * B := by
  classical
  have hsum : (∑ k ∈ Finset.range N, ∑ i ∈ s with level i = k, mass i) = ∑ i ∈ s, mass i :=
    Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_range.mpr (hlevel i hi)) mass
  rw [← hsum]
  calc
    _ ≤ ∑ _k ∈ Finset.range N, B := Finset.sum_le_sum (fun k hk => hslice k (Finset.mem_range.mp hk))
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_LatticeOscillationTotalMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

theorem measure_tsum_le_of_real_finset_bounds {ι X : Type*} [MeasurableSpace X]
    (μ : Measure X) (A : ι → Set X) (B : ℝ)
    (hfinite : ∀ i, μ (A i) ≠ ∞)
    (hbound : ∀ s : Finset ι, ∑ i ∈ s, μ.real (A i) ≤ B) :
    ∑' i, μ (A i) ≤ ENNReal.ofReal B := by
  rw [ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro s
  have heq : ∑ i ∈ s, μ (A i) = ENNReal.ofReal (∑ i ∈ s, μ.real (A i)) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => measureReal_nonneg)]
    apply Finset.sum_congr rfl
    intro i _
    exact (ENNReal.ofReal_toReal (hfinite i)).symm
  rw [heq]
  exact ENNReal.ofReal_le_ofReal (hbound s)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Packing_CellHaarOrthogonality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

theorem integral_mul_zero_of_constant_on_set {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (A : Set X) (f g : X → ℝ) (c : ℝ)
    (hf : ∀ x ∈ A, f x = c) (hg : ∀ x ∉ A, g x = 0) (hzero : (∫ x, g x ∂μ) = 0) :
    (∫ x, f x * g x ∂μ) = 0 := by
  have heq : (fun x => f x * g x) = fun x => c * g x := by
    funext x
    by_cases hx : x ∈ A
    · rw [hf x hx]
    · rw [hg x hx, mul_zero, mul_zero]
  rw [heq, integral_const_mul, hzero, mul_zero]

theorem integral_mul_zero_of_disjoint_support_sets {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (A B : Set X) (f g : X → ℝ) (hAB : Disjoint A B)
    (hf : ∀ x ∉ A, f x = 0) (hg : ∀ x ∉ B, g x = 0) :
    (∫ x, f x * g x ∂μ) = 0 := by
  apply integral_eq_zero_of_ae
  exact Filter.Eventually.of_forall fun x => by
    change f x * g x = 0
    by_cases hx : x ∈ A
    · rw [hg x (fun hy => Set.disjoint_left.mp hAB hx hy), mul_zero]
    · rw [hf x hx, zero_mul]

theorem SupportCellDescendant.disjoint_of_same_depth {d : ℕ} {μ : Measure (Ambient d)}
    {R : ℝ} {hR : 0 < R} {k : ℕ} {z : (supportLatticeNets μ R hR k).points}
    (i j : SupportCellDescendant μ R hR k z) (hdepth : i.depth = j.depth) (hne : i ≠ j) :
    Disjoint i.cell j.cell := by
  rcases i with ⟨ti, xi, hxi, hai⟩
  rcases j with ⟨tj, xj, hxj, haj⟩
  dsimp only at hdepth
  subst tj
  have hc : xi ≠ xj := by
    intro heq
    subst xj
    exact hne rfl
  exact cleanSupportCell_disjoint μ R hR (k + ti) ⟨xi, hxi⟩ ⟨xj, hxj⟩
    (fun h => hc (congrArg Subtype.val h))

theorem cellHaarPair_orthogonal_of_level_gap {d : ℕ} (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) (k l I : ℕ)
    (z : (supportLatticeNets μ R hR k).points) (w : (supportLatticeNets μ R hR l).points)
    (P : CellHaarPair μ R hR k z I) (Q : CellHaarPair μ R hR l w I)
    (hgap : k + I ≤ l) (hzero : (∫ x, Q.test x ∂μ) = 0) :
    (∫ x, P.test x * Q.test x ∂μ) = 0 := by
  obtain ⟨c, hc⟩ := P.test_constant_on_finer l hgap w
  exact integral_mul_zero_of_constant_on_set μ (cleanSupportCell μ R hR l w) P.test Q.test c
    hc Q.test_zero_outside_parent hzero

theorem bounded_depth_cell_haar_orthogonal {n d : ℕ}
    (μ : Measure (Ambient d)) (C G : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
    (R : ℝ) (hR : 0 < R) (k I : ℕ) (z : (supportLatticeNets μ R hR k).points)
    (hcore : AdmissibleRadius μ (latticeRadius R k / 8))
    (P : (i : SupportCellDescendant μ R hR k z) →
      CellHaarPair μ R hR (k + i.depth) ⟨i.center, i.mem_net⟩ I)
    (i j : SupportCellDescendant μ R hR k z) (hmod : i.depth % I = j.depth % I) (hne : i ≠ j) :
    (∫ x, (P i).test x * (P j).test x ∂μ) = 0 := by
  have hzero (a : SupportCellDescendant μ R hR k z) : (∫ x, (P a).test x ∂μ) = 0 :=
    ((P a).test_properties C G hC hG hg hlower
      (lattice_core_admissible_at_later_level μ R hR k (k + a.depth)
        (Nat.le_add_right k a.depth) hcore)).2.1
  rcases lt_trichotomy i.depth j.depth with hij | hij | hij
  · have hgap : i.depth + I ≤ j.depth := Nat.ModEq.add_le_of_lt hmod hij
    exact cellHaarPair_orthogonal_of_level_gap μ R hR (k + i.depth) (k + j.depth) I
      ⟨i.center, i.mem_net⟩ ⟨j.center, j.mem_net⟩ (P i) (P j) (by omega) (hzero j)
  · exact integral_mul_zero_of_disjoint_support_sets μ i.cell j.cell (P i).test (P j).test
      (i.disjoint_of_same_depth j hij hne) (P i).test_zero_outside_parent (P j).test_zero_outside_parent
  · have hgap : j.depth + I ≤ i.depth := Nat.ModEq.add_le_of_lt hmod.symm hij
    have h := cellHaarPair_orthogonal_of_level_gap μ R hR (k + j.depth) (k + i.depth) I
      ⟨j.center, j.mem_net⟩ ⟨i.center, i.mem_net⟩ (P j) (P i) (by omega) (hzero i)
    simpa only [mul_comm] using! h

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Packing_BoundedDepthHaarBessel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

theorem finite_L2_bessel_of_orthogonal_unit_bounds {ι X : Type*} [MeasurableSpace X]
    (μ : Measure X) (s : Finset ι) (f : ι → X → ℝ) (hf : ∀ i, MemLp (f i) 2 μ)
    (hdiag : ∀ i ∈ s, (∫ x, f i x ^ 2 ∂μ) ≤ 1)
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → (∫ x, f i x * f j x ∂μ) = 0)
    (u : X → ℝ) (hu : MemLp u 2 μ) :
    ∑ i ∈ s, (∫ x, f i x * u x ∂μ) ^ 2 ≤ ∫ x, u x ^ 2 ∂μ := by
  classical
  have hrow : ∀ i ∈ s, ∑ j ∈ s, |∫ x, f i x * f j x ∂μ| * (1 : ℝ) ≤ 1 * 1 := by
    intro i hi
    simp only [mul_one]
    rw [Finset.sum_eq_single i
      (fun j hj hne => by rw [horth i hi j hj hne.symm, abs_zero])
      (fun hnot => False.elim (hnot hi))]
    rw [abs_of_nonneg (integral_nonneg (fun x => mul_self_nonneg (f i x)))]
    simpa only [pow_two] using! hdiag i hi
  simpa only [one_mul] using! finite_L2_bessel_of_weighted_pairings μ s f hf
    (fun _ => 1) 1 (by norm_num) (fun _ _ => by norm_num) hrow u hu

theorem finite_L2_bessel_of_level_classes {ι X : Type*} [MeasurableSpace X]
    (μ : Measure X) (s : Finset ι) (f : ι → X → ℝ) (hf : ∀ i, MemLp (f i) 2 μ)
    (level : ι → ℕ) (I : ℕ) (hI : 0 < I)
    (hdiag : ∀ i ∈ s, (∫ x, f i x ^ 2 ∂μ) ≤ 1)
    (horth : ∀ i ∈ s, ∀ j ∈ s, level i % I = level j % I → i ≠ j →
      (∫ x, f i x * f j x ∂μ) = 0)
    (u : X → ℝ) (hu : MemLp u 2 μ) :
    ∑ i ∈ s, (∫ x, f i x * u x ∂μ) ^ 2 ≤ (I : ℝ) * ∫ x, u x ^ 2 ∂μ := by
  classical
  apply finite_sum_of_bounded_level_slices s (fun i => level i % I)
    (fun i => (∫ x, f i x * u x ∂μ) ^ 2) I (∫ x, u x ^ 2 ∂μ)
    (fun i _ => Nat.mod_lt (level i) hI)
  intro q _
  exact finite_L2_bessel_of_orthogonal_unit_bounds μ (s.filter (fun i => level i % I = q)) f hf
    (fun i hi => hdiag i (Finset.mem_filter.mp hi).1)
    (fun i hi j hj hne => horth i (Finset.mem_filter.mp hi).1 j (Finset.mem_filter.mp hj).1
      ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm) hne) u hu

theorem bounded_depth_cell_haar_bessel {n d : ℕ}
    (μ : Measure (Ambient d)) (C G : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
    (R : ℝ) (hR : 0 < R) (k I : ℕ) (hI : 0 < I) (z : (supportLatticeNets μ R hR k).points)
    (hcore : AdmissibleRadius μ (latticeRadius R k / 8))
    (P : (i : SupportCellDescendant μ R hR k z) →
      CellHaarPair μ R hR (k + i.depth) ⟨i.center, i.mem_net⟩ I)
    (s : Finset (SupportCellDescendant μ R hR k z))
    (u : Ambient d → ℝ) (hu : MemLp u 2 μ) :
    ∑ i ∈ s, (∫ x, (P i).test x * u x ∂μ) ^ 2 ≤ (I : ℝ) * ∫ x, u x ^ 2 ∂μ := by
  have hp (i : SupportCellDescendant μ R hR k z) :=
    (P i).test_properties C G hC hG hg hlower
      (lattice_core_admissible_at_later_level μ R hR k (k + i.depth)
        (Nat.le_add_right k i.depth) hcore)
  exact finite_L2_bessel_of_level_classes μ s (fun i => (P i).test) (fun i => (hp i).1)
    (fun i => i.depth) I hI (fun i _ => (hp i).2.2.1)
    (fun i _ j _ hmod hne => bounded_depth_cell_haar_orthogonal μ C G hC hG hg hlower
      R hR k I z hcore P i j hmod hne) u hu

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Packing_HaarCellMassRatio
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

theorem latticeRadius_le_depth_multiple (R : ℝ) (hR : 0 < R) (k t I : ℕ) (ht : t ≤ I) :
    latticeRadius R k ≤ (64 : ℝ) ^ I * latticeRadius R (k + t) := by
  calc
    _ = latticeRadius R k * ((64 : ℝ) * (1 / 64)) ^ I := by norm_num
    _ = (64 : ℝ) ^ I * latticeRadius R (k + I) := by rw [latticeRadius_add, mul_pow]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (latticeRadius_antitone R hR.le (Nat.add_le_add_left ht k)) (by positivity)

theorem haarCellMassRatio_pos (n : ℕ) (C G : ℝ) (I : ℕ) (hC : 0 < C) (hG : 0 < G) :
    0 < haarCellMassRatio n C G I := by
  unfold haarCellMassRatio
  positivity

theorem CellHaarPair.parent_mass_le_inner {n d : ℕ} {μ : Measure (Ambient d)}
    {R : ℝ} {hR : 0 < R} {k I : ℕ} {z : (supportLatticeNets μ R hR k).points}
    (P : CellHaarPair μ R hR k z I) (C G : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
    (hcore : AdmissibleRadius μ (latticeRadius R k / 8)) :
    μ.real (cleanSupportCell μ R hR k z) ≤ haarCellMassRatio n C G I * μ.real P.innerCell := by
  have hp := cleanSupportCell_real_measure_bounds μ C G hC hG hg hlower R hR k hcore z
  have hc := lattice_core_admissible_at_later_level μ R hR k
    (k + P.outerOffset + P.innerOffset) (by omega) hcore
  have hi := cleanSupportCell_real_measure_bounds μ C G hC hG hg hlower R hR
    (k + P.outerOffset + P.innerOffset) hc P.innerCenter
  have hr : latticeRadius R k ≤ (64 : ℝ) ^ I *
      latticeRadius R (k + P.outerOffset + P.innerOffset) := by
    simpa only [Nat.add_assoc] using! latticeRadius_le_depth_multiple R hR k
      (P.outerOffset + P.innerOffset) I P.depth_bound
  have hid : (G * 3 ^ n) * ((64 : ℝ) ^ I * latticeRadius R
      (k + P.outerOffset + P.innerOffset)) ^ n = haarCellMassRatio n C G I *
        ((latticeRadius R (k + P.outerOffset + P.innerOffset) / 8) ^ n / C) := by
    simp only [haarCellMassRatio, mul_pow, div_pow, pow_mul]
    field_simp
  calc
    _ ≤ (G * 3 ^ n) * latticeRadius R k ^ n := hp.2
    _ ≤ (G * 3 ^ n) * ((64 : ℝ) ^ I * latticeRadius R
        (k + P.outerOffset + P.innerOffset)) ^ n :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (latticeRadius_pos R hR k).le hr n) (by positivity)
    _ = _ := hid
    _ ≤ _ := mul_le_mul_of_nonneg_left hi.1 (haarCellMassRatio_pos n C G I hC hG).le

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Packing_HaarRieszBessel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

theorem bounded_depth_cell_haar_vector_bessel {n d : ℕ}
    (μ : Measure (Ambient d)) (C G : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
    (R : ℝ) (hR : 0 < R) (k I : ℕ) (hI : 0 < I) (z : (supportLatticeNets μ R hR k).points)
    (hcore : AdmissibleRadius μ (latticeRadius R k / 8))
    (P : (i : SupportCellDescendant μ R hR k z) →
      CellHaarPair μ R hR (k + i.depth) ⟨i.center, i.mem_net⟩ I)
    (s : Finset (SupportCellDescendant μ R hR k z))
    (u : Ambient d → Ambient d) (hu : MemLp u 2 μ)
    (e : SupportCellDescendant μ R hR k z → Ambient d) (he : ∀ i ∈ s, ‖e i‖ ≤ 1) :
    ∑ i ∈ s, (∫ x, (P i).test x * inner ℝ (e i) (u x) ∂μ) ^ 2 ≤
      (I : ℝ) * ∫ x, ‖u x‖ ^ 2 ∂μ := by
  have hp (i : SupportCellDescendant μ R hR k z) :=
    (P i).test_properties C G hC hG hg hlower
      (lattice_core_admissible_at_later_level μ R hR k (k + i.depth)
        (Nat.le_add_right k i.depth) hcore)
  exact finite_vector_bessel_of_scalar (EuclideanSpace.basisFun (Fin d) ℝ) μ s
    (fun i => (P i).test) (fun i => (hp i).1) (I : ℝ)
    (fun v hv => bounded_depth_cell_haar_bessel μ C G hC hG hg hlower R hR k I hI z hcore P s v hv)
    u hu e he

theorem bounded_depth_vector_average_bessel {n d : ℕ}
    (μ : Measure (Ambient d)) (C G : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
    (R : ℝ) (hR : 0 < R) (k I : ℕ) (hI : 0 < I) (z : (supportLatticeNets μ R hR k).points)
    (hcore : AdmissibleRadius μ (latticeRadius R k / 8))
    (P : (i : SupportCellDescendant μ R hR k z) →
      CellHaarPair μ R hR (k + i.depth) ⟨i.center, i.mem_net⟩ I)
    (s : Finset (SupportCellDescendant μ R hR k z))
    (u : Ambient d → Ambient d) (hu : MemLp u 2 μ)
    (e : SupportCellDescendant μ R hR k z → Ambient d) (he : ∀ i ∈ s, ‖e i‖ ≤ 1) :
    ∑ i ∈ s, μ.real (P i).innerCell *
      (cellMean (μ.restrict (P i).innerCell) (fun x => inner ℝ (e i) (u x)) -
        cellMean (μ.restrict (P i).outerCell) (fun x => inner ℝ (e i) (u x))) ^ 2 ≤
      (I : ℝ) * ∫ x, ‖u x‖ ^ 2 ∂μ := by
  have hp (i : SupportCellDescendant μ R hR k z) :=
    (P i).test_properties C G hC hG hg hlower
      (lattice_core_admissible_at_later_level μ R hR k (k + i.depth)
        (Nat.le_add_right k i.depth) hcore)
  have heq (i : SupportCellDescendant μ R hR k z) :
      (∫ x, (P i).test x * inner ℝ (e i) (u x) ∂μ) ^ 2 = μ.real (P i).innerCell *
        (cellMean (μ.restrict (P i).innerCell) (fun x => inner ℝ (e i) (u x)) -
          cellMean (μ.restrict (P i).outerCell) (fun x => inner ℝ (e i) (u x))) ^ 2 := by
    rw [(hp i).2.2.2 _ (memLp_inner_const_of_vector μ u hu (e i)), mul_pow,
      Real.sq_sqrt measureReal_nonneg]
  have hb := bounded_depth_cell_haar_vector_bessel μ C G hC hG hg hlower R hR k I hI z hcore P s u hu e he
  simpa only [heq] using! hb

theorem bounded_depth_riesz_average_bessel {n d : ℕ}
    (μ : Measure (Ambient d)) (C G : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
    (R : ℝ) (hR : 0 < R) (k I : ℕ) (hI : 0 < I) (z : (supportLatticeNets μ R hR k).points)
    (hcore : AdmissibleRadius μ (latticeRadius R k / 8))
    (P : (i : SupportCellDescendant μ R hR k z) →
      CellHaarPair μ R hR (k + i.depth) ⟨i.center, i.mem_net⟩ I)
    (s : Finset (SupportCellDescendant μ R hR k z)) (D : ℝ≥0)
    (hRiesz : ∀ ε : ℝ, 0 < ε → ∀ f : Ambient d → ℝ, MemLp f 2 μ →
      MemLp (truncated n μ ε f) 2 μ ∧
        eLpNorm (truncated n μ ε f) 2 μ ≤ (D : ℝ≥0∞) * eLpNorm f 2 μ)
    (ε : ℝ) (hε : 0 < ε) (f : Ambient d → ℝ) (hf : MemLp f 2 μ)
    (e : SupportCellDescendant μ R hR k z → Ambient d) (he : ∀ i ∈ s, ‖e i‖ ≤ 1) :
    ∑ i ∈ s, μ.real (P i).innerCell *
      (cellMean (μ.restrict (P i).innerCell) (fun x => inner ℝ (e i) (truncated n μ ε f x)) -
        cellMean (μ.restrict (P i).outerCell) (fun x => inner ℝ (e i) (truncated n μ ε f x))) ^ 2 ≤
      ((I : ℝ) * (D : ℝ) ^ 2) * ∫ x, f x ^ 2 ∂μ := by
  obtain ⟨hT, hN⟩ := hRiesz ε hε f hf
  have hb := bounded_depth_vector_average_bessel μ C G hC hG hg hlower R hR k I hI z hcore
    P s (truncated n μ ε f) hT e he
  have hn := mul_le_mul_of_nonneg_left
    (vector_sq_integral_of_native_norm_bound μ f _ hf hT D hN) (Nat.cast_nonneg I)
  exact hb.trans (by simpa only [mul_assoc] using! hn)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Packing_HaarAverageGapPacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

theorem bounded_depth_riesz_average_gap_packing {n d : ℕ}
    (μ : Measure (Ambient d)) (C G : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
    (R : ℝ) (hR : 0 < R) (k I : ℕ) (hI : 0 < I) (z : (supportLatticeNets μ R hR k).points)
    (hcore : AdmissibleRadius μ (latticeRadius R k / 8))
    (P : (i : SupportCellDescendant μ R hR k z) →
      CellHaarPair μ R hR (k + i.depth) ⟨i.center, i.mem_net⟩ I)
    (s : Finset (SupportCellDescendant μ R hR k z)) (D : ℝ≥0)
    (hRiesz : ∀ ε : ℝ, 0 < ε → ∀ f : Ambient d → ℝ, MemLp f 2 μ →
      MemLp (truncated n μ ε f) 2 μ ∧
        eLpNorm (truncated n μ ε f) 2 μ ≤ (D : ℝ≥0∞) * eLpNorm f 2 μ)
    (ε : ℝ) (hε : 0 < ε) (f : Ambient d → ℝ) (hf : MemLp f 2 μ)
    (e : SupportCellDescendant μ R hR k z → Ambient d) (he : ∀ i ∈ s, ‖e i‖ ≤ 1)
    (v : ℝ) (hv : 0 < v)
    (hgap : ∀ i ∈ s, v ≤
      |cellMean (μ.restrict (P i).innerCell) (fun x => inner ℝ (e i) (truncated n μ ε f x)) -
        cellMean (μ.restrict (P i).outerCell) (fun x => inner ℝ (e i) (truncated n μ ε f x))|) :
    ∑ i ∈ s, μ.real i.cell ≤
      ((haarCellMassRatio n C G I * (I : ℝ) * (D : ℝ) ^ 2) * ∫ x, f x ^ 2 ∂μ) / v ^ 2 := by
  let a := fun i : SupportCellDescendant μ R hR k z =>
    cellMean (μ.restrict (P i).innerCell) (fun x => inner ℝ (e i) (truncated n μ ε f x)) -
      cellMean (μ.restrict (P i).outerCell) (fun x => inner ℝ (e i) (truncated n μ ε f x))
  have hK : 0 ≤ haarCellMassRatio n C G I := (haarCellMassRatio_pos n C G I hC hG).le
  have hm (i : SupportCellDescendant μ R hR k z) :
      μ.real i.cell ≤ haarCellMassRatio n C G I * μ.real (P i).innerCell :=
    (P i).parent_mass_le_inner C G hC hG hg hlower
      (lattice_core_admissible_at_later_level μ R hR k (k + i.depth)
        (Nat.le_add_right k i.depth) hcore)
  have hterm (i : SupportCellDescendant μ R hR k z) (hi : i ∈ s) :
      μ.real i.cell * v ^ 2 ≤ haarCellMassRatio n C G I * (μ.real (P i).innerCell * a i ^ 2) := by
    have hs : v ^ 2 ≤ a i ^ 2 := by
      simpa only [← pow_two, sq_abs] using! mul_self_le_mul_self hv.le (hgap i hi)
    calc
      _ ≤ (haarCellMassRatio n C G I * μ.real (P i).innerCell) * v ^ 2 :=
        mul_le_mul_of_nonneg_right (hm i) (sq_nonneg v)
      _ = haarCellMassRatio n C G I * (μ.real (P i).innerCell * v ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hs measureReal_nonneg) hK
  have hb := bounded_depth_riesz_average_bessel μ C G hC hG hg hlower R hR k I hI z hcore
    P s D hRiesz ε hε f hf e he
  apply (le_div_iff₀ (sq_pos_of_pos hv)).mpr
  calc
    _ = ∑ i ∈ s, μ.real i.cell * v ^ 2 := Finset.sum_mul ..
    _ ≤ ∑ i ∈ s, haarCellMassRatio n C G I * (μ.real (P i).innerCell * a i ^ 2) :=
      Finset.sum_le_sum hterm
    _ = haarCellMassRatio n C G I * ∑ i ∈ s, μ.real (P i).innerCell * a i ^ 2 :=
      (Finset.mul_sum ..).symm
    _ ≤ haarCellMassRatio n C G I * (((I : ℝ) * (D : ℝ) ^ 2) * ∫ x, f x ^ 2 ∂μ) :=
      mul_le_mul_of_nonneg_left hb hK
    _ = _ := by ring

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Packing_HaarTopBallPacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

theorem top_cell_ball_real_mass_bound {n d : ℕ}
    (μ : Measure (Ambient d)) (C G A : ℝ) (hC : 0 < C) (hG : 0 < G) (hA : 0 < A)
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points)
    (hcore : AdmissibleRadius μ (latticeRadius R k / 8)) :
    μ.real (ball (z : Ambient d) (A * latticeRadius R k)) ≤
      (C * G * (8 * A) ^ n) * μ.real (cleanSupportCell μ R hR k z) := by
  have hr := latticeRadius_pos R hR k
  have hu : μ.real (ball (z : Ambient d) (A * latticeRadius R k)) ≤
      G * (A * latticeRadius R k) ^ n :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) (hg.2 z _ (mul_pos hA hr))
  have hl := (cleanSupportCell_real_measure_bounds μ C G hC hG hg hlower R hR k hcore z).1
  have hid : G * (A * latticeRadius R k) ^ n =
      (C * G * (8 * A) ^ n) * ((latticeRadius R k / 8) ^ n / C) := by
    simp only [mul_pow, div_pow]
    field_simp
  exact hu.trans (hid.le.trans (mul_le_mul_of_nonneg_left hl (by positivity)))

theorem bounded_depth_haar_top_ball_packing {n d : ℕ}
    (μ : Measure (Ambient d)) (C G A : ℝ) (hC : 0 < C) (hG : 0 < G) (hA : 0 < A)
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
    (R : ℝ) (hR : 0 < R) (k I : ℕ) (hI : 0 < I) (z : (supportLatticeNets μ R hR k).points)
    (hcore : AdmissibleRadius μ (latticeRadius R k / 8))
    (P : (i : SupportCellDescendant μ R hR k z) →
      CellHaarPair μ R hR (k + i.depth) ⟨i.center, i.mem_net⟩ I)
    (s : Finset (SupportCellDescendant μ R hR k z)) (D : ℝ≥0)
    (hRiesz : ∀ ε : ℝ, 0 < ε → ∀ f : Ambient d → ℝ, MemLp f 2 μ →
      MemLp (truncated n μ ε f) 2 μ ∧
        eLpNorm (truncated n μ ε f) 2 μ ≤ (D : ℝ≥0∞) * eLpNorm f 2 μ)
    (ε : ℝ) (hε : 0 < ε)
    (e : SupportCellDescendant μ R hR k z → Ambient d) (he : ∀ i ∈ s, ‖e i‖ ≤ 1)
    (v : ℝ) (hv : 0 < v)
    (hgap : ∀ i ∈ s, v ≤
      |cellMean (μ.restrict (P i).innerCell)
          (fun x => inner ℝ (e i) (truncated n μ ε (topCellBallIndicator μ R hR k z A) x)) -
        cellMean (μ.restrict (P i).outerCell)
          (fun x => inner ℝ (e i) (truncated n μ ε (topCellBallIndicator μ R hR k z A) x))|) :
    ∑ i ∈ s, μ.real i.cell ≤
      haarTopBallPackingConstant n C G A v D I * μ.real (cleanSupportCell μ R hR k z) := by
  have hf : MemLp (topCellBallIndicator μ R hR k z A) 2 μ ∧
      (∫ x, topCellBallIndicator μ R hR k z A x ^ 2 ∂μ) =
        μ.real (ball (z : Ambient d) (A * latticeRadius R k)) :=
    ball_indicator_one_memLp_and_sq_integral n G μ hg z (A * latticeRadius R k)
      (mul_pos hA (latticeRadius_pos R hR k))
  have hb := bounded_depth_riesz_average_gap_packing μ C G hC hG hg hlower R hR k I hI z hcore
    P s D hRiesz ε hε (topCellBallIndicator μ R hR k z A) hf.1 e he v hv hgap
  rw [hf.2] at hb
  have hm := top_cell_ball_real_mass_bound μ C G A hC hG hA hg hlower R hR k z hcore
  have hK : 0 ≤ haarCellMassRatio n C G I * (I : ℝ) * (D : ℝ) ^ 2 := by
    have hp := haarCellMassRatio_pos n C G I hC hG
    positivity
  calc
    _ ≤ _ := hb
    _ ≤ (haarCellMassRatio n C G I * (I : ℝ) * (D : ℝ) ^ 2) *
        ((C * G * (8 * A) ^ n) * μ.real (cleanSupportCell μ R hR k z)) / v ^ 2 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hm hK) (sq_nonneg v)
    _ = _ := by unfold haarTopBallPackingConstant; ring

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Packing_FiniteAnnularCarleson
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite annular witness packing

Annular witnesses with bounded lattice depth give Haar mean gaps at one common
positive truncation scale. Applying top-ball Haar packing to those gaps bounds
the total mass of the selected descendant cells by the original top-cell mass.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

theorem finite_annular_witness_mass_packing {n d : ℕ} (hn : 1 ≤ n)
    (μ : Measure (Ambient d)) (C G ρ v : ℝ) (hC : 0 < C) (hG : 0 < G) (hv : 0 < v)
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
    (R₀ : ℝ) (hR₀ : 0 < R₀) (k I : ℕ) (hI : 0 < I)
    (z : (supportLatticeNets μ R₀ hR₀ k).points)
    (hcore : AdmissibleRadius μ (latticeRadius R₀ k / 8))
    (s : Finset (SupportCellDescendant μ R₀ hR₀ k z))
    (W : (i : s) → CellAnnulus μ R₀ hR₀ (k + i.val.depth) ⟨i.val.center, i.val.mem_net⟩ ρ)
    (hdepth : ∀ i : s, annularLatticeDepth R₀ (k + i.val.depth) (W i).innerRadius (W i).inner_pos ≤ I)
    (D : ℝ≥0)
    (hRiesz : ∀ ε : ℝ, 0 < ε → ∀ f : Ambient d → ℝ, MemLp f 2 μ →
      MemLp (truncated n μ ε f) 2 μ ∧
        eLpNorm (truncated n μ ε f) 2 μ ≤ (D : ℝ≥0∞) * eLpNorm f 2 μ)
    (hlarge : ∀ i : s, annularCellComparisonError n C G D + v ≤ ‖(W i).transform n‖) :
    ∑ i ∈ s, μ.real i.cell ≤
      haarTopBallPackingConstant n C G 4 v D I * μ.real (cleanSupportCell μ R₀ hR₀ k z) := by
  classical
  let S := ball (z : Ambient d) (4 * latticeRadius R₀ k)
  have hSfin : μ S < ∞ := (hg.2 z _ (by have hp := latticeRadius_pos R₀ hR₀ k; positivity)).trans_lt
    ENNReal.ofReal_lt_top
  have hchoose (i : s) := exists_annular_cell_gap hn μ C G hC hG hg hlower R₀ hR₀
    (k + i.val.depth) ⟨i.val.center, i.val.mem_net⟩
    (lattice_core_admissible_at_later_level μ R₀ hR₀ k _ (by omega) hcore)
    (W i).center (W i).center_mem (W i).center_dist (W i).innerRadius (W i).outerRadius
    (W i).inner_pos (W i).inner_le_outer (W i).outer_upper I (hdepth i)
    S measurableSet_ball hSfin ((W i).top_ball_contains i.val) D hRiesz
  choose P e he hgap using hchoose
  obtain ⟨ε, hε, hsmall⟩ := exists_positive_below_finset (Finset.univ : Finset s)
    (fun i : s => (W i).innerRadius / 2) (fun i _ => half_pos (W i).inner_pos)
  let P' : (i : SupportCellDescendant μ R₀ hR₀ k z) →
      CellHaarPair μ R₀ hR₀ (k + i.depth) ⟨i.center, i.mem_net⟩ I := fun i =>
    if hi : i ∈ s then P ⟨i, hi⟩ else CellHaarPair.refl μ R₀ hR₀ (k + i.depth) ⟨i.center, i.mem_net⟩ I
  let e' : SupportCellDescendant μ R₀ hR₀ k z → Ambient d := fun i =>
    if hi : i ∈ s then e ⟨i, hi⟩ else 0
  have he' : ∀ i ∈ s, ‖e' i‖ ≤ 1 := by
    intro i hi
    simpa only [e', dite_eq_left hi] using! he ⟨i, hi⟩
  have hgap' : ∀ i ∈ s, v ≤
      |cellMean (μ.restrict (P' i).innerCell) (fun x => inner ℝ (e' i)
          (truncated n μ ε (topCellBallIndicator μ R₀ hR₀ k z 4) x)) -
        cellMean (μ.restrict (P' i).outerCell) (fun x => inner ℝ (e' i)
          (truncated n μ ε (topCellBallIndicator μ R₀ hR₀ k z 4) x))| := by
    intro i hi
    have hb := hgap ⟨i, hi⟩ ε hε (hsmall ⟨i, hi⟩ (Finset.mem_univ _))
    have hl := hlarge ⟨i, hi⟩
    change ‖(W ⟨i, hi⟩).transform n‖ - annularCellComparisonError n C G D ≤ _ at hb
    simp only [P', e', dite_eq_left hi, topCellBallIndicator]
    change v ≤ _
    dsimp only [S] at hb
    linarith
  exact bounded_depth_haar_top_ball_packing μ C G 4 hC hG (by norm_num) hg hlower
    R₀ hR₀ k I hI z hcore P' s D hRiesz ε hε e' he' v hv hgap'

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Packing_UniformAnnularCarleson
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

theorem exists_uniform_large_annulus_carleson_constant (n d : ℕ) (hn : 1 ≤ n)
    (C G ρ v : ℝ) (D : ℝ≥0) (hC : 0 < C) (hG : 0 < G) (hρ : 0 < ρ) (hv : 0 < v) :
    ∃ K : ℝ, 0 < K ∧ ∀ μ : Measure (Ambient d),
      GlobalUpperGrowth n G μ →
      (∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
        ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r)) →
      (∀ ε : ℝ, 0 < ε → ∀ f : Ambient d → ℝ, MemLp f 2 μ →
        MemLp (truncated n μ ε f) 2 μ ∧
          eLpNorm (truncated n μ ε f) 2 μ ≤ (D : ℝ≥0∞) * eLpNorm f 2 μ) →
      ∀ (R₀ : ℝ) (hR₀ : 0 < R₀) (k : ℕ) (z : (supportLatticeNets μ R₀ hR₀ k).points),
      AdmissibleRadius μ (latticeRadius R₀ k / 8) →
      ∀ s : Finset (SupportCellDescendant μ R₀ hR₀ k z),
        (∀ i ∈ s, HasLargeCellAnnulus n μ R₀ hR₀ (k + i.depth) ⟨i.center, i.mem_net⟩
          ρ (annularCellComparisonError n C G D + v)) →
        ∑ i ∈ s, μ.real i.cell ≤ K * μ.real (cleanSupportCell μ R₀ hR₀ k z) := by
  classical
  obtain ⟨I, hI, hdepth⟩ := exists_uniform_depth_for_cell_annuli ρ hρ
  let K₀ := haarTopBallPackingConstant n C G 4 v D I
  have hK₀ : 0 ≤ K₀ := by
    have hm := haarCellMassRatio_pos n C G I hC hG
    unfold K₀ haarTopBallPackingConstant
    positivity
  refine ⟨K₀ + 1, by linarith, ?_⟩
  intro μ hg hlower hRiesz R₀ hR₀ k z hcore s hlarge
  have hchoice (i : s) : ∃ W : CellAnnulus μ R₀ hR₀ (k + i.val.depth)
      ⟨i.val.center, i.val.mem_net⟩ ρ, annularCellComparisonError n C G D + v ≤ ‖W.transform n‖ :=
    hlarge i.val i.property
  choose W hW using hchoice
  have hb := finite_annular_witness_mass_packing hn μ C G ρ v hC hG hv hg hlower
    R₀ hR₀ k I hI z hcore s W
    (fun i => hdepth d μ R₀ hR₀ (k + i.val.depth) ⟨i.val.center, i.val.mem_net⟩ (W i))
    D hRiesz hW
  exact hb.trans (mul_le_mul_of_nonneg_right (by change K₀ ≤ K₀ + 1; linarith) measureReal_nonneg)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Packing_NoFlatDescendantPacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

theorem exists_uniform_no_flat_descendant_total_mass_oai {n d : ℕ} (hn : 1 ≤ n) (hnd : n ≤ d)
    (C G A α : ℝ) (D : ℝ≥0) (hC : 0 < C) (hG : 0 < G) (hA : 1 ≤ A) (hα : 0 < α) :
    ∃ I : ℕ, 0 < I ∧ ∃ K : ℝ, 0 < K ∧ ∀ μ : Measure (Ambient d),
      GlobalUpperGrowth n G μ →
      (∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
        ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r)) →
      (∀ ε : ℝ, 0 < ε → ∀ f : Ambient d → ℝ, MemLp f 2 μ →
        MemLp (truncated n μ ε f) 2 μ ∧
          eLpNorm (truncated n μ ε f) 2 μ ≤ (D : ℝ≥0∞) * eLpNorm f 2 μ) →
      ∀ (R₀ : ℝ) (hR₀ : 0 < R₀) (k : ℕ) (z : (supportLatticeNets μ R₀ hR₀ k).points),
      AdmissibleRadius μ (latticeRadius R₀ k / 8) →
      ∑' i : NoFlatDescendant n μ R₀ hR₀ k z I A α,
        μ i.val.cell ≤ ENNReal.ofReal K * μ (cleanSupportCell μ R₀ hR₀ k z) := by
  classical
  obtain ⟨ρ, hρ, _, I, hI, hchoose⟩ := exists_uniform_flat_descendant_annular_alternative hn hnd
    C G (annularCellComparisonError n C G D + 1) A α hC hA hα
  obtain ⟨K, hK, hpack⟩ := exists_uniform_large_annulus_carleson_constant n d hn C G ρ 1 D
    hC hG hρ (by norm_num)
  refine ⟨I, hI, K, hK, ?_⟩
  intro μ hg hlower hRiesz R₀ hR₀ k z hcore
  let Bad := NoFlatDescendant n μ R₀ hR₀ k z I A α
  have hann (i : Bad) : HasLargeCellAnnulus n μ R₀ hR₀ (k + i.val.depth)
      ⟨i.val.center, i.val.mem_net⟩ ρ (annularCellComparisonError n C G D + 1) := by
    have hicore : AdmissibleRadius μ (latticeRadius R₀ (k + i.val.depth) / 8) := by
      simpa only [one_div_mul_eq_div, SupportCellDescendant.radius] using! i.val.core_admissible hcore
    exact (hchoose μ hg hlower R₀ hR₀ (k + i.val.depth)
      ⟨i.val.center, i.val.mem_net⟩ hicore).resolve_left i.property
  let emb : Bad ↪ SupportCellDescendant μ R₀ hR₀ k z := ⟨Subtype.val, Subtype.val_injective⟩
  have hbound (s : Finset Bad) : ∑ i ∈ s, μ.real i.val.cell ≤
      K * μ.real (cleanSupportCell μ R₀ hR₀ k z) := by
    have hs : ∀ i ∈ s.map emb, HasLargeCellAnnulus n μ R₀ hR₀ (k + i.depth)
        ⟨i.center, i.mem_net⟩ ρ (annularCellComparisonError n C G D + 1) := by
      intro i hi
      obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hi
      exact hann j
    have hb := hpack μ hg hlower hRiesz R₀ hR₀ k z hcore (s.map emb) hs
    simpa only [Finset.sum_map] using! hb
  have hb := measure_tsum_le_of_real_finset_bounds μ (fun i : Bad => i.val.cell)
    (K * μ.real (cleanSupportCell μ R₀ hR₀ k z))
    (fun i => (cleanSupportCell_finite_of_growth μ G hg R₀ hR₀ (k + i.val.depth)
      ⟨i.val.center, i.val.mem_net⟩).ne) hbound
  have hf := (cleanSupportCell_finite_of_growth μ G hg R₀ hR₀ k z).ne
  simpa only [ENNReal.ofReal_mul hK.le, Measure.real, ENNReal.ofReal_toReal hf] using! hb

end

end RieszRectifiability

end OAI
end

theorem solution : type_of% @OAI.RieszRectifiability.exists_uniform_no_flat_descendant_total_mass_oai := @OAI.RieszRectifiability.exists_uniform_no_flat_descendant_total_mass_oai
