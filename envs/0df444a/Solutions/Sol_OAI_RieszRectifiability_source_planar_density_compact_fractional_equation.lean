-- Prove2me | solution 1 for OAI.RieszRectifiability.source_planar_density_compact_fractional_equation
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:27:13.026876+00:00
-- url     : https://prove2.me/submissions/c317e0a4-bfd0-4945-b2b0-f3e94a5cc67b

import Mathlib
import Definitions.Def_RieszQuantitative
import Definitions.Def_OAIQ231Rr000
import Theorems.Thm_OAI_RieszRectifiability_exists_source_planar_unweighted_capped_equation

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_MeasureBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Metric
open scoped NNReal ENNReal

theorem kernel_antisymm {d : ℕ} (n : ℕ) (x y : Ambient d) :
    kernel n y x = -kernel n x y := by
  rw [kernel, kernel, norm_sub_rev, ← neg_sub x y, smul_neg]

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_EnergyIdentity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory

theorem centered_coordinate_difference (u v c : ℝ) :
    (u - c) - (v - c) = u - v := by
  ring

theorem normal_coordinate_difference {d : ℕ} (e z x y : Ambient d) :
    inner ℝ e (x - z) - inner ℝ e (y - z) = inner ℝ e (x - y) := by
  simp only [inner_sub_right]
  ring

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
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_FarHeightTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal

theorem lipschitz_height_radial_bound {d : ℕ} (w : Ambient d → ℝ)
    (K : ℝ≥0) (hw : LipschitzWith K w) (a y : Ambient d) (R : ℝ)
    (hR : 0 < R) (hy : R ≤ dist a y) :
    |w y| ≤ ((K : ℝ) + |w a| / R) * dist a y := by
  have hdiff : |w y - w a| ≤ (K : ℝ) * dist a y := by
    simpa only [Real.dist_eq, dist_comm y a] using! hw.dist_le_mul y a
  have hconstant : |w a| ≤ (|w a| / R) * dist a y := by
    have h := mul_le_mul_of_nonneg_left hy (div_nonneg (abs_nonneg (w a)) hR.le)
    simpa only [div_mul_cancel₀ _ hR.ne'] using! h
  calc
    _ ≤ |w y - w a| + |w a| := by
      simpa only [sub_add_cancel] using! abs_add_le (w y - w a) (w a)
    _ ≤ (K : ℝ) * dist a y + (|w a| / R) * dist a y := add_le_add hdiff hconstant
    _ = _ := by ring

theorem cancelled_height_far_bound {d : ℕ} (m : ℕ)
    (w : Ambient d → ℝ) (K : ℝ≥0) (hw : LipschitzWith K w)
    (a x y : Ambient d) (R : ℝ) (hR : 0 < R)
    (hx : 2 * dist x a ≤ R) (hy : R ≤ dist a y) :
    |w y * (inverseDistancePow (m + 1) x y - inverseDistancePow (m + 1) a y)| ≤
      (((K : ℝ) + |w a| / R) * (m + 1 : ℝ) * 2 ^ (m + 2) * dist x a) *
        inverseDistancePow (m + 1) a y := by
  have hpos : 0 < dist a y := lt_of_lt_of_le hR hy
  have hdiff := inverseDistancePow_far_difference m a x y hpos (hx.trans hy)
  rw [abs_mul]
  calc
    _ ≤ (((K : ℝ) + |w a| / R) * dist a y) *
        ((m + 1 : ℝ) * 2 ^ (m + 2) * dist x a * inverseDistancePow (m + 2) a y) :=
      mul_le_mul (lipschitz_height_radial_bound w K hw a y R hR hy) hdiff (abs_nonneg _)
        (by positivity)
    _ = _ := by
      unfold inverseDistancePow
      rw [show m + 2 = (m + 1) + 1 by omega, pow_succ]
      field_simp
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
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_RieszPairingIdentification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Scalar Riesz pairings and affine normal heights

Pairing the Riesz kernel with a fixed normal identifies its interior contribution
with the fractional bilinear form. For mean-zero tests, the exterior correction
integrates to zero, identifying the scalar Riesz pairing with the normal cutoff pairing.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function
open scoped NNReal

theorem affineNormalHeight_difference {d : ℕ} (e z : Ambient d) (b : ℝ) (x y : Ambient d) :
    affineNormalHeight e z b x - affineNormalHeight e z b y = inner ℝ e (x - y) := by
  rw [affineNormalHeight, affineNormalHeight, centered_coordinate_difference]
  exact normal_coordinate_difference e z x y

theorem affineNormalHeight_lipschitz {d : ℕ} (e z : Ambient d) (b : ℝ) :
    LipschitzWith ‖e‖₊ (affineNormalHeight e z b) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq, affineNormalHeight_difference]
  simpa only [Real.norm_eq_abs, coe_nnnorm, dist_eq_norm] using!
    norm_inner_le_norm (𝕜 := ℝ) e (x - y)

theorem kernel_inner_normal_difference {d : ℕ} (m : ℕ) (e : Ambient d)
    (w : Ambient d → ℝ) (hw : ∀ x y, w x - w y = inner ℝ e (x - y)) (x y : Ambient d) :
    inner ℝ e (kernel m x y) = (w x - w y) * inverseDistancePow (m + 1) x y := by
  rw [kernel, real_inner_smul_right, ← hw x y, ← dist_eq_norm]
  unfold inverseDistancePow
  ring

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_CappedRieszInterior
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function
open scoped NNReal

theorem distance_mul_cappedInverseDistancePow_bound {X : Type*} [PseudoMetricSpace X]
    (m : ℕ) (ε : ℝ) (hε : 0 < ε) (q : X × X) :
    dist q.1 q.2 * cappedInverseDistancePow (m + 1) ε q ≤ (ε ^ m)⁻¹ := by
  have hmax : 0 < max ε (dist q.1 q.2) := hε.trans_le (le_max_left _ _)
  calc
    _ ≤ max ε (dist q.1 q.2) * cappedInverseDistancePow (m + 1) ε q :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (cappedInverseDistancePow_nonneg _ _ _)
    _ = ((max ε (dist q.1 q.2)) ^ m)⁻¹ := by
      unfold cappedInverseDistancePow
      rw [pow_succ]
      field_simp
    _ ≤ _ := inv_anti₀ (pow_pos hε m) (pow_le_pow_left₀ hε.le (le_max_left _ _) m)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_CappedRieszKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Capped Riesz kernels

Capping the radial singularity gives a continuous bounded vector kernel agreeing
with the Riesz kernel away from the cap. The scalar difference from hard truncation
is controlled by a symmetric weight supported on close pairs.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function

theorem cappedRieszKernel_norm_bound {d : ℕ} (m : ℕ) (ε : ℝ) (hε : 0 < ε)
    (q : Ambient d × Ambient d) : ‖cappedRieszKernel m ε q‖ ≤ (ε ^ m)⁻¹ := by
  rw [cappedRieszKernel, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (cappedInverseDistancePow_nonneg _ _ _), ← dist_eq_norm, mul_comm]
  exact distance_mul_cappedInverseDistancePow_bound m ε hε q

theorem scalarCappedRieszKernel_continuous {d : ℕ} (m : ℕ) (e : Ambient d)
    (ε : ℝ) (hε : 0 < ε) : Continuous (scalarCappedRieszKernel m e ε) :=
  continuous_const.inner (cappedRieszKernel_continuous m ε hε)

theorem scalarCappedRieszKernel_bound {d : ℕ} (m : ℕ) (e : Ambient d)
    (ε : ℝ) (hε : 0 < ε) (q : Ambient d × Ambient d) :
    |scalarCappedRieszKernel m e ε q| ≤ ‖e‖ * (ε ^ m)⁻¹ := by
  have hi : |inner ℝ e (cappedRieszKernel m ε q)| ≤ ‖e‖ * ‖cappedRieszKernel m ε q‖ := by
    simpa only [Real.norm_eq_abs] using! norm_inner_le_norm (𝕜 := ℝ) e (cappedRieszKernel m ε q)
  exact hi.trans (mul_le_mul_of_nonneg_left (cappedRieszKernel_norm_bound m ε hε q) (norm_nonneg e))

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_CappedTransform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Filter
open scoped BoundedContinuousFunction

theorem scalarCappedTransform_integrable_and_bound {d : ℕ} (m : ℕ)
    (μ : Measure (Ambient d)) (e : Ambient d) (ε : ℝ) (hε : 0 < ε)
    (f : Ambient d → ℝ) (hfm : Measurable f) (hf : Integrable f μ) (x : Ambient d) :
    Integrable (fun y => f y * scalarCappedRieszKernel m e ε (x, y)) μ ∧
      |scalarCappedTransform m μ e ε f x| ≤ (∫ y, |f y| ∂μ) * (‖e‖ * (ε ^ m)⁻¹) := by
  have hm : Measurable (fun y => f y * scalarCappedRieszKernel m e ε (x, y)) :=
    hfm.mul ((scalarCappedRieszKernel_continuous m e ε hε).comp
      (continuous_const.prodMk continuous_id)).measurable
  have hb (y : Ambient d) : |f y * scalarCappedRieszKernel m e ε (x, y)| ≤
      |f y| * (‖e‖ * (ε ^ m)⁻¹) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (scalarCappedRieszKernel_bound m e ε hε (x, y)) (abs_nonneg _)
  have hI : Integrable (fun y => f y * scalarCappedRieszKernel m e ε (x, y)) μ := by
    apply (hf.abs.mul_const (‖e‖ * (ε ^ m)⁻¹)).mono' hm.aestronglyMeasurable
    exact Eventually.of_forall fun y => by simpa only [Real.norm_eq_abs] using! hb y
  refine ⟨hI, ?_⟩
  calc
    _ ≤ ∫ y, |f y * scalarCappedRieszKernel m e ε (x, y)| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ y, |f y| * (‖e‖ * (ε ^ m)⁻¹) ∂μ :=
      integral_mono hI.abs (hf.abs.mul_const (‖e‖ * (ε ^ m)⁻¹)) hb
    _ = _ := integral_mul_const _ _

theorem scalarCappedTransform_continuous {d : ℕ} (m : ℕ)
    (μ : Measure (Ambient d)) (e : Ambient d) (ε : ℝ) (hε : 0 < ε)
    (f : Ambient d → ℝ) (hfm : Measurable f) (hf : Integrable f μ) :
    Continuous (scalarCappedTransform m μ e ε f) := by
  apply continuous_of_dominated (bound := fun y => |f y| * (‖e‖ * (ε ^ m)⁻¹))
  · intro x
    exact (scalarCappedTransform_integrable_and_bound m μ e ε hε f hfm hf x).1.aestronglyMeasurable
  · intro x
    apply Eventually.of_forall
    intro y
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (scalarCappedRieszKernel_bound m e ε hε (x, y)) (abs_nonneg _)
  · exact hf.abs.mul_const _
  · exact Eventually.of_forall fun y => continuous_const.mul
      ((scalarCappedRieszKernel_continuous m e ε hε).comp (continuous_id.prodMk continuous_const))

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_CappedPairingSymmetrization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Function

theorem scalarCappedRieszKernel_swap {d : ℕ} (m : ℕ) (e : Ambient d) (ε : ℝ)
    (q : Ambient d × Ambient d) :
    scalarCappedRieszKernel m e ε q.swap = -scalarCappedRieszKernel m e ε q := by
  have hcap : cappedInverseDistancePow (m + 1) ε q.swap = cappedInverseDistancePow (m + 1) ε q := by
    simp only [cappedInverseDistancePow, Prod.fst_swap, Prod.snd_swap, dist_comm q.2 q.1]
  unfold scalarCappedRieszKernel cappedRieszKernel
  rw [hcap]
  simp only [Prod.fst_swap, Prod.snd_swap]
  rw [← neg_sub q.1 q.2, smul_neg, inner_neg_right]

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_CappedTransformAdjoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Filter

theorem bounded_kernel_two_measures_bilinear_integrable {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) [SFinite μ] [SFinite ν] (k : X × X → ℝ) (hk : Measurable k)
    (B : ℝ) (hB : ∀ q, |k q| ≤ B)
    (f g : X → ℝ) (hfm : Measurable f) (hgm : Measurable g)
    (hf : Integrable f μ) (hg : Integrable g ν) :
    Integrable (fun q : X × X => f q.1 * g q.2 * k q) (μ.prod ν) := by
  apply ((hf.abs.mul_prod hg.abs).mul_const B).mono'
    (((hfm.comp measurable_fst).mul (hgm.comp measurable_snd)).mul hk).aestronglyMeasurable
  exact Eventually.of_forall fun q => by
    simp only [Pi.mul_apply, Function.comp_apply, Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (hB q) (mul_nonneg (abs_nonneg _) (abs_nonneg _))

theorem scalarCappedTransform_adjoint {d : ℕ} (m : ℕ)
    (μ ν : Measure (Ambient d)) [SFinite μ] [SFinite ν]
    (e : Ambient d) (ε : ℝ) (hε : 0 < ε)
    (f g : Ambient d → ℝ) (hfm : Measurable f) (hgm : Measurable g)
    (hf : Integrable f ν) (hg : Integrable g μ) :
    Integrable (fun x => scalarCappedTransform m ν e ε f x * g x) μ ∧
      Integrable (fun y => f y * scalarCappedTransform m μ e ε g y) ν ∧
      (∫ x, scalarCappedTransform m ν e ε f x * g x ∂μ) =
        -(∫ y, f y * scalarCappedTransform m μ e ε g y ∂ν) := by
  let F : Ambient d × Ambient d → ℝ := fun q => g q.1 * f q.2 * scalarCappedRieszKernel m e ε q
  have hF : Integrable F (μ.prod ν) := bounded_kernel_two_measures_bilinear_integrable μ ν
    (scalarCappedRieszKernel m e ε) (scalarCappedRieszKernel_continuous m e ε hε).measurable
    (‖e‖ * (ε ^ m)⁻¹) (scalarCappedRieszKernel_bound m e ε hε) g f hgm hfm hg hf
  have hleft (x : Ambient d) : (∫ y, F (x, y) ∂ν) =
      scalarCappedTransform m ν e ε f x * g x := by
    calc
      _ = g x * ∫ y, f y * scalarCappedRieszKernel m e ε (x, y) ∂ν := by
        simp only [F, mul_assoc, integral_const_mul]
      _ = _ := by rw [scalarCappedTransform]; ring
  have hright (y : Ambient d) : (∫ x, F (x, y) ∂μ) =
      -(f y * scalarCappedTransform m μ e ε g y) := by
    calc
      _ = ∫ x, -(f y * (g x * scalarCappedRieszKernel m e ε (y, x))) ∂μ := by
        apply integral_congr_ae
        apply Eventually.of_forall
        intro x
        dsimp only [F]
        have hs : scalarCappedRieszKernel m e ε (x, y) =
            -scalarCappedRieszKernel m e ε (y, x) :=
          scalarCappedRieszKernel_swap m e ε (y, x)
        rw [hs]
        ring
      _ = _ := by rw [integral_neg, integral_const_mul]; rfl
  have hLI : Integrable (fun x => scalarCappedTransform m ν e ε f x * g x) μ :=
    hF.integral_prod_left.congr (Eventually.of_forall hleft)
  have hRIneg : Integrable (fun y => -(f y * scalarCappedTransform m μ e ε g y)) ν :=
    hF.integral_prod_right.congr (Eventually.of_forall hright)
  have hRI : Integrable (fun y => f y * scalarCappedTransform m μ e ε g y) ν := by
    have hd : Integrable (fun y => -(-(f y * scalarCappedTransform m μ e ε g y))) ν := hRIneg.neg
    simpa only [neg_neg] using! hd
  refine ⟨hLI, hRI, ?_⟩
  calc
    _ = ∫ q, F q ∂μ.prod ν :=
      ((integral_prod F hF).trans (integral_congr_ae (Eventually.of_forall hleft))).symm
    _ = ∫ y, -(f y * scalarCappedTransform m μ e ε g y) ∂ν :=
      (integral_prod_symm F hF).trans (integral_congr_ae (Eventually.of_forall hright))
    _ = _ := integral_neg _

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_FarRieszTransform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The scalar far Riesz transform

Subtracting the kernel at the localization center gives an integrable far-field
kernel under global upper growth. Quantitative decay bounds yield measurability
and local `L²` control of its scalar integral on the inner ball.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter
open scoped NNReal

theorem scalar_far_kernel_bound {d : ℕ} (m : ℕ) (e a x y : Ambient d)
    (R : ℝ) (hR : 0 < R) (hx : 2 * dist x a ≤ R) (hy : R ≤ dist a y) :
    |inner ℝ e (kernel m x y - kernel m a y)| ≤
      ((2 ^ (m + 1) + (m + 1 : ℝ) * 2 ^ (m + 2)) * (‖e‖ * dist x a)) *
        inverseDistancePow (m + 1) a y := by
  let w := affineNormalHeight e a 0
  have hw : LipschitzWith ‖e‖₊ w := affineNormalHeight_lipschitz e a 0
  have hwa : w a = 0 := by simp only [w, affineNormalHeight, sub_self, inner_zero_right]
  have hwx : |w x| ≤ ‖e‖ * dist x a := by
    simpa only [Real.dist_eq, hwa, sub_zero, coe_nnnorm] using! hw.dist_le_mul x a
  have hcancel := cancelled_height_far_bound m w ‖e‖₊ hw a x y R hR hx hy
  simp only [hwa, abs_zero, zero_div, add_zero, coe_nnnorm] at hcancel
  have hk := inverseDistancePow_far_le (m + 1) a x y (hR.trans_le hy) (hx.trans hy)
  have heq : inner ℝ e (kernel m x y - kernel m a y) =
      w x * inverseDistancePow (m + 1) x y -
        w y * (inverseDistancePow (m + 1) x y - inverseDistancePow (m + 1) a y) := by
    rw [inner_sub_right, kernel_inner_normal_difference m e w (affineNormalHeight_difference e a 0),
      kernel_inner_normal_difference m e w (affineNormalHeight_difference e a 0), hwa]
    ring
  rw [heq]
  calc
    _ ≤ |w x * inverseDistancePow (m + 1) x y| +
        |w y * (inverseDistancePow (m + 1) x y - inverseDistancePow (m + 1) a y)| := by
      simpa only [sub_zero, zero_sub, abs_neg] using!
        abs_sub_le (w x * inverseDistancePow (m + 1) x y) 0
          (w y * (inverseDistancePow (m + 1) x y - inverseDistancePow (m + 1) a y))
    _ ≤ (‖e‖ * dist x a) * (2 ^ (m + 1) * inverseDistancePow (m + 1) a y) +
        (‖e‖ * (m + 1 : ℝ) * 2 ^ (m + 2) * dist x a) * inverseDistancePow (m + 1) a y := by
      apply add_le_add _ hcancel
      rw [abs_mul, abs_of_nonneg (inverseDistancePow_nonneg _ _ _)]
      exact mul_le_mul hwx hk (inverseDistancePow_nonneg _ _ _) (by positivity)
    _ = _ := by ring

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_CappedMeanZeroTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Filter Set

theorem scalarCappedRieszKernel_far_center_difference {d : ℕ} (m : ℕ)
    (e a x y : Ambient d) (H ε : ℝ) (hH : 0 < H) (hεH : ε ≤ H)
    (hy : dist y a ≤ H) (hx : 2 * H ≤ dist a x) :
    |scalarCappedRieszKernel m e ε (x, y) - scalarCappedRieszKernel m e ε (x, a)| ≤
      ((2 ^ (m + 1) + (m + 1 : ℝ) * 2 ^ (m + 2)) * (‖e‖ * H)) *
        inverseDistancePow (m + 1) a x := by
  have hxy : ε ≤ dist x y := by
    have ht := dist_triangle a y x
    rw [dist_comm a y, dist_comm y x] at ht
    linarith
  have hxa : ε ≤ dist x a := by rw [dist_comm x a]; linarith
  have heq : scalarCappedRieszKernel m e ε (x, y) - scalarCappedRieszKernel m e ε (x, a) =
      -inner ℝ e (kernel m y x - kernel m a x) := by
    rw [scalarCappedRieszKernel, scalarCappedRieszKernel,
      cappedRieszKernel_eq_kernel m ε (x, y) hxy,
      cappedRieszKernel_eq_kernel m ε (x, a) hxa,
      kernel_antisymm m y x, kernel_antisymm m a x]
    simp only [inner_neg_right, inner_sub_right]
    ring
  rw [heq, abs_neg]
  apply (scalar_far_kernel_bound m e a y x (2 * H) (by linarith) (by linarith) hx).trans
  apply mul_le_mul_of_nonneg_right _ (inverseDistancePow_nonneg _ _ _)
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hy (norm_nonneg _)) (by positivity)

theorem scalarCappedTransform_mean_zero_tail {d : ℕ} (m : ℕ)
    (μ : Measure (Ambient d)) (e a : Ambient d) (H ε : ℝ)
    (hH : 0 < H) (hε : 0 < ε) (hεH : ε ≤ H)
    (g : Ambient d → ℝ) (hgm : Measurable g) (hg : Integrable g μ)
    (hmean : (∫ y, g y ∂μ) = 0) (hgs : ∀ y, g y ≠ 0 → dist y a ≤ H)
    (x : Ambient d) (hx : 2 * H ≤ dist a x) :
    |scalarCappedTransform m μ e ε g x| ≤
      ((∫ y, |g y| ∂μ) *
        ((2 ^ (m + 1) + (m + 1 : ℝ) * 2 ^ (m + 2)) * (‖e‖ * H))) *
          inverseDistancePow (m + 1) a x := by
  let c := scalarCappedRieszKernel m e ε (x, a)
  let F : Ambient d → ℝ := fun y => g y * (scalarCappedRieszKernel m e ε (x, y) - c)
  let B := ((2 ^ (m + 1) + (m + 1 : ℝ) * 2 ^ (m + 2)) * (‖e‖ * H)) *
    inverseDistancePow (m + 1) a x
  have hcap := (scalarCappedTransform_integrable_and_bound m μ e ε hε g hgm hg x).1
  have hF : Integrable F μ := by
    have heq : F = fun y => g y * scalarCappedRieszKernel m e ε (x, y) - g y * c := by
      funext y
      dsimp only [F]
      ring
    rw [heq]
    exact hcap.sub (hg.mul_const c)
  have hId : (∫ y, F y ∂μ) = scalarCappedTransform m μ e ε g x := by
    simp only [F, mul_sub]
    rw [integral_sub hcap (hg.mul_const c), integral_mul_const, hmean, zero_mul, sub_zero]
    rfl
  have hb (y : Ambient d) : |F y| ≤ |g y| * B := by
    by_cases hy : g y = 0
    · simp only [F, hy, zero_mul, abs_zero, le_refl]
    · dsimp only [F, B, c]
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left
        (scalarCappedRieszKernel_far_center_difference m e a x y H ε hH hεH (hgs y hy) hx)
        (abs_nonneg _)
  rw [← hId]
  calc
    _ ≤ ∫ y, |F y| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ y, |g y| * B ∂μ := integral_mono hF.abs (hg.abs.mul_const B) hb
    _ = _ := by rw [integral_mul_const]; dsimp only [B] <;> ring

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_RieszExteriorAdjoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Renormalized exterior adjoints

Mean-zero cancellation removes the constant kernel term from the capped
transform. The far-kernel difference is integrable against bounded densities
and integrable compactly supported tests, so Fubini and kernel antisymmetry give
the exterior adjoint identity with its minus sign.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Filter Set

theorem mean_zero_centered_capped_integral {d : ℕ} (m : ℕ)
    (ν : Measure (Ambient d)) (e : Ambient d) (ε : ℝ) (hε : 0 < ε)
    (g : Ambient d → ℝ) (hgm : Measurable g) (hg : Integrable g ν)
    (hmean : (∫ x, g x ∂ν) = 0) (y : Ambient d) (c : ℝ) :
    (∫ x, g x * (scalarCappedRieszKernel m e ε (y, x) - c) ∂ν) =
      scalarCappedTransform m ν e ε g y := by
  have hi := (scalarCappedTransform_integrable_and_bound m ν e ε hε g hgm hg y).1
  simp only [mul_sub]
  rw [integral_sub hi (hg.mul_const c), integral_mul_const, hmean, zero_mul, sub_zero]
  rfl

theorem density_renormalized_cross_product_integrable {d : ℕ} (m : ℕ) (C : ℝ)
    (μ ν : Measure (Ambient d)) [SFinite μ] [SFinite ν] (hμ : GlobalUpperGrowth m C μ)
    (e a : Ambient d) (H R : ℝ) (hH : 0 < H) (hR : 0 < R) (hHR : 2 * H ≤ R)
    (f g : Ambient d → ℝ) (hfm : Measurable f) (hgm : Measurable g)
    (M : ℝ) (hfb : ∀ y, |f y| ≤ M) (hg : Integrable g ν)
    (hgs : ∀ x, g x ≠ 0 → dist x a ≤ H) :
    Integrable (fun q : Ambient d × Ambient d =>
      f q.2 * g q.1 * inner ℝ e (kernel m q.1 q.2 - kernel m a q.2))
      (ν.prod (μ.restrict (closedExterior a R))) := by
  let E := closedExterior a R
  let A := (2 ^ (m + 1) + (m + 1 : ℝ) * 2 ^ (m + 2)) * (‖e‖ * H)
  have hA : 0 ≤ A := by dsimp only [A] <;> positivity
  have hM : 0 ≤ M := (abs_nonneg (f 0)).trans (hfb 0)
  have hk := (inverseDistancePow_closedExterior_integrable_and_bound m C μ hμ a R hR).1
  have hmeas : Measurable (fun q : Ambient d × Ambient d =>
      f q.2 * g q.1 * inner ℝ e (kernel m q.1 q.2 - kernel m a q.2)) := by
    let : ContinuousSMul ℝ (Ambient d) := IsBoundedSMul.continuousSMul
    unfold kernel
    fun_prop
  apply ((hg.abs.mul_prod hk).const_mul (M * A)).mono' hmeas.aestronglyMeasurable
  have hE : MeasurableSet E := closedExterior_measurable a R
  have hmem : ∀ᵐ q ∂ν.prod (μ.restrict E), q.2 ∈ E :=
    (Measure.ae_prod_iff_ae_ae (hE.preimage measurable_snd)).mpr
      (Eventually.of_forall fun _ => ae_restrict_mem hE)
  filter_upwards [hmem] with q hq
  by_cases hx : g q.1 = 0
  · simp only [hx, mul_zero, zero_mul, norm_zero, abs_zero, le_refl]
  have hinner : |inner ℝ e (kernel m q.1 q.2 - kernel m a q.2)| ≤
      A * inverseDistancePow (m + 1) a q.2 := by
    apply (scalar_far_kernel_bound m e a q.1 q.2 R hR
      ((mul_le_mul_of_nonneg_left (hgs q.1 hx) (by norm_num)).trans hHR) hq).trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hgs q.1 hx) (norm_nonneg _))
        (by positivity)) (inverseDistancePow_nonneg _ _ _)
  rw [Real.norm_eq_abs, abs_mul, abs_mul]
  calc
    _ ≤ (M * |g q.1|) * (A * inverseDistancePow (m + 1) a q.2) :=
      mul_le_mul (mul_le_mul_of_nonneg_right (hfb q.2) (abs_nonneg _)) hinner
        (abs_nonneg _) (mul_nonneg hM (abs_nonneg _))
    _ = _ := by ring

theorem density_renormalized_exterior_adjoint {d : ℕ} (m : ℕ) (C : ℝ)
    (μ ν : Measure (Ambient d)) [SFinite μ] [SFinite ν] (hμ : GlobalUpperGrowth m C μ)
    (e a : Ambient d) (H R ε : ℝ) (hH : 0 < H) (hR : 0 < R) (hHR : 2 * H ≤ R)
    (hε : 0 < ε) (hεH : ε ≤ H)
    (f g : Ambient d → ℝ) (hfm : Measurable f) (hgm : Measurable g)
    (M : ℝ) (hfb : ∀ y, |f y| ≤ M) (hg : Integrable g ν)
    (hmean : (∫ x, g x ∂ν) = 0) (hgs : ∀ x, g x ≠ 0 → dist x a ≤ H) :
    Integrable (fun x => (∫ y in closedExterior a R,
      f y * inner ℝ e (kernel m x y - kernel m a y) ∂μ) * g x) ν ∧
      IntegrableOn (fun y => f y * scalarCappedTransform m ν e ε g y) (closedExterior a R) μ ∧
      (∫ x, (∫ y in closedExterior a R,
        f y * inner ℝ e (kernel m x y - kernel m a y) ∂μ) * g x ∂ν) =
        -(∫ y in closedExterior a R, f y * scalarCappedTransform m ν e ε g y ∂μ) := by
  let E := closedExterior a R
  let F : Ambient d × Ambient d → ℝ := fun q =>
    f q.2 * g q.1 * inner ℝ e (kernel m q.1 q.2 - kernel m a q.2)
  have hF : Integrable F (ν.prod (μ.restrict E)) :=
    density_renormalized_cross_product_integrable m C μ ν hμ e a H R hH hR hHR f g hfm hgm M hfb hg hgs
  have hleft (x : Ambient d) : (∫ y in E, F (x, y) ∂μ) =
      (∫ y in E, f y * inner ℝ e (kernel m x y - kernel m a y) ∂μ) * g x := by
    calc
      _ = ∫ y in E, (f y * inner ℝ e (kernel m x y - kernel m a y)) * g x ∂μ := by
        apply integral_congr_ae
        exact Eventually.of_forall fun y => by dsimp only [F] <;> ring
      _ = _ := integral_mul_const _ _
  have hright : (fun y => ∫ x, F (x, y) ∂ν) =ᵐ[μ.restrict E]
      (fun y => -(f y * scalarCappedTransform m ν e ε g y)) := by
    filter_upwards [ae_restrict_mem (closedExterior_measurable a R)] with y hy
    have hya : ε ≤ dist y a := by
      have hy' : R ≤ dist a y := hy
      rw [dist_comm y a]
      linarith
    calc
      _ = ∫ x, -(f y * (g x * (scalarCappedRieszKernel m e ε (y, x) -
          scalarCappedRieszKernel m e ε (y, a)))) ∂ν := by
        apply integral_congr_ae
        apply Eventually.of_forall
        intro x
        dsimp only [F]
        by_cases hx : g x = 0
        · simp only [hx, mul_zero, zero_mul, neg_zero]
        have hyx : ε ≤ dist y x := by
          have ht := dist_triangle a x y
          rw [dist_comm a x, dist_comm x y] at ht
          have hxH := hgs x hx
          have hyR : R ≤ dist a y := hy
          linarith
        rw [scalarCappedRieszKernel, scalarCappedRieszKernel,
          cappedRieszKernel_eq_kernel m ε (y, x) hyx,
          cappedRieszKernel_eq_kernel m ε (y, a) hya,
          kernel_antisymm m x y, kernel_antisymm m a y]
        simp only [inner_neg_right, inner_sub_right]
        ring
      _ = -(f y * scalarCappedTransform m ν e ε g y) := by
        rw [integral_neg, integral_const_mul,
          mean_zero_centered_capped_integral m ν e ε hε g hgm hg hmean]
  have hLI := hF.integral_prod_left.congr (Eventually.of_forall hleft)
  have hRIneg := hF.integral_prod_right.congr hright
  have hRI : IntegrableOn (fun y => f y * scalarCappedTransform m ν e ε g y) E μ := by
    have hd : IntegrableOn (fun y => -(-(f y * scalarCappedTransform m ν e ε g y))) E μ := hRIneg.neg
    simpa only [neg_neg] using! hd
  refine ⟨hLI, hRI, ?_⟩
  calc
    _ = ∫ q, F q ∂ν.prod (μ.restrict E) :=
      ((integral_prod F hF).trans (integral_congr_ae (Eventually.of_forall hleft))).symm
    _ = ∫ y in E, -(f y * scalarCappedTransform m ν e ε g y) ∂μ :=
      (integral_prod_symm F hF).trans (integral_congr_ae hright)
    _ = _ := integral_neg _

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_CappedDensityPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Local and exterior capped density pairings

The ball and its closed exterior partition the global density pairing. Local
and renormalized exterior adjoint identities combine to prove integrability
and identify their sum with the negative global capped-transform pairing.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Filter Set

theorem local_plus_exterior_capped_density_pairing {d : ℕ} (m : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) [SFinite μ] (hμ : GlobalUpperGrowth m C μ)
    (e a : Ambient d) (H R ε : ℝ) (hH : 0 < H) (hR : 0 < R) (hHR : 2 * H ≤ R)
    (hε : 0 < ε) (hεH : ε ≤ H)
    (f g : Ambient d → ℝ) (hfm : Measurable f) (hgm : Measurable g)
    (M : ℝ) (hfb : ∀ y, |f y| ≤ M) (hg : Integrable g μ)
    (hmean : (∫ x, g x ∂μ) = 0) (hgs : ∀ x, g x ≠ 0 → dist x a ≤ H) :
    Integrable (fun y => f y * scalarCappedTransform m μ e ε g y) μ ∧
      ((∫ x, scalarCappedTransform m (μ.restrict (ball a R)) e ε f x * g x ∂μ) +
        ∫ x, (∫ y in closedExterior a R,
          f y * inner ℝ e (kernel m x y - kernel m a y) ∂μ) * g x ∂μ) =
        -(∫ y, f y * scalarCappedTransform m μ e ε g y ∂μ) := by
  have hfinite : μ (ball a R) ≠ ⊤ :=
    ne_of_lt ((hμ.2 a R hR).trans_lt ENNReal.ofReal_lt_top)
  have hfI : IntegrableOn f (ball a R) μ := by
    apply (integrableOn_const (C := M) hfinite).mono' hfm.aestronglyMeasurable.restrict
    exact Eventually.of_forall fun y => by simpa only [Real.norm_eq_abs] using! hfb y
  obtain ⟨_, hinside, hlocal⟩ := scalarCappedTransform_adjoint m μ (μ.restrict (ball a R))
    e ε hε f g hfm hgm hfI hg
  obtain ⟨_, houtside, hfar⟩ := density_renormalized_exterior_adjoint m C μ μ hμ e a H R ε
    hH hR hHR hε hεH f g hfm hgm M hfb hg hmean hgs
  have hcomp : (ball a R)ᶜ = closedExterior a R := by
    ext y
    simp only [mem_compl_iff, mem_ball, closedExterior, mem_ofPred_eq, not_lt, dist_comm y a]
  have hI : Integrable (fun y => f y * scalarCappedTransform m μ e ε g y) μ := by
    have hinside' : IntegrableOn (fun y => f y * scalarCappedTransform m μ e ε g y) (ball a R) μ := hinside
    have hu := hinside'.union houtside
    rw [← hcomp, union_compl_self] at hu
    exact integrableOn_univ.mp hu
  refine ⟨hI, ?_⟩
  rw [hlocal, hfar, ← integral_add_compl measurableSet_ball hI, hcomp]
  ring

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_CappedTestSymmetry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Filter Set

theorem scalarCappedRieszKernel_add {d : ℕ} (m : ℕ) (e : Ambient d)
    (ε : ℝ) (x h : Ambient d) :
    scalarCappedRieszKernel m e ε (x, x + h) =
      -(cappedInverseDistancePow (m + 1) ε (0, h) * inner ℝ e h) := by
  have heq : x - (x + h) = -h := by abel
  simp only [scalarCappedRieszKernel, cappedRieszKernel, cappedInverseDistancePow,
    dist_eq_norm, heq, zero_sub, norm_neg, inner_smul_right, inner_neg_right]
  ring

theorem scalarCappedRieszKernel_sub {d : ℕ} (m : ℕ) (e : Ambient d)
    (ε : ℝ) (x h : Ambient d) :
    scalarCappedRieszKernel m e ε (x, x - h) =
      cappedInverseDistancePow (m + 1) ε (0, h) * inner ℝ e h := by
  have heq : x - (x - h) = h := by abel
  simp only [scalarCappedRieszKernel, cappedRieszKernel, cappedInverseDistancePow,
    dist_eq_norm, heq, zero_sub, norm_neg, inner_smul_right]

theorem scalarCappedTransform_symmetric_identity {d : ℕ} (m : ℕ)
    (e : Ambient d) (ε : ℝ) (hε : 0 < ε) (g : Ambient d → ℝ)
    (hgm : Measurable g) (hg : Integrable g volume) (x : Ambient d) :
    Integrable (symmetricScalarCappedTestKernel m e ε g x) volume ∧
      scalarCappedTransform m volume e ε g x =
        (-1 / 2 : ℝ) * ∫ h, symmetricScalarCappedTestKernel m e ε g x h := by
  let F : Ambient d → ℝ := fun y => g y * scalarCappedRieszKernel m e ε (x, y)
  have hF : Integrable F volume :=
    (scalarCappedTransform_integrable_and_bound m volume e ε hε g hgm hg x).1
  have heq : symmetricScalarCappedTestKernel m e ε g x =
      (fun h => -F (x + h) - F (x - h)) := by
    funext h
    dsimp only [symmetricScalarCappedTestKernel, F]
    rw [scalarCappedRieszKernel_add, scalarCappedRieszKernel_sub]
    ring
  have hp := hF.comp_add_left x
  have hm := hF.comp_sub_left x
  have hpneg : Integrable (fun h => -F (x + h)) volume := hp.neg
  have hI : Integrable (symmetricScalarCappedTestKernel m e ε g x) volume := by
    rw [heq]
    exact hp.neg.sub hm
  refine ⟨hI, ?_⟩
  rw [heq]
  dsimp only
  rw [integral_sub hpneg hm, integral_neg,
    integral_add_left_eq_self F x, integral_sub_left_eq_self F volume x]
  change (∫ y, F y) = (-1 / 2 : ℝ) * (-(∫ y, F y) - ∫ y, F y)
  ring

theorem symmetricScalarCappedTestKernel_norm_le {d : ℕ} (m : ℕ)
    (e : Ambient d) (ε : ℝ) (g : Ambient d → ℝ) (x h : Ambient d) :
    ‖symmetricScalarCappedTestKernel m e ε g x h‖ ≤
      ‖symmetricScalarRieszTestKernel m e g x h‖ := by
  by_cases hh : h = 0
  · subst h
    simp only [symmetricScalarCappedTestKernel, symmetricScalarRieszTestKernel,
      inner_zero_right, zero_mul, mul_zero, norm_zero, le_refl]
  have hn : 0 < ‖h‖ := norm_pos_iff.mpr hh
  have hc : cappedInverseDistancePow (m + 1) ε (0, h) ≤
      inverseDistancePow (m + 1) 0 h := by
    simp only [cappedInverseDistancePow, inverseDistancePow, dist_zero_left]
    exact inv_anti₀ (pow_pos hn _) (pow_le_pow_left₀ hn.le (le_max_right _ _) _)
  simp only [symmetricScalarCappedTestKernel, symmetricScalarRieszTestKernel, norm_mul,
    Real.norm_of_nonneg (cappedInverseDistancePow_nonneg _ _ _),
    Real.norm_of_nonneg (inverseDistancePow_nonneg _ _ _)]
  exact mul_le_mul_of_nonneg_right hc (mul_nonneg (norm_nonneg _) (norm_nonneg _))

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_ExteriorDilation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set
open scoped Pointwise

theorem inverseDistancePow_origin_smul {d : ℕ} (q : ℕ)
    (r : ℝ) (hr : 0 < r) (x : Ambient d) :
    inverseDistancePow q 0 (r • x) = (r ^ q)⁻¹ * inverseDistancePow q 0 x := by
  simp only [inverseDistancePow, dist_zero_left, norm_smul, Real.norm_eq_abs,
    abs_of_pos hr, mul_pow, mul_inv]

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Rigidity_FractionalTestDilation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory SchwartzMap Metric Filter Topology Set

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem dilatedFractionalKernel_scaling {d : ℕ} (m : ℕ) (g : Ambient d → F)
    (x : Ambient d) (t : ℝ) (ht : 0 < t) (h : Ambient d) :
    dilatedFractionalKernel m g x t h =
      t ^ (m + 1) • fractionalSchwartzKernel m g x (t • h) := by
  unfold dilatedFractionalKernel fractionalSchwartzKernel
  rw [inverseDistancePow_origin_smul (m + 1) t ht, smul_smul]
  rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ ht.ne'), one_mul]

theorem dilatedFractionalKernel_integral_scaling (n : ℕ) (g : Ambient n → F)
    (x : Ambient n) (t : ℝ) (ht : 0 < t) :
    (∫ h, dilatedFractionalKernel n g x t h) = t • ∫ h, fractionalSchwartzKernel n g x h := by
  have heq : dilatedFractionalKernel n g x t =
      fun h => t ^ (n + 1) • fractionalSchwartzKernel n g x (t • h) :=
    funext (dilatedFractionalKernel_scaling n g x t ht)
  rw [heq, integral_smul,
    Measure.integral_comp_smul_of_nonneg (volume : Measure (Ambient n))
      (fractionalSchwartzKernel n g x) t (hR := ht.le), smul_smul]
  congr 1
  simp only [Ambient, finrank_euclideanSpace, Fintype.card_fin, pow_succ]
  field_simp

theorem dilatedFractionalKernel_hasDerivAt {d : ℕ} (m : ℕ)
    (g : Ambient d → F) (hg : Differentiable ℝ g) (x h : Ambient d) (t : ℝ) :
    HasDerivAt (fun r => dilatedFractionalKernel m g x r h)
      (dilatedFractionalGradientKernel m g x t h) t := by
  have hp : HasDerivAt (fun r : ℝ => g (x + r • h)) (fderiv ℝ g (x + t • h) h) t := by
    simpa only [zero_add, one_smul] using!
      (hg (x + t • h)).hasFDerivAt.comp_hasDerivAt t
        ((hasDerivAt_const t x).add ((hasDerivAt_id t).smul_const h))
  have hm : HasDerivAt (fun r : ℝ => g (x - r • h)) (-fderiv ℝ g (x - t • h) h) t := by
    simpa only [zero_sub, one_smul, map_neg] using!
      (hg (x - t • h)).hasFDerivAt.comp_hasDerivAt t
        ((hasDerivAt_const t x).sub ((hasDerivAt_id t).smul_const h))
  have hdiff := ((hp.add hm).sub (hasDerivAt_const t ((2 : ℝ) • g x))).const_smul
    (inverseDistancePow (m + 1) 0 h)
  simpa only [dilatedFractionalKernel, dilatedFractionalGradientKernel,
    symmetricSecondDifference, Pi.smul_apply, Pi.sub_apply, Pi.add_apply,
    sub_zero, sub_eq_add_neg, neg_zero, add_zero] using! hdiff

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Rigidity_FractionalGradientBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Bounds for dilated fractional gradients

Lipschitz control of the derivative bounds symmetric dilated differences near the
origin. Radial Schwartz decay controls the far region, providing the two estimates
needed for fractional-gradient integrability and dilation arguments.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory SchwartzMap Metric Filter Topology Set
open scoped NNReal

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem lipschitz_fderiv_dilated_difference_bound {d : ℕ}
    (g : Ambient d → F) (L : ℝ≥0) (hL : LipschitzWith L (fderiv ℝ g))
    (x h : Ambient d) (t : ℝ) (ht : |t| ≤ 2) :
    ‖fderiv ℝ g (x + t • h) h - fderiv ℝ g (x - t • h) h‖ ≤
      4 * (L : ℝ) * ‖h‖ ^ 2 := by
  have hpoint : ‖(x + t • h) - (x - t • h)‖ ≤ 4 * ‖h‖ := by
    calc
      _ = ‖t • h + t • h‖ := by congr 1; abel
      _ ≤ ‖t • h‖ + ‖t • h‖ := norm_add_le _ _
      _ = 2 * |t| * ‖h‖ := by rw [norm_smul, Real.norm_eq_abs]; ring
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right ht (norm_nonneg h)]
  calc
    _ = ‖(fderiv ℝ g (x + t • h) - fderiv ℝ g (x - t • h)) h‖ := by
      rw [sub_apply]
    _ ≤ ‖fderiv ℝ g (x + t • h) - fderiv ℝ g (x - t • h)‖ * ‖h‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ ((L : ℝ) * (4 * ‖h‖)) * ‖h‖ :=
      mul_le_mul_of_nonneg_right ((hL.norm_sub_le _ _).trans
        (mul_le_mul_of_nonneg_left hpoint L.coe_nonneg)) (norm_nonneg _)
    _ = _ := by ring

theorem schwartz_dilated_fractional_gradient_near_bound {d : ℕ} (p : ℕ)
    (g : 𝓢(Ambient d, F)) (x h : Ambient d) (t : ℝ) (ht : |t| ≤ 2) :
    ‖dilatedFractionalGradientKernel (p + 1) g x t h‖ ≤
      (4 * SchwartzMap.seminorm ℝ 0 0
        (fderivCLM ℝ (Ambient d) (Ambient d →L[ℝ] F) (fderivCLM ℝ (Ambient d) F g))) *
          inverseDistancePow p 0 h := by
  let Dg := fderivCLM ℝ (Ambient d) F g
  let DDg := fderivCLM ℝ (Ambient d) (Ambient d →L[ℝ] F) Dg
  let L : ℝ≥0 := ⟨SchwartzMap.seminorm ℝ 0 0 DDg, apply_nonneg _ _⟩
  have hL : LipschitzWith L Dg := by
    apply lipschitzWith_of_nnnorm_fderiv_le Dg.differentiable
    intro y
    have hb : ‖fderiv ℝ Dg y‖ ≤ (L : ℝ) := DDg.norm_le_seminorm ℝ y
    exact_mod_cast hb
  have hb := lipschitz_fderiv_dilated_difference_bound g L hL x h t ht
  rw [dilatedFractionalGradientKernel, norm_smul,
    Real.norm_of_nonneg (inverseDistancePow_nonneg _ _ _)]
  by_cases hh : h = 0
  · subst h
    simp only [map_zero, sub_zero, norm_zero, mul_zero]
    exact mul_nonneg (mul_nonneg (by norm_num) (apply_nonneg _ _))
      (inverseDistancePow_nonneg _ _ _)
  have hn : ‖h‖ ≠ 0 := norm_ne_zero_iff.mpr hh
  calc
    _ ≤ inverseDistancePow (p + 1 + 1) 0 h * (4 * (L : ℝ) * ‖h‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hb (inverseDistancePow_nonneg _ _ _)
    _ = _ := by
      dsimp only [L, DDg, Dg]
      simp only [inverseDistancePow, dist_zero_left, pow_succ]
      field_simp
      rfl

theorem norm_le_twice_affine_shift {d : ℕ} (x h : Ambient d) (t : ℝ) (ht : 1 / 2 ≤ t) :
    ‖h‖ ≤ 2 * (‖x + t • h‖ + ‖x‖) := by
  have hpos : 0 < t := by linarith
  have hn := norm_sub_le (x + t • h) x
  have heq : x + t • h - x = t • h := by abel
  rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos hpos] at hn
  nlinarith [mul_le_mul_of_nonneg_right ht (norm_nonneg h)]

theorem schwartz_operator_apply_radial_bound {d : ℕ}
    (G : 𝓢(Ambient d, Ambient d →L[ℝ] F)) (x z h : Ambient d)
    (hh : ‖h‖ ≤ 2 * (‖z‖ + ‖x‖)) :
    ‖G z h‖ ≤ 2 * (SchwartzMap.seminorm ℝ 1 0 G + ‖x‖ * SchwartzMap.seminorm ℝ 0 0 G) := by
  have h0 := G.norm_le_seminorm ℝ z
  have h1 : ‖z‖ * ‖G z‖ ≤ SchwartzMap.seminorm ℝ 1 0 G := by
    simpa only [pow_one] using! G.norm_pow_mul_le_seminorm ℝ 1 z
  calc
    _ ≤ ‖G z‖ * ‖h‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖G z‖ * (2 * (‖z‖ + ‖x‖)) := mul_le_mul_of_nonneg_left hh (norm_nonneg _)
    _ = 2 * (‖z‖ * ‖G z‖ + ‖x‖ * ‖G z‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (add_le_add h1 (mul_le_mul_of_nonneg_left h0 (norm_nonneg _))) (by norm_num)

theorem schwartz_dilated_fractional_gradient_far_bound {d : ℕ} (m : ℕ)
    (g : 𝓢(Ambient d, F)) (x h : Ambient d) (t : ℝ) (ht : 1 / 2 ≤ t) :
    ‖dilatedFractionalGradientKernel m g x t h‖ ≤
      (4 * (SchwartzMap.seminorm ℝ 1 0 (fderivCLM ℝ (Ambient d) F g) +
        ‖x‖ * SchwartzMap.seminorm ℝ 0 0 (fderivCLM ℝ (Ambient d) F g))) *
          inverseDistancePow (m + 1) 0 h := by
  let Dg := fderivCLM ℝ (Ambient d) F g
  have hp := schwartz_operator_apply_radial_bound Dg x (x + t • h) h
    (norm_le_twice_affine_shift x h t ht)
  have hminus : ‖h‖ ≤ 2 * (‖x - t • h‖ + ‖x‖) := by
    simpa only [norm_neg, smul_neg, sub_eq_add_neg] using! norm_le_twice_affine_shift x (-h) t ht
  have hm := schwartz_operator_apply_radial_bound Dg x (x - t • h) h hminus
  rw [dilatedFractionalGradientKernel, norm_smul,
    Real.norm_of_nonneg (inverseDistancePow_nonneg _ _ _)]
  calc
    _ ≤ inverseDistancePow (m + 1) 0 h * (‖Dg (x + t • h) h‖ + ‖Dg (x - t • h) h‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) (inverseDistancePow_nonneg _ _ _)
    _ ≤ inverseDistancePow (m + 1) 0 h *
        (2 * (SchwartzMap.seminorm ℝ 1 0 Dg + ‖x‖ * SchwartzMap.seminorm ℝ 0 0 Dg) +
         2 * (SchwartzMap.seminorm ℝ 1 0 Dg + ‖x‖ * SchwartzMap.seminorm ℝ 0 0 Dg)) :=
      mul_le_mul_of_nonneg_left (add_le_add hp hm) (inverseDistancePow_nonneg _ _ _)
    _ = _ := by dsimp only [Dg] <;> ring

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_ScalarRieszTestBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Bounds for symmetric scalar Riesz tests

Derivative bounds control the symmetric test kernel near the origin, and Schwartz
seminorms control its far-field decay. The resulting inverse-distance majorants
establish integrability by splitting into a unit ball and its closed exterior.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory SchwartzMap Metric Filter Topology Set
open scoped NNReal

theorem symmetricScalarRieszTestKernel_near_bound {d : ℕ} (p : ℕ)
    (e : Ambient d) (g : 𝓢(Ambient d, ℝ)) (x h : Ambient d) :
    ‖symmetricScalarRieszTestKernel (p + 1) e g x h‖ ≤
      (2 * ‖e‖ * SchwartzMap.seminorm ℝ 0 0 (fderivCLM ℝ (Ambient d) ℝ g)) *
        inverseDistancePow p 0 h := by
  let Dg := fderivCLM ℝ (Ambient d) ℝ g
  let L : ℝ≥0 := ⟨SchwartzMap.seminorm ℝ 0 0 Dg, apply_nonneg _ _⟩
  have hL : LipschitzWith L g := by
    apply lipschitzWith_of_nnnorm_fderiv_le g.differentiable
    intro y
    have hb : ‖fderiv ℝ g y‖ ≤ (L : ℝ) := Dg.norm_le_seminorm ℝ y
    exact_mod_cast hb
  have hpoint : ‖(x + h) - (x - h)‖ ≤ 2 * ‖h‖ := by
    calc
      _ = ‖h + h‖ := by congr 1; abel
      _ ≤ ‖h‖ + ‖h‖ := norm_add_le _ _
      _ = _ := by ring
  have hd : |g (x + h) - g (x - h)| ≤ 2 * (L : ℝ) * ‖h‖ := by
    simpa only [Real.norm_eq_abs, mul_left_comm, mul_assoc] using!
      (hL.norm_sub_le (x + h) (x - h)).trans
        (mul_le_mul_of_nonneg_left hpoint L.coe_nonneg)
  have hi : |inner ℝ e h| ≤ ‖e‖ * ‖h‖ := by
    simpa only [Real.norm_eq_abs] using! norm_inner_le_norm (𝕜 := ℝ) e h
  by_cases hh : h = 0
  · subst h
    simp only [symmetricScalarRieszTestKernel, inner_zero_right, zero_mul, mul_zero, norm_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (norm_nonneg _))
      (apply_nonneg _ _)) (inverseDistancePow_nonneg _ _ _)
  have hn : ‖h‖ ≠ 0 := norm_ne_zero_iff.mpr hh
  rw [symmetricScalarRieszTestKernel, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (inverseDistancePow_nonneg _ _ _), abs_mul]
  calc
    _ ≤ inverseDistancePow (p + 1 + 1) 0 h *
        ((‖e‖ * ‖h‖) * (2 * (L : ℝ) * ‖h‖)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul hi hd (abs_nonneg _)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))) (inverseDistancePow_nonneg _ _ _)
    _ = _ := by
      dsimp only [L, Dg]
      simp only [inverseDistancePow, dist_zero_left, pow_succ]
      field_simp
      rfl

theorem schwartz_value_radial_bound {d : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : 𝓢(Ambient d, F)) (x z h : Ambient d)
    (hh : ‖h‖ ≤ 2 * (‖z‖ + ‖x‖)) :
    ‖h‖ * ‖g z‖ ≤ 2 * (SchwartzMap.seminorm ℝ 1 0 g +
      ‖x‖ * SchwartzMap.seminorm ℝ 0 0 g) := by
  have h0 := g.norm_le_seminorm ℝ z
  have h1 : ‖z‖ * ‖g z‖ ≤ SchwartzMap.seminorm ℝ 1 0 g := by
    simpa only [pow_one] using! g.norm_pow_mul_le_seminorm ℝ 1 z
  calc
    _ ≤ (2 * (‖z‖ + ‖x‖)) * ‖g z‖ := mul_le_mul_of_nonneg_right hh (norm_nonneg _)
    _ = 2 * (‖z‖ * ‖g z‖ + ‖x‖ * ‖g z‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (add_le_add h1 (mul_le_mul_of_nonneg_left h0 (norm_nonneg _))) (by norm_num)

theorem symmetricScalarRieszTestKernel_far_bound {d : ℕ} (m : ℕ)
    (e : Ambient d) (g : 𝓢(Ambient d, ℝ)) (x h : Ambient d) :
    ‖symmetricScalarRieszTestKernel m e g x h‖ ≤
      (4 * ‖e‖ * (SchwartzMap.seminorm ℝ 1 0 g +
        ‖x‖ * SchwartzMap.seminorm ℝ 0 0 g)) * inverseDistancePow (m + 1) 0 h := by
  have hp := schwartz_value_radial_bound g x (x + h) h
    (by simpa only [one_smul] using! norm_le_twice_affine_shift x h 1 (by norm_num))
  have hm := schwartz_value_radial_bound g x (x - h) h
    (by simpa only [one_smul, norm_neg, sub_eq_add_neg] using!
      norm_le_twice_affine_shift x (-h) 1 (by norm_num))
  have hi : |inner ℝ e h| ≤ ‖e‖ * ‖h‖ := by
    simpa only [Real.norm_eq_abs] using! norm_inner_le_norm (𝕜 := ℝ) e h
  have hd : |g (x + h) - g (x - h)| ≤ ‖g (x + h)‖ + ‖g (x - h)‖ := by
    simpa only [Real.norm_eq_abs] using! norm_sub_le (g (x + h)) (g (x - h))
  have hb : |inner ℝ e h| * |g (x + h) - g (x - h)| ≤
      4 * ‖e‖ * (SchwartzMap.seminorm ℝ 1 0 g + ‖x‖ * SchwartzMap.seminorm ℝ 0 0 g) := by
    calc
      _ ≤ (‖e‖ * ‖h‖) * (‖g (x + h)‖ + ‖g (x - h)‖) :=
        mul_le_mul hi hd (abs_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = ‖e‖ * (‖h‖ * ‖g (x + h)‖ + ‖h‖ * ‖g (x - h)‖) := by ring
      _ ≤ ‖e‖ * (2 * (SchwartzMap.seminorm ℝ 1 0 g + ‖x‖ * SchwartzMap.seminorm ℝ 0 0 g) +
          2 * (SchwartzMap.seminorm ℝ 1 0 g + ‖x‖ * SchwartzMap.seminorm ℝ 0 0 g)) :=
        mul_le_mul_of_nonneg_left (add_le_add hp hm) (norm_nonneg _)
      _ = _ := by ring
  rw [symmetricScalarRieszTestKernel, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (inverseDistancePow_nonneg _ _ _), abs_mul]
  exact (mul_le_mul_of_nonneg_left hb (inverseDistancePow_nonneg _ _ _)).trans_eq (mul_comm _ _)

theorem symmetricScalarRieszTestKernel_integrable {d : ℕ} (p : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) (hμ : GlobalUpperGrowth (p + 1) C μ)
    (e : Ambient d) (g : 𝓢(Ambient d, ℝ)) (x : Ambient d) :
    Integrable (symmetricScalarRieszTestKernel (p + 1) e g x) μ := by
  have hc : Continuous (fun h : Ambient d => inner ℝ e h * (g (x + h) - g (x - h))) := by
    fun_prop
  have hmeas : AEStronglyMeasurable (symmetricScalarRieszTestKernel (p + 1) e g x) μ :=
    (inverseDistancePow_measurable (p + 1 + 1) (0 : Ambient d)).aestronglyMeasurable.mul
      hc.aestronglyMeasurable
  have hn : IntegrableOn (symmetricScalarRieszTestKernel (p + 1) e g x) (closedBall 0 1) μ := by
    have hi := (inverseDistancePow_near_integrable_and_bound p C μ hμ 0 1 (by norm_num)).1
    apply (hi.const_mul (2 * ‖e‖ * SchwartzMap.seminorm ℝ 0 0
      (fderivCLM ℝ (Ambient d) ℝ g))).mono' hmeas.restrict
    exact Eventually.of_forall (symmetricScalarRieszTestKernel_near_bound p e g x)
  have hf : IntegrableOn (symmetricScalarRieszTestKernel (p + 1) e g x) (closedExterior 0 1) μ := by
    have hi := (inverseDistancePow_closedExterior_integrable_and_bound (p + 1) C μ hμ 0 1
      (by norm_num)).1
    apply (hi.const_mul (4 * ‖e‖ * (SchwartzMap.seminorm ℝ 1 0 g +
      ‖x‖ * SchwartzMap.seminorm ℝ 0 0 g))).mono' hmeas.restrict
    exact Eventually.of_forall (symmetricScalarRieszTestKernel_far_bound (p + 1) e g x)
  have hs : closedBall (0 : Ambient d) 1 ∪ closedExterior 0 1 = univ := by
    ext h
    simp only [mem_union, mem_closedBall, dist_zero_right, closedExterior, mem_ofPred_eq,
      dist_zero_left, mem_univ, iff_true]
    exact le_total ‖h‖ 1
  have hi := hn.union hf
  rw [hs] at hi
  exact integrableOn_univ.mp hi

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_ScalarRieszLocalBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Uniform local bounds for scalar Riesz transforms

Near and far inverse-distance kernels give an integrable majorant for symmetric
Schwartz test kernels. Its coefficients depend on Schwartz seminorms and a bound
on the base point, yielding a local bound uniform over positive truncation scales.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory SchwartzMap Metric Filter Topology Set

theorem scalarRieszLocalDominator_integrable (p : ℕ) (e : Ambient (p + 1))
    (g : 𝓢(Ambient (p + 1), ℝ)) (R : ℝ) :
    Integrable (scalarRieszLocalDominator p e g R) volume := by
  have hn := (inverseDistancePow_near_integrable_and_bound (d := p + 1) p _ volume
    (volume_global_upper_growth (p + 1)) 0 1 (by norm_num)).1
  have hf := (inverseDistancePow_closedExterior_integrable_and_bound (d := p + 1) (p + 1) _ volume
    (volume_global_upper_growth (p + 1)) 0 1 (by norm_num)).1
  exact ((hn.integrable_indicator measurableSet_closedBall).const_mul _).add
    ((hf.integrable_indicator (closedExterior_measurable 0 1)).const_mul _)

theorem symmetricScalarRieszTestKernel_le_localDominator {d : ℕ} (p : ℕ)
    (e : Ambient d) (g : 𝓢(Ambient d, ℝ)) (R : ℝ) (x h : Ambient d) (hx : ‖x‖ ≤ R) :
    ‖symmetricScalarRieszTestKernel (p + 1) e g x h‖ ≤ scalarRieszLocalDominator p e g R h := by
  have hR : 0 ≤ R := (norm_nonneg _).trans hx
  have hn : 0 ≤ (closedBall (0 : Ambient d) 1).indicator (inverseDistancePow p 0) h :=
    indicator_nonneg (fun y _ => inverseDistancePow_nonneg p 0 y) h
  have hf : 0 ≤ (closedExterior (0 : Ambient d) 1).indicator (inverseDistancePow (p + 2) 0) h :=
    indicator_nonneg (fun y _ => inverseDistancePow_nonneg (p + 2) 0 y) h
  have hnear : 0 ≤ (2 * ‖e‖ * SchwartzMap.seminorm ℝ 0 0 (fderivCLM ℝ (Ambient d) ℝ g)) *
      (closedBall (0 : Ambient d) 1).indicator (inverseDistancePow p 0) h :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (norm_nonneg _)) (apply_nonneg _ _)) hn
  by_cases hh : ‖h‖ ≤ 1
  · have hmem : h ∈ closedBall (0 : Ambient d) 1 := by
      simpa only [mem_closedBall, dist_zero_right] using! hh
    unfold scalarRieszLocalDominator
    rw [indicator_of_mem hmem]
    apply (symmetricScalarRieszTestKernel_near_bound p e g x h).trans
    apply le_add_of_nonneg_right
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (norm_nonneg _))
      (add_nonneg (apply_nonneg _ _) (mul_nonneg hR (apply_nonneg _ _)))) hf
  · have hmem : h ∈ closedExterior (0 : Ambient d) 1 := by
      simpa only [closedExterior, mem_ofPred_eq, dist_zero_left] using! (lt_of_not_ge hh).le
    unfold scalarRieszLocalDominator
    rw [indicator_of_mem hmem]
    apply (symmetricScalarRieszTestKernel_far_bound (p + 1) e g x h).trans
    apply le_trans _ (le_add_of_nonneg_left hnear)
    apply mul_le_mul_of_nonneg_right _ (inverseDistancePow_nonneg _ _ _)
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) (norm_nonneg _))
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hx
      (show 0 ≤ SchwartzMap.seminorm ℝ 0 0 g from apply_nonneg _ _))

theorem exists_uniform_local_scalarCappedTransform_bound (p : ℕ) (e : Ambient (p + 1))
    (g : 𝓢(Ambient (p + 1), ℝ)) (R : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ ε : ℝ, 0 < ε → ∀ x : Ambient (p + 1), ‖x‖ ≤ R →
      |scalarCappedTransform (p + 1) volume e ε g x| ≤ B := by
  let D := scalarRieszLocalDominator p e g R
  let B := ∫ h, ‖D h‖
  have hD : Integrable D volume := scalarRieszLocalDominator_integrable p e g R
  have hB : 0 ≤ B := integral_nonneg fun _ => norm_nonneg _
  refine ⟨B, hB, ?_⟩
  intro ε hε x hx
  obtain ⟨hI, heq⟩ := scalarCappedTransform_symmetric_identity (p + 1) e ε hε g
    g.continuous.measurable g.integrable x
  have hb : |∫ h, symmetricScalarCappedTestKernel (p + 1) e ε g x h| ≤ B := by
    calc
      _ ≤ ∫ h, ‖symmetricScalarCappedTestKernel (p + 1) e ε g x h‖ := by
        simpa only [Real.norm_eq_abs] using! norm_integral_le_integral_norm
          (μ := volume) (symmetricScalarCappedTestKernel (p + 1) e ε g x)
      _ ≤ B := by
        apply integral_mono hI.norm hD.norm
        intro h
        exact (symmetricScalarCappedTestKernel_norm_le (p + 1) e ε g x h).trans
          ((symmetricScalarRieszTestKernel_le_localDominator p e g R x h hx).trans (le_abs_self _))
  rw [heq, abs_mul]
  norm_num
  nlinarith

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_ScalarRieszSpatialDomination
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Spatial domination of scalar capped transforms

A uniform local bound and the mean-zero tail estimate combine into a measurable,
nonnegative majorant for compactly supported Schwartz tests. Global upper growth
makes this majorant integrable against the ambient measure, uniformly in the
positive truncation scales bounded by the support radius.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory SchwartzMap Metric Filter Topology Set

theorem exists_integrable_scalarCappedTransform_dominator (p : ℕ) (C : ℝ)
    (μ : Measure (Ambient (p + 1))) (hμ : GlobalUpperGrowth (p + 1) C μ)
    (e a : Ambient (p + 1)) (H : ℝ) (hH : 0 < H)
    (g : 𝓢(Ambient (p + 1), ℝ)) (hmean : (∫ y, g y) = 0)
    (hgs : ∀ y, g y ≠ 0 → dist y a ≤ H) :
    ∃ D : Ambient (p + 1) → ℝ, Measurable D ∧ Integrable D μ ∧ (∀ x, 0 ≤ D x) ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ H → ∀ x,
        ‖scalarCappedTransform (p + 1) volume e ε g x‖ ≤ D x := by
  obtain ⟨B, hB, hlocal⟩ := exists_uniform_local_scalarCappedTransform_bound p e g (‖a‖ + 2 * H)
  let A := (∫ y, |g y|) *
    ((2 ^ (p + 1 + 1) + (p + 1 + 1 : ℝ) * 2 ^ (p + 1 + 2)) * (‖e‖ * H))
  have hA : 0 ≤ A := by
    dsimp only [A]
    exact mul_nonneg (integral_nonneg fun _ => abs_nonneg _) (by positivity)
  let D : Ambient (p + 1) → ℝ := fun x =>
    (ball a (2 * H)).indicator (fun _ => B) x +
      A * (closedExterior a (2 * H)).indicator (inverseDistancePow (p + 2) a) x
  have hfinite : μ (ball a (2 * H)) ≠ ⊤ :=
    ne_of_lt ((hμ.2 a (2 * H) (by linarith)).trans_lt ENNReal.ofReal_lt_top)
  have hnear : IntegrableOn (fun _ : Ambient (p + 1) => B) (ball a (2 * H)) μ :=
    integrableOn_const hfinite
  have hfar := (inverseDistancePow_closedExterior_integrable_and_bound (p + 1) C μ hμ a (2 * H)
    (by linarith)).1
  have hDm : Measurable D :=
    (measurable_const.indicator measurableSet_ball).add
      (measurable_const.mul ((inverseDistancePow_measurable (p + 2) a).indicator
        (closedExterior_measurable a (2 * H))))
  have hDI : Integrable D μ :=
    (hnear.integrable_indicator measurableSet_ball).add
      ((hfar.integrable_indicator (closedExterior_measurable a (2 * H))).const_mul A)
  have hDn (x : Ambient (p + 1)) : 0 ≤ D x := by
    exact add_nonneg (indicator_nonneg (fun _ _ => hB) x)
      (mul_nonneg hA (indicator_nonneg (fun y _ => inverseDistancePow_nonneg _ _ y) x))
  refine ⟨D, hDm, hDI, hDn, ?_⟩
  intro ε hε hεH x
  by_cases hx : x ∈ ball a (2 * H)
  · have hxnorm : ‖x‖ ≤ ‖a‖ + 2 * H := by
      have ht' : ‖x‖ ≤ ‖x - a‖ + ‖a‖ := by
        simpa only [sub_add_cancel] using! norm_add_le (x - a) a
      have hx' : ‖x - a‖ < 2 * H := by simpa only [mem_ball, dist_eq_norm] using! hx
      linarith
    dsimp only [D]
    rw [indicator_of_mem hx, Real.norm_eq_abs]
    apply (hlocal ε hε x hxnorm).trans
    exact le_add_of_nonneg_right (mul_nonneg hA
      (indicator_nonneg (fun y _ => inverseDistancePow_nonneg _ _ y) x))
  · have hxext : x ∈ closedExterior a (2 * H) := by
      simpa only [closedExterior, mem_ofPred_eq, mem_ball, not_lt, dist_comm x a] using! hx
    dsimp only [D]
    rw [indicator_of_notMem hx, zero_add, indicator_of_mem hxext, Real.norm_eq_abs]
    simpa only [A, Nat.cast_add, Nat.cast_one] using!
      scalarCappedTransform_mean_zero_tail (p + 1) volume e a H ε hH hε hεH g
        g.continuous.measurable g.integrable hmean hgs x hxext

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_ScalarRieszTestLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory SchwartzMap Metric Filter Topology Set

theorem symmetricScalarCappedTestKernel_tendsto {d : ℕ} (m : ℕ)
    (e : Ambient d) (g : Ambient d → ℝ) (x h : Ambient d)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun j => symmetricScalarCappedTestKernel m e (ε j) g x h) atTop
      (𝓝 (symmetricScalarRieszTestKernel m e g x h)) := by
  by_cases hh : h = 0
  · subst h
    simpa only [symmetricScalarCappedTestKernel, symmetricScalarRieszTestKernel,
      inner_zero_right, zero_mul, mul_zero] using!
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  have hn : 0 < ‖h‖ := norm_pos_iff.mpr hh
  apply tendsto_const_nhds.congr'
  filter_upwards [hε.eventually (gt_mem_nhds hn)] with j hj
  simp only [symmetricScalarCappedTestKernel, symmetricScalarRieszTestKernel,
    cappedInverseDistancePow, inverseDistancePow, dist_zero_left, max_eq_right hj.le]

theorem scalarCappedTransform_tendsto_schwartz (p : ℕ)
    (e : Ambient (p + 1)) (g : 𝓢(Ambient (p + 1), ℝ)) (x : Ambient (p + 1))
    (ε : ℕ → ℝ) (hεpos : ∀ j, 0 < ε j) (hε : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun j => scalarCappedTransform (p + 1) volume e (ε j) g x) atTop
      (𝓝 (scalarRieszSchwartzTest (p + 1) e g x)) := by
  have hI := symmetricScalarRieszTestKernel_integrable p _ volume
    (volume_global_upper_growth (p + 1)) e g x
  have hsym (j : ℕ) := scalarCappedTransform_symmetric_identity (p + 1) e (ε j)
    (hεpos j) g g.continuous.measurable g.integrable x
  have hlim := tendsto_integral_of_dominated_convergence
    (fun h => ‖symmetricScalarRieszTestKernel (p + 1) e g x h‖)
    (fun j => (hsym j).1.aestronglyMeasurable) hI.norm
    (fun j => Eventually.of_forall fun h =>
      symmetricScalarCappedTestKernel_norm_le (p + 1) e (ε j) g x h)
    (Eventually.of_forall fun h => symmetricScalarCappedTestKernel_tendsto (p + 1) e g x h ε hε)
  have hm := hlim.const_mul (-1 / 2 : ℝ)
  apply hm.congr'
  exact Eventually.of_forall fun j => (hsym j).2.symm

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_ScalarRieszDensityLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory SchwartzMap Metric Filter Topology Set

theorem scalarCappedTransform_density_integral_tendsto (p : ℕ) (C : ℝ)
    (μ : Measure (Ambient (p + 1))) (hμ : GlobalUpperGrowth (p + 1) C μ)
    (e a : Ambient (p + 1)) (H : ℝ) (hH : 0 < H)
    (g : 𝓢(Ambient (p + 1), ℝ)) (hmean : (∫ y, g y) = 0)
    (hgs : ∀ y, g y ≠ 0 → dist y a ≤ H)
    (f : Ambient (p + 1) → ℝ) (hfm : Measurable f)
    (M : ℝ) (hfb : ∀ y, |f y| ≤ M)
    (ε : ℕ → ℝ) (hεpos : ∀ j, 0 < ε j) (hε : Tendsto ε atTop (𝓝 0)) :
    Integrable (fun y => f y * scalarRieszSchwartzTest (p + 1) e g y) μ ∧
      Tendsto (fun j => ∫ y, f y * scalarCappedTransform (p + 1) volume e (ε j) g y ∂μ)
        atTop (𝓝 (∫ y, f y * scalarRieszSchwartzTest (p + 1) e g y ∂μ)) := by
  obtain ⟨D, _, hDI, _, hDb⟩ :=
    exists_integrable_scalarCappedTransform_dominator p C μ hμ e a H hH g hmean hgs
  have hM : 0 ≤ M := (abs_nonneg (f 0)).trans (hfb 0)
  have hsmall : ∀ᶠ j in atTop, ε j ≤ H :=
    (hε.eventually (gt_mem_nhds hH)).mono fun _ h => h.le
  have hmeas (j : ℕ) : AEStronglyMeasurable
      (fun y => f y * scalarCappedTransform (p + 1) volume e (ε j) g y) μ :=
    hfm.aestronglyMeasurable.mul (scalarCappedTransform_continuous (p + 1) volume e
      (ε j) (hεpos j) g g.continuous.measurable g.integrable).aestronglyMeasurable
  have hbound (j : ℕ) (hj : ε j ≤ H) (y : Ambient (p + 1)) :
      ‖f y * scalarCappedTransform (p + 1) volume e (ε j) g y‖ ≤ M * D y := by
    rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul (hfb y) (hDb (ε j) (hεpos j) hj y) (norm_nonneg _) hM
  have hlim (y : Ambient (p + 1)) :
      Tendsto (fun j => f y * scalarCappedTransform (p + 1) volume e (ε j) g y) atTop
        (𝓝 (f y * scalarRieszSchwartzTest (p + 1) e g y)) :=
    (scalarCappedTransform_tendsto_schwartz p e g y ε hεpos hε).const_mul (f y)
  have hfm' : AEStronglyMeasurable (fun y => f y * scalarRieszSchwartzTest (p + 1) e g y) μ :=
    aestronglyMeasurable_of_tendsto_ae atTop hmeas (Eventually.of_forall hlim)
  have hI : Integrable (fun y => f y * scalarRieszSchwartzTest (p + 1) e g y) μ := by
    apply (hDI.const_mul M).mono' hfm'
    apply Eventually.of_forall
    intro y
    exact le_of_tendsto (hlim y).norm (hsmall.mono fun j hj => hbound j hj y)
  refine ⟨hI, ?_⟩
  exact tendsto_integral_filter_of_dominated_convergence (fun y => M * D y)
    (Eventually.of_forall hmeas)
    (hsmall.mono fun j hj => Eventually.of_forall (hbound j hj))
    (hDI.const_mul M) (Eventually.of_forall hlim)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_CappedDensityEquation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory SchwartzMap Metric Filter Topology Set

theorem density_riesz_test_equation_of_capped_equation (p : ℕ)
    (e a : Ambient (p + 1)) (H R : ℝ) (hH : 0 < H) (hR : 0 < R) (hHR : 2 * H ≤ R)
    (f : Ambient (p + 1) → ℝ) (hfm : Measurable f) (M : ℝ) (hfb : ∀ y, |f y| ≤ M)
    (g : 𝓢(Ambient (p + 1), ℝ)) (hmean : (∫ y, g y) = 0)
    (hgs : ∀ y, g y ≠ 0 → dist y a ≤ H)
    (ε : ℕ → ℝ) (hεpos : ∀ j, 0 < ε j) (hε : Tendsto ε atTop (𝓝 0))
    (hEq : Tendsto (fun j =>
      (∫ x, scalarCappedTransform (p + 1) (volume.restrict (ball a R)) e (ε j) f x * g x) +
        ∫ x, (∫ y in closedExterior a R,
          f y * inner ℝ e (kernel (p + 1) x y - kernel (p + 1) a y)) * g x) atTop (𝓝 0)) :
    Integrable (fun y => f y * scalarRieszSchwartzTest (p + 1) e g y) volume ∧
      (∫ y, f y * scalarRieszSchwartzTest (p + 1) e g y) = 0 := by
  have hlimit := scalarCappedTransform_density_integral_tendsto p _ volume
    (volume_global_upper_growth (p + 1)) e a H hH g hmean hgs f hfm M hfb ε hεpos hε
  have hsmall : ∀ᶠ j in atTop, ε j ≤ H :=
    (hε.eventually (gt_mem_nhds hH)).mono fun _ h => h.le
  have heq : (fun j =>
      (∫ x, scalarCappedTransform (p + 1) (volume.restrict (ball a R)) e (ε j) f x * g x) +
        ∫ x, (∫ y in closedExterior a R,
          f y * inner ℝ e (kernel (p + 1) x y - kernel (p + 1) a y)) * g x) =ᶠ[atTop]
      (fun j => -(∫ y, f y * scalarCappedTransform (p + 1) volume e (ε j) g y)) := by
    filter_upwards [hsmall] with j hj
    exact (local_plus_exterior_capped_density_pairing (p + 1) _ volume
      (volume_global_upper_growth (p + 1)) e a H R (ε j) hH hR hHR (hεpos j) hj
      f g hfm g.continuous.measurable M hfb g.integrable hmean hgs).2
  have hz : -(∫ y, f y * scalarRieszSchwartzTest (p + 1) e g y) = 0 :=
    tendsto_nhds_unique hlimit.2.neg (hEq.congr' heq)
  exact ⟨hlimit.1, neg_eq_zero.mp hz⟩

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Rigidity_FractionalGradientDomination
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# An integrable dominator for fractional gradients

Schwartz derivative seminorms control the near and far parts separately, with
inverse-distance powers `p` and `p + 2`. In dimension `p + 1` their sum is
integrable and uniformly bounds the dilated gradient kernel for dilation
parameters between one half and two.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory SchwartzMap Metric Filter Topology Set

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem fractionalGradientDominator_integrable (p : ℕ)
    (g : 𝓢(Ambient (p + 1), F)) (x : Ambient (p + 1)) :
    Integrable (fractionalGradientDominator p g x) volume := by
  have hn := (inverseDistancePow_near_integrable_and_bound (d := p + 1) p _ volume
    (volume_global_upper_growth (p + 1)) 0 1 (by norm_num)).1
  have hf := (inverseDistancePow_closedExterior_integrable_and_bound (d := p + 1) (p + 1) _ volume
    (volume_global_upper_growth (p + 1)) 0 1 (by norm_num)).1
  exact ((hn.integrable_indicator measurableSet_closedBall).const_mul _).add
    ((hf.integrable_indicator (closedExterior_measurable 0 1)).const_mul _)

theorem dilatedFractionalGradientKernel_le_dominator {d : ℕ} (p : ℕ)
    (g : 𝓢(Ambient d, F)) (x h : Ambient d) (t : ℝ) (ht : t ∈ Icc (1 / 2 : ℝ) 2) :
    ‖dilatedFractionalGradientKernel (p + 1) g x t h‖ ≤ fractionalGradientDominator p g x h := by
  have htpos : 0 ≤ t := by linarith [ht.1]
  have htAbs : |t| ≤ 2 := by rw [abs_of_nonneg htpos]; exact ht.2
  have hn : 0 ≤ (closedBall (0 : Ambient d) 1).indicator (inverseDistancePow p 0) h :=
    indicator_nonneg (fun y _ => inverseDistancePow_nonneg p 0 y) h
  have hf : 0 ≤ (closedExterior (0 : Ambient d) 1).indicator (inverseDistancePow (p + 2) 0) h :=
    indicator_nonneg (fun y _ => inverseDistancePow_nonneg (p + 2) 0 y) h
  by_cases hh : ‖h‖ ≤ 1
  · have hmem : h ∈ closedBall (0 : Ambient d) 1 := by
      simpa only [mem_closedBall, dist_zero_right] using! hh
    unfold fractionalGradientDominator
    rw [indicator_of_mem hmem]
    apply (schwartz_dilated_fractional_gradient_near_bound p g x h t htAbs).trans
    apply le_add_of_nonneg_right
    exact mul_nonneg (mul_nonneg (by norm_num)
      (add_nonneg (apply_nonneg _ _) (mul_nonneg (norm_nonneg _) (apply_nonneg _ _)))) hf
  · have hmem : h ∈ closedExterior (0 : Ambient d) 1 := by
      simpa only [closedExterior, mem_ofPred_eq, dist_zero_left] using! (lt_of_not_ge hh).le
    unfold fractionalGradientDominator
    rw [indicator_of_mem hmem]
    apply (schwartz_dilated_fractional_gradient_far_bound (p + 1) g x h t ht.1).trans
    apply le_add_of_nonneg_left
    exact mul_nonneg (mul_nonneg (by norm_num) (apply_nonneg _ _)) hn

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Rigidity_FractionalDilationDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Differentiating dilated fractional kernels

Measurability and the gradient dominator justify differentiation under the
integral near dilation one. Comparing with the dilation scaling identity
identifies the integrated gradient kernel with the fractional Schwartz kernel,
and hence gives the gradient representation of the fractional test.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory SchwartzMap Metric Filter Topology Set

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem dilatedFractionalKernel_aestronglyMeasurable {d : ℕ} (m : ℕ)
    (g : 𝓢(Ambient d, F)) (μ : Measure (Ambient d)) (x : Ambient d) (t : ℝ) :
    AEStronglyMeasurable (dilatedFractionalKernel m g x t) μ := by
  have hc : Continuous (fun h : Ambient d => symmetricSecondDifference g x (t • h)) := by
    unfold symmetricSecondDifference
    fun_prop
  exact (inverseDistancePow_measurable (m + 1) (0 : Ambient d)).aestronglyMeasurable.smul
    hc.aestronglyMeasurable

theorem dilatedFractionalGradientKernel_aestronglyMeasurable {d : ℕ} (m : ℕ)
    (g : 𝓢(Ambient d, F)) (μ : Measure (Ambient d)) (x : Ambient d) (t : ℝ) :
    AEStronglyMeasurable (dilatedFractionalGradientKernel m g x t) μ := by
  let : ContinuousSMul ℝ (Ambient d) := IsBoundedSMul.continuousSMul
  have hD : Continuous (fderiv ℝ (g : Ambient d → F)) :=
    (g.smooth ⊤).continuous_fderiv (by simp)
  have hp : Continuous (fun h : Ambient d => fderiv ℝ g (x + t • h) h) :=
    (hD.comp ((continuous_const (y := x)).add ((continuous_const (y := t)).smul continuous_id))).clm_apply continuous_id
  have hm : Continuous (fun h : Ambient d => fderiv ℝ g (x - t • h) h) :=
    (hD.comp ((continuous_const (y := x)).sub ((continuous_const (y := t)).smul continuous_id))).clm_apply continuous_id
  exact (inverseDistancePow_measurable (m + 1) (0 : Ambient d)).aestronglyMeasurable.smul
    (hp.sub hm).aestronglyMeasurable

theorem fractional_gradient_integral_identity [CompleteSpace F] (p : ℕ)
    (g : 𝓢(Ambient (p + 1), F)) (x : Ambient (p + 1)) :
    Integrable (dilatedFractionalGradientKernel (p + 1) g x 1) volume ∧
      (∫ h, dilatedFractionalGradientKernel (p + 1) g x 1 h) =
        ∫ h, fractionalSchwartzKernel (p + 1) g x h := by
  have hI : Integrable (dilatedFractionalKernel (p + 1) g x 1) volume := by
    have heq : dilatedFractionalKernel (p + 1) g x 1 =
        fractionalSchwartzKernel (p + 1) g x := by
      funext h
      simp only [dilatedFractionalKernel, one_smul, fractionalSchwartzKernel]
    rw [heq]
    exact fractionalSchwartzKernel_integrable_of_growth p _ volume
      (volume_global_upper_growth (p + 1)) g x
  have hparam := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun t h => dilatedFractionalKernel (p + 1) g x t h)
    (F' := fun t h => dilatedFractionalGradientKernel (p + 1) g x t h)
    (μ := (volume : Measure (Ambient (p + 1))))
    (show Icc (1 / 2 : ℝ) 2 ∈ 𝓝 (1 : ℝ) from Icc_mem_nhds (by norm_num) (by norm_num))
    (Eventually.of_forall fun t => dilatedFractionalKernel_aestronglyMeasurable (p + 1) g volume x t)
    hI (dilatedFractionalGradientKernel_aestronglyMeasurable (p + 1) g volume x 1)
    (Eventually.of_forall fun h t ht => dilatedFractionalGradientKernel_le_dominator p g x h t ht)
    (fractionalGradientDominator_integrable p g x)
    (Eventually.of_forall fun h t _ => dilatedFractionalKernel_hasDerivAt (p + 1) g g.differentiable x h t)
  have hscale : (fun t : ℝ => ∫ h, dilatedFractionalKernel (p + 1) g x t h) =ᶠ[𝓝 (1 : ℝ)]
      (fun t => t • ∫ h, fractionalSchwartzKernel (p + 1) g x h) := by
    filter_upwards [Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1)] with t ht
    exact dilatedFractionalKernel_integral_scaling (p + 1) g x t ht
  have hlinear : HasDerivAt (fun t : ℝ => t • ∫ h, fractionalSchwartzKernel (p + 1) g x h)
      (∫ h, fractionalSchwartzKernel (p + 1) g x h) 1 := by
    simpa only [one_smul] using! (hasDerivAt_id (1 : ℝ)).smul_const
      (∫ h, fractionalSchwartzKernel (p + 1) g x h)
  exact ⟨hparam.1, hparam.2.unique (hlinear.congr_of_eventuallyEq hscale)⟩

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_GradientRieszTestIdentity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Gradient identities for scalar Riesz tests

Summing directional Schwartz derivatives over an orthonormal basis recovers the
dilated fractional gradient kernel. Integrating this identity and passing to
vanishing capped truncations yields the fractional Schwartz integral with its
factor of negative one half.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory SchwartzMap Metric Filter Topology Set LineDeriv

theorem sum_symmetricScalarRieszTestKernel_gradient {d : ℕ} {ι : Type*}
    [Fintype ι] (b : OrthonormalBasis ι ℝ (Ambient d)) (m : ℕ)
    (g : 𝓢(Ambient d, ℝ)) (x h : Ambient d) :
    (∑ i, symmetricScalarRieszTestKernel m (b i) (scalarSchwartzDerivative g (b i)) x h) =
      dilatedFractionalGradientKernel m g x 1 h := by
  have hsum (A : Ambient d →L[ℝ] ℝ) :
      (∑ i, inner ℝ (b i) h * A (b i)) = A h := by
    simpa only [map_sum, map_smul, smul_eq_mul] using!
      congrArg (fun z => A z) (b.sum_repr' h)
  simp only [symmetricScalarRieszTestKernel, scalarSchwartzDerivative, lineDerivOp_apply_eq_fderiv,
    dilatedFractionalGradientKernel, one_smul, smul_eq_mul]
  rw [← Finset.mul_sum]
  congr 1
  simp only [mul_sub, Finset.sum_sub_distrib, hsum]

theorem sum_scalarRieszSchwartzTest_gradient (p : ℕ) {ι : Type*}
    [Fintype ι] (b : OrthonormalBasis ι ℝ (Ambient (p + 1)))
    (g : 𝓢(Ambient (p + 1), ℝ)) (x : Ambient (p + 1)) :
    (∑ i, scalarRieszSchwartzTest (p + 1) (b i) (scalarSchwartzDerivative g (b i)) x) =
      (-1 / 2 : ℝ) * ∫ h, fractionalSchwartzKernel (p + 1) g x h := by
  have hI (i : ι) : Integrable
      (symmetricScalarRieszTestKernel (p + 1) (b i) (scalarSchwartzDerivative g (b i)) x) volume :=
    symmetricScalarRieszTestKernel_integrable p _ volume
      (volume_global_upper_growth (p + 1)) (b i) (scalarSchwartzDerivative g (b i)) x
  have hsum : (∫ h, ∑ i, symmetricScalarRieszTestKernel (p + 1) (b i) (scalarSchwartzDerivative g (b i)) x h) =
      ∑ i, ∫ h, symmetricScalarRieszTestKernel (p + 1) (b i) (scalarSchwartzDerivative g (b i)) x h :=
    integral_finsetSum Finset.univ (fun i _ => hI i)
  calc
    _ = (-1 / 2 : ℝ) *
        (∑ i, ∫ h, symmetricScalarRieszTestKernel (p + 1) (b i) (scalarSchwartzDerivative g (b i)) x h) := by
      simp only [scalarRieszSchwartzTest, Finset.mul_sum]
    _ = (-1 / 2 : ℝ) *
        (∫ h, ∑ i, symmetricScalarRieszTestKernel (p + 1) (b i) (scalarSchwartzDerivative g (b i)) x h) := by rw [hsum]
    _ = (-1 / 2 : ℝ) * ∫ h, dilatedFractionalGradientKernel (p + 1) g x 1 h := by
      congr 1
      apply integral_congr_ae
      exact Eventually.of_forall (sum_symmetricScalarRieszTestKernel_gradient b (p + 1) g x)
    _ = _ := by rw [(fractional_gradient_integral_identity p g x).2]

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_CompactDerivativeTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Compactly supported directional derivative tests

Directional derivatives of smooth compactly supported functions remain
continuous and compactly supported, with support inside that of the original
function. Integration by parts against the constant function shows that their
volume integral vanishes, making them mean-zero test functions.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set
open scoped ContDiff

theorem compact_smooth_directional_derivative_test {n : ℕ}
    (ψ : Ambient n → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) (e : Ambient n) :
    Continuous (fun x => fderiv ℝ ψ x e) ∧
      HasCompactSupport (fun x => fderiv ℝ ψ x e) ∧
      tsupport (fun x => fderiv ℝ ψ x e) ⊆ tsupport ψ ∧
      Integrable (fun x => fderiv ℝ ψ x e) volume ∧
      (∫ x, fderiv ℝ ψ x e) = 0 := by
  have hD : Continuous (fun x => fderiv ℝ ψ x e) :=
    (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hDc : HasCompactSupport (fun x => fderiv ℝ ψ x e) := hψc.fderiv_apply ℝ e
  have hDI : Integrable (fun x => fderiv ℝ ψ x e) volume := hD.integrable_of_hasCompactSupport hDc
  refine ⟨hD, hDc, tsupport_fderiv_apply_subset ℝ e, hDI, ?_⟩
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure (Ambient n))) (f := fun _ => (1 : ℝ)) (g := ψ) (v := e)
    (by simp only [fderiv_const_apply, zero_apply, zero_mul]; exact integrable_zero _ _ _)
    (by simpa only [one_mul] using! hDI)
    (by simpa only [one_mul] using! hψ.continuous.integrable_of_hasCompactSupport hψc)
    (fun x _ => differentiableAt_const (1 : ℝ))
    (fun x _ => hψ.differentiable (by simp) x)
  simpa only [one_mul, fderiv_const_apply, zero_apply, zero_mul, integral_zero, neg_zero] using! h

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_DensityGradientEquation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The fractional equation from density Riesz tests

Summing the vanishing Riesz pairings against directional derivatives over an
orthonormal basis gives the fractional Schwartz equation. The finite sum also
supplies integrability, with the factor `-1 / 2` fixed by the gradient identity.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory SchwartzMap Metric Set Filter Topology

theorem density_fractional_equation_of_riesz_tests (p : ℕ)
    (f : Ambient (p + 1) → ℝ) (ψ : 𝓢(Ambient (p + 1), ℝ))
    (hEq : ∀ e : Ambient (p + 1),
      Integrable (fun y => f y * scalarRieszSchwartzTest (p + 1) e (scalarSchwartzDerivative ψ e) y) volume ∧
        (∫ y, f y * scalarRieszSchwartzTest (p + 1) e (scalarSchwartzDerivative ψ e) y) = 0) :
    Integrable (fun y => f y * ((-1 / 2 : ℝ) * ∫ h, fractionalSchwartzKernel (p + 1) ψ y h)) volume ∧
      (∫ y, f y * ((-1 / 2 : ℝ) * ∫ h, fractionalSchwartzKernel (p + 1) ψ y h)) = 0 := by
  let b := EuclideanSpace.basisFun (Fin (p + 1)) ℝ
  let F : Fin (p + 1) → Ambient (p + 1) → ℝ := fun i y =>
    f y * scalarRieszSchwartzTest (p + 1) (b i) (scalarSchwartzDerivative ψ (b i)) y
  have hI (i : Fin (p + 1)) : Integrable (F i) volume := (hEq (b i)).1
  have heq : (fun y => f y * ((-1 / 2 : ℝ) * ∫ h, fractionalSchwartzKernel (p + 1) ψ y h)) =
      fun y => ∑ i, F i y := by
    funext y
    dsimp only [F]
    rw [← Finset.mul_sum]
    exact congrArg (fun z : ℝ => f y * z) (sum_scalarRieszSchwartzTest_gradient p b ψ y).symm
  rw [heq]
  refine ⟨integrable_finsetSum Finset.univ (fun i _ => hI i), ?_⟩
  rw [integral_finsetSum Finset.univ (fun i _ => hI i)]
  exact Finset.sum_eq_zero fun i _ => (hEq (b i)).2

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_SourceDensityRieszEquation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory SchwartzMap Metric Set Filter Topology
open scoped NNReal ENNReal

theorem source_planar_density_riesz_test_equation {d : ℕ} (p : ℕ) (C G : ℝ)
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hgrowth : ∀ j, GlobalUpperGrowth (p + 1) C (μ j))
    (hgν : GlobalUpperGrowth (p + 1) G ν) (hweak : CompactTestConvergence μ ν)
    (D : ℝ≥0)
    (hB : ∀ j ε, 0 < ε → ∀ u : Ambient d → ℝ, MemLp u 2 (μ j) →
      MemLp (truncated (p + 1) (μ j) ε u) 2 (μ j) ∧
        eLpNorm (truncated (p + 1) (μ j) ε u) 2 (μ j) ≤ (D : ℝ≥0∞) * eLpNorm u 2 (μ j))
    (L : Ambient (p + 1) →ₗᵢ[ℝ] Ambient d) (f : Ambient (p + 1) → ℝ)
    (hf : Measurable f) (c : ℝ) (hc : 0 < c) (hlower : ∀ x, c ≤ f x)
    (M : ℝ) (hupper : ∀ x, |f x| ≤ M)
    (hdensity : ((volume : Measure (Ambient (p + 1))).withDensity
      (fun x => ENNReal.ofReal (f x))).map L = ν)
    (e a : Ambient (p + 1)) (H R : ℝ) (hH : 0 < H) (hR : 0 < R) (hHR : 2 * H ≤ R)
    (hboundary : ν (frontier (ball (L a) R)) = 0) (hmass : ν (ball (L a) R) ≠ 0)
    (cMass : ℝ) (hcMass : 0 < cMass)
    (hlowerMass : ENNReal.ofReal (cMass * (H / 4) ^ (p + 1)) ≤ ν (ball (L a) (H / 4)))
    (hreflect : ScalarReflectionlessAt (p + 1) ν (L a))
    (g : 𝓢(Ambient (p + 1), ℝ)) (hmean : (∫ y, g y) = 0)
    (hgs : ∀ x, g x ≠ 0 → x ∈ ball a H) :
    Integrable (fun y => f y * scalarRieszSchwartzTest (p + 1) e g y) volume ∧
      (∫ y, f y * scalarRieszSchwartzTest (p + 1) e g y) = 0 := by
  obtain ⟨s, _, hε, b, hEq⟩ := exists_source_planar_unweighted_capped_equation p C G μ ν
    hgrowth hgν hweak D hB L f hf c hc hlower hdensity e a H R hH hR hHR
    hboundary hmass cMass hcMass hlowerMass hreflect
  have htest := hEq g g.continuous.measurable (SchwartzMap.seminorm ℝ 0 0 g)
    (fun x => by simpa only [Real.norm_eq_abs] using! g.norm_le_seminorm ℝ x) g.integrable hgs
  apply density_riesz_test_equation_of_capped_equation p e a H R hH hR hHR f hf M hupper
    g hmean (fun x hx => (hgs x hx).le) (fun j => (1 / 2 : ℝ) ^ (s j))
    (fun _ => pow_pos (by norm_num) _) hε
  simpa only [hmean, mul_zero] using! htest

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Rigidity_SourceDensityFractionalEquation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory SchwartzMap Metric Set Filter Topology
open scoped NNReal ENNReal

theorem source_planar_density_fractional_equation {d : ℕ} (p : ℕ) (C G : ℝ)
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hgrowth : ∀ j, GlobalUpperGrowth (p + 1) C (μ j))
    (hgν : GlobalUpperGrowth (p + 1) G ν) (hweak : CompactTestConvergence μ ν)
    (D : ℝ≥0)
    (hB : ∀ j ε, 0 < ε → ∀ u : Ambient d → ℝ, MemLp u 2 (μ j) →
      MemLp (truncated (p + 1) (μ j) ε u) 2 (μ j) ∧
        eLpNorm (truncated (p + 1) (μ j) ε u) 2 (μ j) ≤ (D : ℝ≥0∞) * eLpNorm u 2 (μ j))
    (L : Ambient (p + 1) →ₗᵢ[ℝ] Ambient d) (f : Ambient (p + 1) → ℝ)
    (hf : Measurable f) (c : ℝ) (hc : 0 < c) (hlower : ∀ x, c ≤ f x)
    (M : ℝ) (hupper : ∀ x, |f x| ≤ M)
    (hdensity : ((volume : Measure (Ambient (p + 1))).withDensity
      (fun x => ENNReal.ofReal (f x))).map L = ν)
    (a : Ambient (p + 1)) (H R : ℝ) (hH : 0 < H) (hR : 0 < R) (hHR : 2 * H ≤ R)
    (hboundary : ν (frontier (ball (L a) R)) = 0) (hmass : ν (ball (L a) R) ≠ 0)
    (cMass : ℝ) (hcMass : 0 < cMass)
    (hlowerMass : ENNReal.ofReal (cMass * (H / 4) ^ (p + 1)) ≤ ν (ball (L a) (H / 4)))
    (hreflect : ScalarReflectionlessAt (p + 1) ν (L a))
    (ψ : 𝓢(Ambient (p + 1), ℝ)) (hψc : HasCompactSupport ψ) (hψs : tsupport ψ ⊆ ball a H) :
    Integrable (fun y => f y * ((-1 / 2 : ℝ) * ∫ h, fractionalSchwartzKernel (p + 1) ψ y h)) volume ∧
      (∫ y, f y * ((-1 / 2 : ℝ) * ∫ h, fractionalSchwartzKernel (p + 1) ψ y h)) = 0 := by
  apply density_fractional_equation_of_riesz_tests p f ψ
  intro e
  obtain ⟨_, _, hDs, _, hmean⟩ :=
    compact_smooth_directional_derivative_test ψ (ψ.smooth ⊤) hψc e
  have hsupport : ∀ x, scalarSchwartzDerivative ψ e x ≠ 0 → x ∈ ball a H := by
    intro x hx
    exact hψs (hDs (subset_tsupport (fun y => fderiv ℝ ψ y e) hx))
  exact source_planar_density_riesz_test_equation p C G μ ν hgrowth hgν hweak D hB
    L f hf c hc hlower M hupper hdensity e a H R hH hR hHR hboundary hmass cMass hcMass
    hlowerMass hreflect (scalarSchwartzDerivative ψ e) hmean hsupport

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_SourceDensityCompactEquation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory SchwartzMap Metric Set Filter Topology
open scoped NNReal ENNReal

theorem source_planar_density_compact_fractional_equation_oai {d : ℕ} (p : ℕ) (C G : ℝ)
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hgrowth : ∀ j, GlobalUpperGrowth (p + 1) C (μ j))
    (hgν : GlobalUpperGrowth (p + 1) G ν) (hweak : CompactTestConvergence μ ν)
    (D : ℝ≥0)
    (hB : ∀ j ε, 0 < ε → ∀ u : Ambient d → ℝ, MemLp u 2 (μ j) →
      MemLp (truncated (p + 1) (μ j) ε u) 2 (μ j) ∧
        eLpNorm (truncated (p + 1) (μ j) ε u) 2 (μ j) ≤ (D : ℝ≥0∞) * eLpNorm u 2 (μ j))
    (L : Ambient (p + 1) →ₗᵢ[ℝ] Ambient d) (f : Ambient (p + 1) → ℝ)
    (hf : Measurable f) (c : ℝ) (hc : 0 < c) (hlower : ∀ x, c ≤ f x)
    (M : ℝ) (hupper : ∀ x, |f x| ≤ M)
    (hdensity : ((volume : Measure (Ambient (p + 1))).withDensity
      (fun x => ENNReal.ofReal (f x))).map L = ν)
    (cMass : ℝ) (hcMass : 0 < cMass)
    (hlowerMass : ∀ r : ℝ, 0 < r →
      ENNReal.ofReal (cMass * r ^ (p + 1)) ≤ ν (ball 0 r))
    (hreflect : ScalarReflectionlessAt (p + 1) ν 0)
    (ψ : 𝓢(Ambient (p + 1), ℝ)) (hψc : HasCompactSupport ψ) :
    Integrable (fun y => f y * ((-1 / 2 : ℝ) *
      ∫ h, fractionalSchwartzKernel (p + 1) ψ y h)) volume ∧
      (∫ y, f y * ((-1 / 2 : ℝ) *
        ∫ h, fractionalSchwartzKernel (p + 1) ψ y h)) = 0 := by
  obtain ⟨H, hH, hψs⟩ := hψc.isBounded.subset_ball_lt 0 (0 : Ambient (p + 1))
  obtain ⟨R, hRi, hboundary⟩ := exists_null_frontier_thickening ν {(0 : Ambient d)}
    (show 2 * H < 2 * H + 1 by linarith)
  simp only [thickening_singleton] at hboundary
  have hR : 0 < R := by linarith [hRi.1]
  have hmass : ν (ball 0 R) ≠ 0 :=
    ((ENNReal.ofReal_pos.mpr (mul_pos hcMass (pow_pos hR _))).trans_le
      (hlowerMass R hR)).ne'
  have hquarter : 0 < H / 4 := by positivity
  apply source_planar_density_fractional_equation p C G μ ν hgrowth hgν hweak D hB
    L f hf c hc hlower M hupper hdensity 0 H R hH hR (le_of_lt hRi.1)
  · simpa only [map_zero] using! hboundary
  · simpa only [map_zero] using! hmass
  · exact hcMass
  · simpa only [map_zero] using! hlowerMass (H / 4) hquarter
  · simpa only [map_zero] using! hreflect
  · exact hψc
  · exact hψs

end

end RieszRectifiability

end OAI
end

theorem solution : type_of% @OAI.RieszRectifiability.source_planar_density_compact_fractional_equation_oai := @OAI.RieszRectifiability.source_planar_density_compact_fractional_equation_oai
