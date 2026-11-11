-- Prove2me | solution 1 for OAI.RieszRectifiability.exists_dyadic_flat_measure_limit_with_energy
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:27:11.617123+00:00
-- url     : https://prove2.me/submissions/460fe33b-e50e-4ad6-ae74-42c01a4d6c65

import Mathlib
import Definitions.Def_RieszQuantitative
import Definitions.Def_OAIQ231Rr000
import Theorems.Thm_OAI_RieszRectifiability_exists_dyadic_full_planar_measure_limit
import Theorems.Thm_OAI_RieszRectifiability_normal_frame_source_data_on_ball
import Theorems.Thm_OAI_RieszRectifiability_represented_fractional_height_ae_affine
import Theorems.Thm_OAI_RieszRectifiability_source_planar_density_compact_fractional_equation

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
-- module Solutions.OAIQ231_RR.RieszRectifiability_Flatness_BoundedAffineConstant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Bounded affine functions are constant

A nonzero linear part grows along a suitable ray, contradicting any global
bound on its affine translate. Density of volume-almost-everywhere sets extends
an almost-everywhere affine bound to every point, so a bounded function that is
almost everywhere affine is almost everywhere constant.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Filter

theorem bounded_affine_linear_part_zero {d : ℕ} (c : ℝ)
    (L : Ambient d →L[ℝ] ℝ) (M : ℝ) (hb : ∀ x, |c + L x| ≤ M) : L = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  change L x = 0
  by_contra hx
  let t : ℝ := (M + |c| + 1) / L x
  have hvalue : L (t • x) = M + |c| + 1 := by
    rw [map_smul, smul_eq_mul]
    exact div_mul_cancel₀ _ hx
  have hle := (le_abs_self (c + L (t • x))).trans (hb (t • x))
  rw [hvalue] at hle
  linarith [neg_abs_le c]

theorem ae_bounded_affine_is_constant {d : ℕ} (f : Ambient d → ℝ)
    (M : ℝ) (hb : ∀ x, |f x| ≤ M) (c : ℝ) (L : Ambient d →L[ℝ] ℝ)
    (heq : ∀ᵐ x ∂volume, f x = c + L x) :
    L = 0 ∧ ∀ᵐ x ∂volume, f x = c := by
  have haeb : ∀ᵐ x ∂volume, |c + L x| ≤ M := by
    filter_upwards [heq] with x hx
    rw [← hx]
    exact hb x
  have hclosed : IsClosed {x : Ambient d | |c + L x| ≤ M} :=
    isClosed_le (continuous_const.add L.continuous).abs continuous_const
  have hs := (Measure.dense_of_ae haeb).closure_eq
  rw [hclosed.closure_eq] at hs
  have hbound (x : Ambient d) : |c + L x| ≤ M := by
    have hx : x ∈ {x : Ambient d | |c + L x| ≤ M} := by
      rw [hs]
      exact mem_univ x
    exact hx
  have hzero := bounded_affine_linear_part_zero c L M hbound
  refine ⟨hzero, ?_⟩
  simpa only [hzero, zero_apply, add_zero] using! heq

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Flatness_BoundedPlaneBoxes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open BoxIntegral MeasureTheory Metric Set Function Filter Topology
open scoped NNReal ENNReal

theorem planeBoxOuterRadius_pos (K : ℝ≥0) (H : ℕ) : 0 < planeBoxOuterRadius K H := by
  unfold planeBoxOuterRadius
  positivity

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_CellEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set

variable {X : Type*} [MeasurableSpace X]

variable [MetricSpace X]

omit [MeasurableSpace X] in
theorem fractionalPairEnergy_nonneg (m : ℕ) (w : X → ℝ) (x y : X) :
    0 ≤ fractionalPairEnergy m w x y := by
  unfold fractionalPairEnergy
  positivity

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
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_FinitePairingCancellation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal

theorem closedExterior_eq_compl_ball {d : ℕ} (a : Ambient d) (R : ℝ) :
    closedExterior a R = (ball a R)ᶜ := by
  ext y
  change (R ≤ dist a y) ↔ ¬ dist y a < R
  rw [dist_comm y a, not_lt]

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Rigidity_TemperedHeightWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology

theorem polynomialDecay_le_one {d : ℕ} (q : ℕ) (x : Ambient d) : polynomialDecay q x ≤ 1 := by
  unfold polynomialDecay
  apply inv_le_one_of_one_le₀
  exact one_le_pow₀ (by linarith [norm_nonneg x] : (1 : ℝ) ≤ 1 + ‖x‖)

theorem polynomialDecay_le_far {d : ℕ} (q : ℕ) (a x : Ambient d) (hx : 0 < dist a x) :
    polynomialDecay q x ≤ (1 + ‖a‖) ^ q * inverseDistancePow q a x := by
  have hd : dist a x ≤ (1 + ‖a‖) * (1 + ‖x‖) := by
    have h : dist a x ≤ ‖a‖ + ‖x‖ := by
      rw [dist_eq_norm]
      exact norm_sub_le a x
    nlinarith [norm_nonneg a, norm_nonneg x, mul_nonneg (norm_nonneg a) (norm_nonneg x)]
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ dist a x) hd q
  rw [inverseDistancePow, ← div_eq_mul_inv]
  apply (le_div_iff₀ (pow_pos hx q)).mpr
  calc
    _ ≤ polynomialDecay q x * ((1 + ‖a‖) * (1 + ‖x‖)) ^ q :=
      mul_le_mul_of_nonneg_left hp (polynomialDecay_nonneg q x)
    _ = _ := by
      unfold polynomialDecay
      rw [mul_pow]
      field_simp

theorem polynomial_weight_integrable_from_height_tail {d : ℕ} (q : ℕ)
    (μ : Measure (Ambient d)) (f : Ambient d → ℝ) (hf : Measurable f)
    (a : Ambient d) (R : ℝ) (hR : 0 < R)
    (hnear : IntegrableOn f (ball a R) μ)
    (hfar : IntegrableOn (fun x => |f x| * inverseDistancePow q a x) (closedExterior a R) μ) :
    Integrable (fun x => |f x| * polynomialDecay q x) μ := by
  have hm : Measurable (fun x => |f x| * polynomialDecay q x) :=
    hf.abs.mul (polynomialDecay_measurable q)
  have hi : IntegrableOn (fun x => |f x| * polynomialDecay q x) (ball a R) μ := by
    apply hnear.abs.mono' hm.aestronglyMeasurable
    apply Eventually.of_forall
    intro x
    rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (polynomialDecay_nonneg q x))]
    simpa only [mul_one] using! mul_le_mul_of_nonneg_left (polynomialDecay_le_one q x) (abs_nonneg _)
  have ho : IntegrableOn (fun x => |f x| * polynomialDecay q x) (closedExterior a R) μ := by
    apply (hfar.const_mul ((1 + ‖a‖) ^ q)).mono' hm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem (closedExterior_measurable a R)] with x hx
    rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (polynomialDecay_nonneg q x))]
    calc
      _ ≤ |f x| * ((1 + ‖a‖) ^ q * inverseDistancePow q a x) :=
        mul_le_mul_of_nonneg_left (polynomialDecay_le_far q a x (hR.trans_le hx)) (abs_nonneg _)
      _ = _ := by ring
  have hu := hi.union ho
  rw [closedExterior_eq_compl_ball, union_compl_self, integrableOn_univ] at hu
  exact hu

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Rigidity_HeightTemperedDistribution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Tempered distributions associated with heights

Polynomially weighted integrability makes the positive and negative height
measures temperate. Their difference defines a tempered distribution whose action
on a Schwartz test function is integration against the signed height.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology SchwartzMap
open scoped NNReal ENNReal

theorem positivePart_sub_negativePart (r : ℝ) :
    (Real.toNNReal r : ℝ) - (Real.toNNReal (-r) : ℝ) = r := by
  rw [Real.coe_toNNReal', Real.coe_toNNReal']
  rcases le_total 0 r with hr | hr
  · rw [max_eq_left hr, max_eq_right (by linarith : -r ≤ 0), sub_zero]
  · rw [max_eq_right hr, max_eq_left (by linarith : 0 ≤ -r)]
    ring

theorem heightTemperedDistribution_apply {d : ℕ}
    (μ : Measure (Ambient d)) (f : Ambient d → ℝ) (hf : Measurable f) (q : ℕ)
    (hweight : Integrable (fun x => |f x| * polynomialDecay q x) μ)
    (g : 𝓢(Ambient d, ℂ)) : heightTemperedDistribution μ f hf q hweight g = ∫ x, f x • g x ∂μ := by
  let := positive_height_measure_temperate μ f hf q hweight
  have hnweight : Integrable (fun x => |(-f x)| * polynomialDecay q x) μ := by
    simpa only [abs_neg] using! hweight
  let := positive_height_measure_temperate μ (fun x => -f x) hf.neg q hnweight
  have hip : Integrable (fun x => (Real.toNNReal (f x) : ℝ) • g x) μ :=
    (integrable_withDensity_iff_integrable_coe_smul hf.real_toNNReal).mp
      (g.integrable (μ := positiveHeightMeasure μ f))
  have hin : Integrable (fun x => (Real.toNNReal (-f x) : ℝ) • g x) μ :=
    (integrable_withDensity_iff_integrable_coe_smul hf.neg.real_toNNReal).mp
      (g.integrable (μ := positiveHeightMeasure μ (fun x => -f x)))
  change (∫ x, g x ∂positiveHeightMeasure μ f) -
    (∫ x, g x ∂positiveHeightMeasure μ (fun x => -f x)) = ∫ x, f x • g x ∂μ
  unfold positiveHeightMeasure
  rw [integral_withDensity_eq_integral_smul hf.real_toNNReal,
    integral_withDensity_eq_integral_smul (show Measurable (fun x => Real.toNNReal (-f x)) from hf.neg.real_toNNReal)]
  simp only [NNReal.smul_def]
  refine (integral_sub hip hin).symm.trans (integral_congr_ae (Eventually.of_forall ?_))
  intro x
  calc
    _ = ((Real.toNNReal (f x) : ℝ) - (Real.toNNReal (-f x) : ℝ)) • g x :=
      (sub_smul (Real.toNNReal (f x) : ℝ) (Real.toNNReal (-f x) : ℝ) (g x)).symm
    _ = _ := congrArg (fun r : ℝ => r • g x) (positivePart_sub_negativePart (f x))

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_BoundedDensityWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter

theorem bounded_measurable_integrableOn_finite {d : ℕ}
    (μ : Measure (Ambient d)) (f : Ambient d → ℝ) (hf : Measurable f)
    (M : ℝ) (hb : ∀ x, |f x| ≤ M) (s : Set (Ambient d)) (hs : μ s ≠ ⊤) :
    IntegrableOn f s μ := by
  have hI : IntegrableOn (fun _ : Ambient d => M) s μ := integrableOn_const hs
  apply hI.mono' hf.aestronglyMeasurable
  exact Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using! hb x

theorem bounded_measurable_locallyIntegrable {d : ℕ}
    (μ : Measure (Ambient d)) [IsFiniteMeasureOnCompacts μ]
    (f : Ambient d → ℝ) (hf : Measurable f) (M : ℝ) (hb : ∀ x, |f x| ≤ M) :
    LocallyIntegrable f μ := by
  apply locallyIntegrable_iff.mpr
  intro K hK
  exact bounded_measurable_integrableOn_finite μ f hf M hb K hK.measure_ne_top

theorem bounded_density_exterior_integrable (d : ℕ)
    (f : Ambient d → ℝ) (hf : Measurable f) (M : ℝ) (hb : ∀ x, |f x| ≤ M) :
    IntegrableOn (fun x => |f x| * inverseDistancePow (d + 2) 0 x)
      (closedExterior 0 1) volume := by
  have hM : 0 ≤ M := (abs_nonneg (f 0)).trans (hb 0)
  have hi := (inverseDistancePow_closedExterior_integrable_and_bound (d := d) d _ volume
    (volume_global_upper_growth d) 0 1 zero_lt_one).1
  apply (hi.const_mul M).mono'
    ((hf.abs.mul (inverseDistancePow_measurable (d + 2) 0)).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem (closedExterior_measurable (0 : Ambient d) 1)] with x hx
  have hp : dist (0 : Ambient d) x ^ (d + 1) ≤ dist 0 x ^ (d + 2) := by
    calc
      _ = dist (0 : Ambient d) x ^ (d + 1) * 1 := (mul_one _).symm
      _ ≤ dist (0 : Ambient d) x ^ (d + 1) * dist 0 x :=
        mul_le_mul_of_nonneg_left hx (pow_nonneg dist_nonneg _)
      _ = _ := (pow_succ _ _).symm
  have hinv : inverseDistancePow (d + 2) 0 x ≤ inverseDistancePow (d + 1) 0 x :=
    inv_anti₀ (pow_pos (zero_lt_one.trans_le hx) _) hp
  rw [Pi.mul_apply, Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (inverseDistancePow_nonneg _ _ _))]
  exact (mul_le_mul_of_nonneg_right (hb x) (inverseDistancePow_nonneg _ _ _)).trans
    (mul_le_mul_of_nonneg_left hinv hM)

theorem bounded_density_polynomial_weight_integrable (d : ℕ)
    (f : Ambient d → ℝ) (hf : Measurable f) (M : ℝ) (hb : ∀ x, |f x| ≤ M) :
    Integrable (fun x => |f x| * polynomialDecay (d + 2) x) volume := by
  exact polynomial_weight_integrable_from_height_tail (d + 2) volume f hf 0 1 zero_lt_one
    (bounded_measurable_integrableOn_finite volume f hf M hb (ball 0 1) measure_ball_lt_top.ne)
    (bounded_density_exterior_integrable d f hf M hb)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_ExpandingSmoothCutoffs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Expanding smooth cutoffs

Dilating a fixed bump gives compactly supported smooth cutoffs equal to one on
balls of increasing radius. Composition with linear contractions bounds all
derivatives by Schwartz seminorms and supplies uniform derivative bounds for
the cutoff errors.
-/

namespace RieszRectifiability

noncomputable section

open SchwartzMap MeasureTheory Metric Filter Topology
open scoped ContDiff

theorem expandingSmoothCutoff_smooth (d j : ℕ) :
    ContDiff ℝ ∞ (expandingSmoothCutoff d j) := by
  apply (unitSmoothCutoff d).contDiff.comp
  exact (contDiff_id : ContDiff ℝ ∞ (fun x : Ambient d => x)).const_smul _

theorem expandingSmoothCutoff_compact (d j : ℕ) :
    HasCompactSupport (expandingSmoothCutoff d j) := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : Ambient d) (2 * ((j : ℝ) + 1)))
  intro x hx
  apply (unitSmoothCutoff d).zero_of_le_dist
  have hR : 0 < (j : ℝ) + 1 := by positivity
  have hx' : 2 * ((j : ℝ) + 1) < ‖x‖ := by
    simpa only [mem_closedBall, dist_zero_right, not_le] using! hx
  change 2 ≤ dist (((j : ℝ) + 1)⁻¹ • x) 0
  rw [dist_zero_right, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hR.le)]
  exact (le_div_iff₀ hR).2 hx'.le |>.trans_eq (div_eq_inv_mul _ _)

theorem expandingSmoothCutoff_one (d j : ℕ) (x : Ambient d)
    (hx : x ∈ ball (0 : Ambient d) ((j : ℝ) + 1)) :
    expandingSmoothCutoff d j x = 1 := by
  apply (unitSmoothCutoff d).one_of_mem_closedBall
  have hR : 0 < (j : ℝ) + 1 := by positivity
  have hx' : ‖x‖ < (j : ℝ) + 1 := by
    simpa only [mem_ball, dist_zero_right] using! hx
  change dist (((j : ℝ) + 1)⁻¹ • x) 0 ≤ 1
  rw [dist_zero_right, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hR.le)]
  have hh : ‖x‖ / ((j : ℝ) + 1) ≤ 1 := (div_le_one hR).2 hx'.le
  simpa only [div_eq_inv_mul] using! hh

theorem schwartz_contraction_derivative_bound {d : ℕ} (g : 𝓢(Ambient d, ℝ))
    (S : Ambient d →L[ℝ] Ambient d) (hS : ‖S‖ ≤ 1) (n : ℕ) (x : Ambient d) :
    ‖iteratedFDeriv ℝ n (g ∘ S) x‖ ≤ SchwartzMap.seminorm ℝ 0 n g := by
  rw [S.iteratedFDeriv_comp_right (g.smooth n) x le_rfl]
  have hp : (∏ _ : Fin n, ‖S‖) ≤ 1 := by
    exact Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun _ _ => hS)
  calc
    _ ≤ ‖iteratedFDeriv ℝ n g (S x)‖ * ∏ _ : Fin n, ‖S‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ ‖iteratedFDeriv ℝ n g (S x)‖ := by nlinarith [norm_nonneg (iteratedFDeriv ℝ n g (S x))]
    _ ≤ _ := g.norm_iteratedFDeriv_le_seminorm ℝ n (S x)

theorem expandingSmoothCutoff_error_uniform_derivatives (d : ℕ) :
    ∃ C : ℕ → ℝ, (∀ n, 0 ≤ C n) ∧ ∀ j n x,
      ‖iteratedFDeriv ℝ n (fun y => expandingSmoothCutoff d j y - 1) x‖ ≤ C n := by
  let β : 𝓢(Ambient d, ℝ) := (unitSmoothCutoff d).hasCompactSupport.toSchwartzMap
    (unitSmoothCutoff d).contDiff
  refine ⟨fun n => SchwartzMap.seminorm ℝ 0 n β + 1, fun n => by positivity, ?_⟩
  intro j n x
  let S : Ambient d →L[ℝ] Ambient d := ((j : ℝ) + 1)⁻¹ • ContinuousLinearMap.id ℝ (Ambient d)
  have hR : 1 ≤ (j : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) j]
  have hS : ‖S‖ ≤ 1 := by
    calc
      ‖S‖ ≤ ‖((j : ℝ) + 1)⁻¹‖ * ‖ContinuousLinearMap.id ℝ (Ambient d)‖ :=
        ContinuousLinearMap.opNorm_smul_le _ _
      _ ≤ 1 * 1 := mul_le_mul
        (by rw [Real.norm_of_nonneg (by positivity)]; exact inv_le_one_of_one_le₀ hR)
        ContinuousLinearMap.norm_id_le (norm_nonneg _) (by norm_num)
      _ = 1 := one_mul 1
  have heq : (expandingSmoothCutoff d j : Ambient d → ℝ) = β ∘ S := rfl
  have hb := schwartz_contraction_derivative_bound β S hS n x
  have hs : ContDiff ℝ n (expandingSmoothCutoff d j) := by
    rw [heq]
    exact (β.smooth n).comp S.contDiff
  have hc : ‖iteratedFDeriv ℝ n (fun _ : Ambient d => (1 : ℝ)) x‖ ≤ 1 := by
    cases n with
    | zero => simp
    | succ n => simp [iteratedFDeriv_succ_const]
  have hh := iteratedFDeriv_sub_apply hs.contDiffAt
    (contDiffAt_const (c := (1 : ℝ)) : ContDiffAt ℝ n (fun _ : Ambient d => (1 : ℝ)) x)
  change ‖iteratedFDeriv ℝ n ((expandingSmoothCutoff d j) - (fun _ => 1)) x‖ ≤ _
  rw [hh]
  exact (norm_sub_le _ _).trans (add_le_add (by simpa only [heq] using! hb) hc)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_SchwartzCutoffConvergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open SchwartzMap MeasureTheory Metric Filter Topology
open scoped ContDiff

variable {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem schwartz_cutoff_error_seminorm_le
    (g : 𝓢(Ambient d, F)) (q : Ambient d → ℝ) (hq : q.HasTemperateGrowth)
    (C : ℕ → ℝ) (hC : ∀ i, 0 ≤ C i)
    (hbound : ∀ i x, ‖iteratedFDeriv ℝ i q x‖ ≤ C i)
    (R : ℝ) (hR : 0 < R) (hzero : ∀ x ∈ ball (0 : Ambient d) R, q x = 0)
    (k n : ℕ) :
    SchwartzMap.seminorm ℝ k n (smulLeftCLM F q g) ≤
      (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * C i *
        SchwartzMap.seminorm ℝ (k + 1) (n - i) g) / R := by
  have hM : 0 ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * C i *
      SchwartzMap.seminorm ℝ (k + 1) (n - i) g := by
    exact Finset.sum_nonneg fun i _ => mul_nonneg (mul_nonneg (by positivity) (hC i))
      (apply_nonneg _ _)
  apply seminorm_le_bound ℝ k n _ (div_nonneg hM hR.le)
  intro x
  rw [smulLeftCLM_apply hq]
  by_cases hx : x ∈ ball (0 : Ambient d) R
  · have heq : (fun y => q y • g y) =ᶠ[𝓝 x] (fun _ => (0 : F)) := by
      filter_upwards [isOpen_ball.mem_nhds hx] with y hy
      simp [hzero y hy]
    have he := (heq.iteratedFDeriv ℝ n).eq_of_nhds
    rw [he]
    simpa only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero, mul_zero] using! div_nonneg hM hR.le
  · have hxR : R ≤ ‖x‖ := by simpa only [mem_ball, dist_zero_right, not_lt] using! hx
    have hp := norm_iteratedFDeriv_smul_le hq.1 (g.smooth ⊤) x (n := n) (mod_cast le_top)
    apply (le_div_iff₀ hR).2
    calc
      (‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun y => q y • g y) x‖) * R ≤
          R * ‖x‖ ^ k * (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
            ‖iteratedFDeriv ℝ i q x‖ * ‖iteratedFDeriv ℝ (n - i) g x‖) := by
        nlinarith [mul_le_mul_of_nonneg_left hp (pow_nonneg (norm_nonneg x) k)]
      _ = ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i q x‖ *
            (R * (‖x‖ ^ k * ‖iteratedFDeriv ℝ (n - i) g x‖)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * C i *
          SchwartzMap.seminorm ℝ (k + 1) (n - i) g := by
        apply Finset.sum_le_sum
        intro i _
        have hw : R * (‖x‖ ^ k * ‖iteratedFDeriv ℝ (n - i) g x‖) ≤
            SchwartzMap.seminorm ℝ (k + 1) (n - i) g := by
          calc
            _ ≤ ‖x‖ * (‖x‖ ^ k * ‖iteratedFDeriv ℝ (n - i) g x‖) := by gcongr
            _ = ‖x‖ ^ (k + 1) * ‖iteratedFDeriv ℝ (n - i) g x‖ := by ring
            _ ≤ _ := le_seminorm ℝ (k + 1) (n - i) g x
        exact mul_le_mul (mul_le_mul_of_nonneg_left (hbound i x) (by positivity)) hw
          (by positivity) (mul_nonneg (by positivity) (hC i))

theorem schwartz_cutoff_errors_tendsto_zero
    (g : 𝓢(Ambient d, F)) (q : ℕ → Ambient d → ℝ)
    (hq : ∀ j, (q j).HasTemperateGrowth)
    (C : ℕ → ℝ) (hC : ∀ i, 0 ≤ C i)
    (hbound : ∀ j i x, ‖iteratedFDeriv ℝ i (q j) x‖ ≤ C i)
    (R : ℕ → ℝ) (hR : ∀ j, 0 < R j) (hRt : Tendsto R atTop atTop)
    (hzero : ∀ j x, x ∈ ball (0 : Ambient d) (R j) → q j x = 0) :
    Tendsto (fun j => smulLeftCLM F (q j) g) atTop (𝓝 0) := by
  apply (schwartz_withSeminorms ℝ (Ambient d) F).tendsto_nhds _ _ |>.2
  rintro ⟨k, n⟩ ε hε
  let M := ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * C i *
    SchwartzMap.seminorm ℝ (k + 1) (n - i) g
  have ht : Tendsto (fun j => M / R j) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using! tendsto_const_nhds.mul hRt.inv_tendsto_atTop
  filter_upwards [ht.eventually (gt_mem_nhds hε)] with j hj
  simpa only [sub_zero, schwartzSeminormFamily_apply] using!
    (schwartz_cutoff_error_seminorm_le g (q j) (hq j) C hC (hbound j)
      (R j) (hR j) (hzero j) k n).trans_lt hj

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_CompactSchwartzApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Compactly supported approximation in Schwartz space

Expanding smooth cutoffs approximate Schwartz functions in the Schwartz topology.
Continuity of directional differentiation preserves this convergence, while compact
support ensures the approximating derivatives have zero integral. Consequently,
tempered distributions are determined by their compactly supported Schwartz tests.
-/

namespace RieszRectifiability

noncomputable section

open SchwartzMap MeasureTheory Metric Filter Topology
open scoped ContDiff LineDeriv

theorem exists_compact_schwartz_approximation {d : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (g : 𝓢(Ambient d, F)) :
    ∃ G : ℕ → 𝓢(Ambient d, F), (∀ j, HasCompactSupport (G j)) ∧
      Tendsto G atTop (𝓝 g) := by
  let G : ℕ → 𝓢(Ambient d, F) := fun j => smulLeftCLM F (expandingSmoothCutoff d j) g
  let q : ℕ → Ambient d → ℝ := fun j x => expandingSmoothCutoff d j x - 1
  have hβ : ∀ j, (expandingSmoothCutoff d j).HasTemperateGrowth :=
    fun j => (expandingSmoothCutoff_compact d j).hasTemperateGrowth (expandingSmoothCutoff_smooth d j)
  have hq : ∀ j, (q j).HasTemperateGrowth :=
    fun j => (hβ j).sub (Function.HasTemperateGrowth.const 1)
  obtain ⟨C, hC, hbound⟩ := expandingSmoothCutoff_error_uniform_derivatives d
  have hRt : Tendsto (fun j : ℕ => (j : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hzero : ∀ (j : ℕ) x, x ∈ ball (0 : Ambient d) ((j : ℝ) + 1) → q j x = 0 := by
    intro j x hx
    simp only [q, expandingSmoothCutoff_one d j x hx, sub_self]
  have ht := schwartz_cutoff_errors_tendsto_zero g q hq C hC hbound
    (fun j : ℕ => (j : ℝ) + 1) (fun j => by positivity) hRt hzero
  refine ⟨G, ?_, ?_⟩
  · intro j
    have hc : HasCompactSupport (fun x => expandingSmoothCutoff d j x • g x) :=
      (expandingSmoothCutoff_compact d j).smul_right
    simpa only [G, smulLeftCLM_apply (hβ j)] using! hc
  · have heq : G = fun j => g + smulLeftCLM F (q j) g := by
      funext j
      ext x
      simp only [G, add_apply, smulLeftCLM_apply_apply (hβ j),
        smulLeftCLM_apply_apply (hq j), q, sub_smul, one_smul]
      abel
    rw [heq]
    simpa only [add_zero] using! tendsto_const_nhds.add ht

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_SchwartzFirstMomentTails
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open SchwartzMap MeasureTheory Metric Filter Topology Set

theorem first_absolute_moment_bound_on_set {d : ℕ}
    (μ : Measure (Ambient d)) (g : Ambient d → ℂ) (hg : Integrable g μ)
    (hm : Integrable (fun y => ‖y‖ * ‖g y‖) μ)
    (s : Set (Ambient d)) (hs : MeasurableSet s) (R : ℝ) (hR : 0 < R)
    (hsep : ∀ y ∈ s, R ≤ ‖y‖) :
    (∫ y in s, ‖g y‖ ∂μ) ≤ (∫ y, ‖y‖ * ‖g y‖ ∂μ) / R := by
  calc
    _ ≤ ∫ y in s, (‖y‖ * ‖g y‖) / R ∂μ := by
      apply integral_mono_ae hg.norm.restrict (hm.div_const R).restrict
      filter_upwards [ae_restrict_mem hs] with y hy
      apply (le_div_iff₀ hR).2
      nlinarith [mul_le_mul_of_nonneg_right (hsep y hy) (norm_nonneg (g y))]
    _ = (∫ y in s, ‖y‖ * ‖g y‖ ∂μ) / R := integral_div R _
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ hR.le
      exact integral_mono_measure Measure.restrict_le_self
        (Filter.Eventually.of_forall fun y => mul_nonneg (norm_nonneg y) (norm_nonneg (g y))) hm

theorem schwartz_first_absolute_moment_integrable {d : ℕ} (g : 𝓢(Ambient d, ℂ)) :
    Integrable (fun y : Ambient d => ‖y‖ * ‖g y‖) := by
  simpa only [pow_one] using! g.integrable_pow_mul (volume : Measure (Ambient d)) 1

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_PolynomialDecayBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

theorem polynomial_decay_from_uniform_and_far_bound {d : ℕ} (q : ℕ)
    (f : Ambient d → ℂ) (U D : ℝ) (hU : 0 ≤ U) (hD : 0 ≤ D)
    (hu : ∀ x, ‖f x‖ ≤ U)
    (hd : ∀ x, 0 < ‖x‖ → ‖f x‖ ≤ D / ‖x‖ ^ q) (x : Ambient d) :
    ‖f x‖ ≤ (2 ^ q * (U + D)) * polynomialDecay q x := by
  rw [polynomialDecay, ← div_eq_mul_inv]
  apply (le_div_iff₀ (pow_pos (by positivity : 0 < 1 + ‖x‖) q)).2
  by_cases hx : 1 ≤ ‖x‖
  · have hp : 0 < ‖x‖ := lt_of_lt_of_le zero_lt_one hx
    have hb : (1 + ‖x‖) ^ q ≤ (2 * ‖x‖) ^ q :=
      pow_le_pow_left₀ (by positivity) (by linarith) q
    calc
      _ ≤ (D / ‖x‖ ^ q) * (2 * ‖x‖) ^ q :=
        mul_le_mul (hd x hp) hb (by positivity) (div_nonneg hD (by positivity))
      _ = 2 ^ q * D := by
        rw [mul_pow]
        field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith : D ≤ U + D) (by positivity)
  · have hb : (1 + ‖x‖) ^ q ≤ (2 : ℝ) ^ q :=
      pow_le_pow_left₀ (by positivity) (by linarith) q
    calc
      _ ≤ U * 2 ^ q := mul_le_mul (hu x) hb (by positivity) hU
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_left (by linarith : U ≤ U + D)
          (by positivity : 0 ≤ (2 : ℝ) ^ q)
        simpa only [mul_comm] using! hh

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_SchwartzMomentContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open SchwartzMap MeasureTheory Filter Topology

theorem schwartz_first_absolute_moment_seminorm_bound {d : ℕ} (g : 𝓢(Ambient d, ℂ)) :
    (∫ y : Ambient d, ‖y‖ * ‖g y‖) ≤
      2 ^ (volume : Measure (Ambient d)).integrablePower *
        (∫ y : Ambient d, (1 + ‖y‖) ^ (-((volume : Measure (Ambient d)).integrablePower : ℝ))) *
        (SchwartzMap.seminorm ℝ 0 0 g +
          SchwartzMap.seminorm ℝ (1 + (volume : Measure (Ambient d)).integrablePower) 0 g) := by
  simpa only [pow_one, norm_iteratedFDeriv_zero] using!
    SchwartzMap.integral_pow_mul_iteratedFDeriv_le ℝ (volume : Measure (Ambient d)) g 1 0

theorem schwartz_seminorm_tendsto_zero {d : ℕ} (G : ℕ → 𝓢(Ambient d, ℂ))
    (ht : Tendsto G atTop (𝓝 0)) (k n : ℕ) :
    Tendsto (fun j => SchwartzMap.seminorm ℝ k n (G j)) atTop (𝓝 0) := by
  simpa only [schwartzSeminormFamily_apply, map_zero] using!
    ((schwartz_withSeminorms ℝ (Ambient d) ℂ).continuous_seminorm (k, n)).tendsto 0 |>.comp ht

theorem schwartz_first_absolute_moment_tendsto_zero {d : ℕ}
    (G : ℕ → 𝓢(Ambient d, ℂ)) (ht : Tendsto G atTop (𝓝 0)) :
    Tendsto (fun j => ∫ y : Ambient d, ‖y‖ * ‖G j y‖) atTop (𝓝 0) := by
  let C := 2 ^ (volume : Measure (Ambient d)).integrablePower *
    (∫ y : Ambient d, (1 + ‖y‖) ^ (-((volume : Measure (Ambient d)).integrablePower : ℝ)))
  have h0 := schwartz_seminorm_tendsto_zero G ht 0 0
  have h1 := schwartz_seminorm_tendsto_zero G ht
    (1 + (volume : Measure (Ambient d)).integrablePower) 0
  have hb : Tendsto (fun j => C * (SchwartzMap.seminorm ℝ 0 0 (G j) +
      SchwartzMap.seminorm ℝ (1 + (volume : Measure (Ambient d)).integrablePower) 0 (G j)))
      atTop (𝓝 0) := by
    simpa only [add_zero, mul_zero] using! (h0.add h1).const_mul C
  exact squeeze_zero (fun j => integral_nonneg fun y => mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (fun j => schwartz_first_absolute_moment_seminorm_bound (G j)) hb

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_FarTestKernelBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter

theorem inverseDistancePow_bound_of_separation {d : ℕ} (q : ℕ)
    (x y : Ambient d) (R : ℝ) (hR : 0 < R) (hsep : R ≤ dist x y) :
    inverseDistancePow q x y ≤ (R ^ q)⁻¹ := by
  simpa only [inverseDistancePow, one_div] using!
    one_div_le_one_div_of_le (pow_pos hR q) (pow_le_pow_left₀ hR.le hsep q)

theorem subtracted_far_test_kernel_uniform_bound {d : ℕ} (m : ℕ)
    (x y : Ambient d) (R : ℝ) (hR : 0 < R) (hx : R ≤ ‖x‖)
    (hy : y ∈ closedExterior x R) :
    |inverseDistancePow (m + 1) x y - inverseDistancePow (m + 1) 0 x| ≤
      2 * (R ^ (m + 1))⁻¹ := by
  have ha := inverseDistancePow_bound_of_separation (m + 1) x y R hR hy
  have hb := inverseDistancePow_bound_of_separation (m + 1) 0 x R hR
    (by simpa only [dist_zero_left] using! hx)
  have hna := inverseDistancePow_nonneg (m + 1) x y
  have hnb := inverseDistancePow_nonneg (m + 1) 0 x
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem subtracted_far_test_kernel_central_bound {d : ℕ} (m : ℕ)
    (x y : Ambient d) (hx : 0 < ‖x‖) (hy : ‖y‖ ≤ ‖x‖ / 2) :
    |inverseDistancePow (m + 1) x y - inverseDistancePow (m + 1) 0 x| ≤
      (m + 1 : ℝ) * 2 ^ (m + 2) * ‖y‖ * inverseDistancePow (m + 2) 0 x := by
  have hh := inverseDistancePow_far_difference m (0 : Ambient d) y x
    (by simpa only [dist_zero_left] using! hx)
    (by simpa only [dist_zero_left, dist_zero_right] using! (show 2 * ‖y‖ ≤ ‖x‖ by linarith))
  simpa only [inverseDistancePow, dist_comm y x, dist_zero_right] using! hh

theorem subtracted_far_test_kernel_integrable {d : ℕ}
    (μ : Measure (Ambient d)) (g : Ambient d → ℂ) (hg : Integrable g μ)
    (m : ℕ) (x : Ambient d) (R : ℝ) (hR : 0 < R) (hx : R ≤ ‖x‖) :
    IntegrableOn (fun y => (inverseDistancePow (m + 1) x y - inverseDistancePow (m + 1) 0 x) • g y)
      (closedExterior x R) μ := by
  apply hg.restrict.bdd_smul (2 * (R ^ (m + 1))⁻¹)
    (((inverseDistancePow_measurable (m + 1) x).sub measurable_const).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem (closedExterior_measurable x R)] with y hy
  exact subtracted_far_test_kernel_uniform_bound m x y R hR hx hy

theorem raw_far_test_kernel_integrable {d : ℕ}
    (μ : Measure (Ambient d)) (g : Ambient d → ℂ) (hg : Integrable g μ)
    (m : ℕ) (x : Ambient d) (R : ℝ) (hR : 0 < R) :
    IntegrableOn (fun y => inverseDistancePow (m + 1) x y • g y) (closedExterior x R) μ := by
  apply hg.restrict.bdd_smul ((R ^ (m + 1))⁻¹)
    (inverseDistancePow_measurable (m + 1) x).aestronglyMeasurable
  filter_upwards [ae_restrict_mem (closedExterior_measurable x R)] with y hy
  rw [Real.norm_of_nonneg (inverseDistancePow_nonneg _ _ _)]
  exact inverseDistancePow_bound_of_separation (m + 1) x y R hR hy

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_SubtractedFarTestEstimate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# First-moment control of the subtracted far test

The far-region integral splits at the ball of radius `‖x‖ / 2` about the origin.
The central part uses the kernel difference estimate, while the outer part uses
the first absolute moment to gain the same decay of order `‖x‖ ^ (m + 2)`.
-/

namespace RieszRectifiability

noncomputable section

open SchwartzMap MeasureTheory Metric Filter Topology Set

theorem subtracted_far_test_integral_norm_bound {d : ℕ}
    (μ : Measure (Ambient d)) (g : Ambient d → ℂ) (hg : Integrable g μ)
    (hm : Integrable (fun y => ‖y‖ * ‖g y‖) μ) (m : ℕ)
    (x : Ambient d) (hx : 0 < ‖x‖) :
    (∫ y in closedExterior x (‖x‖ / 2),
      ‖(inverseDistancePow (m + 1) x y - inverseDistancePow (m + 1) 0 x) • g y‖ ∂μ) ≤
      (((m + 1 : ℝ) * 2 ^ (m + 2) + 2 ^ (m + 3)) *
        (∫ y, ‖y‖ * ‖g y‖ ∂μ)) / ‖x‖ ^ (m + 2) := by
  let R := ‖x‖ / 2
  let E := closedExterior x R
  let B := closedBall (0 : Ambient d) R
  let F := fun y => (inverseDistancePow (m + 1) x y - inverseDistancePow (m + 1) 0 x) • g y
  let M := ∫ y, ‖y‖ * ‖g y‖ ∂μ
  let D := (m + 1 : ℝ) * 2 ^ (m + 2) * inverseDistancePow (m + 2) 0 x
  let A := 2 * (R ^ (m + 1))⁻¹
  have hR : 0 < R := by dsimp [R] <;> positivity
  have hxR : R ≤ ‖x‖ := by dsimp [R] <;> linarith
  have hD : 0 ≤ D := mul_nonneg (by positivity) (inverseDistancePow_nonneg _ _ _)
  have hA : 0 ≤ A := by dsimp [A] <;> positivity
  have hF : IntegrableOn F E μ := subtracted_far_test_kernel_integrable μ g hg m x R hR hxR
  have hcentral : (∫ y in E ∩ B, ‖F y‖ ∂μ) ≤ D * M := by
    have hf : IntegrableOn (fun y => ‖F y‖) (E ∩ B) μ :=
      hF.norm.mono_measure (Measure.restrict_mono inter_subset_left le_rfl)
    have hmi := hm.restrict (s := E ∩ B)
    calc
      _ ≤ ∫ y in E ∩ B, D * (‖y‖ * ‖g y‖) ∂μ := by
        apply integral_mono_ae hf (hmi.const_mul D)
        filter_upwards [ae_restrict_mem ((closedExterior_measurable x R).inter measurableSet_closedBall)] with y hy
        have hyR : ‖y‖ ≤ ‖x‖ / 2 := by simpa only [B, mem_closedBall, dist_zero_right] using! hy.2
        have hb := subtracted_far_test_kernel_central_bound m x y hx hyR
        change ‖(inverseDistancePow (m + 1) x y - inverseDistancePow (m + 1) 0 x) • g y‖ ≤ _
        rw [RCLike.real_smul_eq_coe_mul, norm_mul, RCLike.norm_ofReal]
        calc
          _ ≤ ((m + 1 : ℝ) * 2 ^ (m + 2) * ‖y‖ * inverseDistancePow (m + 2) 0 x) * ‖g y‖ :=
            mul_le_mul_of_nonneg_right hb (norm_nonneg _)
          _ = _ := by dsimp [D] <;> ring
      _ = D * (∫ y in E ∩ B, ‖y‖ * ‖g y‖ ∂μ) := integral_const_mul _ _
      _ ≤ D * M := mul_le_mul_of_nonneg_left
        (integral_mono_measure Measure.restrict_le_self
          (Filter.Eventually.of_forall fun y => mul_nonneg (norm_nonneg y) (norm_nonneg (g y))) hm) hD
  have houter : (∫ y in E \ B, ‖F y‖ ∂μ) ≤ A * (M / R) := by
    have hf : IntegrableOn (fun y => ‖F y‖) (E \ B) μ :=
      hF.norm.mono_measure (Measure.restrict_mono sdiff_subset le_rfl)
    have hsep : ∀ y ∈ E \ B, R ≤ ‖y‖ := by
      intro y hy
      exact (lt_of_not_ge (by simpa only [B, mem_closedBall, dist_zero_right] using! hy.2)).le
    have ht := first_absolute_moment_bound_on_set μ g hg hm (E \ B)
      ((closedExterior_measurable x R).diff measurableSet_closedBall) R hR hsep
    calc
      _ ≤ ∫ y in E \ B, A * ‖g y‖ ∂μ := by
        apply integral_mono_ae hf (hg.norm.restrict.const_mul A)
        filter_upwards [ae_restrict_mem ((closedExterior_measurable x R).diff measurableSet_closedBall)] with y hy
        change ‖(inverseDistancePow (m + 1) x y - inverseDistancePow (m + 1) 0 x) • g y‖ ≤ _
        rw [RCLike.real_smul_eq_coe_mul, norm_mul, RCLike.norm_ofReal]
        exact mul_le_mul_of_nonneg_right (subtracted_far_test_kernel_uniform_bound m x y R hR hxR hy.1)
          (norm_nonneg _)
      _ = A * (∫ y in E \ B, ‖g y‖ ∂μ) := integral_const_mul _ _
      _ ≤ A * (M / R) := mul_le_mul_of_nonneg_left ht hA
  calc
    _ = (∫ y in E ∩ B, ‖F y‖ ∂μ) + ∫ y in E \ B, ‖F y‖ ∂μ :=
      (integral_inter_add_sdiff measurableSet_closedBall hF.norm).symm
    _ ≤ D * M + A * (M / R) := add_le_add hcentral houter
    _ = _ := by
      dsimp [D, A, R, M]
      simp only [inverseDistancePow, dist_zero_left, pow_add, div_pow]
      field_simp

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_MeanZeroFarTestEstimate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Mean-zero decay of the far test integral

Subtracting the kernel value at the origin exposes a first-moment bound.
The mean-zero hypothesis replaces the remaining far-region integral by its
complement, whose distance from the origin gives the same extra decay power.
-/

namespace RieszRectifiability

noncomputable section

open SchwartzMap MeasureTheory Metric Filter Topology Set

theorem mean_zero_far_test_integral_bound {d : ℕ}
    (μ : Measure (Ambient d)) (g : Ambient d → ℂ) (hg : Integrable g μ)
    (hm : Integrable (fun y => ‖y‖ * ‖g y‖) μ) (hmean : (∫ y, g y ∂μ) = 0)
    (m : ℕ) (x : Ambient d) (hx : 0 < ‖x‖) :
    ‖∫ y in closedExterior x (‖x‖ / 2), inverseDistancePow (m + 1) x y • g y ∂μ‖ ≤
      (((m + 1 : ℝ) * 2 ^ (m + 2) + 2 ^ (m + 3) + 2) *
        (∫ y, ‖y‖ * ‖g y‖ ∂μ)) / ‖x‖ ^ (m + 2) := by
  let R := ‖x‖ / 2
  let E := closedExterior x R
  let K := inverseDistancePow (m + 1) 0 x
  let F := fun y => (inverseDistancePow (m + 1) x y - K) • g y
  let M := ∫ y, ‖y‖ * ‖g y‖ ∂μ
  have hR : 0 < R := by dsimp [R] <;> positivity
  have hE : MeasurableSet E := closedExterior_measurable x R
  have hK : 0 ≤ K := inverseDistancePow_nonneg _ _ _
  have hF : IntegrableOn F E μ := subtracted_far_test_kernel_integrable μ g hg m x R hR
    (by dsimp [R] <;> linarith)
  have hmissing : (∫ y in Eᶜ, ‖g y‖ ∂μ) ≤ M / R := by
    apply first_absolute_moment_bound_on_set μ g hg hm Eᶜ hE.compl R hR
    intro y hy
    have hd : dist x y < R := by
      simpa only [E, closedExterior, mem_compl_iff, mem_ofPred_eq, not_le] using! hy
    have hn := norm_sub_norm_le x y
    rw [← dist_eq_norm] at hn
    dsimp [R] at hd ⊢
    linarith
  have hmeanE : (∫ y in E, g y ∂μ) = -(∫ y in Eᶜ, g y ∂μ) := by
    apply eq_neg_iff_add_eq_zero.mpr
    exact (integral_add_compl hE hg).trans hmean
  have hdecomp : (∫ y in E, inverseDistancePow (m + 1) x y • g y ∂μ) =
      (∫ y in E, F y ∂μ) + K • (∫ y in E, g y ∂μ) := by
    have heq : (fun y => inverseDistancePow (m + 1) x y • g y) = fun y => F y + K • g y := by
      funext y
      dsimp only [F]
      simp only [RCLike.real_smul_eq_coe_mul, map_sub]
      ring
    have hKg : IntegrableOn (fun y => K • g y) E μ := hg.restrict.smul K
    rw [heq, integral_add hF hKg]
    congr 1
    exact integral_smul K g
  have hsub := (norm_integral_le_integral_norm (μ := μ.restrict E) F).trans
    (subtracted_far_test_integral_norm_bound μ g hg hm m x hx)
  have hcorrection : ‖K • (-(∫ y in Eᶜ, g y ∂μ))‖ ≤ K * (M / R) := by
    rw [RCLike.real_smul_eq_coe_mul, norm_mul, RCLike.norm_ofReal, abs_of_nonneg hK, norm_neg]
    exact mul_le_mul_of_nonneg_left
      ((norm_integral_le_integral_norm (μ := μ.restrict Eᶜ) g).trans hmissing) hK
  rw [hdecomp, hmeanE]
  calc
    _ ≤ ‖∫ y in E, F y ∂μ‖ + ‖K • (-(∫ y in Eᶜ, g y ∂μ))‖ := norm_add_le _ _
    _ ≤ (((m + 1 : ℝ) * 2 ^ (m + 2) + 2 ^ (m + 3)) * M) / ‖x‖ ^ (m + 2) + K * (M / R) :=
      add_le_add hsub hcorrection
    _ = _ := by
      dsimp [K, R, M]
      simp only [inverseDistancePow, dist_zero_left, pow_add]
      field_simp

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_TranslatedFarTestIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open SchwartzMap MeasureTheory Metric Set

theorem far_kernel_add_translation {d : ℕ} (m : ℕ) (g : Ambient d → ℂ)
    (x : Ambient d) (R : ℝ) :
    (IntegrableOn (fun h => inverseDistancePow (m + 1) 0 h • g (x + h)) (closedExterior 0 R) ↔
      IntegrableOn (fun y => inverseDistancePow (m + 1) x y • g y) (closedExterior x R)) ∧
    (∫ h in closedExterior 0 R, inverseDistancePow (m + 1) 0 h • g (x + h)) =
      ∫ y in closedExterior x R, inverseDistancePow (m + 1) x y • g y := by
  have hp := measurePreserving_add_left (volume : Measure (Ambient d)) x
  have he := (MeasurableEquiv.addLeft x).measurableEmbedding
  have hs : (fun h => x + h) ⁻¹' closedExterior x R = closedExterior 0 R := by
    ext h
    simp [closedExterior, dist_eq_norm]
  have hk : ∀ h : Ambient d, inverseDistancePow (m + 1) x (x + h) = inverseDistancePow (m + 1) 0 h := by
    intro h
    simp [inverseDistancePow, dist_eq_norm]
  constructor
  · simpa only [hs, Function.comp_def, hk] using! hp.integrableOn_comp_preimage he
      (f := fun y => inverseDistancePow (m + 1) x y • g y) (s := closedExterior x R)
  · simpa only [hs, hk] using! hp.setIntegral_preimage_emb he
      (fun y => inverseDistancePow (m + 1) x y • g y) (closedExterior x R)

theorem far_kernel_sub_translation {d : ℕ} (m : ℕ) (g : Ambient d → ℂ)
    (x : Ambient d) (R : ℝ) :
    (IntegrableOn (fun h => inverseDistancePow (m + 1) 0 h • g (x - h)) (closedExterior 0 R) ↔
      IntegrableOn (fun y => inverseDistancePow (m + 1) x y • g y) (closedExterior x R)) ∧
    (∫ h in closedExterior 0 R, inverseDistancePow (m + 1) 0 h • g (x - h)) =
      ∫ y in closedExterior x R, inverseDistancePow (m + 1) x y • g y := by
  have hp := (volume : Measure (Ambient d)).measurePreserving_sub_left x
  have he := (MeasurableEquiv.subLeft x).measurableEmbedding
  have hs : (fun h => x - h) ⁻¹' closedExterior x R = closedExterior 0 R := by
    ext h
    simp [closedExterior, dist_eq_norm]
  have hk : ∀ h : Ambient d, inverseDistancePow (m + 1) x (x - h) = inverseDistancePow (m + 1) 0 h := by
    intro h
    simp [inverseDistancePow, dist_eq_norm]
  constructor
  · simpa only [hs, Function.comp_def, hk] using! hp.integrableOn_comp_preimage he
      (f := fun y => inverseDistancePow (m + 1) x y • g y) (s := closedExterior x R)
  · simpa only [hs, hk] using! hp.setIntegral_preimage_emb he
      (fun y => inverseDistancePow (m + 1) x y • g y) (closedExterior x R)

theorem fractionalSchwartz_far_integral_identity (p : ℕ) (g : 𝓢(Ambient (p + 1), ℂ))
    (x : Ambient (p + 1)) (R : ℝ) (hR : 0 < R) :
    (-1 / 2 : ℝ) • (∫ h in closedExterior 0 R, fractionalSchwartzKernel (p + 1) g x h) =
      (∫ h in closedExterior (0 : Ambient (p + 1)) R, inverseDistancePow (p + 1 + 1) 0 h) • g x -
        ∫ y in closedExterior x R, inverseDistancePow (p + 1 + 1) x y • g y := by
  obtain ⟨hplus, heqplus⟩ := far_kernel_add_translation (p + 1) g x R
  obtain ⟨hminus, heqminus⟩ := far_kernel_sub_translation (p + 1) g x R
  have hr := raw_far_test_kernel_integrable volume g g.integrable (p + 1) x R hR
  have hp := hplus.mpr hr
  have hm := hminus.mpr hr
  have hk := (inverseDistancePow_closedExterior_integrable_and_bound (d := p + 1) (p + 1) _ volume
    (volume_global_upper_growth (p + 1)) 0 R hR).1
  have hc := hk.smul_const (g x)
  have heq : fractionalSchwartzKernel (p + 1) g x = fun h =>
      (inverseDistancePow (p + 1 + 1) 0 h • g (x + h) +
        inverseDistancePow (p + 1 + 1) 0 h • g (x - h)) -
      (2 : ℝ) • (inverseDistancePow (p + 1 + 1) 0 h • g x) := by
    funext h
    change inverseDistancePow (p + 1 + 1) 0 h •
      (g (x + h) + g (x - h) - (2 : ℝ) • g x) = _
    exact (smul_sub (inverseDistancePow (p + 1 + 1) 0 h)
      (g (x + h) + g (x - h)) ((2 : ℝ) • g x)).trans
      (congrArg₂ (fun a b : ℂ => a - b)
        (smul_add (inverseDistancePow (p + 1 + 1) 0 h) (g (x + h)) (g (x - h)))
        (smul_comm (inverseDistancePow (p + 1 + 1) 0 h) (2 : ℝ) (g x)))
  have hpm : IntegrableOn (fun h => inverseDistancePow (p + 1 + 1) 0 h • g (x + h) +
      inverseDistancePow (p + 1 + 1) 0 h • g (x - h)) (closedExterior 0 R) := hp.add hm
  have hcc : IntegrableOn (fun h : Ambient (p + 1) =>
      (2 : ℝ) • (inverseDistancePow (p + 1 + 1) 0 h • g x))
      (closedExterior 0 R) := hc.smul (2 : ℝ)
  have hci : (∫ h in closedExterior (0 : Ambient (p + 1)) R,
      (2 : ℝ) • (inverseDistancePow (p + 1 + 1) 0 h • g x)) =
      (2 : ℝ) • ((∫ h in closedExterior (0 : Ambient (p + 1)) R,
        inverseDistancePow (p + 1 + 1) 0 h) • g x) := by
    calc
      _ = (2 : ℝ) • (∫ h in closedExterior (0 : Ambient (p + 1)) R,
          inverseDistancePow (p + 1 + 1) 0 h • g x) := integral_smul (2 : ℝ) _
      _ = _ := congrArg (fun z : ℂ => (2 : ℝ) • z)
        (integral_smul_const (inverseDistancePow (p + 1 + 1) (0 : Ambient (p + 1))) (g x))
  rw [heq, integral_sub hpm hcc, integral_add hp hm, hci, heqplus, heqminus]
  norm_num [RCLike.real_smul_eq_coe_mul]
  ring

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Rigidity_FractionalFarSpatialDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open SchwartzMap MeasureTheory Metric Set

theorem far_kernel_mass_times_schwartz_value {d : ℕ} (m : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) (hgrowth : GlobalUpperGrowth m C μ)
    (g : 𝓢(Ambient d, ℂ)) (x : Ambient d) (hx : 0 < ‖x‖) :
    ‖(∫ h in closedExterior (0 : Ambient d) (‖x‖ / 2),
      inverseDistancePow (m + 1) 0 h ∂μ) • g x‖ ≤
      (4 * C * 2 ^ m * SchwartzMap.seminorm ℝ (m + 1) 0 g) / ‖x‖ ^ (m + 2) := by
  have hR : 0 < ‖x‖ / 2 := by positivity
  have hC := hgrowth.1
  have hI : 0 ≤ ∫ h in closedExterior (0 : Ambient d) (‖x‖ / 2),
      inverseDistancePow (m + 1) 0 h ∂μ := integral_nonneg fun h => inverseDistancePow_nonneg _ _ _
  have htail := (inverseDistancePow_closedExterior_integrable_and_bound m C μ
    hgrowth 0 (‖x‖ / 2) hR).2
  have hg : ‖g x‖ ≤ SchwartzMap.seminorm ℝ (m + 1) 0 g / ‖x‖ ^ (m + 1) := by
    apply (le_div_iff₀ (pow_pos hx _)).2
    simpa only [mul_comm] using! SchwartzMap.norm_pow_mul_le_seminorm ℝ g (m + 1) x
  rw [RCLike.real_smul_eq_coe_mul, norm_mul, RCLike.norm_ofReal, abs_of_nonneg hI]
  calc
    _ ≤ (2 * (C * 2 ^ m / (‖x‖ / 2))) *
        (SchwartzMap.seminorm ℝ (m + 1) 0 g / ‖x‖ ^ (m + 1)) :=
      mul_le_mul htail hg (norm_nonneg _) (by positivity)
    _ = _ := by
      simp only [pow_add]
      field_simp
      ring

theorem fractionalSchwartz_far_spatial_decay (p : ℕ) (g : 𝓢(Ambient (p + 1), ℂ))
    (hmean : (∫ y, g y) = 0) (x : Ambient (p + 1)) (hx : 0 < ‖x‖) :
    ‖(-1 / 2 : ℝ) • (∫ h in closedExterior 0 (‖x‖ / 2),
      fractionalSchwartzKernel (p + 1) g x h)‖ ≤
      (4 * (((volume : Measure (Ambient (p + 1))) (ball 0 1)).toReal) * 2 ^ (p + 1) *
          SchwartzMap.seminorm ℝ (p + 2) 0 g +
        (((p + 1 : ℝ) + 1) * 2 ^ (p + 3) + 2 ^ (p + 4) + 2) *
          (∫ y : Ambient (p + 1), ‖y‖ * ‖g y‖)) / ‖x‖ ^ (p + 3) := by
  rw [fractionalSchwartz_far_integral_identity p g x (‖x‖ / 2) (by positivity)]
  have hmass := far_kernel_mass_times_schwartz_value (p + 1) _ volume
    (volume_global_upper_growth (p + 1)) g x hx
  have hraw := mean_zero_far_test_integral_bound volume g g.integrable
    (schwartz_first_absolute_moment_integrable g) hmean (p + 1) x hx
  have hn := norm_sub_le
    ((∫ h in closedExterior (0 : Ambient (p + 1)) (‖x‖ / 2),
      inverseDistancePow (p + 1 + 1) 0 h) • g x)
    (∫ y in closedExterior x (‖x‖ / 2), inverseDistancePow (p + 1 + 1) x y • g y)
  simpa only [Nat.add_assoc, Nat.cast_add, Nat.cast_one, ← add_div] using!
    hn.trans (add_le_add hmass hraw)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_LocalSchwartzSecondDifference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open SchwartzMap MeasureTheory Metric Filter Topology Set
open scoped NNReal

variable {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem first_order_remainder_from_segment_hessian
    (g : Ambient d → F) (hg : Differentiable ℝ g)
    (hdg : Differentiable ℝ (fderiv ℝ g)) (M : ℝ) (hM : 0 ≤ M)
    (x h : Ambient d)
    (hbound : ∀ z ∈ segment ℝ x (x + h), ‖fderiv ℝ (fderiv ℝ g) z‖ ≤ M) :
    ‖g (x + h) - g x - fderiv ℝ g x h‖ ≤ M * ‖h‖ ^ 2 := by
  have hgrad : ∀ z ∈ segment ℝ x (x + h),
      ‖fderiv ℝ g z - fderiv ℝ g x‖ ≤ M * ‖h‖ := by
    intro z hz
    have hh := (convex_segment x (x + h)).norm_image_sub_le_of_norm_fderiv_le
      (fun y _ => hdg y) hbound (left_mem_segment ℝ x (x + h)) hz
    calc
      _ ≤ M * ‖z - x‖ := hh
      _ ≤ M * ‖h‖ := mul_le_mul_of_nonneg_left
        (by simpa only [add_sub_cancel_left] using! norm_sub_le_of_mem_segment hz) hM
  have hh := (convex_segment x (x + h)).norm_image_sub_le_of_norm_fderiv_le'
    (fun y _ => hg y) hgrad (left_mem_segment ℝ x (x + h)) (right_mem_segment ℝ x (x + h))
  simpa only [add_sub_cancel_left, pow_two, mul_assoc] using! hh

theorem schwartz_hessian_bound_on_short_segment
    (g : 𝓢(Ambient d, F)) (k : ℕ) (x h : Ambient d) (hx : 0 < ‖x‖)
    (hh : ‖h‖ ≤ ‖x‖ / 2) (z : Ambient d) (hz : z ∈ segment ℝ x (x + h)) :
    ‖fderiv ℝ (fderiv ℝ g) z‖ ≤ SchwartzMap.seminorm ℝ k 2 g / (‖x‖ / 2) ^ k := by
  have hzx : ‖z - x‖ ≤ ‖h‖ := by
    simpa only [add_sub_cancel_left] using! norm_sub_le_of_mem_segment hz
  have hnorm := norm_sub_norm_le x z
  rw [norm_sub_rev x z] at hnorm
  have hzlow : ‖x‖ / 2 ≤ ‖z‖ := by linarith
  have hbase : 0 < ‖x‖ / 2 := by positivity
  have he : ‖fderiv ℝ (fderiv ℝ g) z‖ = ‖iteratedFDeriv ℝ 2 g z‖ := by
    rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
  rw [he]
  apply (le_div_iff₀ (pow_pos hbase k)).2
  calc
    _ = (‖x‖ / 2) ^ k * ‖iteratedFDeriv ℝ 2 g z‖ := mul_comm _ _
    _ ≤ ‖z‖ ^ k * ‖iteratedFDeriv ℝ 2 g z‖ := by gcongr
    _ ≤ _ := le_seminorm ℝ k 2 g z

theorem schwartz_second_difference_spatial_bound
    (g : 𝓢(Ambient d, F)) (k : ℕ) (x h : Ambient d) (hx : 0 < ‖x‖)
    (hh : ‖h‖ ≤ ‖x‖ / 2) :
    ‖symmetricSecondDifference g x h‖ ≤
      2 * (SchwartzMap.seminorm ℝ k 2 g / (‖x‖ / 2) ^ k) * ‖h‖ ^ 2 := by
  let M := SchwartzMap.seminorm ℝ k 2 g / (‖x‖ / 2) ^ k
  have hM : 0 ≤ M := by dsimp [M] <;> positivity
  have hdg : Differentiable ℝ (fderiv ℝ g) :=
    (fderivCLM ℝ (Ambient d) F g).differentiable
  have hp := first_order_remainder_from_segment_hessian g g.differentiable hdg M hM x h
    (schwartz_hessian_bound_on_short_segment g k x h hx hh)
  have hn : ‖-h‖ ≤ ‖x‖ / 2 := by simpa only [norm_neg] using! hh
  have hm := first_order_remainder_from_segment_hessian g g.differentiable hdg M hM x (-h)
    (schwartz_hessian_bound_on_short_segment g k x (-h) hx hn)
  have heq : symmetricSecondDifference g x h =
      (g (x + h) - g x - fderiv ℝ g x h) +
      (g (x + -h) - g x - fderiv ℝ g x (-h)) := by
    simp only [symmetricSecondDifference, map_neg, sub_eq_add_neg, two_smul]
    abel
  rw [heq]
  calc
    _ ≤ ‖g (x + h) - g x - fderiv ℝ g x h‖ +
        ‖g (x + -h) - g x - fderiv ℝ g x (-h)‖ := norm_add_le _ _
    _ ≤ M * ‖h‖ ^ 2 + M * ‖-h‖ ^ 2 := add_le_add hp hm
    _ = _ := by rw [norm_neg]; ring

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Rigidity_FractionalNearSpatialDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open SchwartzMap MeasureTheory Metric Filter Topology Set
open scoped NNReal ENNReal

theorem fractional_kernel_bound_from_quadratic_difference {d : ℕ}
    (p : ℕ) (g : Ambient d → ℂ) (x h : Ambient d) (M : ℝ) (hM : 0 ≤ M)
    (hb : ‖symmetricSecondDifference g x h‖ ≤ M * ‖h‖ ^ 2) :
    ‖fractionalSchwartzKernel (p + 1) g x h‖ ≤ M * inverseDistancePow p 0 h := by
  rw [fractionalSchwartzKernel, norm_smul,
    Real.norm_of_nonneg (inverseDistancePow_nonneg _ _ _)]
  by_cases hh : h = 0
  · subst h
    simp only [inverseDistancePow, dist_self, zero_pow (by omega : p + 1 + 1 ≠ 0), inv_zero, zero_mul]
    positivity
  · have hn : ‖h‖ ≠ 0 := norm_ne_zero_iff.mpr hh
    calc
      _ ≤ inverseDistancePow (p + 1 + 1) 0 h * (M * ‖h‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hb (inverseDistancePow_nonneg _ _ _)
      _ = _ := by
        simp only [inverseDistancePow, dist_zero_left, pow_succ]
        field_simp

theorem fractionalSchwartzKernel_near_spatial_decay {d : ℕ}
    (p : ℕ) (C : ℝ) (μ : Measure (Ambient d)) (hgrowth : GlobalUpperGrowth (p + 1) C μ)
    (g : 𝓢(Ambient d, ℂ)) (x : Ambient d) (hx : 0 < ‖x‖) :
    (∫ h in closedBall 0 (‖x‖ / 2), ‖fractionalSchwartzKernel (p + 1) g x h‖ ∂μ) ≤
      (4 * (C * 2 ^ (p + 1) * 2 ^ p) * 2 ^ (p + 3) *
        SchwartzMap.seminorm ℝ (p + 4) 2 g) / ‖x‖ ^ (p + 3) := by
  let R := ‖x‖ / 2
  let M := SchwartzMap.seminorm ℝ (p + 4) 2 g / R ^ (p + 4)
  have hR : 0 < R := by dsimp [R] <;> positivity
  have hM : 0 ≤ M := by dsimp [M] <;> positivity
  have hK := fractionalSchwartzKernel_integrable_of_growth p C μ hgrowth g x
  obtain ⟨hi, _⟩ := inverseDistancePow_near_integrable_and_bound p C μ hgrowth 0 R hR
  have hb' : (∫ h in closedBall 0 R, inverseDistancePow p 0 h ∂μ) ≤
      2 * (C * 2 ^ (p + 1) * 2 ^ p * R) :=
    inverseDistancePow_near_integral_bound p C μ hgrowth 0 R hR
  calc
    _ ≤ ∫ h in closedBall 0 R, (2 * M) * inverseDistancePow p 0 h ∂μ := by
      apply integral_mono_ae hK.norm.restrict (hi.const_mul _)
      filter_upwards [ae_restrict_mem measurableSet_closedBall] with h hh
      have hh' : ‖h‖ ≤ ‖x‖ / 2 := by simpa only [mem_closedBall, dist_zero_right] using! hh
      exact fractional_kernel_bound_from_quadratic_difference p g x h (2 * M) (by positivity)
        (schwartz_second_difference_spatial_bound g (p + 4) x h hx hh')
    _ = (2 * M) * ∫ h in closedBall 0 R, inverseDistancePow p 0 h ∂μ := integral_const_mul _ _
    _ ≤ (2 * M) * (2 * (C * 2 ^ (p + 1) * 2 ^ p * R)) :=
      mul_le_mul_of_nonneg_left hb' (by positivity)
    _ = _ := by
      dsimp [M, R]
      simp only [pow_add, div_pow]
      field_simp
      ring

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_MeanZeroSchwartzApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open SchwartzMap MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform

theorem unitSmoothCutoff_integral_pos (d : ℕ) :
    0 < ∫ x : Ambient d, unitSmoothCutoff d x := by
  have hc := ((unitSmoothCutoff d).contDiff (n := ⊤)).continuous
  have hi : Integrable (unitSmoothCutoff d) (volume : Measure (Ambient d)) :=
    hc.integrable_of_hasCompactSupport (unitSmoothCutoff d).hasCompactSupport
  apply integral_pos_of_integrable_nonneg_nonzero hc hi
    (fun x => (unitSmoothCutoff d).nonneg' x)
  have h : unitSmoothCutoff d (0 : Ambient d) = 1 :=
    (unitSmoothCutoff d).one_of_mem_closedBall (by simp [unitSmoothCutoff])
  exact h.trans_ne one_ne_zero

theorem exists_compact_complex_schwartz_unit_integral (d : ℕ) :
    ∃ η : 𝓢(Ambient d, ℂ), HasCompactSupport η ∧ (∫ x, η x) = 1 := by
  let b : Ambient d → ℂ := fun x => (unitSmoothCutoff d x : ℂ)
  have hb : HasCompactSupport b := (unitSmoothCutoff d).hasCompactSupport.comp_left
    (g := fun r : ℝ => (r : ℂ)) Complex.ofReal_zero
  have hs : ContDiff ℝ ∞ b := Complex.ofRealCLM.contDiff.comp
    ((unitSmoothCutoff d).contDiff (n := ⊤))
  let B : 𝓢(Ambient d, ℂ) := hb.toSchwartzMap hs
  have hc : HasCompactSupport B := hb
  have hI : (∫ x, B x) ≠ 0 := by
    change (∫ x : Ambient d, (unitSmoothCutoff d x : ℂ)) ≠ 0
    rw [integral_complex_ofReal]
    exact_mod_cast ne_of_gt (unitSmoothCutoff_integral_pos d)
  refine ⟨(∫ x, B x)⁻¹ • B, ?_, ?_⟩
  · exact hc.smul_left
  · change (∫ x, (∫ y, B y)⁻¹ • B x) = 1
    rw [integral_smul, smul_eq_mul, inv_mul_cancel₀ hI]

theorem exists_compact_mean_zero_schwartz_approximation {d : ℕ}
    (g : 𝓢(Ambient d, ℂ)) (hg : (∫ x, g x) = 0) :
    ∃ G : ℕ → 𝓢(Ambient d, ℂ),
      (∀ j, HasCompactSupport (G j) ∧ (∫ x, G j x) = 0) ∧ Tendsto G atTop (𝓝 g) := by
  obtain ⟨G, hc, ht⟩ := exists_compact_schwartz_approximation g
  obtain ⟨η, hcη, hη⟩ := exists_compact_complex_schwartz_unit_integral d
  let I : 𝓢(Ambient d, ℂ) →L[ℂ] ℂ := integralCLM ℂ volume
  let H : ℕ → 𝓢(Ambient d, ℂ) := fun j => G j - I (G j) • η
  have hIη : I η = 1 := hη
  have hIg : I g = 0 := hg
  refine ⟨H, ?_, ?_⟩
  · intro j
    refine ⟨(hc j).sub hcη.smul_left, ?_⟩
    change I (G j - I (G j) • η) = 0
    rw [map_sub, map_smul, hIη, smul_eq_mul, mul_one, sub_self]
  · have hi : Tendsto (fun j => I (G j)) atTop (𝓝 0) := by
      simpa only [hIg] using! I.continuous.tendsto g |>.comp ht
    have hs := hi.smul (tendsto_const_nhds (x := η))
    simpa only [zero_smul, sub_zero] using! ht.sub hs

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Rigidity_FractionalSchwartzContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Continuity of fractional Schwartz tests

The integral defining a fractional Schwartz test respects addition and scalar
multiplication. Uniform seminorm bounds control these tests and support their
continuity under Schwartz approximation.
-/

namespace RieszRectifiability

noncomputable section

open SchwartzMap MeasureTheory Metric Filter Topology
open scoped NNReal ENNReal

theorem fractionalSchwartzTest_measurable (p : ℕ) (g : 𝓢(Ambient (p + 1), ℂ)) :
    Measurable (fractionalSchwartzTest p g) := by
  have hm : Measurable (fun q : Ambient (p + 1) × Ambient (p + 1) =>
      fractionalSchwartzKernel (p + 1) g q.1 q.2) := by
    unfold fractionalSchwartzKernel symmetricSecondDifference inverseDistancePow
    fun_prop
  unfold fractionalSchwartzTest
  simp_rw [RCLike.real_smul_eq_coe_mul]
  exact measurable_const.mul (hm.stronglyMeasurable.integral_prod_right'
    (ν := (volume : Measure (Ambient (p + 1))))).measurable

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Rigidity_FractionalSpatialDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open SchwartzMap MeasureTheory Metric Set

theorem fractionalSchwartzDecaySize_nonneg (p : ℕ) (g : 𝓢(Ambient (p + 1), ℂ)) :
    0 ≤ fractionalSchwartzDecaySize p g := by
  unfold fractionalSchwartzDecaySize
  positivity

theorem fractionalSchwartzTest_spatial_decay (p : ℕ) (g : 𝓢(Ambient (p + 1), ℂ))
    (hmean : (∫ y, g y) = 0) (x : Ambient (p + 1)) (hx : 0 < ‖x‖) :
    ‖fractionalSchwartzTest p g x‖ ≤ fractionalSchwartzDecaySize p g / ‖x‖ ^ (p + 3) := by
  let C := ((volume : Measure (Ambient (p + 1))) (ball 0 1)).toReal
  let N := 4 * (C * 2 ^ (p + 1) * 2 ^ p) * 2 ^ (p + 3) *
    SchwartzMap.seminorm ℝ (p + 4) 2 g
  let R := ‖x‖ / 2
  let K := fractionalSchwartzKernel (p + 1) g x
  have hi : Integrable K := fractionalSchwartzKernel_integrable p g x
  have hsplit : (∫ h, K h) = (∫ h in ball 0 R, K h) +
      (∫ h in closedExterior 0 R, K h) := by
    rw [closedExterior_eq_compl_ball]
    exact (integral_add_compl measurableSet_ball hi).symm
  have hnear : ‖(-1 / 2 : ℝ) • (∫ h in ball 0 R, K h)‖ ≤ N / ‖x‖ ^ (p + 3) := by
    calc
      _ ≤ ‖∫ h in ball 0 R, K h‖ := by
        rw [RCLike.real_smul_eq_coe_mul, norm_mul, RCLike.norm_ofReal]
        norm_num
        linarith [norm_nonneg (∫ h in ball 0 R, K h)]
      _ ≤ ∫ h in ball 0 R, ‖K h‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ h in closedBall 0 R, ‖K h‖ :=
        integral_mono_measure (Measure.restrict_mono ball_subset_closedBall le_rfl)
          (Filter.Eventually.of_forall fun h => norm_nonneg (K h)) hi.norm.restrict
      _ ≤ _ := fractionalSchwartzKernel_near_spatial_decay p C volume
        (volume_global_upper_growth (p + 1)) g x hx
  have hfar := fractionalSchwartz_far_spatial_decay p g hmean x hx
  have he : fractionalSchwartzTest p g x =
      (-1 / 2 : ℝ) • (∫ h in ball 0 R, K h) +
      (-1 / 2 : ℝ) • (∫ h in closedExterior 0 R, K h) := by
    change (-1 / 2 : ℝ) • (∫ h, K h) = _
    rw [hsplit]
    exact smul_add (-1 / 2 : ℝ) _ _
  rw [he]
  calc
    _ ≤ ‖(-1 / 2 : ℝ) • (∫ h in ball 0 R, K h)‖ +
        ‖(-1 / 2 : ℝ) • (∫ h in closedExterior 0 R, K h)‖ := norm_add_le _ _
    _ ≤ _ := by
      have hh := add_le_add hnear hfar
      simpa only [← add_div, N, C, fractionalSchwartzDecaySize] using! hh

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Rigidity_FractionalWeightedDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open SchwartzMap MeasureTheory Metric Filter Topology

theorem fractionalSchwartzTest_polynomial_decay (p : ℕ) (g : 𝓢(Ambient (p + 1), ℂ))
    (hmean : (∫ y, g y) = 0) (x : Ambient (p + 1)) :
    ‖fractionalSchwartzTest p g x‖ ≤
      fractionalSchwartzWeightedSize p g * polynomialDecay (p + 3) x := by
  apply polynomial_decay_from_uniform_and_far_bound (p + 3) (fractionalSchwartzTest p g)
    (fractionalSchwartzUniformSize p g) (fractionalSchwartzDecaySize p g)
  · unfold fractionalSchwartzUniformSize
    positivity
  · exact fractionalSchwartzDecaySize_nonneg p g
  · exact fractionalSchwartzTest_uniform_bound p g
  · exact fractionalSchwartzTest_spatial_decay p g hmean

theorem fractionalSchwartzWeightedSize_tendsto_zero (p : ℕ)
    (G : ℕ → 𝓢(Ambient (p + 1), ℂ)) (ht : Tendsto G atTop (𝓝 0)) :
    Tendsto (fun j => fractionalSchwartzWeightedSize p (G j)) atTop (𝓝 0) := by
  let C := ((volume : Measure (Ambient (p + 1))) (ball 0 1)).toReal
  have hsem := schwartz_seminorm_tendsto_zero G ht
  have hmoment := schwartz_first_absolute_moment_tendsto_zero G ht
  have hU : Tendsto (fun j => fractionalSchwartzUniformSize p (G j)) atTop (𝓝 0) := by
    simpa only [fractionalSchwartzUniformSize, C, mul_zero, add_zero] using!
      ((hsem 0 2).const_mul (4 * (C * 2 ^ (p + 1) * 2 ^ p))).add
        ((hsem 0 0).const_mul (8 * (C * 2 ^ (p + 1))))
  have hD : Tendsto (fun j => fractionalSchwartzDecaySize p (G j)) atTop (𝓝 0) := by
    simpa only [fractionalSchwartzDecaySize, C, mul_zero, add_zero] using!
      ((hsem (p + 4) 2).const_mul (4 * (C * 2 ^ (p + 1) * 2 ^ p) * 2 ^ (p + 3))).add
        (((hsem (p + 2) 0).const_mul (4 * C * 2 ^ (p + 1))).add
          (hmoment.const_mul (((p + 1 : ℝ) + 1) * 2 ^ (p + 3) + 2 ^ (p + 4) + 2)))
  simpa only [fractionalSchwartzWeightedSize, add_zero, mul_zero] using!
    (hU.add hD).const_mul ((2 : ℝ) ^ (p + 3))

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Rigidity_FractionalHeightPairingContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open SchwartzMap MeasureTheory Metric Filter Topology

theorem height_fractional_test_integrable_and_bound (p : ℕ)
    (μ : Measure (Ambient (p + 1))) (f : Ambient (p + 1) → ℝ) (hf : Measurable f)
    (hweight : Integrable (fun x => |f x| * polynomialDecay (p + 3) x) μ)
    (g : 𝓢(Ambient (p + 1), ℂ)) (hmean : (∫ y, g y) = 0) :
    Integrable (fun x => f x • fractionalSchwartzTest p g x) μ ∧
      ‖∫ x, f x • fractionalSchwartzTest p g x ∂μ‖ ≤
        fractionalSchwartzWeightedSize p g * (∫ x, |f x| * polynomialDecay (p + 3) x ∂μ) := by
  let W := fractionalSchwartzWeightedSize p g
  have hm : Measurable (fun x => f x • fractionalSchwartzTest p g x) := by
    simp_rw [RCLike.real_smul_eq_coe_mul]
    exact (Complex.continuous_ofReal.measurable.comp hf).mul (fractionalSchwartzTest_measurable p g)
  have hb (x : Ambient (p + 1)) : ‖f x • fractionalSchwartzTest p g x‖ ≤
      W * (|f x| * polynomialDecay (p + 3) x) := by
    rw [RCLike.real_smul_eq_coe_mul, norm_mul, RCLike.norm_ofReal]
    calc
      _ ≤ |f x| * (W * polynomialDecay (p + 3) x) :=
        mul_le_mul_of_nonneg_left (fractionalSchwartzTest_polynomial_decay p g hmean x) (abs_nonneg _)
      _ = _ := by ring
  have hi : Integrable (fun x => W * (|f x| * polynomialDecay (p + 3) x)) μ := hweight.const_mul W
  have hp : Integrable (fun x => f x • fractionalSchwartzTest p g x) μ :=
    hi.mono' hm.aestronglyMeasurable (Eventually.of_forall hb)
  refine ⟨hp, ?_⟩
  calc
    _ ≤ ∫ x, ‖f x • fractionalSchwartzTest p g x‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, W * (|f x| * polynomialDecay (p + 3) x) ∂μ := integral_mono hp.norm hi hb
    _ = _ := integral_const_mul W _

theorem height_fractional_test_integral_tendsto (p : ℕ)
    (μ : Measure (Ambient (p + 1))) (f : Ambient (p + 1) → ℝ) (hf : Measurable f)
    (hweight : Integrable (fun x => |f x| * polynomialDecay (p + 3) x) μ)
    (G : ℕ → 𝓢(Ambient (p + 1), ℂ)) (g : 𝓢(Ambient (p + 1), ℂ))
    (ht : Tendsto G atTop (𝓝 g)) (hG : ∀ j, (∫ y, G j y) = 0) (hg : (∫ y, g y) = 0) :
    Tendsto (fun j => ∫ x, f x • fractionalSchwartzTest p (G j) x ∂μ)
      atTop (𝓝 (∫ x, f x • fractionalSchwartzTest p g x ∂μ)) := by
  let H := fun j => G j - g
  have hHt : Tendsto H atTop (𝓝 0) := by
    simpa only [sub_self] using! ht.sub (tendsto_const_nhds (x := g))
  have hHm (j : ℕ) : (∫ y, H j y) = 0 := by
    change (∫ y, G j y - g y) = 0
    rw [integral_sub (G j).integrable g.integrable, hG j, hg, sub_self]
  have hIG (j : ℕ) := (height_fractional_test_integrable_and_bound p μ f hf hweight (G j) (hG j)).1
  have hIg := (height_fractional_test_integrable_and_bound p μ f hf hweight g hg).1
  have hdiff (j : ℕ) : (∫ x, f x • fractionalSchwartzTest p (G j) x ∂μ) -
      (∫ x, f x • fractionalSchwartzTest p g x ∂μ) =
      ∫ x, f x • fractionalSchwartzTest p (H j) x ∂μ := by
    refine (integral_sub (hIG j) hIg).symm.trans (integral_congr_ae (Eventually.of_forall ?_))
    intro x
    calc
      _ = f x • (fractionalSchwartzTest p (G j) x - fractionalSchwartzTest p g x) :=
        (smul_sub (f x) (fractionalSchwartzTest p (G j) x) (fractionalSchwartzTest p g x)).symm
      _ = _ := congrArg (fun z : ℂ => f x • z)
        ((fractionalSchwartzTestCLM p x).map_sub (G j) g).symm
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hb (j : ℕ) :
      ‖(∫ x, f x • fractionalSchwartzTest p (G j) x ∂μ) -
        (∫ x, f x • fractionalSchwartzTest p g x ∂μ)‖ ≤
      fractionalSchwartzWeightedSize p (H j) *
        (∫ x, |f x| * polynomialDecay (p + 3) x ∂μ) := by
    rw [hdiff j]
    exact (height_fractional_test_integrable_and_bound p μ f hf hweight (H j) (hHm j)).2
  apply squeeze_zero (fun j => norm_nonneg _) hb
  simpa only [zero_mul] using! (fractionalSchwartzWeightedSize_tendsto_zero p H hHt).mul_const
    (∫ x, |f x| * polynomialDecay (p + 3) x ∂μ)

theorem height_fractional_test_zero_on_mean_zero_tests (p : ℕ)
    (μ : Measure (Ambient (p + 1))) (f : Ambient (p + 1) → ℝ) (hf : Measurable f)
    (hweight : Integrable (fun x => |f x| * polynomialDecay (p + 3) x) μ)
    (hcompact : ∀ g : 𝓢(Ambient (p + 1), ℂ), HasCompactSupport g → (∫ y, g y) = 0 →
      (∫ x, f x • fractionalSchwartzTest p g x ∂μ) = 0)
    (g : 𝓢(Ambient (p + 1), ℂ)) (hg : (∫ y, g y) = 0) :
    (∫ x, f x • fractionalSchwartzTest p g x ∂μ) = 0 := by
  obtain ⟨G, hG, ht⟩ := exists_compact_mean_zero_schwartz_approximation g hg
  have hlim := height_fractional_test_integral_tendsto p μ f hf hweight G g ht
    (fun j => (hG j).2) hg
  have hz : (fun j => ∫ x, f x • fractionalSchwartzTest p (G j) x ∂μ) =
      fun _ : ℕ => (0 : ℂ) := funext fun j => hcompact (G j) (hG j).1 (hG j).2
  rw [hz] at hlim
  exact tendsto_nhds_unique hlim tendsto_const_nhds

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Rigidity_FractionalRealComponents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory SchwartzMap Filter

theorem fractionalSchwartzTest_re (p : ℕ) (g : 𝓢(Ambient (p + 1), ℂ))
    (x : Ambient (p + 1)) :
    (fractionalSchwartzTest p g x).re = (-1 / 2 : ℝ) *
      ∫ h, fractionalSchwartzKernel (p + 1) (g.postcompCLM Complex.reCLM) x h := by
  have hi := fractionalSchwartzKernel_integrable p g x
  have hcomm : (∫ h, fractionalSchwartzKernel (p + 1) g x h).re =
      ∫ h, (fractionalSchwartzKernel (p + 1) g x h).re :=
    (Complex.reCLM.integral_comp_comm hi).symm
  unfold fractionalSchwartzTest
  rw [Complex.smul_re, smul_eq_mul, hcomm]
  congr 1
  apply integral_congr_ae (Eventually.of_forall fun h => ?_)
  change Complex.reCLM (inverseDistancePow (p + 1 + 1) 0 h •
    (g (x + h) + g (x - h) - (2 : ℝ) • g x)) =
    inverseDistancePow (p + 1 + 1) 0 h •
      (Complex.reCLM (g (x + h)) + Complex.reCLM (g (x - h)) -
        (2 : ℝ) • Complex.reCLM (g x))
  rw [map_smul, map_sub, map_add, map_smul]

theorem fractionalSchwartzTest_im (p : ℕ) (g : 𝓢(Ambient (p + 1), ℂ))
    (x : Ambient (p + 1)) :
    (fractionalSchwartzTest p g x).im = (-1 / 2 : ℝ) *
      ∫ h, fractionalSchwartzKernel (p + 1) (g.postcompCLM Complex.imCLM) x h := by
  have hi := fractionalSchwartzKernel_integrable p g x
  have hcomm : (∫ h, fractionalSchwartzKernel (p + 1) g x h).im =
      ∫ h, (fractionalSchwartzKernel (p + 1) g x h).im :=
    (Complex.imCLM.integral_comp_comm hi).symm
  unfold fractionalSchwartzTest
  rw [Complex.smul_im, smul_eq_mul, hcomm]
  congr 1
  apply integral_congr_ae (Eventually.of_forall fun h => ?_)
  change Complex.imCLM (inverseDistancePow (p + 1 + 1) 0 h •
    (g (x + h) + g (x - h) - (2 : ℝ) • g x)) =
    inverseDistancePow (p + 1 + 1) 0 h •
      (Complex.imCLM (g (x + h)) + Complex.imCLM (g (x - h)) -
        (2 : ℝ) • Complex.imCLM (g x))
  rw [map_smul, map_sub, map_add, map_smul]

theorem compact_complex_fractional_equation_of_real (p : ℕ)
    (f : Ambient (p + 1) → ℝ)
    (hreal : ∀ ψ : 𝓢(Ambient (p + 1), ℝ), HasCompactSupport ψ →
      Integrable (fun y => f y * ((-1 / 2 : ℝ) *
        ∫ h, fractionalSchwartzKernel (p + 1) ψ y h)) volume ∧
      (∫ y, f y * ((-1 / 2 : ℝ) *
        ∫ h, fractionalSchwartzKernel (p + 1) ψ y h)) = 0)
    (g : 𝓢(Ambient (p + 1), ℂ)) (hc : HasCompactSupport g) :
    Integrable (fun x => f x • fractionalSchwartzTest p g x) volume ∧
      (∫ x, f x • fractionalSchwartzTest p g x) = 0 := by
  let gr : 𝓢(Ambient (p + 1), ℝ) := g.postcompCLM Complex.reCLM
  let gi : 𝓢(Ambient (p + 1), ℝ) := g.postcompCLM Complex.imCLM
  have hcr : HasCompactSupport gr := hc.comp_left (g := Complex.re) rfl
  have hci : HasCompactSupport gi := hc.comp_left (g := Complex.im) rfl
  obtain ⟨hrI, hr⟩ := hreal gr hcr
  obtain ⟨hiI, hi⟩ := hreal gi hci
  have hRI : Integrable (fun x => (f x • fractionalSchwartzTest p g x).re) volume := by
    simpa only [Complex.smul_re, fractionalSchwartzTest_re] using! hrI
  have hII : Integrable (fun x => (f x • fractionalSchwartzTest p g x).im) volume := by
    simpa only [Complex.smul_im, fractionalSchwartzTest_im] using! hiI
  have hI : Integrable (fun x => f x • fractionalSchwartzTest p g x) volume :=
    Integrable.re_im_iff.mp ⟨hRI, hII⟩
  refine ⟨hI, Complex.ext ?_ ?_⟩
  · have hcomm : (∫ x, f x • fractionalSchwartzTest p g x).re =
        ∫ x, (f x • fractionalSchwartzTest p g x).re :=
      (Complex.reCLM.integral_comp_comm hI).symm
    rw [hcomm]
    simpa only [Complex.smul_re, fractionalSchwartzTest_re, Complex.zero_re] using! hr
  · have hcomm : (∫ x, f x • fractionalSchwartzTest p g x).im =
        ∫ x, (f x • fractionalSchwartzTest p g x).im :=
      (Complex.imCLM.integral_comp_comm hI).symm
    rw [hcomm]
    simpa only [Complex.smul_im, fractionalSchwartzTest_im, Complex.zero_im] using! hi

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Rigidity_BoundedFractionalRigidity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory SchwartzMap

theorem bounded_density_ae_affine_of_compact_fractional_equation (p : ℕ)
    (f : Ambient (p + 1) → ℝ) (hf : Measurable f) (M : ℝ) (hb : ∀ x, |f x| ≤ M)
    (hreal : ∀ ψ : 𝓢(Ambient (p + 1), ℝ), HasCompactSupport ψ →
      Integrable (fun y => f y * ((-1 / 2 : ℝ) *
        ∫ h, fractionalSchwartzKernel (p + 1) ψ y h)) volume ∧
      (∫ y, f y * ((-1 / 2 : ℝ) *
        ∫ h, fractionalSchwartzKernel (p + 1) ψ y h)) = 0) :
    ∃ c : ℝ, ∃ L : Ambient (p + 1) →L[ℝ] ℝ, ∀ᵐ x ∂volume, f x = c + L x := by
  have hweight := bounded_density_polynomial_weight_integrable (p + 1) f hf M hb
  let T := heightTemperedDistribution volume f hf (p + 3) hweight
  have hT (g : 𝓢(Ambient (p + 1), ℂ)) : T g = ∫ x, f x • g x :=
    heightTemperedDistribution_apply volume f hf (p + 3) hweight g
  have hcompact (g : 𝓢(Ambient (p + 1), ℂ)) (hc : HasCompactSupport g) :
      (∫ x, f x • fractionalSchwartzTest p g x) = 0 :=
    (compact_complex_fractional_equation_of_real p f hreal g hc).2
  have heq (g : 𝓢(Ambient (p + 1), ℂ)) (hg : (∫ x, g x) = 0) :
      (∫ x, f x • fractionalSchwartzTest p g x) = 0 :=
    height_fractional_test_zero_on_mean_zero_tests p volume f hf hweight
      (fun g hc _ => hcompact g hc) g hg
  exact represented_fractional_height_ae_affine p f
    (bounded_measurable_locallyIntegrable volume f hf M hb) T hT heq
    (bounded_density_exterior_integrable (p + 1) f hf M hb)

theorem bounded_density_ae_constant_of_compact_fractional_equation (p : ℕ)
    (f : Ambient (p + 1) → ℝ) (hf : Measurable f) (M : ℝ) (hb : ∀ x, |f x| ≤ M)
    (hreal : ∀ ψ : 𝓢(Ambient (p + 1), ℝ), HasCompactSupport ψ →
      Integrable (fun y => f y * ((-1 / 2 : ℝ) *
        ∫ h, fractionalSchwartzKernel (p + 1) ψ y h)) volume ∧
      (∫ y, f y * ((-1 / 2 : ℝ) *
        ∫ h, fractionalSchwartzKernel (p + 1) ψ y h)) = 0) :
    ∃ c : ℝ, ∀ᵐ x ∂volume, f x = c := by
  obtain ⟨c, L, heq⟩ := bounded_density_ae_affine_of_compact_fractional_equation p f hf M hb hreal
  exact ⟨c, (ae_bounded_affine_is_constant f M hb c L heq).2⟩

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_SourceDensityConstant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Constant planar densities

An almost-everywhere constant density pushes forward under a linear isometry to a scalar multiple
of planar volume. The compact fractional equation and bounded-density rigidity identify this
constant for reflectionless weak limits, retaining its positive lower and finite upper bounds.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory SchwartzMap Metric Set Filter Topology
open scoped NNReal ENNReal

theorem ae_constant_planar_density_measure {n d : ℕ}
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (f : Ambient n → ℝ) (q : ℝ)
    (heq : ∀ᵐ x ∂volume, f x = q) :
    ((volume : Measure (Ambient n)).withDensity
      (fun x => ENNReal.ofReal (f x))).map L =
      ENNReal.ofReal q • (volume : Measure (Ambient n)).map L := by
  have hd : (fun x => ENNReal.ofReal (f x)) =ᵐ[volume] fun _ => ENNReal.ofReal q :=
    heq.mono fun _ hx => congrArg ENNReal.ofReal hx
  rw [withDensity_congr_ae hd, withDensity_const,
    Measure.map_smul]

theorem source_planar_density_ae_constant {d : ℕ} (p : ℕ) (C G : ℝ)
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
    (hreflect : ScalarReflectionlessAt (p + 1) ν 0) :
    ∃ q : ℝ, c ≤ q ∧ q ≤ M ∧ 0 < q ∧
      (∀ᵐ x ∂volume, f x = q) ∧
      ν = ENNReal.ofReal q • (volume : Measure (Ambient (p + 1))).map L := by
  obtain ⟨q, heq⟩ := bounded_density_ae_constant_of_compact_fractional_equation p f hf M hupper
    (source_planar_density_compact_fractional_equation p C G μ ν hgrowth hgν hweak D hB
      L f hf c hc hlower M hupper hdensity cMass hcMass hlowerMass hreflect)
  obtain ⟨x, hx⟩ := heq.exists
  have hcq : c ≤ q := hx ▸ hlower x
  have hqM : q ≤ M := hx ▸ (le_abs_self (f x)).trans (hupper x)
  exact ⟨q, hcq, hqM, hc.trans_le hcq, heq,
    hdensity.symm.trans (ae_constant_planar_density_measure L f q heq)⟩

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_SourceNormalizedRegionData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Normalized height data on bounded projection regions

Uniform square-integral and fractional-energy bounds on balls restrict to the
bounded projection regions inside them. Choosing bounds at each region's outer
radius produces constants indexed by the region size, independent of the
sequence index. Positivity of the integrands and monotonicity of restricted
product measures preserve both estimates.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter
open scoped NNReal

theorem normalized_region_data_of_ball_data {ι : Type*} [Fintype ι] {d : ℕ} (n : ℕ)
    (μ : ℕ → Measure (Ambient d)) [∀ j, SFinite (μ j)]
    (w : ℕ → Ambient d → ℝ) (a : Ambient d)
    (hball : ∀ r : ℝ, 0 < r → ∃ B E : ℝ, 0 ≤ B ∧ 0 ≤ E ∧ ∀ j,
      MemLp (w j) 2 ((μ j).restrict (ball a r)) ∧
      (∫ x in ball a r, w j x ^ 2 ∂μ j) ≤ B ∧
      Integrable (fun q : Ambient d × Ambient d => fractionalPairEnergy n (w j) q.1 q.2)
        (((μ j).restrict (ball a r)).prod ((μ j).restrict (ball a r))) ∧
      (∫ q : Ambient d × Ambient d, fractionalPairEnergy n (w j) q.1 q.2
        ∂((μ j).restrict (ball a r)).prod ((μ j).restrict (ball a r))) ≤ E)
    (π : Ambient d → ι → ℝ) (K : ℝ≥0) :
    ∃ B E : ℕ → ℝ, ∀ H, 0 ≤ B H ∧ 0 ≤ E H ∧ ∀ j,
      MemLp (w j) 2 ((μ j).restrict (boundedProjectionRegion π a K H)) ∧
      (∫ x in boundedProjectionRegion π a K H, w j x ^ 2 ∂μ j) ≤ B H ∧
      Integrable (fun q : Ambient d × Ambient d => fractionalPairEnergy n (w j) q.1 q.2)
        (((μ j).restrict (boundedProjectionRegion π a K H)).prod
          ((μ j).restrict (boundedProjectionRegion π a K H))) ∧
      (∫ q : Ambient d × Ambient d, fractionalPairEnergy n (w j) q.1 q.2
        ∂((μ j).restrict (boundedProjectionRegion π a K H)).prod
          ((μ j).restrict (boundedProjectionRegion π a K H))) ≤ E H := by
  choose B E hB hE hd using
    (fun H => hball (planeBoxOuterRadius K H) (planeBoxOuterRadius_pos K H))
  refine ⟨B, E, fun H => ⟨hB H, hE H, fun j => ?_⟩⟩
  have hs : boundedProjectionRegion π a K H ⊆ ball a (planeBoxOuterRadius K H) := inter_subset_right
  have hμ := Measure.restrict_mono (μ := μ j) hs le_rfl
  have hprod : ((μ j).restrict (boundedProjectionRegion π a K H)).prod
      ((μ j).restrict (boundedProjectionRegion π a K H)) ≤
      ((μ j).restrict (ball a (planeBoxOuterRadius K H))).prod
        ((μ j).restrict (ball a (planeBoxOuterRadius K H))) := by
    rw [Measure.prod_restrict, Measure.prod_restrict]
    exact Measure.restrict_mono (prod_mono hs hs) le_rfl
  exact ⟨MemLp.mono_measure hμ (hd H j).1,
    (integral_mono_measure hμ (Eventually.of_forall fun x => sq_nonneg (w j x))
      (hd H j).1.integrable_sq).trans (hd H j).2.1,
    (hd H j).2.2.1.mono_measure hprod,
    (integral_mono_measure hprod
      (Eventually.of_forall fun q => fractionalPairEnergy_nonneg n (w j) q.1 q.2)
      (hd H j).2.2.1).trans (hd H j).2.2.2⟩

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_TwoSidedIntrinsicDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Two-sided intrinsic densities

Lower ball-growth bounds give a positive multiple of Euclidean volume dominated
by the measure. Together with the upper-growth domination, this produces a
measurable density with pointwise lower and upper bounds by clipping its
Radon–Nikodym derivative without changing the represented measure.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

theorem intrinsicLowerDensityBound_pos (n : ℕ) (C : ℝ) (hC : 0 < C) :
    0 < intrinsicLowerDensityBound n C := by
  apply Real.toNNReal_pos.mpr
  apply inv_pos.mpr
  exact mul_pos hC (ENNReal.toReal_pos
    (ne_of_gt (measure_ball_pos volume (0 : Ambient n) zero_lt_one)) measure_ball_lt_top.ne)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_DyadicFlatMeasureLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Flat limits from dyadic moment bounds

Dyadic plane-approximation bounds and vanishing scalar oscillation produce a planar weak limit.
Uniform hard-truncation bounds then force its density to be a positive constant. The conclusion
retains the limiting coordinates, quantitative density bounds, and normal-coordinate moments.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

theorem exists_dyadic_flat_measure_limit {p d : ℕ}
    (μ : ℕ → Measure (Ambient d)) [∀ j, IsFiniteMeasureOnCompacts (μ j)]
    (C G : ℝ) (hC : 0 < C) (hg : ∀ j, GlobalUpperGrowth (p + 1) G (μ j))
    (hlower : ∀ j x, x ∈ (μ j).support → ∀ r : ℝ, AdmissibleRadius (μ j) r →
      ENNReal.ofReal (r ^ (p + 1) / C) ≤ (μ j) (ball x r))
    (hdiam : ∀ r : ℝ, 0 < r → ∀ᶠ j in atTop, ENNReal.ofReal r ≤ ediam (μ j).support)
    (hzero : ∀ j, (0 : Ambient d) ∈ (μ j).support)
    (S : ℕ → AffineSubspace ℝ (Ambient d)) (hS : ∀ j, IsAffineNPlane (p + 1) (S j))
    (δ : ℕ → ℝ) (T : ℕ → ℕ) (hδ : Tendsto δ atTop (𝓝 0)) (hT : Tendsto T atTop atTop)
    (M b : ℝ)
    (hmoment : ∀ j l, l ≤ T j →
      (∫ x in ball (0 : Ambient d) ((2 : ℝ) ^ l), infDist x (S j : Set (Ambient d)) ^ 2 ∂μ j) ≤
        M * (δ j * b ^ l) ^ 2 * ((2 : ℝ) ^ l) ^ (p + 1 + 2))
    (A v : ℕ → ℝ) (hA : Tendsto A atTop atTop) (hv : Tendsto v atTop (𝓝 0))
    (hosc : ∀ j, ScalarOscillationBound (p + 1) (μ j) 0 (A j) (v j))
    (D : ℝ≥0)
    (hB : ∀ j ε, 0 < ε → ∀ u : Ambient d → ℝ, MemLp u 2 (μ j) →
      MemLp (truncated (p + 1) (μ j) ε u) 2 (μ j) ∧
        eLpNorm (truncated (p + 1) (μ j) ε u) 2 (μ j) ≤ (D : ℝ≥0∞) * eLpNorm u 2 (μ j)) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∃ ν : Measure (Ambient d),
      ∃ a : ℕ → Ambient d, ∃ L : ℕ → Ambient (p + 1) →ₗᵢ[ℝ] Ambient d,
      ∃ N : ℕ → Ambient (d - (p + 1)) →ₗᵢ[ℝ] Ambient d,
      ∃ Llim : Ambient (p + 1) →ₗᵢ[ℝ] Ambient d,
        IsFiniteMeasureOnCompacts ν ∧ ν ≠ 0 ∧
        CompactTestConvergence (fun j => μ (ρ j)) ν ∧
        GlobalUpperGrowth (p + 1) (G * 2 ^ (p + 1)) ν ∧
        (∀ x ∈ ν.support, ∀ r : ℝ, 0 < r →
          ENNReal.ofReal (r ^ (p + 1) / (C * 4 ^ (p + 1))) ≤ ν (ball x r)) ∧
        ν.support = (Llim.toLinearMap.range : Set (Ambient d)) ∧
        (0 : Ambient d) ∈ ν.support ∧
        (∃ f : Ambient (p + 1) → ℝ, Measurable f ∧
          (∀ x, intrinsicLowerDensityBound (p + 1) (C * 4 ^ (p + 1)) ≤ f x ∧
            f x ≤ intrinsicGrowthDensityBound (p + 1) (G * 2 ^ (p + 1))) ∧
          ((volume : Measure (Ambient (p + 1))).withDensity
            (fun x => ENNReal.ofReal (f x))).map Llim = ν ∧
          ∃ q : ℝ, 0 < q ∧
            (intrinsicLowerDensityBound (p + 1) (C * 4 ^ (p + 1)) : ℝ) ≤ q ∧
            q ≤ intrinsicGrowthDensityBound (p + 1) (G * 2 ^ (p + 1)) ∧
            (∀ᵐ x ∂volume, f x = q) ∧
            ν = ENNReal.ofReal q • (volume : Measure (Ambient (p + 1))).map Llim) ∧
        Tendsto a atTop (𝓝 0) ∧
        Tendsto (fun j => (L j).toContinuousLinearMap) atTop (𝓝 Llim.toContinuousLinearMap) ∧
        (∀ j, a j ∈ S (ρ j)) ∧ (∀ j, (L j).toLinearMap.range = (S (ρ j)).direction) ∧
        (∀ j y, (L j).toContinuousLinearMap.adjoint (N j y) = 0) ∧
        (∀ j y, L j ((L j).toContinuousLinearMap.adjoint y) +
          N j ((N j).toContinuousLinearMap.adjoint y) = y) ∧
        (∀ j x, infDist x (S (ρ j) : Set (Ambient d)) =
          ‖(N j).toContinuousLinearMap.adjoint (x - a j)‖) ∧
        (∀ i : Fin (d - (p + 1)), ∀ j : ℕ, ∀ R : ℝ, 0 < R →
          MemLp (fun x => normalCoordinate (a j) (N j) i x / δ (ρ j)) 2
            ((μ (ρ j)).restrict (ball 0 R))) ∧
        (∀ i : Fin (d - (p + 1)), ∀ j l, l ≤ T (ρ j) →
          (∫ x in ball (0 : Ambient d) ((2 : ℝ) ^ l),
            normalCoordinate (a j) (N j) i x ^ 2 ∂μ (ρ j)) ≤
            δ (ρ j) ^ 2 * M * ((2 : ℝ) ^ l) ^ (p + 1) * ((2 : ℝ) ^ l * b ^ l) ^ 2) ∧
        ∀ c : Ambient d, ScalarReflectionlessAt (p + 1) ν c := by
  obtain ⟨ρ, hρ, ν, a, L, N, Llim, hfinite, hne, hweak, hgν, hlowerν, hsupport,
    horigin, ⟨f, hf, hfb, hpush⟩, ha, hLlim, hcenter, hL, horth, hsplit, hdist,
    hmem, hsource, hreflect⟩ :=
    exists_dyadic_full_planar_measure_limit μ C G hC hg hlower hdiam hzero
      S hS δ T hδ hT M b hmoment A v hA hv hosc
  let : IsFiniteMeasureOnCompacts ν := hfinite
  have hC' : 0 < C * 4 ^ (p + 1) := mul_pos hC (pow_pos (by norm_num) _)
  have hpos : 0 < (intrinsicLowerDensityBound (p + 1) (C * 4 ^ (p + 1)) : ℝ) :=
    NNReal.coe_pos.mpr (intrinsicLowerDensityBound_pos (p + 1) _ hC')
  have habs (x : Ambient (p + 1)) :
      |f x| ≤ intrinsicGrowthDensityBound (p + 1) (G * 2 ^ (p + 1)) := by
    rw [abs_of_nonneg (hpos.le.trans (hfb x).1)]
    exact (hfb x).2
  have hlm (r : ℝ) (hr : 0 < r) :
      ENNReal.ofReal ((C * 4 ^ (p + 1))⁻¹ * r ^ (p + 1)) ≤ ν (ball 0 r) := by
    simpa only [div_eq_mul_inv, mul_comm] using! hlowerν 0 horigin r hr
  obtain ⟨q, hcq, hqM, hq, hfq, hflat⟩ :=
    source_planar_density_ae_constant p G (G * 2 ^ (p + 1)) (fun j => μ (ρ j)) ν
      (fun j => hg (ρ j)) hgν hweak D (fun j => hB (ρ j)) Llim f hf
      (intrinsicLowerDensityBound (p + 1) (C * 4 ^ (p + 1))) hpos (fun x => (hfb x).1)
      (intrinsicGrowthDensityBound (p + 1) (G * 2 ^ (p + 1))) habs hpush
      (C * 4 ^ (p + 1))⁻¹ (inv_pos.mpr hC') hlm (hreflect 0)
  exact ⟨ρ, hρ, ν, a, L, N, Llim, hfinite, hne, hweak, hgν, hlowerν, hsupport,
    horigin, ⟨f, hf, hfb, hpush, q, hq, hcq, hqM, hfq, hflat⟩,
    ha, hLlim, hcenter, hL, horth, hsplit, hdist, hmem, hsource, hreflect⟩

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_DyadicFlatEnergyLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Dyadic flat limits with normalized height energy

The flat-measure subsequence construction is augmented with uniform local square
and fractional-energy bounds for every normalized normal coordinate. The ball
estimates also restrict to bounded projection regions, while the same subsequence
retains the convergent plane frames, constant positive planar density, and scalar
reflectionlessness of the limit measure.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

theorem exists_dyadic_flat_measure_limit_with_energy_oai {p d : ℕ}
    (μ : ℕ → Measure (Ambient d)) [∀ j, IsFiniteMeasureOnCompacts (μ j)]
    (C G : ℝ) (hC : 0 < C) (hg : ∀ j, GlobalUpperGrowth (p + 1) G (μ j))
    (hlower : ∀ j x, x ∈ (μ j).support → ∀ r : ℝ, AdmissibleRadius (μ j) r →
      ENNReal.ofReal (r ^ (p + 1) / C) ≤ (μ j) (ball x r))
    (hdiam : ∀ r : ℝ, 0 < r → ∀ᶠ j in atTop, ENNReal.ofReal r ≤ ediam (μ j).support)
    (hzero : ∀ j, (0 : Ambient d) ∈ (μ j).support)
    (S : ℕ → AffineSubspace ℝ (Ambient d)) (hS : ∀ j, IsAffineNPlane (p + 1) (S j))
    (δ : ℕ → ℝ) (T : ℕ → ℕ) (hδ : Tendsto δ atTop (𝓝 0)) (hT : Tendsto T atTop atTop)
    (M b : ℝ)
    (hmoment : ∀ j l, l ≤ T j →
      (∫ x in ball (0 : Ambient d) ((2 : ℝ) ^ l), infDist x (S j : Set (Ambient d)) ^ 2 ∂μ j) ≤
        M * (δ j * b ^ l) ^ 2 * ((2 : ℝ) ^ l) ^ (p + 1 + 2))
    (A : ℕ → ℝ) (hA : Tendsto A atTop atTop)
    (hosc : ∀ j, ScalarOscillationBound (p + 1) (μ j) 0 (A j) (δ j ^ 3))
    (D : ℝ≥0)
    (hB : ∀ j ε, 0 < ε → ∀ u : Ambient d → ℝ, MemLp u 2 (μ j) →
      MemLp (truncated (p + 1) (μ j) ε u) 2 (μ j) ∧
        eLpNorm (truncated (p + 1) (μ j) ε u) 2 (μ j) ≤ (D : ℝ≥0∞) * eLpNorm u 2 (μ j))
    (hδpos : ∀ j, 0 < δ j) (hb1 : 1 ≤ b) (hb2 : b < 2)
    (hlast : Tendsto (fun j => ((2 : ℝ) ^ T j)⁻¹ / δ j) atTop (𝓝 0)) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∃ ν : Measure (Ambient d),
      ∃ a : ℕ → Ambient d, ∃ L : ℕ → Ambient (p + 1) →ₗᵢ[ℝ] Ambient d,
      ∃ N : ℕ → Ambient (d - (p + 1)) →ₗᵢ[ℝ] Ambient d,
      ∃ Llim : Ambient (p + 1) →ₗᵢ[ℝ] Ambient d,
        IsFiniteMeasureOnCompacts ν ∧ ν ≠ 0 ∧
        CompactTestConvergence (fun j => μ (ρ j)) ν ∧
        GlobalUpperGrowth (p + 1) (G * 2 ^ (p + 1)) ν ∧
        (∀ x ∈ ν.support, ∀ r : ℝ, 0 < r →
          ENNReal.ofReal (r ^ (p + 1) / (C * 4 ^ (p + 1))) ≤ ν (ball x r)) ∧
        ν.support = (Llim.toLinearMap.range : Set (Ambient d)) ∧
        (0 : Ambient d) ∈ ν.support ∧
        (∃ f : Ambient (p + 1) → ℝ, Measurable f ∧
          (∀ x, intrinsicLowerDensityBound (p + 1) (C * 4 ^ (p + 1)) ≤ f x ∧
            f x ≤ intrinsicGrowthDensityBound (p + 1) (G * 2 ^ (p + 1))) ∧
          ((volume : Measure (Ambient (p + 1))).withDensity
            (fun x => ENNReal.ofReal (f x))).map Llim = ν ∧
          ∃ q : ℝ, 0 < q ∧
            (intrinsicLowerDensityBound (p + 1) (C * 4 ^ (p + 1)) : ℝ) ≤ q ∧
            q ≤ intrinsicGrowthDensityBound (p + 1) (G * 2 ^ (p + 1)) ∧
            (∀ᵐ x ∂volume, f x = q) ∧
            ν = ENNReal.ofReal q • (volume : Measure (Ambient (p + 1))).map Llim) ∧
        Tendsto a atTop (𝓝 0) ∧
        Tendsto (fun j => (L j).toContinuousLinearMap) atTop (𝓝 Llim.toContinuousLinearMap) ∧
        (∀ j, a j ∈ S (ρ j)) ∧ (∀ j, (L j).toLinearMap.range = (S (ρ j)).direction) ∧
        (∀ j y, (L j).toContinuousLinearMap.adjoint (N j y) = 0) ∧
        (∀ j y, L j ((L j).toContinuousLinearMap.adjoint y) +
          N j ((N j).toContinuousLinearMap.adjoint y) = y) ∧
        (∀ j x, infDist x (S (ρ j) : Set (Ambient d)) =
          ‖(N j).toContinuousLinearMap.adjoint (x - a j)‖) ∧
        (∀ i : Fin (d - (p + 1)), ∀ j : ℕ, ∀ R : ℝ, 0 < R →
          MemLp (fun x => normalCoordinate (a j) (N j) i x / δ (ρ j)) 2
            ((μ (ρ j)).restrict (ball 0 R))) ∧
        (∀ i : Fin (d - (p + 1)), ∀ j l, l ≤ T (ρ j) →
          (∫ x in ball (0 : Ambient d) ((2 : ℝ) ^ l),
            normalCoordinate (a j) (N j) i x ^ 2 ∂μ (ρ j)) ≤
            δ (ρ j) ^ 2 * M * ((2 : ℝ) ^ l) ^ (p + 1) * ((2 : ℝ) ^ l * b ^ l) ^ 2) ∧
        (∀ i : Fin (d - (p + 1)), ∀ r : ℝ, 0 < r → ∃ B E : ℝ, 0 ≤ B ∧ 0 ≤ E ∧ ∀ j,
          MemLp (fun x => normalCoordinate (a j) (N j) i x / δ (ρ j)) 2
            ((μ (ρ j)).restrict (ball 0 r)) ∧
          (∫ x in ball 0 r, (normalCoordinate (a j) (N j) i x / δ (ρ j)) ^ 2 ∂μ (ρ j)) ≤ B ∧
          Integrable (fun v : Ambient d × Ambient d =>
            fractionalPairEnergy (p + 1) (fun x => normalCoordinate (a j) (N j) i x / δ (ρ j)) v.1 v.2)
            (((μ (ρ j)).restrict (ball 0 r)).prod ((μ (ρ j)).restrict (ball 0 r))) ∧
          (∫ v : Ambient d × Ambient d,
            fractionalPairEnergy (p + 1) (fun x => normalCoordinate (a j) (N j) i x / δ (ρ j)) v.1 v.2
              ∂((μ (ρ j)).restrict (ball 0 r)).prod ((μ (ρ j)).restrict (ball 0 r))) ≤ E) ∧
        (∀ i : Fin (d - (p + 1)), ∀ π : Ambient d → Fin (p + 1) → ℝ, ∀ K : ℝ≥0,
          ∃ B E : ℕ → ℝ, ∀ H, 0 ≤ B H ∧ 0 ≤ E H ∧ ∀ j,
            MemLp (fun x => normalCoordinate (a j) (N j) i x / δ (ρ j)) 2
              ((μ (ρ j)).restrict (boundedProjectionRegion π 0 K H)) ∧
            (∫ x in boundedProjectionRegion π 0 K H,
              (normalCoordinate (a j) (N j) i x / δ (ρ j)) ^ 2 ∂μ (ρ j)) ≤ B H ∧
            Integrable (fun v : Ambient d × Ambient d =>
              fractionalPairEnergy (p + 1) (fun x => normalCoordinate (a j) (N j) i x / δ (ρ j)) v.1 v.2)
              (((μ (ρ j)).restrict (boundedProjectionRegion π 0 K H)).prod
                ((μ (ρ j)).restrict (boundedProjectionRegion π 0 K H))) ∧
            (∫ v : Ambient d × Ambient d,
              fractionalPairEnergy (p + 1) (fun x => normalCoordinate (a j) (N j) i x / δ (ρ j)) v.1 v.2
                ∂((μ (ρ j)).restrict (boundedProjectionRegion π 0 K H)).prod
                  ((μ (ρ j)).restrict (boundedProjectionRegion π 0 K H))) ≤ E H) ∧
        ∀ c : Ambient d, ScalarReflectionlessAt (p + 1) ν c := by
  have hv : Tendsto (fun j => δ j ^ 3) atTop (𝓝 0) := by
    simpa only [zero_pow (by decide : (3 : ℕ) ≠ 0)] using! hδ.pow 3
  obtain ⟨ρ, hρ, ν, a, L, N, Llim, hfinite, hne, hweak, hgν, hlowerν, hsupport,
    horigin, hdensity, ha, hLlim, hcenter, hL, horth, hsplit, hdist,
    hmem, hsource, hreflect⟩ :=
    exists_dyadic_flat_measure_limit μ C G hC hg hlower hdiam hzero
      S hS δ T hδ hT M b hmoment A (fun j => δ j ^ 3) hA hv hosc D hB
  have hdata := normal_frame_source_data_on_ball p C G (fun j => μ (ρ j))
    (fun j => hg (ρ j)) hC (fun j r hr => hlower (ρ j) 0 (hzero (ρ j)) r hr)
    (fun r hr => hρ.tendsto_atTop.eventually (hdiam r hr)) a ha N
    (fun j => δ (ρ j)) (fun j => A (ρ j)) (fun j => hδpos (ρ j))
    (hδ.comp hρ.tendsto_atTop) (hA.comp hρ.tendsto_atTop) (fun j => hosc (ρ j))
    (fun j => T (ρ j)) (hT.comp hρ.tendsto_atTop) M b hb1 hb2
    (hlast.comp hρ.tendsto_atTop) hsource
  refine ⟨ρ, hρ, ν, a, L, N, Llim, hfinite, hne, hweak, hgν, hlowerν, hsupport,
    horigin, hdensity, ha, hLlim, hcenter, hL, horth, hsplit, hdist, hmem, hsource,
    hdata, ?_, hreflect⟩
  intro i π K
  exact normalized_region_data_of_ball_data (p + 1) (fun j => μ (ρ j))
    (fun j x => normalCoordinate (a j) (N j) i x / δ (ρ j)) 0 (hdata i) π K

end

end RieszRectifiability

end OAI
end

theorem solution : type_of% @OAI.RieszRectifiability.exists_dyadic_flat_measure_limit_with_energy_oai := @OAI.RieszRectifiability.exists_dyadic_flat_measure_limit_with_energy_oai
