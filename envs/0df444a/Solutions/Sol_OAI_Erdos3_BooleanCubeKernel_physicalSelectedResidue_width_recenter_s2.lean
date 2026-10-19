-- Prove2me | solution 1 for OAI.Erdos3.BooleanCubeKernel.physicalSelectedResidue_width_recenter_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-17T11:12:43.649032+00:00
-- url     : https://prove2.me/submissions/175ad996-6007-4320-94d6-79f69077bde6

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B126
import Definitions.Def_OAIE3v2B162

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.NormalizedDensityL1
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem positive_mass_inverse_difference {I J : ℝ} (hI : 0 < I) (hJ : 0 < J) :
    J * |1 / I - 1 / J| = |I - J| / I := by
  have he : 1 / I - 1 / J = (J - I) / (I * J) := by field_simp
  rw [he, abs_div, abs_mul, abs_of_pos hI, abs_of_pos hJ, abs_sub_comm J I]
  field_simp

theorem normalized_density_l1 {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (f g : X → ℝ) (hf : Integrable f μ) (hg : Integrable g μ)
    (hg0 : ∀ x, 0 ≤ g x) (hI : 0 < ∫ x, f x ∂μ) (hJ : 0 < ∫ x, g x ∂μ) :
    (∫ x, |f x / (∫ y, f y ∂μ) - g x / (∫ y, g y ∂μ)| ∂μ) ≤
      2 * (∫ x, |f x - g x| ∂μ) / (∫ x, f x ∂μ) := by
  let I := ∫ x, f x ∂μ
  let J := ∫ x, g x ∂μ
  have hI' : 0 < I := hI
  have hJ' : 0 < J := hJ
  have habs : Integrable (fun x => |f x - g x|) μ := (hf.sub hg).abs
  have hpoint (x : X) : |f x / I - g x / J| ≤
      |f x - g x| / I + g x * |1 / I - 1 / J| := by
    have he : f x / I - g x / J = (f x - g x) / I + g x * (1 / I - 1 / J) := by ring
    rw [he]
    simpa only [abs_div, abs_of_pos hI', abs_mul, abs_of_nonneg (hg0 x)] using
      abs_add_le ((f x - g x) / I) (g x * (1 / I - 1 / J))
  have hbound := integral_mono ((hf.div_const I).sub (hg.div_const J)).abs
    ((habs.div_const I).add (hg.mul_const |1 / I - 1 / J|)) hpoint
  dsimp only [Pi.sub_apply, Pi.add_apply] at hbound
  rw [integral_add (habs.div_const I) (hg.mul_const _), integral_div, integral_mul_const] at hbound
  change (∫ x, |f x / I - g x / J| ∂μ) ≤
    (∫ x, |f x - g x| ∂μ) / I + J * |1 / I - 1 / J| at hbound
  rw [positive_mass_inverse_difference hI' hJ'] at hbound
  have hm := abs_integral_le_integral_abs (f := fun x => f x - g x) (μ := μ)
  rw [integral_sub hf hg] at hm
  have hd := div_le_div_of_nonneg_right hm hI'.le
  change |I - J| / I ≤ (∫ x, |f x - g x| ∂μ) / I at hd
  change (∫ x, |f x / I - g x / J| ∂μ) ≤ 2 * (∫ x, |f x - g x| ∂μ) / I
  calc
    _ ≤ (∫ x, |f x - g x| ∂μ) / I + |I - J| / I := hbound
    _ ≤ (∫ x, |f x - g x| ∂μ) / I + (∫ x, |f x - g x| ∂μ) / I :=
      by linarith
    _ = _ := by ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.SampledWeightCellLaw
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem abs_sub_eq_add_sub_two_min (x y : ℝ) : |x - y| = x + y - 2 * min x y := by
  rcases le_total x y with h | h
  · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]
    ring

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem measured_density_overlap {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (f g : X → ℝ) (hf : Integrable f μ) (hg : Integrable g μ)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hfmass : (∫ x, f x ∂μ) = 1) (hgmass : (∫ x, g x ∂μ) = 1) :
    (∫ x, min (f x) (g x) ∂μ) ∈ Set.Icc (0 : ℝ) 1 ∧
      (∫ x, |f x-g x| ∂μ) = 2 - 2 * ∫ x, min (f x) (g x) ∂μ := by
  have hm : Integrable (fun x => min (f x) (g x)) μ := hf.inf hg
  have hsum : Integrable (fun x => f x + g x) μ := hf.add hg
  constructor
  · exact ⟨integral_nonneg (fun x => le_min (hf0 x) (hg0 x)),
      (integral_mono hm hf (fun x => min_le_left _ _)).trans_eq hfmass⟩
  · simp_rw [abs_sub_eq_add_sub_two_min]
    rw [integral_sub hsum (hm.const_mul 2), integral_add hf hg,
      integral_const_mul, hfmass, hgmass]
    norm_num

theorem tensor_density_l1_le_sum {D : Type*} [Fintype D] [DecidableEq D]
    {X : D → Type*} [∀ d, MeasurableSpace (X d)] (μ : ∀ d, Measure (X d)) [∀ d, SigmaFinite (μ d)]
    (f g : ∀ d, X d → ℝ) (hf : ∀ d, Integrable (f d) (μ d)) (hg : ∀ d, Integrable (g d) (μ d))
    (hf0 : ∀ d x, 0 ≤ f d x) (hg0 : ∀ d x, 0 ≤ g d x)
    (hfmass : ∀ d, (∫ x, f d x ∂μ d) = 1) (hgmass : ∀ d, (∫ x, g d x ∂μ d) = 1) :
    (∫ x, |(∏ d, f d (x d)) - ∏ d, g d (x d)| ∂Measure.pi μ) ≤
      ∑ d, ∫ x, |f d x-g d x| ∂μ d := by
  let F := fun x : ∀ d, X d => ∏ d, f d (x d)
  let G := fun x : ∀ d, X d => ∏ d, g d (x d)
  let H := fun x : ∀ d, X d => ∏ d, min (f d (x d)) (g d (x d))
  let mass := fun d => ∫ x, min (f d x) (g d x) ∂μ d
  have hF : Integrable F (Measure.pi μ) := Integrable.fintype_prod_dep hf
  have hG : Integrable G (Measure.pi μ) := Integrable.fintype_prod_dep hg
  have hH : Integrable H (Measure.pi μ) := Integrable.fintype_prod_dep (fun d => (hf d).inf (hg d))
  have hpoint (x : ∀ d, X d) : |F x-G x| ≤ F x+G x-2*H x := by
    have hl : H x ≤ F x := Finset.prod_le_prod
      (fun d _ => le_min (hf0 d _) (hg0 d _)) (fun d _ => min_le_left _ _)
    have hr : H x ≤ G x := Finset.prod_le_prod
      (fun d _ => le_min (hf0 d _) (hg0 d _)) (fun d _ => min_le_right _ _)
    rw [abs_sub_eq_add_sub_two_min]
    have hh := le_min hl hr
    linarith
  have hFm : (∫ x, F x ∂Measure.pi μ) = 1 := by
    rw [show F = (fun x => ∏ d, f d (x d)) from rfl, integral_fintype_prod_eq_prod]
    simp only [hfmass, Finset.prod_const_one]
  have hGm : (∫ x, G x ∂Measure.pi μ) = 1 := by
    rw [show G = (fun x => ∏ d, g d (x d)) from rfl, integral_fintype_prod_eq_prod]
    simp only [hgmass, Finset.prod_const_one]
  have hHm : (∫ x, H x ∂Measure.pi μ) = ∏ d, mass d :=
    integral_fintype_prod_eq_prod (fun d x => min (f d x) (g d x))
  have hsum : Integrable (fun x => F x + G x) (Measure.pi μ) := hF.add hG
  have he := integral_mono (hF.sub hG).abs ((hF.add hG).sub (hH.const_mul 2)) hpoint
  change (∫ x, |F x-G x| ∂Measure.pi μ) ≤
    ∫ x, F x+G x-2*H x ∂Measure.pi μ at he
  rw [integral_sub hsum (hH.const_mul 2), integral_add hF hG,
    integral_const_mul, hFm, hGm, hHm] at he
  have hm (d) := measured_density_overlap (μ d) (f d) (g d) (hf d) (hg d)
    (hf0 d) (hg0 d) (hfmass d) (hgmass d)
  have hp := one_sub_sum_le_positive_prod Finset.univ mass (fun d => 1-mass d)
    (fun d _ => (hm d).1.1) (fun d _ => ⟨by linarith [(hm d).1.2], by linarith [(hm d).1.1]⟩)
    (fun d _ => by linarith)
  have hh : (∑ d, ∫ x, |f d x-g d x| ∂μ d) = 2 * ∑ d, (1-mass d) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    rw [(hm d).2]
    dsimp only [mass]
    ring
  rw [hh]
  change (∫ x, |F x-G x| ∂Measure.pi μ) ≤ _
  linarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.DensityMixtureAELaw
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem pmf_real_mass {X : Type*} (p : PMF X) : (∑' x, (p x).toReal) = 1 := by
  rw [← ENNReal.tsum_toReal_eq (p.apply_ne_top), p.tsum_coe, ENNReal.toReal_one]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedArrayReference
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators ENNReal

theorem pi_count_measure {I : Type*} [Fintype I] {X : I → Type*}
    [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSingletonClass (X i)] [∀ i, Countable (X i)] :
    Measure.pi (fun i => (Measure.count : Measure (X i))) =
      (Measure.count : Measure (∀ i, X i)) := by
  apply Measure.ext_of_singleton
  intro x
  simp only [Measure.pi_singleton, Measure.count_singleton, Finset.prod_const_one]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.FiniteCountDensityError
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem count_integrable_of_zero_off_finset {X : Type*} [MeasurableSpace X]
    [MeasurableSingletonClass X] (s : Finset X) (f : X → ℝ)
    (hs : ∀ x ∉ s, f x = 0) : Integrable f Measure.count := by
  apply integrable_count_iff.mpr
  exact (hasSum_sum_of_ne_finset_zero (fun x hx => by rw [hs x hx, norm_zero])).summable

theorem count_integral_eq_sum_of_zero_off_finset {X : Type*} [Countable X]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (s : Finset X) (f : X → ℝ) (hs : ∀ x ∉ s, f x = 0) :
    (∫ x, f x ∂Measure.count) = ∑ x ∈ s, f x := by
  rw [integral_countable (count_integrable_of_zero_off_finset s f hs)]
  simp only [measureReal_def, Measure.count_singleton, ENNReal.toReal_one, one_smul]
  exact (hasSum_sum_of_ne_finset_zero hs).tsum_eq

theorem count_density_l1_le_card {X : Type*} [Countable X]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (s : Finset X) (f g : X → ℝ) (hf : ∀ x ∉ s, f x = 0) (hg : ∀ x ∉ s, g x = 0)
    {ε : ℝ} (he : ∀ x ∈ s, |f x - g x| ≤ ε) :
    (∫ x, |f x - g x| ∂Measure.count) ≤ (s.card : ℝ) * ε := by
  rw [count_integral_eq_sum_of_zero_off_finset s _ (fun x hx => by
    rw [hf x hx, hg x hx, sub_self, abs_zero])]
  exact (Finset.sum_le_sum he).trans_eq (by simp)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ControlledJointGrid
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem pmf_real_integral_count {X : Type*} [Countable X]
    [MeasurableSpace X] [MeasurableSingletonClass X] (p : PMF X) :
    (∫ x, (p x).toReal ∂Measure.count) = 1 := by
  rw [integral_countable (pmf_real_integrable p)]
  simpa only [measureReal_def, Measure.count_singleton, ENNReal.toReal_one, one_smul]
    using pmf_real_mass p

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem realDensityMeasure_integral_complex {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (φ : X → ℂ) :
    (∫ x, φ x ∂realDensityMeasure μ f) = ∫ x, (f x : ℂ) * φ x ∂μ := by
  unfold realDensityMeasure
  rw [integral_withDensity_eq_integral_toReal_smul hf.ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (hf0 _), Complex.real_smul]

theorem density_bounded_complex_test_error {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f g : X → ℝ) (hf : Integrable f μ) (hg : Integrable g μ)
    (φ : X → ℂ) (hφ : Measurable φ) {B : ℝ} (hb : ∀ x, ‖φ x‖ ≤ B) :
    ‖(∫ x, (f x : ℂ) * φ x ∂μ) - ∫ x, (g x : ℂ) * φ x ∂μ‖ ≤
      B * ∫ x, |f x - g x| ∂μ := by
  have hfi : Integrable (fun x => (f x : ℂ) * φ x) μ :=
    hf.ofReal.mul_bdd hφ.aestronglyMeasurable (Filter.Eventually.of_forall hb)
  have hgi : Integrable (fun x => (g x : ℂ) * φ x) μ :=
    hg.ofReal.mul_bdd hφ.aestronglyMeasurable (Filter.Eventually.of_forall hb)
  rw [← integral_sub hfi hgi]
  refine (norm_integral_le_integral_norm _).trans ?_
  calc
    _ ≤ ∫ x, B * |f x - g x| ∂μ := by
      apply integral_mono (hfi.sub hgi).norm ((hf.sub hg).abs.const_mul B)
      intro x
      change ‖(f x : ℂ) * φ x - (g x : ℂ) * φ x‖ ≤ B * |f x - g x|
      rw [← sub_mul, ← Complex.ofReal_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      simpa only [mul_comm B] using mul_le_mul_of_nonneg_left (hb x) (abs_nonneg (f x - g x))
    _ = _ := integral_const_mul _ _

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ShiftedProductTestError
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem shiftedSmoothSamples_count_integral (a S : ℝ) (hS : 0 < S) :
    (∫ k : ℤ, smoothProbabilityProfile (((k : ℝ) - a) / S) ∂Measure.count) =
      shiftedSmoothSampleSum a S := by
  have hi := count_integrable_of_zero_off_finset (sampledWeightIndices a S 1)
    (fun k : ℤ => smoothProbabilityProfile (((k : ℝ) - a) / S))
    (sampledWeight_zero_off_indices smoothProbabilityProfile hS smoothProbabilityProfile_zero_outside)
  simpa only [measureReal_def, Measure.count_singleton, ENNReal.toReal_one, one_smul,
    shiftedSmoothSampleSum] using integral_countable hi

theorem shiftedSmoothSamples_center_l1 (a b S : ℝ) (hS : 1 ≤ S) :
    (∫ k : ℤ, |smoothProbabilityProfile (((k : ℝ) - a) / S) -
      smoothProbabilityProfile (((k : ℝ) - b) / S)| ∂Measure.count) ≤
      6 * S * ((probabilityProfileLipschitz : ℝ) * (|a - b| / S)) := by
  classical
  have hS0 : 0 < S := zero_lt_one.trans_le hS
  let U := sampledWeightIndices a S 1 ∪ sampledWeightIndices b S 1
  have ha (k : ℤ) (hk : k ∉ U) : smoothProbabilityProfile (((k : ℝ) - a) / S) = 0 :=
    sampledWeight_zero_off_indices smoothProbabilityProfile hS0 smoothProbabilityProfile_zero_outside
      k (fun h => hk (Finset.mem_union_left _ h))
  have hb (k : ℤ) (hk : k ∉ U) : smoothProbabilityProfile (((k : ℝ) - b) / S) = 0 :=
    sampledWeight_zero_off_indices smoothProbabilityProfile hS0 smoothProbabilityProfile_zero_outside
      k (fun h => hk (Finset.mem_union_right _ h))
  have hc : (U.card : ℝ) ≤ 6 * S := by
    have hu : (U.card : ℝ) ≤ (sampledWeightIndices a S 1).card +
        ((sampledWeightIndices b S 1).card : ℝ) := by
      exact_mod_cast Finset.card_union_le (sampledWeightIndices a S 1) (sampledWeightIndices b S 1)
    have hca := sampledWeightIndices_card_le a S 1 hS0.le zero_le_one
    have hcb := sampledWeightIndices_card_le b S 1 hS0.le zero_le_one
    linarith
  have he (k : ℤ) : |smoothProbabilityProfile (((k : ℝ) - a) / S) -
      smoothProbabilityProfile (((k : ℝ) - b) / S)| ≤
      (probabilityProfileLipschitz : ℝ) * (|a - b| / S) := by
    have h := smoothProbabilityProfile_lipschitz.norm_sub_le
      (((k : ℝ) - a) / S) (((k : ℝ) - b) / S)
    have hid : ((k : ℝ) - a) / S - ((k : ℝ) - b) / S = (b - a) / S := by ring
    simpa only [Real.norm_eq_abs, hid, abs_div, abs_of_pos hS0, abs_sub_comm b a] using h
  exact (count_density_l1_le_card U _ _ ha hb (fun k _ => he k)).trans
    (mul_le_mul_of_nonneg_right hc (by positivity))

theorem shiftedSmoothCoefficientPMF_center_l1 (a b S : ℝ) (hS : 0 < S)
    (hZa : 0 < shiftedSmoothSampleSum a S) (hZb : 0 < shiftedSmoothSampleSum b S)
    (hlarge : 8 * (probabilityProfileLipschitz : ℝ) ≤ S) :
    (∫ k : ℤ, |(shiftedSmoothCoefficientPMF a S hS hZa k).toReal -
      (shiftedSmoothCoefficientPMF b S hS hZb k).toReal| ∂Measure.count) ≤
      24 * (probabilityProfileLipschitz : ℝ) * |a - b| / S := by
  have hS1 : 1 ≤ S := by linarith [probabilityProfileLipschitz_one_le]
  have hi (c : ℝ) := count_integrable_of_zero_off_finset (sampledWeightIndices c S 1)
    (fun k : ℤ => smoothProbabilityProfile (((k : ℝ) - c) / S))
    (sampledWeight_zero_off_indices smoothProbabilityProfile hS smoothProbabilityProfile_zero_outside)
  have h := normalized_density_l1 Measure.count _ _ (hi a) (hi b)
    (fun _ => (smoothProbabilityProfile_range _).1)
    (by rw [shiftedSmoothSamples_count_integral a S hS]; exact hZa)
    (by rw [shiftedSmoothSamples_count_integral b S hS]; exact hZb)
  rw [shiftedSmoothSamples_count_integral a S hS, shiftedSmoothSamples_count_integral b S hS] at h
  simp only [shiftedSmoothCoefficientPMF_apply]
  apply h.trans
  have hr : S / shiftedSmoothSampleSum a S ≤ 2 :=
    (div_le_iff₀ hZa).mpr (by linarith [(shiftedSmoothSampleSum_bounds a hlarge).1])
  calc
    _ ≤ 2 * (6 * S * ((probabilityProfileLipschitz : ℝ) * (|a - b| / S))) /
        shiftedSmoothSampleSum a S :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (shiftedSmoothSamples_center_l1 a b S hS1) (by norm_num)) hZa.le
    _ = 12 * (S / shiftedSmoothSampleSum a S) *
        ((probabilityProfileLipschitz : ℝ) * (|a - b| / S)) := by ring
    _ ≤ 12 * 2 * ((probabilityProfileLipschitz : ℝ) * (|a - b| / S)) := by
      gcongr
    _ = _ := by ring

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

variable {X Y : Type*} [Countable X] [MeasurableSpace X] [MeasurableSingletonClass X]
  [Countable Y] [MeasurableSpace Y] [MeasurableSingletonClass Y]

theorem pmf_image_complex_sum_eq_count_integral (p : PMF X) (f : X → Y)
    (φ : Y → ℂ) {B : ℝ} (hb : ∀ y, ‖φ y‖ ≤ B) :
    (∑' x, ((p x).toReal : ℂ) * φ (f x)) =
      ∫ y, (((p.map f) y).toReal : ℂ) * φ y ∂Measure.count := by
  have hi : Integrable (fun x => φ (f x)) p.toMeasure :=
    Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable B
      (ae_of_all _ (fun x => hb (f x)))
  calc
    _ = ∫ x, φ (f x) ∂p.toMeasure := by
      simpa only [Complex.real_smul] using (p.integral_eq_tsum (fun x => φ (f x)) hi).symm
    _ = ∫ y, φ y ∂(p.map f).toMeasure := by
      rw [← PMF.toMeasure_map f p (measurable_of_countable f)]
      exact (integral_map (measurable_of_countable f).aemeasurable
        (measurable_of_countable φ).aestronglyMeasurable).symm
    _ = _ := by
      rw [pmf_realDensity_count]
      exact realDensityMeasure_integral_complex Measure.count _ (measurable_of_countable _)
        (fun _ => ENNReal.toReal_nonneg) φ

theorem pmf_image_count_test_error (p : PMF X) (f : X → Y) (g : Y → ℝ)
    (hg : Integrable g Measure.count) {ε B : ℝ} (hB : 0 ≤ B)
    (he : (∫ y, |((p.map f) y).toReal - g y| ∂Measure.count) ≤ ε)
    (φ : Y → ℂ) (hb : ∀ y, ‖φ y‖ ≤ B) :
    ‖(∑' x, ((p x).toReal : ℂ) * φ (f x)) -
      ∫ y, (g y : ℂ) * φ y ∂Measure.count‖ ≤ B * ε := by
  rw [pmf_image_complex_sum_eq_count_integral p f φ hb]
  exact (density_bounded_complex_test_error Measure.count _ _ (pmf_real_integrable (p.map f)) hg
    φ (measurable_of_countable φ) hb).trans (mul_le_mul_of_nonneg_left he hB)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem shiftedSmoothProductMass_pos_of_large {I : Type*} [Fintype I]
    (a S : I → ℝ) (hS : ∀ i, 8 * (probabilityProfileLipschitz : ℝ) ≤ S i) :
    0 < shiftedSmoothProductMass a S := by
  rw [shiftedSmoothProductMass_eq_prod a S (fun i => smoothSamplingScale_pos (hS i))]
  exact Finset.prod_pos (fun i _ => shiftedSmoothSampleSum_pos (a i) (hS i))

theorem shiftedSmoothProductPMF_zero {I : Type*} [Fintype I]
    (S : I → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass 0 S) :
    shiftedSmoothProductPMF 0 S hS hZ = smoothProductPMF S hS := by
  have hz (z : I → ℤ) : rectangularLatticePoint 0 S z = fun i => (z i : ℝ) / S i := by
    funext i
    change ((z i : ℝ) - 0) / S i = (z i : ℝ) / S i
    rw [sub_zero]
  ext z
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  simp only [shiftedSmoothProductPMF_toReal, smoothProductPMF, realWeightPMF_apply,
    shiftedSmoothProductMass, rectangularWeight, hz]

theorem shiftedSmoothProductPMF_center_l1 {I : Type*} [Fintype I]
    (a b S : I → ℝ) (hS : ∀ i, 0 < S i)
    (hZa : 0 < shiftedSmoothProductMass a S) (hZb : 0 < shiftedSmoothProductMass b S)
    (hlarge : ∀ i, 8 * (probabilityProfileLipschitz : ℝ) ≤ S i) :
    (∫ z, |(shiftedSmoothProductPMF a S hS hZa z).toReal -
      (shiftedSmoothProductPMF b S hS hZb z).toReal| ∂Measure.count) ≤
      24 * (probabilityProfileLipschitz : ℝ) * ∑ i, |a i - b i| / S i := by
  classical
  let pa := fun i => shiftedSmoothCoefficientPMF (a i) (S i) (hS i)
    (shiftedSmoothProductMass_coordinate_pos a S hS hZa i)
  let pb := fun i => shiftedSmoothCoefficientPMF (b i) (S i) (hS i)
    (shiftedSmoothProductMass_coordinate_pos b S hS hZb i)
  have h := tensor_density_l1_le_sum (fun _ : I => (Measure.count : Measure ℤ))
    (fun i k => (pa i k).toReal) (fun i k => (pb i k).toReal)
    (fun i => pmf_real_integrable (pa i)) (fun i => pmf_real_integrable (pb i))
    (fun _ _ => ENNReal.toReal_nonneg) (fun _ _ => ENNReal.toReal_nonneg)
    (fun i => pmf_real_integral_count (pa i)) (fun i => pmf_real_integral_count (pb i))
  rw [pi_count_measure] at h
  simp only [shiftedSmoothProductPMF_eq_independent, independentProductPMF_toReal]
  apply h.trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  simpa only [mul_div_assoc] using shiftedSmoothCoefficientPMF_center_l1 (a i) (b i) (S i)
    (hS i) (shiftedSmoothProductMass_coordinate_pos a S hS hZa i)
    (shiftedSmoothProductMass_coordinate_pos b S hS hZb i) (hlarge i)

theorem shiftedSmoothProductPMF_center_test {I : Type*} [Fintype I]
    (a b S : I → ℝ) (hS : ∀ i, 0 < S i)
    (hZa : 0 < shiftedSmoothProductMass a S) (hZb : 0 < shiftedSmoothProductMass b S)
    (hlarge : ∀ i, 8 * (probabilityProfileLipschitz : ℝ) ≤ S i)
    (φ : (I → ℤ) → ℂ) {B : ℝ} (hB : 0 ≤ B) (hφ : ∀ z, ‖φ z‖ ≤ B) :
    ‖(∑' z, ((shiftedSmoothProductPMF a S hS hZa z).toReal : ℂ) * φ z) -
      ∑' z, ((shiftedSmoothProductPMF b S hS hZb z).toReal : ℂ) * φ z‖ ≤
      B * (24 * (probabilityProfileLipschitz : ℝ) * ∑ i, |a i - b i| / S i) := by
  have h := pmf_image_count_test_error (shiftedSmoothProductPMF a S hS hZa) id
    (fun z => (shiftedSmoothProductPMF b S hS hZb z).toReal)
    (pmf_real_integrable _) hB
    (by simpa only [PMF.map_id] using shiftedSmoothProductPMF_center_l1 a b S hS hZa hZb hlarge) φ hφ
  have hq := pmf_image_complex_sum_eq_count_integral (shiftedSmoothProductPMF b S hS hZb) id φ hφ
  simp only [id_eq, PMF.map_id] at h hq
  rwa [← hq] at h

theorem shiftedSmoothProductPMF_recenter_test {I : Type*} [Fintype I]
    (a S : I → ℝ) (hS : ∀ i, 0 < S i) (hZa : 0 < shiftedSmoothProductMass a S)
    (hlarge : ∀ i, 8 * (probabilityProfileLipschitz : ℝ) ≤ S i)
    (φ : (I → ℤ) → ℂ) {B : ℝ} (hB : 0 ≤ B) (hφ : ∀ z, ‖φ z‖ ≤ B) :
    ‖(∑' z, ((shiftedSmoothProductPMF a S hS hZa z).toReal : ℂ) * φ z) -
      ∑' z, ((smoothProductPMF S hS z).toReal : ℂ) * φ z‖ ≤
      B * (24 * (probabilityProfileLipschitz : ℝ) * ∑ i, |a i| / S i) := by
  have hZb := shiftedSmoothProductMass_pos_of_large (0 : I → ℝ) S hlarge
  have h := shiftedSmoothProductPMF_center_test a 0 S hS hZa hZb hlarge φ hB hφ
  simpa only [shiftedSmoothProductPMF_zero, Pi.zero_apply, sub_zero] using h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SelectedResidueRefinementMean
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {K X : Type*} [Fintype K] [Fintype X]

theorem selectedResidue_bounded_mixture_error (modulus : X → ℕ)
    (hmodulus : ∀ x, 0 < modulus x) (T : Finset (ColumnResiduePattern K X modulus))
    (V : K × X → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T V z)
    (hc : ∀ r : T, 0 < shiftedSmoothProductMass
      (residueProfileCenter (boundedColumnResidueRepresentative modulus r.val) modulus)
      (residueProfileWidth modulus V)) (φ : (K × X → ℤ) → ℂ)
    (target : T → ℂ) (ε : T → ℝ)
    (he : ∀ r : T, ‖(∑' z, ((residueSmoothPMF (boundedColumnResidueRepresentative modulus r.val)
      modulus hmodulus V hV (hc r) z).toReal : ℂ) * φ z) - target r‖ ≤ ε r) :
    ‖(∑' z, ((selectedResidueSmoothPMF modulus T V hV hZ z).toReal : ℂ) * φ z) -
      ∑ r : T, (selectedResidueCellWeight modulus T V r : ℂ) * target r‖ ≤
      ∑ r : T, selectedResidueCellWeight modulus T V r * ε r := by
  rw [selectedResidueSmoothPMF_bounded_mixture modulus hmodulus T V hV hZ hc φ,
    ← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro r _
  rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (selectedResidueCellWeight_nonneg modulus T V r)]
  exact mul_le_mul_of_nonneg_left (he r) (selectedResidueCellWeight_nonneg modulus T V r)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem residueProfile_center_ratio {K X : Type*}
    (r : K × X → ℤ) (q : X → ℕ) (hq : ∀ x, 0 < q x)
    (V : K × X → ℝ) (hV : ∀ z, 0 < V z) (z : K × X) :
    |residueProfileCenter r q z| / residueProfileWidth q V z = |(r z : ℝ)| / V z := by
  have hq0 : (0 : ℝ) < q z.2 := by exact_mod_cast hq z.2
  simp only [residueProfileCenter, residueProfileWidth, abs_div, abs_neg, abs_of_pos hq0]
  field_simp [hq0.ne', (hV z).ne']

theorem residueSmoothIndexPMF_recenter_test {K X : Type*} [Fintype K] [Fintype X]
    (r : K × X → ℤ) (q : X → ℕ) (hq : ∀ x, 0 < q x)
    (V : K × X → ℝ) (hV : ∀ z, 0 < V z)
    (hc : 0 < shiftedSmoothProductMass (residueProfileCenter r q) (residueProfileWidth q V))
    (hlarge : ∀ z, 8 * (probabilityProfileLipschitz : ℝ) ≤ residueProfileWidth q V z)
    (φ : (K × X → ℤ) → ℂ) {B : ℝ} (hB : 0 ≤ B) (hφ : ∀ z, ‖φ z‖ ≤ B) :
    ‖(∑' z, ((residueSmoothIndexPMF r q hq V hV hc z).toReal : ℂ) * φ z) -
      ∑' z, ((smoothProductPMF (residueProfileWidth q V)
        (residueProfileWidth_pos q V hq hV) z).toReal : ℂ) * φ z‖ ≤
      B * (24 * (probabilityProfileLipschitz : ℝ) * ∑ z, |(r z : ℝ)| / V z) := by
  have h := shiftedSmoothProductPMF_recenter_test (residueProfileCenter r q)
    (residueProfileWidth q V) (residueProfileWidth_pos q V hq hV) hc hlarge φ hB hφ
  simpa only [residueSmoothIndexPMF, residueProfile_center_ratio r q hq V hV] using h

theorem residueSmoothPMF_recenter_test {K X : Type*} [Fintype K] [Fintype X]
    (r : K × X → ℤ) (q : X → ℕ) (hq : ∀ x, 0 < q x)
    (V : K × X → ℝ) (hV : ∀ z, 0 < V z)
    (hc : 0 < shiftedSmoothProductMass (residueProfileCenter r q) (residueProfileWidth q V))
    (hlarge : ∀ z, 8 * (probabilityProfileLipschitz : ℝ) ≤ residueProfileWidth q V z)
    (φ : (K × X → ℤ) → ℂ) {B : ℝ} (hB : 0 ≤ B) (hφ : ∀ z, ‖φ z‖ ≤ B) :
    ‖(∑' z, ((residueSmoothPMF r q hq V hV hc z).toReal : ℂ) * φ z) -
      ∑' z, ((smoothProductPMF (residueProfileWidth q V)
        (residueProfileWidth_pos q V hq hV) z).toReal : ℂ) * φ (residueLatticeArray r q z)‖ ≤
      B * (24 * (probabilityProfileLipschitz : ℝ) * ∑ z, |(r z : ℝ)| / V z) := by
  rw [residueSmoothPMF_expectation]
  exact residueSmoothIndexPMF_recenter_test r q hq V hV hc hlarge
    (fun z => φ (residueLatticeArray r q z)) hB (fun z => hφ _)

theorem boundedResidueSmoothPMF_recenter_test {K X : Type*} [Fintype K] [Fintype X]
    (q : X → ℕ) (hq : ∀ x, 0 < q x) (r : ColumnResiduePattern K X q)
    (V : K × X → ℝ) (hV : ∀ z, 0 < V z)
    (hc : 0 < shiftedSmoothProductMass (residueProfileCenter (boundedColumnResidueRepresentative q r) q)
      (residueProfileWidth q V))
    (hlarge : ∀ z, 8 * (probabilityProfileLipschitz : ℝ) ≤ residueProfileWidth q V z)
    (φ : (K × X → ℤ) → ℂ) {B : ℝ} (hB : 0 ≤ B) (hφ : ∀ z, ‖φ z‖ ≤ B) :
    ‖(∑' z, ((residueSmoothPMF (boundedColumnResidueRepresentative q r) q hq V hV hc z).toReal : ℂ) * φ z) -
      ∑' z, ((smoothProductPMF (residueProfileWidth q V)
        (residueProfileWidth_pos q V hq hV) z).toReal : ℂ) *
          φ (residueLatticeArray (boundedColumnResidueRepresentative q r) q z)‖ ≤
      B * (24 * (probabilityProfileLipschitz : ℝ) * ∑ z : K × X, (q z.2 : ℝ) / V z) := by
  apply (residueSmoothPMF_recenter_test (boundedColumnResidueRepresentative q r) q hq V hV hc
    hlarge φ hB hφ).trans
  apply mul_le_mul_of_nonneg_left _ hB
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro z _
  have hr := boundedColumnResidueRepresentative_bounds q hq r z
  have hr0 : (0 : ℝ) ≤ boundedColumnResidueRepresentative q r z := by exact_mod_cast hr.1
  apply div_le_div_of_nonneg_right _ (hV z).le
  rw [abs_of_nonneg hr0]
  exact_mod_cast hr.2.le

theorem selectedResidueSmoothPMF_recenter_test {K X : Type*} [Fintype K] [Fintype X]
    (q : X → ℕ) (hq : ∀ x, 0 < q x) (T : Finset (ColumnResiduePattern K X q))
    (V : K × X → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight q T V z)
    (hlarge : ∀ z, 8 * (probabilityProfileLipschitz : ℝ) ≤ residueProfileWidth q V z)
    (φ : (K × X → ℤ) → ℂ) {B : ℝ} (hB : 0 ≤ B) (hφ : ∀ z, ‖φ z‖ ≤ B) :
    ‖(∑' z, ((selectedResidueSmoothPMF q T V hV hZ z).toReal : ℂ) * φ z) -
      ∑ r : T, (selectedResidueCellWeight q T V r : ℂ) *
        ∑' z, ((smoothProductPMF (residueProfileWidth q V)
          (residueProfileWidth_pos q V hq hV) z).toReal : ℂ) *
            φ (residueLatticeArray (boundedColumnResidueRepresentative q r.val) q z)‖ ≤
      B * (24 * (probabilityProfileLipschitz : ℝ) * ∑ z : K × X, (q z.2 : ℝ) / V z) := by
  have hc (r : T) := shiftedSmoothProductMass_pos_of_large
    (residueProfileCenter (boundedColumnResidueRepresentative q r.val) q) (residueProfileWidth q V) hlarge
  have h := selectedResidue_bounded_mixture_error q hq T V hV hZ hc φ _
    (fun _ => B * (24 * (probabilityProfileLipschitz : ℝ) * ∑ z : K × X, (q z.2 : ℝ) / V z))
    (fun r => boundedResidueSmoothPMF_recenter_test q hq r.val V hV (hc r) hlarge φ hB hφ)
  simpa only [← Finset.sum_mul, selectedResidueCellWeight_sum q T V hV hZ, one_mul] using h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.PhysicalResidueOffsetShift
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

theorem physicalCubeRootDifferences_residue {K X α : Type*} [Fintype K]
    (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
    (residue : Option K × X → ℤ) (modulus : X → ℕ) (z : Option K × X → ℤ) :
    physicalCubeRootDifferences root D base (residueLatticeArray residue modulus z) =
      physicalCubeResidueCoordinates root D base residue modulus z := by
  funext x i
  have hoff : physicalCubeOffset (0 : X → ℤ) x i = 0 := by cases i <;> rfl
  simp only [physicalCubeResidueCoordinates, physicalCubeRootDifferences,
    residueLatticeArray, hoff, zero_add, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  rw [← add_assoc]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  ring

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

theorem physicalSelectedResidue_recenter_test {K X α : Type*} [Fintype K] [Fintype X]
    (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
    (q : X → ℕ) (hq : ∀ x, 0 < q x) (T : Finset (ColumnResiduePattern (Option K) X q))
    (V : Option K × X → ℝ) (hV : ∀ z, 0 < V z)
    (hmass : 0 < ∑' z, selectedResidueSmoothWeight q T V z)
    (hlarge : ∀ z, 8 * (probabilityProfileLipschitz : ℝ) ≤ residueProfileWidth q V z)
    (φ : (X → (Unit ⊕ α) → ℤ) → ℂ) {B Z : ℝ}
    (hB : 0 ≤ B) (hφ : ∀ v, ‖φ v‖ ≤ B) (hZ : 0 < Z) :
    ‖(∑' z, ((selectedResidueSmoothPMF q T V hV hmass z).toReal : ℂ) *
        φ (physicalCubeRootDifferences root D base z)) / (Z : ℂ) -
      (∑ r : T, (selectedResidueCellWeight q T V r : ℂ) *
        ∑' z, ((smoothProductPMF (residueProfileWidth q V)
          (residueProfileWidth_pos q V hq hV) z).toReal : ℂ) *
            φ (physicalCubeResidueCoordinates root D base (boundedColumnResidueRepresentative q r.val) q z)) /
          (Z : ℂ)‖ ≤
      (B * (24 * (probabilityProfileLipschitz : ℝ) * ∑ z : Option K × X, (q z.2 : ℝ) / V z)) / Z := by
  have h := selectedResidueSmoothPMF_recenter_test q hq T V hV hmass hlarge
    (fun z => φ (physicalCubeRootDifferences root D base z)) hB (fun z => hφ _)
  simp_rw [physicalCubeRootDifferences_residue] at h
  rw [← sub_div, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hZ]
  exact div_le_div_of_nonneg_right h hZ.le

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

theorem physicalSelectedResidue_width_recenter_s2_oai {K X α : Type*} [Fintype K] [Fintype X]
    (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
    (q : X → ℕ) (hq : ∀ x, 0 < q x) (T : Finset (ColumnResiduePattern (Option K) X q))
    (V : Option K × X → ℝ) (hV : ∀ z, 0 < V z)
    (hmass : 0 < ∑' z, selectedResidueSmoothWeight q T V z)
    {ρ : ℝ} (hρ : 8 * (probabilityProfileLipschitz : ℝ) ≤ ρ)
    (hwidth : ∀ z, ρ ≤ residueProfileWidth q V z)
    (φ : (X → (Unit ⊕ α) → ℤ) → ℂ) {B Z : ℝ}
    (hB : 0 ≤ B) (hφ : ∀ v, ‖φ v‖ ≤ B) (hZ : 0 < Z) :
    ‖(∑' z, ((selectedResidueSmoothPMF q T V hV hmass z).toReal : ℂ) *
        φ (physicalCubeRootDifferences root D base z)) / (Z : ℂ) -
      (∑ r : T, (selectedResidueCellWeight q T V r : ℂ) *
        ∑' z, ((smoothProductPMF (residueProfileWidth q V)
          (residueProfileWidth_pos q V hq hV) z).toReal : ℂ) *
            φ (physicalCubeResidueCoordinates root D base (boundedColumnResidueRepresentative q r.val) q z)) /
          (Z : ℂ)‖ ≤
      (B * (24 * (probabilityProfileLipschitz : ℝ) * Fintype.card (Option K × X) / ρ)) / Z := by
  have hρ0 : 0 < ρ := by linarith [probabilityProfileLipschitz_one_le]
  have hratio (z : Option K × X) : (q z.2 : ℝ) / V z ≤ 1 / ρ := by
    have hq0 : (0 : ℝ) < q z.2 := by exact_mod_cast hq z.2
    have h := (le_div_iff₀ hq0).mp (hwidth z)
    apply (div_le_div_iff₀ (hV z) hρ0).mpr
    linarith
  have hsum : (∑ z : Option K × X, (q z.2 : ℝ) / V z) ≤ Fintype.card (Option K × X) / ρ := by
    apply (Finset.sum_le_sum (fun z _ => hratio z)).trans_eq
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one_div]
  apply (physicalSelectedResidue_recenter_test root D base q hq T V hV hmass
    (fun z => hρ.trans (hwidth z)) φ hB hφ hZ).trans
  apply div_le_div_of_nonneg_right _ hZ.le
  apply mul_le_mul_of_nonneg_left _ hB
  simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hsum
    (show 0 ≤ 24 * (probabilityProfileLipschitz : ℝ) by positivity)

end Erdos3.BooleanCubeKernel

end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.Erdos3.BooleanCubeKernel.physicalSelectedResidue_width_recenter_s2_oai.{u_1, u_2, u_3} := @OAI.Erdos3.BooleanCubeKernel.physicalSelectedResidue_width_recenter_s2_oai.{u_1, u_2, u_3}
