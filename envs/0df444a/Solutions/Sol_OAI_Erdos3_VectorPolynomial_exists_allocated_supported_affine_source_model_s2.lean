-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.exists_allocated_supported_affine_source_model_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T06:30:45.012684+00:00
-- url     : https://prove2.me/submissions/b75e83fa-b6ac-4402-ab3a-7b351dddf485

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B236
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedAffineRowIdeal_cutoff_fixes_mean_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedProductChartDensityApproximation_error_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedSupportedSlicedProductProfile_combined_error_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_allocated_global_masked_affine_ideal_approximation_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.PairedProductDensity
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem densityMixture_section_integrable {T X : Type*} [MeasurableSpace T]
    (μ : Measure T) (F : T → X → ℝ) (C : T → ℝ) (hC : Integrable C μ)
    (hm : ∀ x, AEStronglyMeasurable (fun t => F t x) μ)
    (hbound : ∀ᵐ t ∂μ, ∀ x, ‖F t x‖ ≤ C t) (x : X) :
    Integrable (fun t => F t x) μ :=
  hC.mono' (hm x) (hbound.mono (fun _ ht => ht x))

theorem densityMixture_cap {T X : Type*} [MeasurableSpace T]
    (μ : Measure T) (F : T → X → ℝ) (C : T → ℝ) (hC : Integrable C μ)
    (hm : ∀ x, AEStronglyMeasurable (fun t => F t x) μ)
    (hbound : ∀ᵐ t ∂μ, ∀ x, F t x ∈ Set.Icc (0 : ℝ) (C t)) (x : X) :
    densityMixture μ F x ∈ Set.Icc (0 : ℝ) (∫ t, C t ∂μ) := by
  have hb : ∀ᵐ t ∂μ, ∀ y, ‖F t y‖ ≤ C t := hbound.mono fun t ht y => by
    rw [Real.norm_of_nonneg (ht y).1]
    exact (ht y).2
  exact ⟨integral_nonneg_of_ae (hbound.mono (fun _ ht => (ht x).1)),
    integral_mono_ae (densityMixture_section_integrable μ F C hC hm hb x) hC
      (hbound.mono (fun _ ht => (ht x).2))⟩

theorem densityMixture_lipschitz {T X : Type*} [MeasurableSpace T] [PseudoMetricSpace X]
    (μ : Measure T) (F : T → X → ℝ) (L : T → ℝ≥0)
    (hL : Integrable (fun t => (L t : ℝ)) μ)
    (hint : ∀ x, Integrable (fun t => F t x) μ)
    (hLip : ∀ᵐ t ∂μ, LipschitzWith (L t) (F t)) :
    LipschitzWith ⟨∫ t, (L t : ℝ) ∂μ, integral_nonneg (fun t => (L t).coe_nonneg)⟩
      (densityMixture μ F) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq]
  change |(∫ t, F t x ∂μ) - ∫ t, F t y ∂μ| ≤ _
  rw [← integral_sub (hint x) (hint y)]
  have hb : ∀ᵐ t ∂μ, ‖F t x - F t y‖ ≤ (L t : ℝ) * dist x y := by
    filter_upwards [hLip] with t ht
    simpa only [Real.dist_eq, Real.norm_eq_abs] using ht.dist_le_mul x y
  have h := norm_integral_le_of_norm_le (hL.mul_const (dist x y)) hb
  rw [Real.norm_eq_abs, integral_mul_const] at h
  exact h

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem densityMixture_uniform_bound {T X : Type*} [MeasurableSpace T] [PseudoMetricSpace X]
    (μ : Measure T) [IsProbabilityMeasure μ] (F : T → X → ℝ) (C L : ℝ≥0)
    (hm : ∀ x, AEStronglyMeasurable (fun t => F t x) μ)
    (hF : ∀ᵐ t ∂μ, (∀ x, F t x ∈ Set.Icc (0 : ℝ) C) ∧ LipschitzWith L (F t)) :
    (∀ x, densityMixture μ F x ∈ Set.Icc (0 : ℝ) C) ∧ LipschitzWith L (densityMixture μ F) := by
  have hb : ∀ᵐ t ∂μ, ∀ x, ‖F t x‖ ≤ (C : ℝ) := by
    filter_upwards [hF] with t ht
    intro x
    rw [Real.norm_of_nonneg (ht.1 x).1]
    exact (ht.1 x).2
  have hi := densityMixture_section_integrable μ F (fun _ => (C : ℝ)) (integrable_const _) hm hb
  constructor
  · intro x
    have h := densityMixture_cap μ F (fun _ => (C : ℝ)) (integrable_const _) hm
      (hF.mono (fun _ ht => ht.1)) x
    simpa only [integral_const, probReal_univ, one_smul] using h
  · have h := densityMixture_lipschitz μ F (fun _ => L) (integrable_const _) hi
      (hF.mono (fun _ ht => ht.2))
    have heq : (⟨∫ _ : T, (L : ℝ) ∂μ, integral_nonneg (fun _ => L.coe_nonneg)⟩ : ℝ≥0) = L := by
      apply Subtype.ext
      simp
    rw [heq] at h
    exact h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SplitSmoothProductProfile
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem tensorCutoffWeight_tsupport {ι : Type*} {E : ι → Type*} [Fintype ι] [∀ i, TopologicalSpace (E i)]
    (w : ∀ i, E i → ℝ) :
    tsupport (tensorCutoffWeight w) ⊆ {x | ∀ i, x i ∈ tsupport (w i)} := by
  have hc : IsClosed {x : ∀ i, E i | ∀ i, x i ∈ tsupport (w i)} := by
    have he : {x : ∀ i, E i | ∀ i, x i ∈ tsupport (w i)} =
        ⋂ i, (fun x : ∀ i, E i => x i) ⁻¹' tsupport (w i) := by ext; simp
    rw [he]
    exact isClosed_iInter (fun i => (isClosed_tsupport _).preimage (continuous_apply i))
  apply closure_minimal _ hc
  intro x hx i
  apply subset_closure
  change w i (x i) ≠ 0
  intro hz
  exact hx (Finset.prod_eq_zero (Finset.mem_univ i) hz)

theorem tensorCutoffWeight_compact {ι : Type*} {E : ι → Type*} [Fintype ι] [∀ i, TopologicalSpace (E i)]
    (w : ∀ i, E i → ℝ) (hw : ∀ i, HasCompactSupport (w i)) :
    HasCompactSupport (tensorCutoffWeight w) :=
  (isCompact_pi_infinite hw).of_isClosed_subset (isClosed_tsupport _)
    (tensorCutoffWeight_tsupport w)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal ContDiff BigOperators

theorem smoothProductProfile_contDiff (I : Type*) [Fintype I] :
    ContDiff ℝ ∞ (smoothProductProfile I) := by
  rw [smoothProductProfile_eq_cutoff]
  exact contDiff_coordinateBoxCutoff _ smoothProbabilityProfile_contDiff 1

theorem smoothProductProfile_compact (I : Type*) [Fintype I] :
    HasCompactSupport (smoothProductProfile I) := by
  rw [smoothProductProfile_eq_cutoff]
  exact hasCompactSupport_coordinateBoxCutoff _ smoothProbabilityProfile_zero zero_lt_one

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BooleanCubeModeWitness
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem booleanCoefficient_map {α R S : Type*} [DecidableEq α] [CommRing R] [CommRing S]
    (φ : R →+* S) (f : Finset α → R) (s : Finset α) :
    φ (booleanCoefficient f s) = booleanCoefficient (fun t => φ (f t)) s := by
  simp only [booleanCoefficient, map_sum, map_mul, map_pow, map_neg, map_one]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialDeterminantDerivativeBound
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem booleanAffinePolynomial_eval {B F α : Type*} [Fintype α] [DecidableEq α]
    (a : BlockParameter B F α → ℝ) (b : B) (v : F) (t : Finset α) :
    MvPolynomial.eval a (booleanAffinePolynomial b v t) =
      ∑ r : Option α, (booleanFeature r t : ℝ) * a (b, v, r) := by
  simp only [booleanAffinePolynomial, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BooleanMinorDimension
namespace OAI

section

namespace Erdos3

open scoped BigOperators ContDiff

variable {B F α O : Type*} [Fintype B] [Fintype F] [Fintype α]
  [DecidableEq B] [DecidableEq F] [DecidableEq α]

omit [DecidableEq B] [DecidableEq F] in
theorem booleanSamplerMap_formula (c : B → ℝ) (sets : O → Finset α)
    (a : BlockParameter B F α → ℝ) (o : O) :
    booleanSamplerMap c sets a o = booleanCoefficient
      (fun t => ∑ b : B, c b * ∏ k : F, ∑ r : Option α, (booleanFeature r t : ℝ) * a (b, k, r)) (sets o) := by
  simp only [booleanSamplerMap, booleanSamplerPolynomial, booleanCoefficient_map, map_sum,
    map_mul, MvPolynomial.eval_C, booleanBlockPolynomial, map_prod, booleanAffinePolynomial_eval]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.BooleanSamplerMeasurability
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem jointBooleanSampler_formula {D α : Type*} [Fintype α] [DecidableEq α]
    {B O : D → Type*} [∀ d, Fintype (B d)] (h : D → ℕ) (c : ∀ d, B d → ℝ)
    (sets : ∀ d, O d → Finset α) (x : JointBlockParameter B h α → ℝ) (o : Σ d, O d) :
    jointBooleanSampler h c sets x o = booleanCoefficient
      (fun t => ∑ b : B o.1, c o.1 b * ∏ v : Fin (h o.1),
        ∑ r : Option α, (booleanFeature r t : ℝ) * x ⟨o.1, (b, v, r)⟩) (sets o.1 o.2) := by
  apply booleanSamplerMap_formula

theorem jointBooleanSampler_measurable_comp {Ω D α : Type*} [MeasurableSpace Ω]
    [Fintype α] [DecidableEq α] {B O : D → Type*} [∀ d, Fintype (B d)]
    (h : D → ℕ) (sets : ∀ d, O d → Finset α)
    (c : Ω → ∀ d, B d → ℝ) (hc : ∀ d b, Measurable (fun ω => c ω d b))
    (x : Ω → JointBlockParameter B h α → ℝ) (hx : ∀ i, Measurable (fun ω => x ω i)) :
    Measurable (fun ω => jointBooleanSampler h (c ω) sets (x ω)) := by
  apply measurable_pi_iff.mpr
  intro o
  simp_rw [jointBooleanSampler_formula, booleanCoefficient]
  fun_prop

theorem jointBooleanSampler_measurable_frozen {Ω D α : Type*} [MeasurableSpace Ω]
    [Fintype α] [DecidableEq α] {B O : D → Type*} [∀ d, Fintype (B d)]
    (h : D → ℕ) (sets : ∀ d, O d → Finset α)
    (c : Ω → ∀ d, B d → ℝ) (hc : ∀ d b, Measurable (fun a => c a d b)) :
    Measurable (fun p : Ω × (JointBlockParameter B h α → ℝ) =>
      jointBooleanSampler h (c p.1) sets p.2) :=
  jointBooleanSampler_measurable_comp (Ω := Ω × (JointBlockParameter B h α → ℝ)) h sets
    (fun p => c p.1) (fun d b => (hc d b).comp measurable_fst)
    (fun p => p.2) (fun i => (measurable_pi_apply i).comp measurable_snd)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineCoefficientLaw
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators ContDiff

theorem affineProductProfile_compact {I : Type*} [Fintype I] (c w : I → ℝ)
    (hw : ∀ i, 0 < w i) : HasCompactSupport (affineProductProfile c w) :=
  tensorCutoffWeight_compact (fun i => affineProbabilityProfile (c i) (w i))
    (fun i => affineProbabilityProfile_compact (c i) (hw i))

theorem affineProductProfile_integrable {I : Type*} [Fintype I] (c w : I → ℝ)
    (hw : ∀ i, 0 < w i) : Integrable (affineProductProfile c w) :=
  (affineProductProfile_contDiff c w).continuous.integrable_of_hasCompactSupport
    (affineProductProfile_compact c w hw)

theorem affineProductProfile_integral {I : Type*} [Fintype I] (c w : I → ℝ)
    (hw : ∀ i, 0 < w i) : (∫ x, affineProductProfile c w x) = 1 := by
  change (∫ x, tensorCutoffWeight (fun i => affineProbabilityProfile (c i) (w i)) x) = 1
  rw [tensorCutoffWeight_integral]
  simp only [affineProbabilityProfile_integral _ (hw _), Finset.prod_const_one]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UnitCoefficientSourceMarginal
namespace OAI

section

namespace Erdos3

open MeasureTheory

instance unitCoefficientSource_probability (I : Type*) [Fintype I] :
    IsProbabilityMeasure (unitCoefficientSource I) :=
  realDensityMeasure_probability volume _
    ((smoothProductProfile_contDiff I).continuous.integrable_of_hasCompactSupport (smoothProductProfile_compact I))
    (fun r => (smoothProductProfile_range I r).1) (smoothProductProfile_integral I)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.RegularizedSigmaDensity
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem affineProductProfile_measurable_center {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (c x : Ω → I → ℝ) (w : I → ℝ)
    (hc : ∀ i, Measurable (fun a => c a i)) (hx : ∀ i, Measurable (fun a => x a i)) :
    Measurable (fun a => affineProductProfile (c a) w (x a)) := by
  unfold affineProductProfile affineProbabilityProfile
  apply Finset.measurable_prod
  intro i _
  exact measurable_const.mul (smoothProbabilityProfile_contDiff.continuous.measurable.comp
    (((hx i).sub (hc i)).div_const (w i)))

theorem regularizedImageDensity_joint_measurable {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (U : Ω → I → ℝ) (hU : Measurable U) (δ : ℝ≥0) :
    Measurable (fun p : Ω × (I → ℝ) => affineProductProfile (U p.1) (fun _ => (δ : ℝ)) p.2) :=
  affineProductProfile_measurable_center _ _ _
    (fun i => (measurable_pi_apply i).comp (hU.comp measurable_fst))
    (fun i => (measurable_pi_apply i).comp measurable_snd)

theorem regularizedImageDensity_probability {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : Ω → I → ℝ) (hU : Measurable U)
    (δ : ℝ≥0) (hδ : 0 < δ) :
    (∀ x, 0 ≤ regularizedImageDensity μ U δ x) ∧ Integrable (regularizedImageDensity μ U δ) ∧
      (∫ x, regularizedImageDensity μ U δ x) = 1 := by
  apply densityMixture_probability_density μ volume _ (regularizedImageDensity_joint_measurable U hU δ)
  exact Filter.Eventually.of_forall (fun a =>
    ⟨affineProductProfile_nonneg (U a) _ (fun _ => hδ),
      affineProductProfile_integrable (U a) _ (fun _ => hδ),
      affineProductProfile_integral (U a) _ (fun _ => hδ)⟩)

theorem regularizedImageDensity_bounds {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : Ω → I → ℝ) (hU : Measurable U)
    (δ : ℝ≥0) (hδ : 0 < δ) :
    (∀ x, regularizedImageDensity μ U δ x ∈ Set.Icc (0 : ℝ) (δ⁻¹ ^ Fintype.card I : ℝ≥0)) ∧
      LipschitzWith (affineProductProfileLip I δ) (regularizedImageDensity μ U δ) := by
  apply densityMixture_uniform_bound μ _ (δ⁻¹ ^ Fintype.card I) (affineProductProfileLip I δ)
  · intro x
    exact ((regularizedImageDensity_joint_measurable U hU δ).comp
      (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  · apply Filter.Eventually.of_forall
    intro a
    refine ⟨?_, affineProductProfile_lipschitz (U a) (fun _ => (δ : ℝ)) hδ (fun _ => le_rfl)⟩
    intro x
    have hn := affineProductProfile_nonneg (U a) (fun _ => (δ : ℝ)) (fun _ => hδ) x
    have hc := affineProductProfile_cap (U a) (fun _ => (δ : ℝ)) hδ (fun _ => le_rfl) x
    rw [Real.norm_of_nonneg hn] at hc
    exact ⟨hn, hc⟩

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem conditionalRegularizedDensity_measurable {W X I : Type*}
    [MeasurableSpace W] [MeasurableSpace X] [Fintype I]
    (ν : Measure X) [SFinite ν] (U : W × X → I → ℝ) (hU : Measurable U) (δ : ℝ≥0) :
    Measurable (fun p : W × (I → ℝ) => regularizedImageDensity ν (fun x => U (p.1, x)) δ p.2) := by
  have hm := affineProductProfile_measurable_center
    (fun p : (W × (I → ℝ)) × X => U (p.1.1, p.2)) (fun p => p.1.2) (fun _ => (δ : ℝ))
    (fun i => (measurable_pi_apply i).comp (hU.comp
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd)))
    (fun i => (measurable_pi_apply i).comp (measurable_snd.comp measurable_fst))
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ConstantJetPostprocessing
namespace OAI

section

namespace Erdos3

theorem booleanConstantJet_measurable_comp {Ω D α : Type*} [MeasurableSpace Ω] [DecidableEq α]
    {O : D → Type*} (sets : ∀ d, O d → Finset α)
    (constant : Ω → D → ℝ) (hc : ∀ d, Measurable (fun a => constant a d)) :
    Measurable (fun a => booleanConstantJet sets (constant a)) := by
  apply measurable_pi_iff.mpr
  intro o
  by_cases hs : sets o.1 o.2 = ∅
  · simpa only [booleanConstantJet, hs, ite_true] using hc o.1
  · simpa only [booleanConstantJet, hs, ite_false] using
      (measurable_const : Measurable (fun _ : Ω => (0 : ℝ)))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ProgressionTupleSliceSupport
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

namespace FiniteProbabilityWeights

theorem condition_weight_pos_iff {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (p : FiniteProbabilityWeights Ω) (S : Finset Ω) (hS : 0 < p.mass S) (x : Ω) :
    0 < (p.condition S hS).weight x ↔ x ∈ S ∧ 0 < p.weight x := by
  change 0 < (if x ∈ S then p.weight x else 0) / p.mass S ↔ _
  rw [lt_div_iff₀ hS, zero_mul]
  by_cases hx : x ∈ S <;> simp [hx]

end FiniteProbabilityWeights

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ActiveProfileNoise
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

variable {D G Z α : Type*} [Fintype D] [Fintype G] [Fintype Z] [Fintype α] [DecidableEq α]
  {B : D → Type*} [∀ d, Fintype (B d)] (h : D → ℕ)
  (P : D → Prop) [DecidablePred P]
  {O : {d // ¬P d} → Type*} [∀ d, Fintype (O d)]
  (sets : ∀ d, O d → Finset α)

omit [Fintype D] [Fintype G] [Fintype Z] [DecidablePred P] [∀ d, Fintype (O d)] in
theorem partitionedIdealMap_measurable {Ω : Type*} [MeasurableSpace Ω]
    (z : Ω → PartitionedProfileNoiseIndex G Z α B h P → ℝ)
    (hz : ∀ j, Measurable (fun a => z a j)) :
    Measurable (fun p : Ω ×
      (PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d) → ℝ) =>
      partitionedIdealMap h P sets (z p.1) p.2) := by
  have hc (d : {d // ¬P d}) (b : B d.val) : Measurable (fun a =>
      partitionedProfilePrincipal h P (unitProfilePrincipalSize (B := B)) (z a) d b) := by
    dsimp [partitionedProfilePrincipal]
    exact measurable_const.add (measurable_const.mul (hz _))
  have hb : Measurable (fun a => booleanConstantJet sets
      (partitionedProfileConstant h P (fun _ => 1 / 4) (z a))) := by
    apply booleanConstantJet_measurable_comp sets
      (fun a => partitionedProfileConstant h P (fun _ => 1 / 4) (z a))
    intro d
    dsimp [partitionedProfileConstant]
    exact measurable_const.mul (hz _)
  unfold partitionedIdealMap
  exact (hb.comp measurable_fst).add
    (jointBooleanSampler_measurable_frozen (fun d : {d // ¬P d} => h d.val) sets
      (fun a => partitionedProfilePrincipal h P (unitProfilePrincipalSize (B := B)) (z a)) hc)

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem profileNoiseWithActive_measurable {Ω D G Z α : Type*} [MeasurableSpace Ω]
    {B : D → Type*} (h : D → ℕ) (P : D → Prop) [DecidablePred P]
    (z : Ω → PartitionedProfileNoiseIndex G Z α B h P → ℝ)
    (r : Ω → ActiveProfileCoefficientIndex G B h P → ℝ)
    (hz : ∀ j, Measurable (fun a => z a j)) (hr : ∀ j, Measurable (fun a => r a j))
    (j : PartitionedProfileNoiseIndex G Z α B h P) :
    Measurable (fun a => profileNoiseWithActive h P (z a) (r a) j) := by
  rcases j with j | ⟨d, e⟩
  · exact hz _
  · by_cases hp : P d
    · simpa only [profileNoiseWithActive, dif_pos hp] using hz (.inr ⟨d, e⟩)
    · simpa only [profileNoiseWithActive, dif_neg hp] using hr ⟨⟨d, hp⟩, e⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedTailProfileIdentity
namespace OAI

section

namespace Erdos3
open MeasureTheory
open scoped NNReal

variable {D G Z α : Type*} [Fintype D] [Fintype G] [Fintype Z] [Fintype α] [DecidableEq α]
  {B : D → Type*} [∀ d, Fintype (B d)] (h : D → ℕ)
  (P : D → Prop) [DecidablePred P]
  {O : {d // ¬P d} → Type*} [∀ d, Fintype (O d)]
  (sets : ∀ d, O d → Finset α)

theorem partitionedSlicedIdealMap_measurable {Ω : Type*} [MeasurableSpace Ω]
    (z : Ω → PartitionedProfileNoiseIndex G Z α B h P → ℝ)
    (hz : ∀ j, Measurable (fun a => z a j))
    (center width : Ω → PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d) → ℝ)
    (hb : ∀ i, Measurable (fun a => center a i)) (hw : ∀ i, Measurable (fun a => width a i)) :
    Measurable (fun p : Ω ×
      (PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d) → ℝ) =>
      partitionedIdealMap h P sets (z p.1) (fun i => center p.1 i + width p.1 i * p.2 i)) := by
  let _ : Fintype D := inferInstance
  let _ : Fintype G := inferInstance
  let _ : Fintype Z := inferInstance
  let _ : DecidablePred P := inferInstance
  let _ : ∀ index, Fintype (O index) := inferInstance
  have hi : Measurable (fun p : Ω ×
      (PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d) → ℝ) =>
      (p.1, fun i => center p.1 i + width p.1 i * p.2 i)) :=
    measurable_fst.prodMk (measurable_pi_iff.mpr (fun i =>
      ((hb i).comp measurable_fst).add (((hw i).comp measurable_fst).mul
        ((measurable_pi_apply i).comp measurable_snd))))
  exact (partitionedIdealMap_measurable h P sets z hz).comp
    (f := fun p : Ω ×
      (PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d) → ℝ) =>
      (p.1, fun i => center p.1 i + width p.1 i * p.2 i)) hi

theorem partitionedSlicedRegularizedIdeal_measurable {Ω : Type*} [MeasurableSpace Ω]
    (ρ : ℝ≥0) (z : Ω → PartitionedProfileNoiseIndex G Z α B h P → ℝ)
    (hz : ∀ j, Measurable (fun a => z a j))
    (center width : Ω → PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d) → ℝ)
    (hb : ∀ i, Measurable (fun a => center a i)) (hw : ∀ i, Measurable (fun a => width a i)) :
    Measurable (fun p : Ω × ((Σ d, O d) → ℝ) =>
      partitionedSlicedRegularizedIdeal h P sets ρ (center p.1) (width p.1) (z p.1) p.2) :=
  conditionalRegularizedDensity_measurable _ _
    (partitionedSlicedIdealMap_measurable h P sets z hz center width hb hw) ρ

theorem partitionedSlicedIdealMap_measurable_fixed
    (center width : PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d) → ℝ)
    (z : PartitionedProfileNoiseIndex G Z α B h P → ℝ) :
    Measurable (fun x : PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d) → ℝ => partitionedIdealMap h P sets z (fun i => center i + width i * x i)) := by
  have hm := partitionedSlicedIdealMap_measurable (Ω := Unit) h P sets (fun _ => z)
    (fun _ => measurable_const) (fun _ => center) (fun _ => width)
    (fun _ => measurable_const) (fun _ => measurable_const)
  exact hm.comp (f := fun x : PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d) → ℝ => ((), x))
    (measurable_const.prodMk measurable_id)

theorem partitionedSlicedRegularizedIdeal_probability (ρ : ℝ≥0) (hρ : 0 < ρ)
    (center width : PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d) → ℝ)
    (z : PartitionedProfileNoiseIndex G Z α B h P → ℝ) :
    (∀ x, 0 ≤ partitionedSlicedRegularizedIdeal h P sets ρ center width z x) ∧
    Integrable (partitionedSlicedRegularizedIdeal h P sets ρ center width z) ∧
    (∫ x, partitionedSlicedRegularizedIdeal h P sets ρ center width z x) = 1 := by
  apply regularizedImageDensity_probability _ _ _ ρ hρ
  exact partitionedSlicedIdealMap_measurable_fixed h P sets center width z

theorem partitionedSlicedRegularizedIdeal_bounds (ρ : ℝ≥0) (hρ : 0 < ρ)
    (center width : PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d) → ℝ)
    (z : PartitionedProfileNoiseIndex G Z α B h P → ℝ) :
    (∀ x, partitionedSlicedRegularizedIdeal h P sets ρ center width z x ∈
      Set.Icc (0 : ℝ) (ρ⁻¹ ^ Fintype.card (Σ d, O d) : ℝ≥0)) ∧
    LipschitzWith (affineProductProfileLip (Σ d, O d) ρ)
      (partitionedSlicedRegularizedIdeal h P sets ρ center width z) := by
  apply regularizedImageDensity_bounds _ _ _ ρ hρ
  exact partitionedSlicedIdealMap_measurable_fixed h P sets center width z

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped NNReal

variable {D G α : Type*} [Fintype D] [Fintype G] [Fintype α] [DecidableEq α]
  (Z : Type*) [Fintype Z] {B : D → Type*} [∀ d, Fintype (B d)] (h : D → ℕ)
  (P : D → Prop) [DecidablePred P]
  {O : {d // ¬P d} → Type*} [∀ d, Fintype (O d)] (sets : ∀ d, O d → Finset α)

theorem activeSlicedProfileIdeal_measurable (ρ : ℝ≥0)
    (center width : PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d) → ℝ) :
    Measurable (Function.uncurry (activeSlicedProfileIdeal (G := G) (B := B) Z h P sets ρ center width)) := by
  apply partitionedSlicedRegularizedIdeal_measurable h P sets ρ _ _
    (fun _ => center) (fun _ => width) (fun _ => measurable_const) (fun _ => measurable_const)
  intro j
  exact profileNoiseWithActive_measurable h P (fun _ _ => 0) id
    (fun _ => measurable_const) (fun i => measurable_pi_apply i) j

theorem activeAveragedSlicedProfileIdeal_spec (ρ : ℝ≥0) (hρ : 0 < ρ)
    (center width : PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d) → ℝ) :
    (∀ v, activeAveragedSlicedProfileIdeal (G := G) (B := B) Z h P sets ρ center width v ∈
      Set.Icc (0 : ℝ) (ρ⁻¹ ^ Fintype.card (Σ d, O d) : ℝ≥0)) ∧
    LipschitzWith (affineProductProfileLip (Σ d, O d) ρ)
      (activeAveragedSlicedProfileIdeal (G := G) (B := B) Z h P sets ρ center width) ∧
    Integrable (activeAveragedSlicedProfileIdeal (G := G) (B := B) Z h P sets ρ center width) ∧
    (∫ v, activeAveragedSlicedProfileIdeal (G := G) (B := B) Z h P sets ρ center width v) = 1 := by
  have hm := activeSlicedProfileIdeal_measurable (G := G) (B := B) Z h P sets ρ center width
  have hb := densityMixture_uniform_bound (unitCoefficientSource (ActiveProfileCoefficientIndex G B h P))
    (activeSlicedProfileIdeal Z h P sets ρ center width) (ρ⁻¹ ^ Fintype.card (Σ d, O d))
    (affineProductProfileLip (Σ d, O d) ρ)
    (fun v => (hm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
    (Filter.Eventually.of_forall (fun r => partitionedSlicedRegularizedIdeal_bounds h P sets ρ hρ center width
      (profileNoiseWithActive (Z := Z) h P (fun _ => 0) r)))
  have hp := densityMixture_probability_density
    (unitCoefficientSource (ActiveProfileCoefficientIndex G B h P)) volume
    (activeSlicedProfileIdeal Z h P sets ρ center width) hm
    (Filter.Eventually.of_forall (fun r => partitionedSlicedRegularizedIdeal_probability h P sets ρ hρ center width
      (profileNoiseWithActive (Z := Z) h P (fun _ => 0) r)))
  exact ⟨hb.1, hb.2, hp.2.1, hp.2.2⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PrincipalCubeSupportedCell
namespace OAI

section

namespace Erdos3
open scoped Classical BigOperators

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable (B : D → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)] (h : D → ℕ)
variable (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ j, 0 < L j)

theorem principalTupleWeights_weight_pos_of_cube (y : PrincipalIntegerTuples B h α L)
    (hy : ∀ j, IntegerScalarCube (L j) (fun a => (y j a : ℤ))) :
    0 < (principalTupleWeights B h L hL).weight y := by
  apply Finset.prod_pos
  intro j _
  apply (FiniteProbabilityWeights.condition_weight_pos_iff _ _ _ (y j)).mpr
  refine ⟨(mem_integerScalarCubeSet (L j) (y j)).mpr (hy j), ?_⟩
  let : Nonempty (IntegerScalarCubeBox α (L j)) := ⟨y j⟩
  change 0 < (Fintype.card (IntegerScalarCubeBox α (L j)) : ℝ)⁻¹
  positivity

theorem principalResidueCell_pos_of_cube (q : ℕ) (y : PrincipalIntegerTuples B h α L)
    (hy : ∀ j, IntegerScalarCube (L j) (fun a => (y j a : ℤ))) :
    0 < (principalTupleWeights B h L hL).mass
      (Finset.univ.filter (fun z => principalResidueLabel q z = principalResidueLabel q y)) := by
  apply lt_of_lt_of_le (principalTupleWeights_weight_pos_of_cube B h L hL y hy)
  exact Finset.single_le_sum (fun z _ => (principalTupleWeights B h L hL).nonneg z)
    (by simp : y ∈ Finset.univ.filter (fun z => principalResidueLabel q z = principalResidueLabel q y))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedRowSlicedIdealCoordinates
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical NNReal

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [Fintype α] in
theorem realRowsSiteValue_coefficient (rows : Finset (Finset α))
    (v : rows → ℝ) (s : rows) :
    booleanCoefficient (realRowsSiteValue rows v) s.val = v s := by
  unfold realRowsSiteValue
  rw [booleanCoefficient_sum]
  simp only [booleanCoefficient_const_mul, booleanCoefficient_monomial]
  rw [Finset.sum_eq_single s]
  · simp
  · intro t _ hts
    have hst : s.val ≠ t.val := fun he => hts (Subtype.ext he.symm)
    simp only [hst, ite_false, mul_zero]
  · simp

namespace VectorPolynomial

open Module

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (rowSets : Fin m → Finset (Finset α))

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "grid" => allocatedGridAxis (I := I) U b S.value

omit [Fintype α] in
theorem allocatedRowIdealCoordinates_jet (z : AllocatedLongJetRows B U b S rowTypes)
    (a : {a // ¬grid a}) (t : rowTypes a.val.1) :
    booleanCoefficient (fun s => allocatedRowIdealCoordinates B U b S rowSets z s a.val) t.val =
      allocatedLongJetRealCoordinates B U b S z ⟨a, t⟩ / R a.val.1 := by
  unfold allocatedRowIdealCoordinates
  rw [realRowsSiteValue_coefficient]
  simp only [dif_pos a.property]

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))
local notation "jets" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "input" => PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n)
  (α := α) (fun a => ¬grid a)
local notation "output" => (Σ a : {a // ¬grid a}, jets (Sigma.fst (Subtype.val a)))

theorem allocatedRowSlicedIdealCoordinates_density (hR : ∀ j, 0 < R j)
    (ρ : ℝ≥0) (center width : input → ℝ) (z : AllocatedLongJetRows B U b S jets) :
    (∏ q : output, R q.1.val.1) *
        allocatedRowSlicedIdeal B U b S rowSets ρ center width (allocatedLongJetRealCoordinates B U b S z) =
      activeAveragedSlicedProfileIdeal (G := G) (B := B) (G × Option α)
        (layerSamplerDegree I n) grid (fun a : {a // ¬grid a} => (Subtype.val : jets a.val.1 → Finset α)) ρ center width
        (booleanSiteJets (fun a : {a // ¬grid a} => (Subtype.val : jets a.val.1 → Finset α))
          (fun s a => allocatedRowIdealCoordinates B U b S rowSets z s a.val)) := by
  have hjet : booleanSiteJets (fun a : {a // ¬grid a} => (Subtype.val : jets a.val.1 → Finset α))
      (fun s a => allocatedRowIdealCoordinates B U b S rowSets z s a.val) =
      (fun q : output => allocatedLongJetRealCoordinates B U b S z q / R q.1.val.1) := by
    funext q
    exact allocatedRowIdealCoordinates_jet B U b S rowSets z q.1 q.2
  rw [hjet]
  unfold allocatedRowSlicedIdeal diagonalImageDensity
  simp only [abs_of_pos (hR _)]
  rw [← mul_assoc, mul_inv_cancel₀ (Finset.prod_ne_zero_iff.mpr (fun q _ => (hR q.1.val.1).ne')), one_mul]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedAffineFiniteModelL2
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))
local notation "jets" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "input" => PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n)
  (α := α) (fun a => ¬grid a)
local notation "output" => (Σ a : {a // ¬grid a}, jets (Sigma.fst (Subtype.val a)))

theorem allocatedRowSlicedIdeal_normalized_cap (hR : ∀ j, 0 < R j)
    (ρ : ℝ≥0) (hρ : 0 < ρ) (center width : input → ℝ)
    (z : AllocatedLongJetRows B U b S jets) :
    ‖((∏ q : output, R q.1.val.1 : ℝ) : ℂ) *
      (allocatedRowSlicedIdeal B U b S rowSets ρ center width
        (allocatedLongJetRealCoordinates B U b S z) : ℂ)‖ ≤
      (ρ⁻¹ ^ Fintype.card output : ℝ≥0) := by
  rw [← Complex.ofReal_mul, allocatedRowSlicedIdealCoordinates_density B U b S rowSets hR ρ center width]
  have hb := (activeAveragedSlicedProfileIdeal_spec (G := G) (B := B) (G × Option α)
    (layerSamplerDegree I n) grid (fun a => (Subtype.val : jets a.val.1 → Finset α)) ρ hρ center width).1
    (booleanSiteJets (fun a => (Subtype.val : jets a.val.1 → Finset α))
      (fun s a => allocatedRowIdealCoordinates B U b S rowSets z s a.val))
  simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hb.1] using hb.2

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "grid" => allocatedGridAxis (I := I) U b S.value

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "inverseNormalizer" => ((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹

variable (hperiod : ∀ j, integerScalarLattice {t : Finset α // t ∈ rowSets j} (period : ℤ) ≤
  (scalarKernelIntegerJet x (j.val + 1) (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)).mulVecLin.range)
variable {M : ℝ} (hM : 1 ≤ M)
variable (hm : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U b S x
  (fun j => (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)) j q
  (integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
    (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
    (fun j => (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)) j
    (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ∧
  allocatedIntegerKernelMask B U b S x
    (fun j => (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)) j q
    (integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
      (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
      (fun j => (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)) j
      (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ≤ M)

variable (hR : ∀ j, 0 < R j) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
variable (hbudget : ∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset α) *
  (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)))) ≤ 1 / 4)

include hperiod hM hm hR hC hchart hbudget in

theorem allocatedAffineProductPrefactor_cap
    (ρ : ℝ≥0) (hρ : 0 < ρ)
    (center width : PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n)
      (α := α) (fun a => ¬grid a) → ℝ)
    (y : EuclideanJetLayers U rowTypes) :
    ‖allocatedProductFullGridPrefactor B U b S rowSets d r hr x hb o bW q y₀
        (allocatedRowSlicedIdeal B U b S rowSets ρ center width) y‖ ≤
      ‖inverseNormalizer‖ * (M ^ Fintype.card (LayerSamplerAxis I n) * coefficientDeckPeriodCap rowTypes E period) *
        (ρ⁻¹ ^ Fintype.card (Σ a : {a // ¬grid a}, rowTypes a.val.1) : ℝ≥0) := by
  let aa : Empty → ℂ := fun i => i.elim
  let ff : Empty → Finset α → (LayerSamplerAxis I n → ℝ) → ℂ := fun i => i.elim
  have herr (v : AllocatedLongJetRows B U b S rowTypes) :
      ‖((∏ q : (Σ a : {a // ¬grid a}, rowTypes a.val.1), R q.1.val.1 : ℝ) : ℂ) *
          (allocatedRowSlicedIdeal B U b S rowSets ρ center width
            (allocatedLongJetRealCoordinates B U b S v) : ℂ) -
        ∑ k, aa k * ∏ s, ff k s (allocatedRowIdealCoordinates B U b S rowSets v s)‖ ≤
      (ρ⁻¹ ^ Fintype.card (Σ a : {a // ¬grid a}, rowTypes a.val.1) : ℝ≥0) := by
    simp only [Finset.univ_eq_empty, Finset.sum_empty, sub_zero]
    exact allocatedRowSlicedIdeal_normalized_cap B U b S rowSets hR ρ hρ center width _
  have he := allocatedProductChartDensityApproximation_error_s2 B U b S rowSets x y₀ q d period r hr hb o bW
    hperiod hM hm hR C hC hchart hbudget aa ff
    (allocatedRowSlicedIdeal B U b S rowSets ρ center width)
    (NNReal.coe_nonneg _) herr y
  simpa only [allocatedProductChartIdealApproximation, Finset.univ_eq_empty, Finset.sum_empty,
    Finset.sum_const_zero, sub_zero] using he

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedSupportedAffineAccurateSource
namespace OAI

section

namespace Erdos3.VectorPolynomial
universe uα

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset α))
local notation "grid" => allocatedGridAxis (I := I) U b S.value

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "cutoff" => allocatedProductSiteCutoff B U b S rowSets o hb bW d r hr
local notation "inverseNormalizer" => ((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹

variable (hperiod : ∀ j, integerScalarLattice {t : Finset α // t ∈ rowSets j} (period : ℤ) ≤
  (scalarKernelIntegerJet x (j.val + 1) (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)).mulVecLin.range)
variable {M : ℝ} (hM : 1 ≤ M)
variable (hm : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U b S x
  (fun j => (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)) j q
  (integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
    (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
    (fun j => (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)) j
    (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ∧
  allocatedIntegerKernelMask B U b S x
    (fun j => (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)) j q
    (integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
      (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
      (fun j => (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)) j
      (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ≤ M)

variable (hR : ∀ j, 0 < R j) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
variable (hbudget : ∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset α) *
  (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)))) ≤ 1 / 4)

variable (ρ : ℝ≥0)
variable (center width : PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n)
  (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a) → ℝ)

variable (hσ : ∀ j, 0 < σ j)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U b S j : ℤ))
variable (label : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = label)))
local notation "gridLaw" => containedSupportedProgressionAxisLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) H step c (allocatedPrincipalSides_pos B U b S) hH hsubset q label hcell grid
variable (hu₀ : (containedSupportedProgressionAxisLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) H step c (allocatedPrincipalSides_pos B U b S) hH hsubset q label hcell
  (allocatedGridAxis (I := I) U b S.value)).weight (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀) ≠ 0)
variable (hmodulus : ∀ j, integerScalarLattice {t : Finset α // t ∈ rowSets j} (q : ℤ) ≤
  (scalarKernelIntegerJet x (j.val + 1) (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)).mulVecLin.range)
variable (hy₀ : ∀ j, IntegerScalarCube (allocatedPrincipalSides B U b S j) (fun a => (y₀ j a : ℤ)))
local notation "gridAxes" => {a // grid a}
local notation "gridDensity" => allocatedSupportedSlicedFullGridDensity B U b hR hσ S rowSets H step c hH hsubset q label hcell x
local notation "ideal" => allocatedRowSlicedIdeal B U b S rowSets ρ center width
local notation "prefactor" => allocatedProductFullGridPrefactor B U b S rowSets d r hr x hb o bW q y₀ ideal

include hperiod hM hm hR hC hchart hbudget hu₀ hmodulus hy₀ in
theorem exists_allocated_supported_affine_ideal_model
    (e : gridAxes → ScalarSiteExpansion.{uα,uα} (Finset α))
    {εgrid : ℝ}
    (he : ∀ z : AllocatedFrozenJetRows B U b S rowTypes,
      ‖(allocatedFullGridNaturalVolume B U b S rowSets : ℂ) * (gridDensity z : ℂ) -
        allocatedFullGridSiteApproximation B U b S rowSets e z‖ ≤ εgrid)
    {Nt V Cc Hs : gridAxes → ℝ} {Lg : ℝ≥0}
    (heb : ∀ a, (e a).Bounds (Nt a) (V a) (Cc a) Lg (Hs a))
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hw : ∀ i, |center i| + |width i| ≤ 1)
    {ε p : ℝ} (hε : 0 < ε) (hp : 0 ≤ p)
    (hbox : 2 * (allocatedRowSlicedSiteRadius rowSets : ℝ) ≤ Real.exp p)
    (hεp : ε⁻¹ ≤ Real.exp p) (hρp : (ρ : ℝ)⁻¹ ≤ Real.exp p) :
    let sourceRadius : ℝ≥0 := allocatedRowSlicedSiteRadius rowSets
    let cutoffLip : ℝ≥0 := Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound / (2 * sourceRadius)
    let Q := idealSiteLogBudget (Fintype.card (Σ a : LayerSamplerAxis I n, rowTypes a.1)) (Fintype.card α) p
    let A := Real.exp ((Fintype.card (Finset α) * Fintype.card (LayerSamplerAxis I n) : ℕ) * (4 * Q + 8) + Q)
    let maskCap := M ^ Fintype.card (LayerSamplerAxis I n) * coefficientDeckPeriodCap rowTypes E period
    ∃ k : ℕ, (k : ℝ) ≤ Real.exp (4 * Q + 8) ∧
      (Fintype.card (Finset α × LayerSamplerAxis I n → Fin k) : ℝ) ≤
        Real.exp ((Fintype.card (Finset α) * Fintype.card (LayerSamplerAxis I n) : ℕ) * (4 * Q + 8)) ∧
      ∃ (a : (Finset α × LayerSamplerAxis I n → Fin k) → ℂ)
        (f : (Finset α × LayerSamplerAxis I n → Fin k) → Finset α → (LayerSamplerAxis I n → ℝ) → ℂ),
        (∑ i, ‖a i‖) ≤ A ∧
        (∀ i s v, ‖f i s v‖ ≤ 1) ∧
        (∀ i s, LipschitzWith (⟨Real.exp (Fintype.card (LayerSamplerAxis I n) + 6 * Q + 12), Real.exp_nonneg _⟩ + cutoffLip) (f i s)) ∧
        (∀ i s v, (∃ j, 2 * (sourceRadius : ℝ) < |v j|) → f i s v = 0) ∧
        (∑ label : Finset α → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)), ∑ i,
          ‖allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label i‖) ≤
          ‖inverseNormalizer‖ * ((Fintype.card ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)) : ℝ) ^ Fintype.card (Finset α) * maskCap * A) ∧
        (∀ label i s y,
          ‖allocatedMaskedSiteChartFactor B U b S o hb bW d r hr period label (f i s) y‖ ≤ 1) ∧
        (∀ label i s, Measurable (allocatedMaskedSiteChartFactor B U b S o hb bW d r hr period label (f i s))) ∧
        Measurable (allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f) ∧
        (∀ y : EuclideanJetLayers U rowTypes,
          ‖allocatedProductFullGridPrefactor B U b S rowSets d r hr x hb o bW q y₀
              (allocatedRowSlicedIdeal B U b S rowSets ρ center width) y -
            allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f y‖ ≤
            ‖inverseNormalizer‖ * maskCap * ε) ∧
        ∀ y : EuclideanJetLayers U rowTypes,
          ‖cutoff y * ((gridLaw).mean (fun u => allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d
              (principalAxisJoin grid u (principalAxisRestrict (fun a => ¬grid a) y₀)) q ideal y) : ℂ) -
            allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f y *
              allocatedFullGridChartModel B U b S rowSets d hb o bW e y‖ ≤
            ‖prefactor y‖ * εgrid + (‖inverseNormalizer‖ * maskCap * ε) * ∏ a, Cc a := by
  intro sourceRadius cutoffLip Q A maskCap
  obtain ⟨k, hk, hcard, a, f, ha', hf, hLf, hs, hc, hfn, hfm, hmeas, herr⟩ :=
    exists_allocated_global_masked_affine_ideal_approximation_s2 B U b S rowSets x y₀ q d period r hr hb o bW
      hperiod hM hm hR C hC hchart hbudget center width ρ hρ hρ1 hw hε hp hbox hεp hρp
  refine ⟨k, hk, hcard, a, f, ha', hf, hLf, hs, hc, hfn, hfm, hmeas, herr, ?_⟩
  have hfullcell := principalResidueCell_pos_of_cube B (layerSamplerDegree I n)
    (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S) q y₀ hy₀
  have hjoin := principalAxisJoin_restrict grid y₀
  intro y
  have hfullcell' : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
      (Finset.univ.filter (fun y => principalResidueLabel q y = principalResidueLabel q
        (principalAxisJoin grid (principalAxisRestrict grid y₀) (principalAxisRestrict (fun a => ¬grid a) y₀)))) := by
    simpa only [hjoin] using hfullcell
  have hlong : ∀ y, ‖allocatedProductFullGridPrefactor B U b S rowSets d r hr x hb o bW q
      (principalAxisJoin grid (principalAxisRestrict grid y₀) (principalAxisRestrict (fun a => ¬grid a) y₀)) ideal y -
      allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f y‖ ≤
        ‖inverseNormalizer‖ * maskCap * ε := by simpa only [hjoin] using herr
  have hη : 0 ≤ ‖inverseNormalizer‖ * maskCap * ε := by
    have hmask : 0 ≤ maskCap := mul_nonneg (pow_nonneg (zero_le_one.trans hM) _) (coefficientDeckPeriodCap_nonneg rowTypes E period)
    exact mul_nonneg (mul_nonneg (norm_nonneg _) hmask) hε.le
  have h := allocatedSupportedSlicedProductProfile_combined_error_s2 B U b hR hσ S rowSets H step c hH hsubset q label hcell
    x (principalAxisRestrict grid y₀) hu₀ (principalAxisRestrict (fun a => ¬grid a) y₀) E d hmodulus hb o bW
    ideal hfullcell' r hr e he heb
    (allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f) hη hlong y
  simpa only [hjoin] using h

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
universe uα

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset α))
local notation "grid" => allocatedGridAxis (I := I) U b S.value

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "inverseNormalizer" => ((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹

variable (hperiod : ∀ j, integerScalarLattice {t : Finset α // t ∈ rowSets j} (period : ℤ) ≤
  (scalarKernelIntegerJet x (j.val + 1) (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)).mulVecLin.range)
variable {M : ℝ} (hM : 1 ≤ M)
variable (hm : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U b S x
  (fun j => (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)) j q
  (integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
    (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
    (fun j => (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)) j
    (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ∧
  allocatedIntegerKernelMask B U b S x
    (fun j => (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)) j q
    (integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
      (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
      (fun j => (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)) j
      (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ≤ M)

variable (hR : ∀ j, 0 < R j) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
variable (hbudget : ∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset α) *
  (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)))) ≤ 1 / 4)

variable (ρ : ℝ≥0)
variable (center width : PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n)
  (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a) → ℝ)

variable (hσ : ∀ j, 0 < σ j)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U b S j : ℤ))
variable (label : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = label)))
local notation "gridLaw" => containedSupportedProgressionAxisLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) H step c (allocatedPrincipalSides_pos B U b S) hH hsubset q label hcell grid
variable (hu₀ : (containedSupportedProgressionAxisLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) H step c (allocatedPrincipalSides_pos B U b S) hH hsubset q label hcell
  (allocatedGridAxis (I := I) U b S.value)).weight (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀) ≠ 0)
variable (hmodulus : ∀ j, integerScalarLattice {t : Finset α // t ∈ rowSets j} (q : ℤ) ≤
  (scalarKernelIntegerJet x (j.val + 1) (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)).mulVecLin.range)
variable (hy₀ : ∀ j, IntegerScalarCube (allocatedPrincipalSides B U b S j) (fun a => (y₀ j a : ℤ)))
local notation "gridAxes" => {a // grid a}
local notation "gridDensity" => allocatedSupportedSlicedFullGridDensity B U b hR hσ S rowSets H step c hH hsubset q label hcell x
local notation "ideal" => allocatedRowSlicedIdeal B U b S rowSets ρ center width
local notation "prefactor" => allocatedProductFullGridPrefactor B U b S rowSets d r hr x hb o bW q y₀ ideal

include hperiod hM hm hR hC hchart hbudget hu₀ hmodulus hy₀ in
theorem exists_allocated_supported_affine_source_model_s2_oai
    (T : Fin m → ℝ) (hT : ∀ j, 0 ≤ T j)
    (hTideal : ∀ j, partitionedIdealRadius α m + 1 ≤ T j)
    (hsource : ∀ j, (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
      ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ (j.val + 1)) ≤ T j)
    (hradius : ∀ j, (rowSets j).card * T j ≤ (r : ℝ)) (hσ1 : ∀ j, σ j ≤ 1)
    (e : gridAxes → ScalarSiteExpansion.{uα,uα} (Finset α))
    {εgrid : ℝ} (hεgrid : 0 ≤ εgrid)
    (he : ∀ z : AllocatedFrozenJetRows B U b S rowTypes,
      ‖(allocatedFullGridNaturalVolume B U b S rowSets : ℂ) * (gridDensity z : ℂ) -
        allocatedFullGridSiteApproximation B U b S rowSets e z‖ ≤ εgrid)
    {Nt V Cc Hs : gridAxes → ℝ} {Lg : ℝ≥0}
    (heb : ∀ a, (e a).Bounds (Nt a) (V a) (Cc a) Lg (Hs a))
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hw : ∀ i, |center i| + |width i| ≤ 1)
    {ε p : ℝ} (hε : 0 < ε) (hp : 0 ≤ p)
    (hbox : 2 * (allocatedRowSlicedSiteRadius rowSets : ℝ) ≤ Real.exp p)
    (hεp : ε⁻¹ ≤ Real.exp p) (hρp : (ρ : ℝ)⁻¹ ≤ Real.exp p) :
    let sourceRadius : ℝ≥0 := allocatedRowSlicedSiteRadius rowSets
    let cutoffLip : ℝ≥0 := Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound / (2 * sourceRadius)
    let Q := idealSiteLogBudget (Fintype.card (Σ a : LayerSamplerAxis I n, rowTypes a.1)) (Fintype.card α) p
    let A := Real.exp ((Fintype.card (Finset α) * Fintype.card (LayerSamplerAxis I n) : ℕ) * (4 * Q + 8) + Q)
    let maskCap := M ^ Fintype.card (LayerSamplerAxis I n) * coefficientDeckPeriodCap rowTypes E period
    ∃ k : ℕ, (k : ℝ) ≤ Real.exp (4 * Q + 8) ∧
      (Fintype.card (Finset α × LayerSamplerAxis I n → Fin k) : ℝ) ≤
        Real.exp ((Fintype.card (Finset α) * Fintype.card (LayerSamplerAxis I n) : ℕ) * (4 * Q + 8)) ∧
      ∃ (a : (Finset α × LayerSamplerAxis I n → Fin k) → ℂ)
        (f : (Finset α × LayerSamplerAxis I n → Fin k) → Finset α → (LayerSamplerAxis I n → ℝ) → ℂ),
        (∑ i, ‖a i‖) ≤ A ∧
        (∀ i s v, ‖f i s v‖ ≤ 1) ∧
        (∀ i s, LipschitzWith (⟨Real.exp (Fintype.card (LayerSamplerAxis I n) + 6 * Q + 12), Real.exp_nonneg _⟩ + cutoffLip) (f i s)) ∧
        (∀ i s v, (∃ j, 2 * (sourceRadius : ℝ) < |v j|) → f i s v = 0) ∧
        (∑ label : Finset α → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)), ∑ i,
          ‖allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label i‖) ≤
          ‖inverseNormalizer‖ * ((Fintype.card ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)) : ℝ) ^ Fintype.card (Finset α) * maskCap * A) ∧
        (∀ label i s y,
          ‖allocatedMaskedSiteChartFactor B U b S o hb bW d r hr period label (f i s) y‖ ≤ 1) ∧
        (∀ label i s, Measurable (allocatedMaskedSiteChartFactor B U b S o hb bW d r hr period label (f i s))) ∧
        Measurable (allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f) ∧
        (∀ y : EuclideanJetLayers U rowTypes,
          ‖allocatedProductFullGridPrefactor B U b S rowSets d r hr x hb o bW q y₀
              (allocatedRowSlicedIdeal B U b S rowSets ρ center width) y -
            allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f y‖ ≤
            ‖inverseNormalizer‖ * maskCap * ε) ∧
        ∀ y : EuclideanJetLayers U rowTypes,
          ‖((gridLaw).mean (fun u => allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d
              (principalAxisJoin grid u (principalAxisRestrict (fun a => ¬grid a) y₀)) q ideal y) : ℂ) -
            allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f y *
              allocatedFullGridChartModel B U b S rowSets d hb o bW e y‖ ≤
            ‖inverseNormalizer‖ * maskCap *
              ((ρ⁻¹ ^ Fintype.card (Σ a : {a // ¬grid a}, rowTypes a.val.1) : ℝ≥0) * εgrid +
                ε * ∏ a, Cc a) := by
  intro sourceRadius cutoffLip Q A maskCap
  obtain ⟨k, hk, hcard, a, f, ha, hf, hLf, hs, hc, hfn, hfm, hmeas, hlong, herr⟩ :=
    exists_allocated_supported_affine_ideal_model B U b S rowSets x y₀ q d period r hr hb o bW
      hperiod hM hm hR C hC hchart hbudget ρ center width hσ H step c hH hsubset label hcell
      hu₀ hmodulus hy₀ e he heb hρ hρ1 hw hε hp hbox hεp hρp
  refine ⟨k, hk, hcard, a, f, ha, hf, hLf, hs, hc, hfn, hfm, hmeas, hlong, ?_⟩
  have hb0 (j : Fin m) : C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)) ≤ 1 / 4 := by
    have hp0 : 0 ≤ C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)) :=
      mul_nonneg (hC j) (mul_nonneg (by positivity) (mul_nonneg (by positivity) (hR j).le))
    have hcard : (1 : ℝ) ≤ Fintype.card (Finset α) := by
      exact_mod_cast Fintype.card_pos_iff.mpr (inferInstance : Nonempty (Finset α))
    have hfac : (1 : ℝ) ≤ ((rowSets j).card + 1 : ℝ) * Fintype.card (Finset α) :=
      one_le_mul_of_one_le_of_one_le (by have := Nat.cast_nonneg (α := ℝ) (rowSets j).card; linarith) hcard
    exact (le_mul_of_one_le_left hp0 hfac).trans (by simpa only [mul_assoc] using hbudget j)
  intro y
  have hfix := allocatedAffineRowIdeal_cutoff_fixes_mean_s2 B U b S rowSets o hb bW d r hr hR hσ
    T hT hsource hradius C hC hchart hb0 hσ1 hTideal ρ hρ hρ1 center width hw x gridLaw
    (fun u => principalAxisJoin grid u (principalAxisRestrict (fun a => ¬grid a) y₀)) q y
  have hh := herr y
  rw [hfix] at hh
  have hcap := allocatedAffineProductPrefactor_cap B U b S rowSets x y₀ q d period r hr hb o bW
    hperiod hM hm hR C hC hchart hbudget ρ hρ center width y
  calc
    _ ≤ ‖prefactor y‖ * εgrid + (‖inverseNormalizer‖ * maskCap * ε) * ∏ a, Cc a := hh
    _ ≤ (‖inverseNormalizer‖ * maskCap *
          (ρ⁻¹ ^ Fintype.card (Σ a : {a // ¬grid a}, rowTypes a.val.1) : ℝ≥0)) * εgrid +
        (‖inverseNormalizer‖ * maskCap * ε) * ∏ a, Cc a :=
      add_le_add (mul_le_mul_of_nonneg_right hcap hεgrid) le_rfl
    _ = _ := by ring

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution.{uα, u_1, u_2, u_3, u_4, u_5} : type_of% @OAI.Erdos3.VectorPolynomial.exists_allocated_supported_affine_source_model_s2_oai.{uα, u_1, u_2, u_3, u_4, u_5} := @OAI.Erdos3.VectorPolynomial.exists_allocated_supported_affine_source_model_s2_oai.{uα, u_1, u_2, u_3, u_4, u_5}
