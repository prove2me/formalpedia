-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.allocatedAffineCoveredProfile_test_integral_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T05:22:27.73804+00:00
-- url     : https://prove2.me/submissions/2984e454-a3b3-4a28-82ad-4400d585128f

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B299
import Definitions.Def_OAIE3v2B194
import Definitions.Def_OAIE3v2B196
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedAffineIdeal_profile_integrable_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedCoveredProfile_test_integral_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedGridlessWeightedKernel_quarter_support_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.DiagonalDensityTransport
namespace OAI

section

namespace Erdos3

open MeasureTheory

variable {ι : Type*}

variable [Fintype ι]

theorem linearDensityPullback_measurable (A : (ι → ℝ) ≃L[ℝ] (ι → ℝ))
    {f : (ι → ℝ) → ℝ} (hf : Measurable f) : Measurable (linearDensityPullback A f) :=
  measurable_const.mul (hf.comp A.symm.continuous.measurable)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {ι : Type*} [Fintype ι] (a : ι → ℝ) (ha : ∀ i, a i ≠ 0)

theorem diagonalDensityTransport_det :
    LinearMap.det (coordinateScaleEquiv a ha).toLinearMap = ∏ i, a i := by
  classical
  have hm : LinearMap.toMatrix' (coordinateScaleEquiv a ha).toLinearMap = Matrix.diagonal a := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [LinearMap.toMatrix'_apply, coordinateScaleEquiv_apply]
    · simp [LinearMap.toMatrix'_apply, coordinateScaleEquiv_apply, hij]
  rw [← LinearMap.det_toMatrix', hm, Matrix.det_diagonal]

theorem diagonalDensityTransport_eq (f : (ι → ℝ) → ℝ) (x : ι → ℝ) :
    diagonalDensityTransport a ha f x = |∏ i, a i|⁻¹ * f (fun i => x i / a i) := by
  unfold diagonalDensityTransport linearDensityPullback
  rw [inverseJacobian_eq]
  change |LinearMap.det (coordinateScaleEquiv a ha).toLinearMap|⁻¹ *
    f (fun i => x i / a i) = _
  rw [diagonalDensityTransport_det]

end Erdos3

end

end OAI
end

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.DiagonalImageDensity
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

theorem diagonalImageDensity_eq_pullback (d : ι → ℝ) (hd : ∀ i, d i ≠ 0)
    (f : (ι → ℝ) → ℝ) :
    diagonalImageDensity d f =
      linearDensityPullback (coordinateScaleEquiv d hd).toContinuousLinearEquiv f := by
  funext x
  simpa only [diagonalImageDensity, diagonalDensityTransport, Finset.abs_prod] using
    (diagonalDensityTransport_eq d hd f x).symm

theorem diagonalImageDensity_measurable (d : ι → ℝ) (hd : ∀ i, d i ≠ 0)
    {f : (ι → ℝ) → ℝ} (hf : Measurable f) : Measurable (diagonalImageDensity d f) := by
  rw [diagonalImageDensity_eq_pullback d hd]
  exact linearDensityPullback_measurable _ hf

theorem diagonalImageDensity_nonneg (d : ι → ℝ)
    {f : (ι → ℝ) → ℝ} (hf : ∀ x, 0 ≤ f x) (x : ι → ℝ) :
    0 ≤ diagonalImageDensity d f x :=
  mul_nonneg (inv_nonneg.mpr (Finset.prod_nonneg (fun i _ => abs_nonneg (d i)))) (hf _)

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

section

namespace Erdos3

open scoped BigOperators

theorem booleanFeature_abs_le_one {α : Type*} [DecidableEq α]
    (r : Option α) (t : Finset α) : |(booleanFeature r t : ℝ)| ≤ 1 := by
  cases r with
  | none => norm_num [booleanFeature]
  | some a => simp only [booleanFeature]; split_ifs <;> norm_num

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ScalarCubeBoundaryMass
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem scalarCubeMeasure_ae_domain (α : Type*) [Fintype α] [DecidableEq α] :
    ∀ᵐ a ∂scalarCubeMeasure α, a ∈ scalarCubeDomain α := by
  apply ae_iff.mpr
  change scalarCubeMeasure α (scalarCubeDomain α)ᶜ = 0
  simp [scalarCubeMeasure, Measure.smul_apply,
    Measure.restrict_apply (scalarCubeDomain_isOpen α).measurableSet.compl]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ScaledCubeProductMeasure
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem scalarCubeProductMeasure_ae_domain (ι α : Type*) [Fintype ι] [Fintype α]
    [DecidableEq α] :
    ∀ᵐ x ∂scalarCubeProductMeasure ι α, x ∈ scalarCubeProductDomain ι α := by
  change ∀ᵐ x ∂Measure.pi (fun _ : ι => scalarCubeMeasure α),
    x ∈ Set.univ.pi (fun _ => scalarCubeDomain α)
  have h : ∀ i : ι, ∀ᵐ x ∂Measure.pi (fun _ : ι => scalarCubeMeasure α),
      x i ∈ scalarCubeDomain α := fun _ =>
    Measure.tendsto_eval_ae_ae.eventually (scalarCubeMeasure_ae_domain α)
  filter_upwards [ae_all_iff.mpr h] with x hx
  exact fun i _ => hx i

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.BooleanPolynomialBudget
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem booleanCoefficient_mass_le {I α : Type*} [DecidableEq α]
    (p : Finset α → MvPolynomial I ℝ) (s : Finset α) {M : ℝ}
    (hp : ∀ t ∈ s.powerset, realPolynomialMass (p t) ≤ M) :
    realPolynomialMass (booleanCoefficient p s) ≤ (2 : ℝ) ^ s.card * M := by
  classical
  unfold booleanCoefficient
  apply (realPolynomialMass_sum_le _ _).trans
  calc
    _ ≤ ∑ _t ∈ s.powerset, M := by
      apply Finset.sum_le_sum
      intro t ht
      have he : (-1 : MvPolynomial I ℝ) ^ (s \ t).card =
          MvPolynomial.C ((-1 : ℝ) ^ (s \ t).card) := by simp
      rw [he]
      exact (realPolynomialMass_C_mul_le _ _).trans (by simpa using hp t ht)
    _ = _ := by simp

theorem booleanAffinePolynomial_mass_le {B F α : Type*} [Fintype α] [DecidableEq α]
    (b : B) (v : F) (t : Finset α) :
    realPolynomialMass (booleanAffinePolynomial b v t) ≤ (Fintype.card α : ℝ) + 1 := by
  classical
  apply (realPolynomialMass_sum_le _ _).trans
  calc
    _ ≤ ∑ _r : Option α, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro r _
      exact (realPolynomialMass_C_mul_le _ _).trans (by
        simpa only [realPolynomialMass_X, mul_one] using booleanFeature_abs_le_one r t)
    _ = _ := by simp

theorem booleanBlockPolynomial_mass_le {B F α : Type*} [Fintype F] [Fintype α] [DecidableEq α]
    (b : B) (t : Finset α) :
    realPolynomialMass (booleanBlockPolynomial (F := F) b t) ≤
      ((Fintype.card α : ℝ) + 1) ^ Fintype.card F := by
  classical
  apply (realPolynomialMass_prod_le _ _).trans
  calc
    _ ≤ ∏ _v : F, ((Fintype.card α : ℝ) + 1) :=
      Finset.prod_le_prod (fun _ _ => realPolynomialMass_nonneg _)
        (fun v _ => booleanAffinePolynomial_mass_le b v t)
    _ = _ := by simp

theorem booleanSamplerPolynomial_mass_le {B F α : Type*}
    [Fintype B] [Fintype F] [Fintype α] [DecidableEq α] (c : B → ℝ) (s : Finset α) :
    realPolynomialMass (booleanSamplerPolynomial (F := F) c s) ≤
      (2 : ℝ) ^ s.card * ((∑ b, |c b|) * ((Fintype.card α : ℝ) + 1) ^ Fintype.card F) := by
  classical
  apply booleanCoefficient_mass_le
  intro t _
  apply (realPolynomialMass_sum_le _ _).trans
  calc
    _ ≤ ∑ b, |c b| * ((Fintype.card α : ℝ) + 1) ^ Fintype.card F := by
      apply Finset.sum_le_sum
      intro b _
      exact (realPolynomialMass_C_mul_le _ _).trans
        (mul_le_mul_of_nonneg_left (booleanBlockPolynomial_mass_le b t) (abs_nonneg _))
    _ = _ := (Finset.sum_mul _ _ _).symm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.CanonicalSamplerTuple
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem jointBooleanSampler_coordinate_abs_le {D α : Type*} [Fintype D] [Fintype α]
    [DecidableEq α] {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
    (h : D → ℕ) (c : ∀ d, B d → ℝ) (sets : ∀ d, O d → Finset α)
    (x : JointBlockParameter B h α → ℝ) (hx : ‖x‖ ≤ 1) (o : Σ d, O d) :
    |jointBooleanSampler h c sets x o| ≤
      (2 : ℝ)^(sets o.1 o.2).card*((∑ b, |c o.1 b|)*((Fintype.card α : ℝ)+1)^h o.1) := by
  apply (mvPolynomial_eval_abs_le_sum_coeff _ _ ?_).trans
  · simpa only [Fintype.card_fin, realPolynomialMass] using
      booleanSamplerPolynomial_mass_le (F := Fin (h o.1)) (c o.1) (sets o.1 o.2)
  · intro j
    change |x ⟨o.1, j⟩| ≤ 1
    exact (Real.norm_eq_abs _).symm.trans_le ((norm_le_pi_norm x _).trans hx)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.SigmaProductMeasure
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem sigmaProductMeasure_flatten {D : Type*} [Fintype D] {I : D → Type*}
    [∀ d, Fintype (I d)] {X : (Σ d, I d) → Type*}
    [∀ s, MeasurableSpace (X s)] (μ : ∀ s, Measure (X s)) [∀ s, IsProbabilityMeasure (μ s)] :
    (Measure.pi (fun d => Measure.pi (fun i => μ ⟨d, i⟩))).map
      (fun x (s : Σ d, I d) => x s.1 s.2) = Measure.pi μ := by
  have hm : Measurable (fun (x : ∀ d i, X ⟨d, i⟩) (s : Σ d, I d) => x s.1 s.2) :=
    measurable_pi_iff.mpr (fun index =>
      (measurable_pi_apply index.2).comp (measurable_pi_apply index.1))
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have he : (fun (x : ∀ d i, X ⟨d, i⟩) (s : Σ d, I d) => x s.1 s.2) ⁻¹' Set.univ.pi s =
      Set.univ.pi (fun d => Set.univ.pi (fun i => s ⟨d, i⟩)) := by
    ext x
    constructor
    · intro hx d _ i _
      exact hx ⟨d, i⟩ (Set.mem_univ _)
    · intro hx t _
      exact hx t.1 (Set.mem_univ _) t.2 (Set.mem_univ _)
  rw [he, Measure.pi_pi]
  simp only [Measure.pi_pi, Fintype.prod_sigma]

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ScalarCubeProductSupport
namespace OAI


namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem principalTupleFlatten_norm_apply_le {D : Type*} [Fintype D]
    (B : D → Type*) [∀ d, Fintype (B d)] (h : D → ℕ) (α : Type*) [Fintype α]
    (x : PrincipalTupleIndex B h → Option α → ℝ) : ‖principalTupleFlatten B h α x‖ ≤ ‖x‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr
  intro z
  exact (norm_le_pi_norm (x ⟨z.1, z.2.1, z.2.2.1⟩) z.2.2.2).trans
    (norm_le_pi_norm x ⟨z.1, z.2.1, z.2.2.1⟩)

theorem jointBooleanSource_eq_principalTuple_map {D α : Type*} [Fintype D] [Fintype α]
    [DecidableEq α] (B : D → Type*) [∀ d, Fintype (B d)] (h : D → ℕ) :
    jointBooleanSource (B := B) (α := α) h =
      (scalarCubeProductMeasure (PrincipalTupleIndex B h) α).map (principalTupleFlatten B h α) := by
  let F : (∀ d, (B d × Fin (h d)) → Option α → ℝ) → (PrincipalTupleIndex B h → Option α → ℝ) :=
    fun x j => x j.1 j.2
  have hF : Measurable F :=
    measurable_pi_iff.mpr (fun j => (measurable_pi_apply j.2).comp (measurable_pi_apply j.1))
  have ht : (Measure.pi (fun d => scalarCubeProductMeasure (B d × Fin (h d)) α)).map F =
      scalarCubeProductMeasure (PrincipalTupleIndex B h) α :=
    sigmaProductMeasure_flatten (fun _ => scalarCubeMeasure α)
  have hblock : Measurable (fun (x : ∀ d, (B d × Fin (h d)) → Option α → ℝ) d =>
      blockCubeFlatten (B d) (Fin (h d)) α (x d)) :=
    measurable_pi_iff.mpr (fun d => (blockCubeFlatten (B d) (Fin (h d)) α).continuous.measurable.comp
      (measurable_pi_apply d))
  rw [jointBooleanSource, sigmaAxisMeasure]
  simp_rw [blockCubeMeasure]
  rw [← Measure.pi_map_pi (fun d => (blockCubeFlatten (B d) (Fin (h d)) α).continuous.measurable.aemeasurable)]
  rw [Measure.map_map (sigmaAxisCoordinates (fun d => BlockParameter (B d) (Fin (h d)) α)).symm.continuous.measurable
    hblock]
  rw [← ht, Measure.map_map (principalTupleFlatten B h α).continuous.measurable hF]
  rfl

end Erdos3


namespace Erdos3

open MeasureTheory

theorem scalarCubeProductMeasure_ae_closedBall (J I : Type*) [Fintype J] [Fintype I]
    [DecidableEq I] : ∀ᵐ x ∂scalarCubeProductMeasure J I, x ∈ Metric.closedBall 0 1 := by
  filter_upwards [scalarCubeProductMeasure_ae_domain J I] with x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro j
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro i
  exact (scalarCubeDomain_coordinate_abs_lt_one (hx j (Set.mem_univ _)) i).le

theorem jointBooleanSource_ae_closedBall {D α : Type*} [Fintype D] [Fintype α]
    [DecidableEq α] (B : D → Type*) [∀ d, Fintype (B d)] (h : D → ℕ) :
    ∀ᵐ x ∂jointBooleanSource (B := B) (α := α) h, x ∈ Metric.closedBall 0 1 := by
  rw [jointBooleanSource_eq_principalTuple_map]
  apply (principalTupleFlatten B h α).toHomeomorph.toMeasurableEquiv.measurableEmbedding.ae_map_iff.mpr
  filter_upwards [scalarCubeProductMeasure_ae_closedBall (PrincipalTupleIndex B h) α] with x hx
  rw [Metric.mem_closedBall, dist_zero_right] at hx ⊢
  exact (principalTupleFlatten_norm_apply_le B h α x).trans hx

end Erdos3

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

theorem unitCoefficientSource_norm_le (I : Type*) [Fintype I] :
    ∀ᵐ r ∂unitCoefficientSource I, ‖r‖ ≤ 1 := by
  have hi : Integrable (smoothProductProfile I) := (smoothProductProfile_contDiff I).continuous.integrable_of_hasCompactSupport
    (smoothProductProfile_compact I)
  have hnull : unitCoefficientSource I {r | 1 < ‖r‖} = 0 := by
    rw [unitCoefficientSource, realDensityMeasure_apply volume _ hi
      (fun r => (smoothProductProfile_range I r).1) (measurableSet_lt measurable_const measurable_norm)]
    have hz : (∫ r in {r : I → ℝ | 1 < ‖r‖}, smoothProductProfile I r) = 0 := by
      apply setIntegral_eq_zero_of_forall_eq_zero
      exact fun r hr => smoothProductProfile_zero_outside I r hr
    rw [hz, ENNReal.ofReal_zero]
  exact (ae_iff.mpr (by simpa only [not_le] using hnull))

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

theorem regularizedImageDensity_support {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (μ : Measure Ω) (U : Ω → I → ℝ) (δ : ℝ≥0) (hδ : 0 < δ)
    {R : ℝ} (hR : 0 ≤ R) (hU : ∀ᵐ a ∂μ, ‖U a‖ ≤ R) :
    ∀ x, R+δ < ‖x‖ → regularizedImageDensity μ U δ x = 0 := by
  intro x hx
  apply integral_eq_zero_of_ae
  filter_upwards [hU] with a ha
  apply affineProductProfile_zero_outside (U a) (fun _ => (δ : ℝ)) (fun _ => hδ)
    (add_nonneg hR δ.coe_nonneg) _ x hx
  intro i
  exact add_le_add ((Real.norm_eq_abs (U a i)).symm.trans_le ((norm_le_pi_norm (U a) i).trans ha)) le_rfl

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ActiveProfileNoise
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {D G Z α : Type*} [Fintype D] [Fintype G] [Fintype α] [DecidableEq α]
variable {B : D → Type*} [∀ d, Fintype (B d)] (h : D → ℕ)
variable (P : D → Prop) [DecidablePred P] (extra : G → Option α → Z)
variable {O : {d // ¬P d} → Type*} (sets : ∀ d, O d → Finset α)

omit [Fintype D] in
theorem unitProfilePrincipalSize_pos (d : D) : 0 < unitProfilePrincipalSize (B := B) d :=
  principalProfileSize_pos zero_lt_one _

omit [Fintype D] [Fintype G] [Fintype α] [DecidableEq α] [DecidablePred P] in
theorem partitionedProfilePrincipal_unit_bounds
    (y : PartitionedProfileNoiseIndex G Z α B h P → ℝ) (hy : ∀ j, |y j| ≤ 1)
    (d : {d // ¬P d}) (b : B d.val) :
    unitProfilePrincipalSize (B := B) d.val ≤
        |partitionedProfilePrincipal h P (unitProfilePrincipalSize (B := B)) y d b| ∧
      |partitionedProfilePrincipal h P (unitProfilePrincipalSize (B := B)) y d b| ≤
        2 * unitProfilePrincipalSize (B := B) d.val := by
  have hγ := unitProfilePrincipalSize_pos (B := B) d.val
  obtain ⟨hl, hu⟩ := abs_le.mp (hy (.inr ⟨d.val, principalCoefficientSlot h d.val b⟩))
  have hlo : unitProfilePrincipalSize (B := B) d.val ≤
      partitionedProfilePrincipal h P (unitProfilePrincipalSize (B := B)) y d b := by
    unfold partitionedProfilePrincipal
    nlinarith
  rw [abs_of_nonneg (hγ.le.trans hlo)]
  refine ⟨hlo, ?_⟩
  unfold partitionedProfilePrincipal
  nlinarith

omit [Fintype D] [Fintype G] [Fintype α] [DecidableEq α] [DecidablePred P] in
theorem partitionedProfilePrincipal_unit_sum
    (y : PartitionedProfileNoiseIndex G Z α B h P → ℝ) (hy : ∀ j, |y j| ≤ 1)
    (d : {d // ¬P d}) :
    (∑ b, |partitionedProfilePrincipal h P (unitProfilePrincipalSize (B := B)) y d b|) ≤ 1 := by
  have hb := allocatedProfile_budget (R := 1) (σ := 1) zero_le_one le_rfl (Fintype.card (B d.val)) 0
  simp only [Nat.cast_zero, mul_zero, add_zero] at hb
  calc
    _ ≤ ∑ _b : B d.val, 2 * unitProfilePrincipalSize (B := B) d.val :=
      Finset.sum_le_sum (fun b _ => (partitionedProfilePrincipal_unit_bounds h P y hy d b).2)
    _ = 2 * principalProfileSize 1 (Fintype.card (B d.val)) * Fintype.card (B d.val) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, unitProfilePrincipalSize]
      ring
    _ ≤ 1 := by linarith

end Erdos3

end

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

theorem profileNoiseWithActive_abs_le {D G Z α : Type*} {B : D → Type*}
    (h : D → ℕ) (P : D → Prop) [DecidablePred P]
    (z : PartitionedProfileNoiseIndex G Z α B h P → ℝ)
    (r : ActiveProfileCoefficientIndex G B h P → ℝ)
    (hz : ∀ j, |z j| ≤ 1) (hr : ∀ j, |r j| ≤ 1)
    (j : PartitionedProfileNoiseIndex G Z α B h P) :
    |profileNoiseWithActive h P z r j| ≤ 1 := by
  rcases j with j | ⟨d, e⟩
  · exact hz _
  · dsimp only [profileNoiseWithActive]
    split_ifs with hp
    · exact hz _
    · exact hr _

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PartitionedIdealSupport
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

theorem partitionedIdealMap_norm_le {D G Z α : Type*}
    [Fintype D] [Fintype G] [Fintype Z] [Fintype α] [DecidableEq α]
    {B : D → Type*} [∀ d, Fintype (B d)] (h : D → ℕ)
    (P : D → Prop) [DecidablePred P]
    {O : {d // ¬P d} → Type*} [∀ d, Fintype (O d)] (sets : ∀ d, O d → Finset α)
    {degree : ℕ} (hdegree : ∀ d, h d ≤ degree)
    (y : PartitionedProfileNoiseIndex G Z α B h P → ℝ) (hy : ∀ j, |y j| ≤ 1)
    (x : PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d) → ℝ)
    (hx : ‖x‖ ≤ 1) :
    ‖partitionedIdealMap h P sets y x‖ ≤ partitionedIdealRadius α degree := by
  apply (pi_norm_le_iff_of_nonneg (partitionedIdealRadius_nonneg α degree)).mpr
  intro o
  have hs := partitionedProfilePrincipal_unit_sum h P y hy o.1
  have hp := jointBooleanSampler_coordinate_abs_le (fun d : {d // ¬P d} => h d.val)
    (partitionedProfilePrincipal h P (unitProfilePrincipalSize (B := B)) y) sets x hx o
  have hb : |jointBooleanSampler (fun d : {d // ¬P d} => h d.val)
      (partitionedProfilePrincipal h P (unitProfilePrincipalSize (B := B)) y) sets x o| ≤
      (2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ degree := by
    apply hp.trans
    have hpow : (2 : ℝ) ^ (sets o.1 o.2).card ≤ 2 ^ Fintype.card α :=
      pow_le_pow_right₀ (by norm_num) (Finset.card_le_univ (sets o.1 o.2))
    have hdp : ((Fintype.card α : ℝ) + 1) ^ h o.1.val ≤
        ((Fintype.card α : ℝ) + 1) ^ degree :=
      pow_le_pow_right₀ (by linarith [Nat.cast_nonneg (α := ℝ) (Fintype.card α)]) (hdegree o.1.val)
    have hinner := mul_le_mul hs hdp (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using mul_le_mul hpow hinner (by positivity) (by positivity)
  have hc : |booleanConstantJet sets (partitionedProfileConstant h P (fun _ => 1 / 4) y) o| ≤ 1 / 4 := by
    unfold booleanConstantJet
    split_ifs
    · dsimp only [partitionedProfileConstant]
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
      exact mul_le_of_le_one_right (by norm_num) (hy _)
    · norm_num
  rw [Real.norm_eq_abs]
  change |booleanConstantJet sets (partitionedProfileConstant h P (fun _ => 1 / 4) y) o +
    jointBooleanSampler (fun d : {d // ¬P d} => h d.val)
      (partitionedProfilePrincipal h P (unitProfilePrincipalSize (B := B)) y) sets x o| ≤ _
  exact (abs_add_le _ _).trans (add_le_add hc hb)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ActiveAveragedProfileComparison
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem unitCoefficientSource_abs_le (I : Type*) [Fintype I] :
    ∀ᵐ r ∂unitCoefficientSource I, ∀ i, |r i| ≤ 1 := by
  filter_upwards [unitCoefficientSource_norm_le I] with r hr i
  exact (Real.norm_eq_abs (r i)).symm.trans_le ((norm_le_pi_norm r i).trans hr)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedRefinedLongJetComparison
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Matrix NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val+1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (rows j)).submatrix id (s j)).det ≠ 0)

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)

omit [∀ j, DecidableEq (O j)] in
theorem allocatedLongJetOutputScale_pos (a : {a // ¬grid a}) :
    0 < allocatedLongJetOutputScale B U basis S (O := O) a := by
  rcases a with ⟨⟨j, a⟩, ha⟩
  cases a with
  | inl i => exact zero_lt_one
  | inr i => exact pow_pos (Nat.cast_pos.mpr (basisAxisScale_pos (basis j) i)) _

end Erdos3.VectorPolynomial

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedPhysicalCoveredDensity
namespace OAI

section

namespace Erdos3

open MeasureTheory Module Submodule
open scoped Classical

theorem standardLatticeClosedQuarterBox_isCompact (J : Type*) [Fintype J] :
    IsCompact (standardLatticeClosedQuarterBox J) := by
  have he : standardLatticeClosedQuarterBox J =
      (PiLp.homeomorph 2 (fun _ : J => ℝ)) ⁻¹'
        Set.Icc (fun _ => -(1 / 4 : ℝ)) (fun _ => (1 / 4 : ℝ)) := by
    ext x
    simp only [standardLatticeClosedQuarterBox, Set.mem_ofPred_eq, Set.mem_preimage,
      Set.mem_Icc, Pi.le_def, abs_le, forall_and]
    rfl
  rw [he]
  exact (PiLp.homeomorph 2 (fun _ : J => ℝ)).isClosedEmbedding.isCompact_preimage isCompact_Icc

theorem standardLatticeClosedQuarterBox_subset_smallBox (J : Type*) [Fintype J] :
    standardLatticeClosedQuarterBox J ⊆ standardLatticeSmallBox J := by
  intro x hx i
  exact (hx i).trans_lt (by norm_num)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedActualProfileControl
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical BigOperators

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]

local notation "grid" => allocatedGridAxis (I := I) U basis S.value

theorem allocatedLongJetRealCoordinates_measurable :
    Measurable (allocatedLongJetRealCoordinates B U basis S (O := O)) := by
  apply measurable_pi_iff.mpr
  intro q
  rcases q with ⟨⟨⟨j, i | i⟩, ha⟩, o⟩
  · exact (measurable_pi_apply o).comp
      (show Measurable (fun z : AllocatedLongJetRows B U basis S O =>
        z ⟨⟨j, .inl i⟩, ha⟩) from measurable_pi_apply _)
  · exact (measurable_of_countable
      (fun z : O j → ℤ => (z o : ℝ) / (basisAxisScale (basis j) i : ℝ))).comp
      (show Measurable (fun z : AllocatedLongJetRows B U basis S O =>
        z ⟨⟨j, .inr i⟩, ha⟩) from measurable_pi_apply _)

variable {α : Type*} [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value) (rows : ∀ j, O j → Finset α)
variable (modulus : ℕ)
variable (residue : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))

theorem allocatedLongJetMask_measurable (a : {a // ¬grid a}) :
    Measurable (allocatedLongJetMask B U basis S x rows modulus residue a) := by
  rcases a with ⟨⟨j, i | i⟩, ha⟩
  · exact measurable_const
  · change Measurable (allocatedIntegerKernelMask B U basis S x rows j modulus (residue j))
    exact measurable_of_countable _

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedLongIntegralMass
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical BigOperators

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]
variable {α : Type*} [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value) (rows : ∀ j, O j → Finset α)
variable (modulus : ℕ)
variable (residue : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "output" => (Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a)))

theorem allocatedLongProfileDensity_measurable (f : (output → ℝ) → ℝ) (hf : Measurable f) :
    Measurable (allocatedLongProfileDensity B U b S x rows modulus residue f) := by
  have hm : Measurable (fun z : AllocatedLongJetRows B U b S O =>
      ∏ a, allocatedLongJetMask B U b S x rows modulus residue a (z a)) :=
    Finset.measurable_prod _ (fun a _ =>
      (allocatedLongJetMask_measurable B U b S x rows modulus residue a).comp (measurable_pi_apply a))
  exact (hm.mul (hf.comp (allocatedLongJetRealCoordinates_measurable B U b S))).div_const _

theorem allocatedLongProfileDensity_nonneg
    (f : (output → ℝ) → ℝ) (hf : ∀ z, 0 ≤ f z)
    (hm : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U b S x rows j modulus (residue j) z)
    (z : AllocatedLongJetRows B U b S O) :
    0 ≤ allocatedLongProfileDensity B U b S x rows modulus residue f z := by
  apply div_nonneg (mul_nonneg ?_ (hf _))
    (Finset.prod_nonneg (fun a _ => (allocatedLongJetOutputScale_pos B U b S a).le))
  apply Finset.prod_nonneg
  intro a _
  rcases a with ⟨⟨j, i | i⟩, ha⟩
  · exact zero_le_one
  · exact hm j _

theorem allocatedLongProfileDensity_ne_zero
    (f : (output → ℝ) → ℝ) (z : AllocatedLongJetRows B U b S O)
    (hz : allocatedLongProfileDensity B U b S x rows modulus residue f z ≠ 0) :
    f (allocatedLongJetRealCoordinates B U b S z) ≠ 0 := by
  intro he
  apply hz
  simp only [allocatedLongProfileDensity, he, mul_zero, zero_div]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedRowSlicedIdealCoordinates
namespace OAI

section

namespace Erdos3
open MeasureTheory
open scoped NNReal BigOperators

 theorem coordinateAffine_norm_le_one {I : Type*} [Fintype I]
    (center width : I → ℝ) (hw : ∀ i, |center i| + |width i| ≤ 1)
    (x : I → ℝ) (hx : ‖x‖ ≤ 1) : ‖fun i => center i + width i * x i‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
  intro i
  have hi : |x i| ≤ 1 := (norm_le_pi_norm x i).trans hx
  calc
    ‖center i + width i * x i‖ ≤ |center i| + |width i| * |x i| := by
      simpa only [Real.norm_eq_abs, abs_mul] using norm_add_le (center i) (width i * x i)
    _ ≤ |center i| + |width i| := add_le_add le_rfl
      (by simpa using mul_le_mul_of_nonneg_left hi (abs_nonneg (width i)))
    _ ≤ 1 := hw i

variable {D G α : Type*} [Fintype D] [Fintype G] [Fintype α] [DecidableEq α]
  (Z : Type*) [Fintype Z] {B : D → Type*} [∀ d, Fintype (B d)] (h : D → ℕ)
  (P : D → Prop) [DecidablePred P]
  {O : {d // ¬P d} → Type*} [∀ d, Fintype (O d)] (sets : ∀ d, O d → Finset α)

 theorem partitionedSlicedRegularizedIdeal_zero_outside {degree : ℕ}
    (hdegree : ∀ d, h d ≤ degree) (ρ : ℝ≥0) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (center width : PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d) → ℝ)
    (hw : ∀ i, |center i| + |width i| ≤ 1)
    (z : PartitionedProfileNoiseIndex G Z α B h P → ℝ) (hz : ∀ j, |z j| ≤ 1)
    (v : (Σ d, O d) → ℝ) (hv : partitionedIdealRadius α degree + 1 < ‖v‖) :
    partitionedSlicedRegularizedIdeal h P sets ρ center width z v = 0 := by
  apply regularizedImageDensity_support
    (jointBooleanSource (fun d : {d // ¬P d} => h d.val))
    (fun x => partitionedIdealMap h P sets z (fun i => center i + width i * x i))
    ρ hρ (partitionedIdealRadius_nonneg α degree)
  · filter_upwards [jointBooleanSource_ae_closedBall
      (α := α) (fun d : {d // ¬P d} => B d.val) (fun d => h d.val)] with x hx
    apply partitionedIdealMap_norm_le h P sets hdegree z hz
    apply coordinateAffine_norm_le_one center width hw x
    simpa only [Metric.mem_closedBall, dist_zero_right] using hx
  · have hd : (ρ : ℝ) ≤ 1 := hρ1
    linarith

 theorem activeAveragedSlicedProfileIdeal_zero_outside {degree : ℕ}
    (hdegree : ∀ d, h d ≤ degree) (ρ : ℝ≥0) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (center width : PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d) → ℝ)
    (hw : ∀ i, |center i| + |width i| ≤ 1)
    (v : (Σ d, O d) → ℝ) (hv : partitionedIdealRadius α degree + 1 < ‖v‖) :
    activeAveragedSlicedProfileIdeal (G := G) (B := B) Z h P sets ρ center width v = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [unitCoefficientSource_abs_le (ActiveProfileCoefficientIndex G B h P)] with r hr
  exact partitionedSlicedRegularizedIdeal_zero_outside Z h P sets hdegree ρ hρ hρ1 center width hw
    (profileNoiseWithActive (Z := Z) h P (fun _ => 0) r)
    (profileNoiseWithActive_abs_le h P (fun _ => 0) r (fun _ => by simp) hr) v hv

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedAffineProfileMeanTransport
namespace OAI

section

namespace Erdos3
open scoped NNReal

theorem activeScaledSlicedIdeal_coordinate_support
    {D G Z α : Type*} [Fintype D] [Fintype G] [Fintype Z] [Fintype α] [DecidableEq α]
    {B : D → Type*} [∀ d, Fintype (B d)] (h : D → ℕ)
    (P : D → Prop) [DecidablePred P]
    {O : {d // ¬P d} → Type*} [∀ d, Fintype (O d)] (sets : ∀ d, O d → Finset α)
    (R : (Σ d, O d) → ℝ) (hR : ∀ q, 0 < R q) {degree : ℕ} (hd : ∀ d, h d ≤ degree)
    (ρ : ℝ≥0) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (center width : PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d) → ℝ)
    (hw : ∀ i, |center i| + |width i| ≤ 1)
    (v : (Σ d, O d) → ℝ)
    (hv : diagonalImageDensity R (activeAveragedSlicedProfileIdeal (G := G) (B := B)
      Z h P sets ρ center width) v ≠ 0) (q : Σ d, O d) :
    |v q| ≤ (partitionedIdealRadius α degree + 1) * R q := by
  have hn : ‖fun q => v q / R q‖ ≤ partitionedIdealRadius α degree + 1 := by
    by_contra hh
    apply hv
    unfold diagonalImageDensity
    rw [activeAveragedSlicedProfileIdeal_zero_outside (G := G) (B := B) Z h P sets
      hd ρ hρ hρ1 center width hw _ (lt_of_not_ge hh), mul_zero]
  have hc := (norm_le_pi_norm (fun q => v q / R q) q).trans hn
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (hR q)] at hc
  exact (div_le_iff₀ (hR q)).mp hc

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "Jet" => (Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a)))
variable (hR : ∀ j, 0 < R j)
variable (ρ : ℝ≥0)
variable (center width : PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n)
  (α := α) (fun a => ¬allocatedGridAxis (I := I) U basis S.value a) → ℝ)

variable (hσ : ∀ j, 0 < σ j)
variable (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U basis S.value a)
  (allocatedPrincipalSides B U basis S))
variable (Q : Fin m → Type*) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

local notation "jetRows" => O
local notation "ideal" => diagonalImageDensity (fun q : Jet => R (Sigma.fst (Subtype.val (Sigma.fst q))))
  (activeAveragedSlicedProfileIdeal (G := G) (B := B) (G × Option α)
    (layerSamplerDegree I n) grid (fun a => rows (Sigma.fst (Subtype.val a))) ρ center width)
local notation "reference" => allocatedLongJetReference B U basis S jetRows

omit [∀ a, DecidableEq (B a)] in
theorem allocatedAffineCoveredProfile_test_integral_s2_oai
    [∀ a, DecidableEq (B a)]
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hw : ∀ i, |center i| + |width i| ≤ 1)
    {P : ℝ}
    (hRbound : ∀ j, R j ≤ Real.exp P) (hInv : ∀ j, (R j)⁻¹ ≤ Real.exp P)
    (modulus : ℕ)
    (residue : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))
    {Cmask : ℝ} (hCmask : 1 ≤ Cmask)
    (hmask : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U basis S x rows j modulus (residue j) z ∧
      allocatedIntegerKernelMask B U basis S x rows j modulus (residue j) z ≤ Cmask)
    (hσ1 : ∀ j, σ j ≤ 1)
    (T : Fin m → ℝ) (hT : ∀ j, partitionedIdealRadius α m + 1 ≤ T j)
    (hsource : ∀ j, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
        ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ (j.val + 1)) ≤ T j)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm v‖ ≤ C j * ‖v‖)
    (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (T j * R j)) ≤ 1 / 4)
    (F : EuclideanJetLayers U jetRows → ℂ) (hF : Measurable F)
    {CF : ℝ} (hFb : ∀ z, ‖F z‖ ≤ CF) :
    let f := allocatedLongProfileDensity B U basis S x rows modulus residue ideal
    (∫ a₀, ∫ z, (f z : ℂ) * allocatedCoveredFixedTest B U basis S x u v₀ rows
      Q hb o bW d (fun p => F p.2) a₀ z ∂reference ∂allocatedFrozenCoefficientSource B U basis hR hσ S) =
      ∫ y, (allocatedCoveredProfileDensity B U basis hR hσ S x u v₀ rows hb o bW d
        (fun j (_ : O j) => standardLatticeClosedQuarterBox (J j)) f y : ℂ) * F y
          ∂Measure.pi (fun j => Measure.pi (fun _ : O j => ν j)) := by
  intro f
  have hIm : Measurable ideal := diagonalImageDensity_measurable
    (fun q : Jet => R q.1.val.1) (fun q => (hR q.1.val.1).ne')
    (activeAveragedSlicedProfileIdeal_spec (G := G) (B := B) (G × Option α)
      (layerSamplerDegree I n) grid (fun a => rows a.val.1) ρ hρ center width).2.1.continuous.measurable
  have hfm : Measurable f := allocatedLongProfileDensity_measurable B U basis S x rows
    modulus residue ideal hIm
  have hfi : Integrable f reference := allocatedAffineIdeal_profile_integrable_s2 B U basis hR S x rows
    hRbound hInv ρ hρ hρ1 center width hw modulus residue hCmask hmask
  have hf0 : ∀ z, 0 ≤ f z := allocatedLongProfileDensity_nonneg B U basis S x rows
    modulus residue ideal
      (diagonalImageDensity_nonneg _ (fun v => (activeAveragedSlicedProfileIdeal_spec
        (G := G) (B := B) (G × Option α) (layerSamplerDegree I n) grid
        (fun a => rows a.val.1) ρ hρ center width).1 v |>.1))
      (fun j z => (hmask j z).1)
  apply allocatedCoveredProfile_test_integral_s2 B U basis hR hσ S x u v₀ rows Q hb o bW d ν
    (fun j (_ : O j) => standardLatticeClosedQuarterBox (J j))
    (fun j _ => (standardLatticeClosedQuarterBox_isCompact (J j)).measurableSet)
    (fun j _ => standardLatticeClosedQuarterBox_subset_smallBox (J j)) f hfm hfi hf0 ?_ F hF hFb
  intro z hz
  by_contra hn
  apply hz
  apply allocatedGridlessWeightedKernel_quarter_support_s2 B U basis hR hσ S x u v₀ rows Q o d
    hσ1 T (fun j => (by have := partitionedIdealRadius_nonneg α m; have := hT j; linarith : 0 ≤ T j)) hsource C hC hchart hbudget f ?_ z hn
  intro w hwne a₀ t
  have hi := allocatedLongProfileDensity_ne_zero B U basis S x rows modulus residue ideal w hwne
  exact (activeScaledSlicedIdeal_coordinate_support (G := G) (Z := G × Option α) (B := B)
    (layerSamplerDegree I n) grid (fun a => rows a.val.1) (fun q : Jet => R q.1.val.1)
    (fun q => hR q.1.val.1) (fun a => Nat.succ_le_of_lt a.1.isLt)
    ρ hρ hρ1 center width hw _ hi ⟨a₀, t⟩).trans
      (mul_le_mul_of_nonneg_right (hT _) (hR _).le)

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4, u_5, u_6, u_7} : type_of% @OAI.Erdos3.VectorPolynomial.allocatedAffineCoveredProfile_test_integral_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6, u_7} := @OAI.Erdos3.VectorPolynomial.allocatedAffineCoveredProfile_test_integral_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6, u_7}
