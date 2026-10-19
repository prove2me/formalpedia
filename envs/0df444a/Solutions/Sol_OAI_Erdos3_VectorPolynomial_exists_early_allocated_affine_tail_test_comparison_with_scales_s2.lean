-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.exists_early_allocated_affine_tail_test_comparison_with_scales_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-17T11:13:16.192984+00:00
-- url     : https://prove2.me/submissions/5d5ec6bf-3d51-48a7-8290-bfb9294056a5

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B126
import Definitions.Def_OAIE3v2B162
import Theorems.Thm_OAI_Erdos3_exists_partitioned_sliced_density_comparison_with_scales_s2

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RealPolynomialEvaluationMass
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem polynomialMonomial_eval {K I : Type*}
    (a : K → MvPolynomial I ℝ) (m : K →₀ ℕ) (x : I → ℝ) :
    MvPolynomial.eval x (polynomialMonomial a m) =
      ∏ k ∈ m.support, MvPolynomial.eval x (a k) ^ m k := by
  simp only [polynomialMonomial, map_prod, map_pow]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RealKernelJetInverse
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

theorem realJetMatrix_apply_coefficients {α K O J : Type*} [DecidableEq α] [Fintype J]
    (basis : J → MvPolynomial K ℝ) (vertices : Finset α → K → ℝ)
    (rows : O → Finset α) (c : J → ℝ) (o : O) :
    (realJetMatrix basis vertices rows *ᵥ c) o =
      booleanCoefficient (fun t => MvPolynomial.eval (vertices t)
        (∑ j, MvPolynomial.C (c j) * basis j)) (rows o) := by
  simp only [map_sum, map_mul, MvPolynomial.eval_C,
    booleanCoefficient_sum, booleanCoefficient_const_mul]
  change (∑ j, realJetMatrix basis vertices rows o j * c j) = _
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.BooleanAffineInput
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem booleanAffineInput_eval {I α : Type*} [Fintype α] [DecidableEq α]
    (a : Option α → MvPolynomial I ℝ) (t : Finset α) (x : I → ℝ) :
    MvPolynomial.eval x (booleanAffineInput a t) =
      ∑ r, (booleanFeature r t : ℝ) * MvPolynomial.eval x (a r) := by
  simp only [booleanAffineInput, map_sum, map_mul, MvPolynomial.eval_C]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoefficientNormalization
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

theorem booleanJetColumnPolynomial_eval {K P α : Type*} [Fintype α] [DecidableEq α]
    (e : K →₀ ℕ) (input : K → Option α → MvPolynomial P ℝ) (s : Finset α) (x : P → ℝ) :
    MvPolynomial.eval x (booleanJetColumnPolynomial e input s) =
      booleanCoefficient (fun t => ∏ k ∈ e.support,
        (∑ r, (booleanFeature r t : ℝ) * MvPolynomial.eval x (input k r)) ^ e k) s := by
  simp only [booleanJetColumnPolynomial, booleanCoefficient_map, polynomialMonomial_eval, booleanAffineInput_eval]

theorem booleanJetColumns_apply_coefficients {K P α O J : Type*} [Fintype α] [DecidableEq α]
    [Fintype O] [Fintype J] (e : J → K →₀ ℕ) (input : K → Option α → MvPolynomial P ℝ)
    (rows : O → Finset α) (x : P → ℝ) (c : J → ℝ) (o : O) :
    polynomialColumns (fun o j => booleanJetColumnPolynomial (e j) input (rows o)) x c o =
      booleanCoefficient (fun t => ∑ j, c j * ∏ k ∈ (e j).support,
        (∑ r, (booleanFeature r t : ℝ) * MvPolynomial.eval x (input k r)) ^ e j k) (rows o) := by
  simp only [booleanCoefficient_sum, booleanCoefficient_const_mul]
  change (∑ j, MvPolynomial.eval x (booleanJetColumnPolynomial (e j) input (rows o)) * c j) = _
  apply Finset.sum_congr rfl
  intro j _
  rw [booleanJetColumnPolynomial_eval, mul_comm]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.MonomialArrayJet
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

theorem realJetMatrix_monomialArray {α K O J : Type*} [DecidableEq α] [Fintype J]
    (e : J → K →₀ ℕ) (vertices : Finset α → K → ℝ) (rows : O → Finset α)
    (a : J → ℝ) (o : O) :
    (realJetMatrix (fun j => MvPolynomial.monomial (e j) 1) vertices rows *ᵥ a) o =
      booleanCoefficient (fun t => MvPolynomial.eval (vertices t) (monomialArrayPolynomial e a)) (rows o) := by
  rw [realJetMatrix_apply_coefficients]
  simp only [MvPolynomial.C_mul_monomial, mul_one, monomialArrayPolynomial]

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

theorem integerScalarCubeBox_normalized_norm_le {I : Type*} [Fintype I] {L : ℕ}
    (hL : 0 < L) (z : IntegerScalarCubeBox I L) : ‖fun i => (z i : ℝ) / L‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro i
  have hz := Finset.mem_Ico.mp (z i).property
  have hbound : |(z i : ℝ)| ≤ L := abs_le.mpr
    ⟨by exact_mod_cast hz.1, by exact_mod_cast hz.2.le⟩
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (by exact_mod_cast hL : (0 : ℝ) < L)]
  exact (div_le_one (by exact_mod_cast hL)).mpr hbound

end Erdos3

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NormalizedJetColumns
namespace OAI

section

namespace Erdos3

open scoped NNReal BigOperators

theorem frozenTupleCoordinate_eval {Z P : Type*} (z : Z → ℝ) (x : P → ℝ) (i : Z ⊕ P) :
    MvPolynomial.eval x (frozenTupleCoordinate z i) = Sum.elim z x i := by
  cases i <;> simp [frozenTupleCoordinate]

theorem normalizedJetColumns_apply_coefficients {Z P K α O J : Type*}
    [Fintype α] [DecidableEq α] [Fintype O] [Fintype J]
    (e : J → K →₀ ℕ) (input : K → Option α → Z ⊕ P) (z : Z → ℝ) (rows : O → Finset α)
    (x : P → ℝ) (c : J → ℝ) (o : O) :
    polynomialColumns (fun o j => normalizedJetColumn (e j) input z (rows o)) x c o =
      booleanCoefficient (fun t => ∑ j, c j * ∏ k ∈ (e j).support,
        (normalizedCubeTuple input z x t k)^e j k) (rows o) := by
  simpa only [normalizedJetColumn, frozenTupleCoordinate_eval, normalizedCubeTuple] using
    booleanJetColumns_apply_coefficients e (fun k r => frozenTupleCoordinate z (input k r)) rows x c o

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerNormalizedJetColumns
namespace OAI


namespace Erdos3

open scoped BigOperators Matrix

theorem normalizedJetColumns_eq_realJetMatrix {Z P K α I N : Type*}
    [Fintype α] [DecidableEq α] [Fintype I] [Fintype N]
    (e : N → K →₀ ℕ) (input : K → Option α → Z ⊕ P) (z : Z → ℝ)
    (rows : I → Finset α) (x : P → ℝ) :
    polynomialColumns (fun i n => normalizedJetColumn (e n) input z (rows i)) x =
      matrixSupCLM (realJetMatrix (fun n => MvPolynomial.monomial (e n) 1)
        (normalizedCubeTuple input z x) rows) := by
  unfold polynomialColumns
  congr 1
  funext i n
  simp only [normalizedJetColumn, booleanJetColumnPolynomial_eval, frozenTupleCoordinate_eval,
    realJetMatrix, MvPolynomial.eval_monomial, one_mul, Finsupp.prod, normalizedCubeTuple]

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.LayerSamplerWitnessScale
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule

variable {m : ℕ}

variable {G : Type*} {I : Fin m → Type*} {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

theorem layerContinuousPrincipalSlots_card (j : Fin m) (i : I j) :
    (layerContinuousPrincipalSlots (G := G) B j i).card = Fintype.card (B ⟨j, Sum.inl i⟩) :=
  principalCoefficientSlots_card _ _ (Nat.zero_lt_succ _)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NestedDiracIntegral
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem integral_dirac_first {Z X : Type*} [MeasurableSpace Z] [MeasurableSpace X]
    (ν : Measure X) [SFinite ν] (z : Z) (f : Z × X → ℝ) (hf : Measurable f) :
    (∫ p, f p ∂(Measure.dirac z).prod ν) = ∫ x, f (z, x) ∂ν := by
  rw [Measure.dirac_prod]
  exact integral_map measurable_prodMk_left.aemeasurable hf.aestronglyMeasurable

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

theorem integral_dirac_first_nested {Z X Y : Type*}
    [MeasurableSpace Z] [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]
    (z : Z) (f : (Z × X) × Y → ℝ) (hf : Measurable f) :
    (∫ p, f p ∂((Measure.dirac z).prod μ).prod ν) =
      ∫ p : X × Y, f ((z, p.1), p.2) ∂μ.prod ν := by
  have he : ((Measure.dirac z).prod μ).prod ν =
      (μ.prod ν).map (fun p : X × Y => ((z, p.1), p.2)) := by
    calc
      _ = (μ.map (Prod.mk z)).prod (ν.map id) := by
        rw [Measure.dirac_prod, Measure.map_id]
      _ = _ := Measure.map_prod_map μ ν measurable_prodMk_left measurable_id
  rw [he]
  exact integral_map
    ((measurable_const.prodMk measurable_fst).prodMk measurable_snd).aemeasurable hf.aestronglyMeasurable

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NormalizedJetMeasurability
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem normalizedCubeTuple_measurable_comp {Ω Z P K α : Type*} [MeasurableSpace Ω]
    [Fintype α] [DecidableEq α] (input : K → Option α → Z ⊕ P)
    (z : Ω → Z → ℝ) (hz : ∀ j, Measurable (fun ω => z ω j))
    (x : Ω → P → ℝ) (hx : ∀ j, Measurable (fun ω => x ω j)) (t : Finset α) (k : K) :
    Measurable (fun ω => normalizedCubeTuple input (z ω) (x ω) t k) := by
  have hs (i : Z ⊕ P) : Measurable (fun ω => Sum.elim (z ω) (x ω) i) := by
    cases i with
    | inl j => exact hz j
    | inr j => exact hx j
  unfold normalizedCubeTuple
  fun_prop

theorem normalizedJetColumns_measurable_comp {Ω Z P K α I N : Type*} [MeasurableSpace Ω]
    [Fintype α] [DecidableEq α] [Fintype I] [Fintype N]
    (e : N → K →₀ ℕ) (input : K → Option α → Z ⊕ P) (rows : I → Finset α)
    (z : Ω → Z → ℝ) (hz : ∀ j, Measurable (fun ω => z ω j))
    (x : Ω → P → ℝ) (hx : ∀ j, Measurable (fun ω => x ω j))
    (c : Ω → N → ℝ) (hc : ∀ j, Measurable (fun ω => c ω j)) :
    Measurable (fun ω => polynomialColumns (fun o n => normalizedJetColumn (e n) input (z ω) (rows o)) (x ω) (c ω)) := by
  apply measurable_pi_iff.mpr
  intro o
  simp_rw [normalizedJetColumns_apply_coefficients, booleanCoefficient]
  have ht (t : Finset α) (k : K) := normalizedCubeTuple_measurable_comp input z hz x hx t k
  fun_prop

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedEnormousProfiles
namespace OAI

section

namespace Erdos3

theorem principalTupleNormalized_norm_le {D α : Type*}
    [Fintype D] [Fintype α] [DecidableEq α]
    (B : D → Type*) [∀ d, Fintype (B d)] (h : D → ℕ)
    (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ j, 0 < L j)
    (y : PrincipalIntegerTuples B h α L) : ‖principalTupleNormalized L y‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro a
  exact (norm_le_pi_norm (fun i => (y ⟨a.1, a.2.1, a.2.2.1⟩ i : ℝ)/L ⟨a.1, a.2.1, a.2.2.1⟩) a.2.2.2).trans
    (integerScalarCubeBox_normalized_norm_le (hL _) (y _))

end Erdos3

end

section

namespace Erdos3

variable {D G Z α : Type*} {B : D → Type*} {h : D → ℕ}

theorem partitionedPrincipalInput_frozen_bound [Fintype D] [∀ d, Fintype (B d)]
    [Fintype α] [DecidableEq α] (P : D → Prop) [DecidablePred P]
    (zr : Z → ℝ) (hz : ∀ j, |zr j| ≤ 1)
    (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ j, 0 < L j)
    (u : PrincipalAxisTuples (α := α) P L)
    (j : Z ⊕ PrincipalAxisParameter (B := B) (h := h) (α := α) P) :
    |Sum.elim zr (principalTupleNormalized (principalAxisLength P L) u) j| ≤ 1 := by
  cases j with
  | inl j => exact hz j
  | inr j =>
    have hb : ‖principalTupleNormalized (principalAxisLength P L) u‖ ≤ 1 :=
      principalTupleNormalized_norm_le
        (fun d : {d // P d} => B d.val) (fun d => h d.val)
        (principalAxisLength P L) (fun k => hL ⟨k.1.val, k.2⟩) u
    exact (norm_le_pi_norm (principalTupleNormalized (principalAxisLength P L) u) j).trans hb

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NonprincipalDilation
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem mem_nonprincipalCoefficientSlots {C B K : Type*} [Fintype C] [Fintype B]
    (e : C → K →₀ ℕ) (principal : B → K →₀ ℕ) (j : C) :
    j ∈ nonprincipalCoefficientSlots e principal ↔
      e j ∈ fixedNonprincipalExponents (monomialExponentSet e) principal := by
  classical
  simp only [nonprincipalCoefficientSlots, Finset.mem_filter, Finset.mem_univ, true_and]

theorem mem_monomialExponentSet {C K : Type*} [Fintype C]
    (e : C → K →₀ ℕ) (m : K →₀ ℕ) :
    m ∈ monomialExponentSet e ↔ ∃ j, e j = m := by
  classical
  simp only [monomialExponentSet, Finset.mem_image, Finset.mem_univ, true_and]

theorem mem_fixedNonprincipalExponents {B K : Type*} [Fintype B]
    (S : Finset (K →₀ ℕ)) (principal : B → K →₀ ℕ) (m : K →₀ ℕ) :
    m ∈ fixedNonprincipalExponents S principal ↔
      m ∈ S ∧ m ≠ 0 ∧ ∀ b, principal b ≠ m := by
  classical
  simp [fixedNonprincipalExponents]

theorem nonprincipalCoefficientSlots_not_principal {C B K : Type*} [Fintype C] [Fintype B]
    (e : C → K →₀ ℕ) (principal : B → K →₀ ℕ) (j : C) (b : B) (hj : e j = principal b) :
    j ∉ nonprincipalCoefficientSlots e principal := by
  classical
  intro hm
  have hn := ((mem_fixedNonprincipalExponents _ principal (e j)).mp
    ((mem_nonprincipalCoefficientSlots e principal j).mp hm)).2.2
  exact hn b hj.symm

theorem nonprincipalCoefficientSlots_not_zero {C B K : Type*} [Fintype C] [Fintype B]
    (e : C → K →₀ ℕ) (principal : B → K →₀ ℕ) (j : C) (hj : e j = 0) :
    j ∉ nonprincipalCoefficientSlots e principal := by
  classical
  intro hm
  have hn := ((mem_fixedNonprincipalExponents _ principal (e j)).mp
    ((mem_nonprincipalCoefficientSlots e principal j).mp hm)).2.1
  exact hn hj

end Erdos3

end

section

namespace Erdos3

theorem nonprincipalDilation_principal {C B K : Type*} [Fintype C] [Fintype B]
    (e : C → K →₀ ℕ) (principal : B → K →₀ ℕ) (t : ℝ) (j : C) (b : B)
    (hj : e j = principal b) : nonprincipalDilation e principal t j = 1 := by
  classical
  simp only [nonprincipalDilation, nonprincipalCoefficientSlots_not_principal e principal j b hj, ite_false]

theorem nonprincipalDilation_zero {C B K : Type*} [Fintype C] [Fintype B]
    (e : C → K →₀ ℕ) (principal : B → K →₀ ℕ) (t : ℝ) (j : C)
    (hj : e j = 0) : nonprincipalDilation e principal t j = 1 := by
  classical
  simp only [nonprincipalDilation, nonprincipalCoefficientSlots_not_zero e principal j hj, ite_false]

theorem nonprincipalDilation_mem {C B K : Type*} [Fintype C] [Fintype B]
    (e : C → K →₀ ℕ) (principal : B → K →₀ ℕ) (t : ℝ) (j : C)
    (hj : j ∈ nonprincipalCoefficientSlots e principal) : nonprincipalDilation e principal t j = t := by
  classical
  simp only [nonprincipalDilation, hj, ite_true]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ActiveProfileNoise
namespace OAI

section

namespace Erdos3

open VectorPolynomial
open scoped BigOperators

variable {D G : Type*} [Fintype D] [Fintype G] {B : D → Type*}
variable [∀ d, Fintype (B d)] (h : D → ℕ) (d : D)

theorem bounded_mem_nonprincipalCoefficientSlots
    (e : BoundedCoefficientExponent (SamplerTupleIndex G B h) (h d)) :
    e ∈ nonprincipalCoefficientSlots Subtype.val (canonicalPrincipalExponent h d) ↔
      e ≠ constantCoefficientSlot _ _ ∧ e ∉ principalCoefficientSlots h d := by
  classical
  rw [mem_nonprincipalCoefficientSlots, mem_fixedNonprincipalExponents]
  have hz : e.val = 0 ↔ e = constantCoefficientSlot _ _ := by
    constructor
    · intro he
      exact Subtype.ext he
    · intro he
      exact congrArg Subtype.val he
  have hp : (∃ b, canonicalPrincipalExponent h d b = e.val) ↔
      e ∈ principalCoefficientSlots h d := by
    rw [mem_principalCoefficientSlots]
    constructor <;> rintro ⟨b, hb⟩
    · exact ⟨b, Subtype.ext hb⟩
    · exact ⟨b, congrArg Subtype.val hb⟩
  have hm : e.val ∈ monomialExponentSet
      (Subtype.val : BoundedCoefficientExponent (SamplerTupleIndex G B h) (h d) → _) :=
    (mem_monomialExponentSet _ _).mpr ⟨e, rfl⟩
  simp only [hm, true_and, ← not_exists, hp]
  exact and_congr (not_congr hz) Iff.rfl

end Erdos3

end

section

namespace Erdos3

open VectorPolynomial
open scoped BigOperators

theorem partitionedProfileInput_source {D G Z α : Type*} [Fintype α] [DecidableEq α]
    {B : D → Type*} {h : D → ℕ} (P : D → Prop) [DecidablePred P]
    (extra : G → Option α → Z) (y : PartitionedProfileNoiseIndex G Z α B h P → ℝ)
    (x : PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d) → ℝ)
    (s : Finset α) (k : SamplerTupleIndex G B h) :
    normalizedCubeTuple (partitionedProfileInput P extra) y x s k =
      normalizedCubeTuple (partitionedPrincipalInput P extra) (fun j => y (.inl j)) x s k := by
  unfold normalizedCubeTuple
  apply Finset.sum_congr rfl
  intro a _
  unfold partitionedProfileInput
  cases partitionedPrincipalInput P extra k a <;> rfl

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

theorem profileNoiseWithActive_active {D G Z α : Type*} {B : D → Type*}
    (h : D → ℕ) (P : D → Prop) [DecidablePred P]
    (z : PartitionedProfileNoiseIndex G Z α B h P → ℝ)
    (r : ActiveProfileCoefficientIndex G B h P → ℝ)
    (d : {d // ¬P d}) (e : SamplerCoefficientSlot G B h d.val) :
    profileNoiseWithActive h P z r (.inr ⟨d.val, e⟩) = r ⟨d, e⟩ := by
  simp only [profileNoiseWithActive, dif_neg d.property]

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

theorem partitionedIdealMap_withActive_eq {D G Z α : Type*} [Fintype α] [DecidableEq α]
    {B : D → Type*} [∀ d, Fintype (B d)] (h : D → ℕ)
    (P : D → Prop) [DecidablePred P] {O : {d // ¬P d} → Type*}
    (sets : ∀ d, O d → Finset α)
    (z : PartitionedProfileNoiseIndex G Z α B h P → ℝ)
    (r : ActiveProfileCoefficientIndex G B h P → ℝ) :
    partitionedIdealMap h P sets (profileNoiseWithActive h P z r) =
      partitionedIdealMap h P sets (profileNoiseWithActive (Z := Z) (α := α) h P (fun _ => 0) r) := by
  have hc : partitionedProfilePrincipal h P (unitProfilePrincipalSize (B := B))
      (profileNoiseWithActive h P z r) =
      partitionedProfilePrincipal h P (unitProfilePrincipalSize (B := B))
        (profileNoiseWithActive (Z := Z) (α := α) h P (fun _ => 0) r) := by
    funext d b
    simp only [partitionedProfilePrincipal, profileNoiseWithActive_active]
  have hb : partitionedProfileConstant h P (fun _ => 1 / 4) (profileNoiseWithActive h P z r) =
      partitionedProfileConstant h P (fun _ => 1 / 4) (profileNoiseWithActive (Z := Z) (α := α) h P (fun _ => 0) r) := by
    funext d
    simp only [partitionedProfileConstant, profileNoiseWithActive_active]
  unfold partitionedIdealMap
  rw [hc, hb]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RawAffinePolynomialJet
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem originalMonomialJetMap_measurable_comp {Ω C Z X K α O : Type*}
    [MeasurableSpace Ω] [Fintype C] [Fintype α] [DecidableEq α] [Fintype O]
    (e : C → K →₀ ℕ) (input : K → Option α → Z ⊕ X) (rows : O → Finset α)
    (c w : C → ℝ) (z : Ω → Z → ℝ) (hz : ∀ j, Measurable (fun a => z a j))
    (x : Ω → X → ℝ) (hx : ∀ j, Measurable (fun a => x a j))
    (r : Ω → C → ℝ) (hr : ∀ j, Measurable (fun a => r a j)) :
    Measurable (fun a => originalMonomialJetMap e input (z a) rows c w (x a) (r a)) := by
  have he (a : Ω) : originalMonomialJetMap e input (z a) rows c w (x a) (r a) =
      polynomialColumns (fun o j => normalizedJetColumn (e j) input (z a) (rows o))
        (x a) (fun j => c j + w j * r a j) := by
    rw [normalizedJetColumns_eq_realJetMatrix]
    funext o
    exact (realJetMatrix_monomialArray e (normalizedCubeTuple input (z a) (x a)) rows
      (fun j => c j + w j * r a j) o).symm
  simp_rw [he]
  exact normalizedJetColumns_measurable_comp e input rows z hz x hx _
    (fun j => measurable_const.add (measurable_const.mul (hr j)))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.CoefficientDensityAverage
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem retained_coefficient_density_average {W R X : Type*}
    [MeasurableSpace W] [MeasurableSpace R] [MeasurableSpace X]
    (μ : Measure W) (ρ : Measure R) (ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ρ] [SFinite ν]
    (D : R → X → ℝ) (hD : Measurable (Function.uncurry D))
    (hprob : ∀ r, (∀ x, 0 ≤ D r x) ∧ Integrable (D r) ν ∧ (∫ x, D r x ∂ν) = 1)
    (φ : W × X → ℝ) (hφ : Measurable φ) {C : ℝ} (hbound : ∀ p, ‖φ p‖ ≤ C) :
    (∫ p : (W × R) × X, D p.1.2 p.2*φ (p.1.1, p.2) ∂(μ.prod ρ).prod ν) =
      ∫ p : W × X, densityMixture ρ D p.2*φ p ∂μ.prod ν := by
  have hD' : Measurable (fun p : (W × R) × X => D p.1.2 p.2) :=
    hD.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  have hj := densityMixture_joint_integrable (μ.prod ρ) ν (fun wr => D wr.2) hD'
    (Filter.Eventually.of_forall (fun wr => hprob wr.2))
  have hi : Integrable (fun p : (W × R) × X => D p.1.2 p.2*φ (p.1.1, p.2)) ((μ.prod ρ).prod ν) :=
    hj.mul_bdd (hφ.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun p => hbound (p.1.1, p.2)))
  have havg := densityMixture_probability_density ρ ν D hD (Filter.Eventually.of_forall hprob)
  have hmavg : Measurable (densityMixture ρ D) := hD.stronglyMeasurable.integral_prod_left'.measurable
  have hiavg := densityMixture_joint_integrable μ ν (fun _ : W => densityMixture ρ D)
    (hmavg.comp measurable_snd) (Filter.Eventually.of_forall (fun _ => havg))
  have hr : Integrable (fun p : W × X => densityMixture ρ D p.2*φ p) (μ.prod ν) :=
    hiavg.mul_bdd hφ.aestronglyMeasurable (Filter.Eventually.of_forall hbound)
  rw [integral_prod _ hi, integral_prod _ hi.integral_prod_left, integral_prod _ hr]
  apply integral_congr_ae
  filter_upwards [] with w
  exact (densityMixture_test_integral ρ ν D
    (densityMixture_joint_integrable ρ ν D hD (Filter.Eventually.of_forall hprob))
    (fun x => φ (w, x)) (hφ.comp (measurable_const.prodMk measurable_id)) (fun x => hbound (w, x))).symm

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedKernelScaleWithCutoff
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators Matrix Classical

namespace VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable (j : Fin m) (i : I j)

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U basis S

variable {α O : Type*} [Fintype α] [DecidableEq α] [Fintype O] [DecidableEq O]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable (rows : O → Finset α) (s : O ↪ BoundedIntegerExponent G (j.val+1))
variable (hA : ((scalarKernelIntegerJet x (j.val+1) rows).submatrix id s).det ≠ 0)

local notation "fixedReal" => Sum.elim
  (fun ga : G × Option α => ((x (Prod.fst ga) (Prod.snd ga) : ℤ) : ℝ) / (S.value : ℝ))
  (principalTupleNormalized (principalAxisLength grid sides) u)

theorem allocatedPartitionedInput_frozen_bound (t) : |fixedReal t| ≤ 1 := by
  apply partitionedPrincipalInput_frozen_bound grid _ _ sides (allocatedPrincipalSides_pos B U basis S) u t
  intro ga
  have h := (norm_le_pi_norm (fun a => ((x ga.1 a : ℤ) : ℝ)/(S.value : ℝ)) ga.2).trans
    (integerScalarCubeBox_normalized_norm_le S.positive (x ga.1))
  simpa only [Real.norm_eq_abs] using h

end VectorPolynomial
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedPartitionedProfileJet
namespace OAI

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

theorem allocatedAxisProfilePolynomial_eq (R σ : Fin m → ℝ) (a : LayerSamplerAxis I n)
    (r : SamplerCoefficientSlot G B (layerSamplerDegree I n) a → ℝ) :
    allocatedAxisProfilePolynomial B R σ a r =
      monomialArrayPolynomial Subtype.val (fun e =>
        coefficientProfileCenter (principalCoefficientSlots (layerSamplerDegree I n) a)
          (principalProfileSize (R a.1) (Fintype.card (B a))) e +
        coefficientProfileWidth (principalCoefficientSlots (layerSamplerDegree I n) a)
          (constantCoefficientSlot _ _) (R a.1 / 4)
          (principalProfileSize (R a.1) (Fintype.card (B a)))
          (tailProfileSize (R a.1) (σ a.1)
            (Fintype.card (SamplerCoefficientSlot G B (layerSamplerDegree I n) a))) e * r e) := by
  rcases a with ⟨j, i⟩
  cases i with
  | inl i =>
    simp only [allocatedAxisProfilePolynomial, allocatedContinuousProfileCenters,
      allocatedContinuousProfileWidths, layerContinuousPrincipalSlots_card]
    rfl
  | inr i =>
    simp only [allocatedAxisProfilePolynomial, allocatedIntegerProfileCenters,
      allocatedIntegerProfileWidths, layerIntegerPrincipalSlots_card]
    rfl

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedDensityParameterBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α O : Type*} [Fintype α] [DecidableEq α] [Fintype O] [DecidableEq O]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable (rows : O → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "sides" => allocatedPrincipalSides B U basis S
local notation "input" => partitionedPrincipalInput grid (fun g a => (g, a))
local notation "fixedReal" => Sum.elim
  (fun ga : G × Option α => ((x (Prod.fst ga) (Prod.snd ga) : ℤ) : ℝ) / (S.value : ℝ))
  (principalTupleNormalized (principalAxisLength grid sides) u)

omit [DecidableEq O] in
theorem allocatedNormalizedProfileJet_measurable (a : LayerSamplerAxis I n) :
    Measurable (fun p :
      (PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n) (α := α) (fun a => ¬grid a) → ℝ) ×
        (SamplerCoefficientSlot G B (layerSamplerDegree I n) a → ℝ) =>
      allocatedNormalizedProfileJet B U basis S x u rows a p.1 p.2) := by
  rcases a with ⟨j, a⟩
  cases a with
  | inl i =>
    exact originalMonomialJetMap_measurable_comp Subtype.val input rows
      (allocatedContinuousProfileCenters (G := G) B R j i)
      (allocatedContinuousProfileWidths (G := G) B R σ j i)
      (fun _ => fixedReal) (fun _ => measurable_const) Prod.fst
      (fun k => (measurable_pi_apply k).comp measurable_fst) Prod.snd
      (fun k => (measurable_pi_apply k).comp measurable_snd)
  | inr i =>
    exact originalMonomialJetMap_measurable_comp Subtype.val input rows
      (allocatedIntegerProfileCenters (G := G) B R j i)
      (allocatedIntegerProfileWidths (G := G) B R σ j i)
      (fun _ => fixedReal) (fun _ => measurable_const) Prod.fst
      (fun k => (measurable_pi_apply k).comp measurable_fst) Prod.snd
      (fun k => (measurable_pi_apply k).comp measurable_snd)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0)

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "activeInput" => PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n) (α := α) (fun a => ¬grid a)
local notation "activeCoefficient" => ActiveProfileCoefficientIndex G B (layerSamplerDegree I n) grid

omit [∀ j, DecidableEq (O j)] in
theorem allocatedNormalizedLongJetMap_measurable :
    Measurable (fun p : (activeInput → ℝ) × (activeCoefficient → ℝ) =>
      allocatedNormalizedLongJetMap B U basis S x u rows p.1 p.2) := by
  unfold allocatedNormalizedLongJetMap sigmaAxisSampler
  apply measurable_pi_iff.mpr
  intro o
  have hc : Measurable (fun p : (activeInput → ℝ) × (activeCoefficient → ℝ) =>
      (p.1, fun e : SamplerCoefficientSlot G B (layerSamplerDegree I n) o.1.val => p.2 ⟨o.1, e⟩)) :=
    measurable_fst.prodMk (measurable_pi_iff.mpr (fun e =>
      (measurable_pi_apply (⟨o.1, e⟩ : activeCoefficient)).comp measurable_snd))
  exact (measurable_pi_apply o.2).comp
    ((allocatedNormalizedProfileJet_measurable B U basis S x u (rows o.1.val.1) o.1.val).comp
      (f := fun p : (activeInput → ℝ) × (activeCoefficient → ℝ) =>
        (p.1, fun e => p.2 ⟨o.1, e⟩)) hc)

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

variable {D G : Type*} [Fintype D] [Fintype G]
  {B : D → Type*} [∀ d, Fintype (B d)] (h : D → ℕ) (P : D → Prop)

theorem activeTailRescale_principal (τ : D → ℝ)
    (r : ActiveProfileCoefficientIndex G B h P → ℝ) (d : {d // ¬P d}) (b : B d.val) :
    activeTailRescale h P τ r ⟨d, principalCoefficientSlot h d.val b⟩ =
      r ⟨d, principalCoefficientSlot h d.val b⟩ := by
  unfold activeTailRescale
  rw [nonprincipalDilation_principal Subtype.val (canonicalPrincipalExponent h d.val)
    (τ d.val) _ b rfl, one_mul]

theorem activeTailRescale_constant (τ : D → ℝ)
    (r : ActiveProfileCoefficientIndex G B h P → ℝ) (d : {d // ¬P d}) :
    activeTailRescale h P τ r ⟨d, constantCoefficientSlot _ _⟩ =
      r ⟨d, constantCoefficientSlot _ _⟩ := by
  unfold activeTailRescale
  rw [nonprincipalDilation_zero Subtype.val (canonicalPrincipalExponent h d.val)
    (τ d.val) _ rfl, one_mul]

theorem activeTailRescale_abs_le (τ : D → ℝ) (hτ : ∀ d, |τ d| ≤ 1)
    (r : ActiveProfileCoefficientIndex G B h P → ℝ) (hr : ∀ j, |r j| ≤ 1)
    (j : ActiveProfileCoefficientIndex G B h P) : |activeTailRescale h P τ r j| ≤ 1 := by
  have hd : |nonprincipalDilation Subtype.val (canonicalPrincipalExponent h j.1.val)
      (τ j.1.val) j.2| ≤ 1 := by
    unfold nonprincipalDilation
    split_ifs
    · exact hτ _
    · norm_num
  unfold activeTailRescale
  rw [abs_mul]
  exact (mul_le_mul hd (hr j) (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)

theorem activeTailRescale_measurable_comp {Ω : Type*} [MeasurableSpace Ω]
    (τ : D → ℝ) (r : Ω → ActiveProfileCoefficientIndex G B h P → ℝ)
    (hr : ∀ j, Measurable (fun a => r a j)) (j : ActiveProfileCoefficientIndex G B h P) :
    Measurable (fun a => activeTailRescale h P τ (r a) j) :=
  measurable_const.mul (hr j)

theorem partitionedIdealMap_activeTailRescale {Z α : Type*}
    [Fintype α] [DecidableEq α] [DecidablePred P]
    {O : {d // ¬P d} → Type*} (sets : ∀ d, O d → Finset α)
    (τ : D → ℝ) (z : PartitionedProfileNoiseIndex G Z α B h P → ℝ)
    (r : ActiveProfileCoefficientIndex G B h P → ℝ) :
    partitionedIdealMap h P sets (profileNoiseWithActive h P z (activeTailRescale h P τ r)) =
      partitionedIdealMap h P sets (profileNoiseWithActive h P z r) := by
  have hc : partitionedProfilePrincipal h P (unitProfilePrincipalSize (B := B))
      (profileNoiseWithActive h P z (activeTailRescale h P τ r)) =
      partitionedProfilePrincipal h P (unitProfilePrincipalSize (B := B)) (profileNoiseWithActive h P z r) := by
    funext d b
    simp only [partitionedProfilePrincipal, profileNoiseWithActive_active, activeTailRescale_principal]
  have hb : partitionedProfileConstant h P (fun _ => 1 / 4)
      (profileNoiseWithActive h P z (activeTailRescale h P τ r)) =
      partitionedProfileConstant h P (fun _ => 1 / 4) (profileNoiseWithActive h P z r) := by
    funext d
    simp only [partitionedProfileConstant, profileNoiseWithActive_active, activeTailRescale_constant]
  unfold partitionedIdealMap
  rw [hc, hb]

theorem boundedProfileWidth_noise_rescale (d : D) (ρ γ ε σ t v : ℝ) (ht : t ≠ 0)
    (e : SamplerCoefficientSlot G B h d) :
    coefficientProfileWidth (principalCoefficientSlots h d) (constantCoefficientSlot _ _)
        ρ γ (t * ε) e * (nonprincipalDilation Subtype.val (canonicalPrincipalExponent h d) (σ / t) e * v) =
      coefficientProfileWidth (principalCoefficientSlots h d) (constantCoefficientSlot _ _)
        ρ γ (σ * ε) e * v := by
  classical
  by_cases hz : e = constantCoefficientSlot _ _
  · rw [nonprincipalDilation_zero Subtype.val (canonicalPrincipalExponent h d)
      (σ / t) e (congrArg Subtype.val hz)]
    simp only [coefficientProfileWidth, hz, ite_true, one_mul]
  · by_cases hp : e ∈ principalCoefficientSlots h d
    · obtain ⟨b, hb⟩ := (mem_principalCoefficientSlots h d e).mp hp
      rw [nonprincipalDilation_principal Subtype.val (canonicalPrincipalExponent h d)
        (σ / t) e b (congrArg Subtype.val hb.symm)]
      simp only [coefficientProfileWidth, hz, hp, ite_false, ite_true, one_mul]
    · rw [nonprincipalDilation_mem Subtype.val (canonicalPrincipalExponent h d) (σ / t) e
        ((bounded_mem_nonprincipalCoefficientSlots h d e).mpr ⟨hz, hp⟩)]
      simp only [coefficientProfileWidth, hz, hp, ite_false]
      field_simp [ht]

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

theorem partitionedSlicedRegularizedIdeal_activeTailRescale (ρ : ℝ≥0)
    (center width : PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d) → ℝ)
    (τ : D → ℝ) (z : PartitionedProfileNoiseIndex G Z α B h P → ℝ)
    (r : ActiveProfileCoefficientIndex G B h P → ℝ) :
    partitionedSlicedRegularizedIdeal h P sets ρ center width
        (profileNoiseWithActive h P z (activeTailRescale h P τ r)) =
      activeSlicedProfileIdeal Z h P sets ρ center width r := by
  let _ : Fintype Z := inferInstance
  unfold activeSlicedProfileIdeal partitionedSlicedRegularizedIdeal
  rw [partitionedIdealMap_activeTailRescale, partitionedIdealMap_withActive_eq]

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "sides" => allocatedPrincipalSides B U basis S
local notation "degree" => layerSamplerDegree I n
local notation "extra" => (fun g a => (g, a) : G → Option α → G × Option α)
local notation "fixedReal" => Sum.elim
  (fun ga : G × Option α => ((x (Prod.fst ga) (Prod.snd ga) : ℤ) : ℝ) / (S.value : ℝ))
  (principalTupleNormalized (principalAxisLength grid sides) u)
local notation "activeInput" => PrincipalAxisParameter (B := B) (h := degree) (α := α) (fun a => ¬grid a)
local notation "activeCoefficient" => ActiveProfileCoefficientIndex G B degree grid

theorem allocatedProfileFrozenNoise_abs_le
    (j : PartitionedProfileNoiseIndex G (G × Option α) α B degree grid) :
    |allocatedProfileFrozenNoise B U basis S x u j| ≤ 1 := by
  cases j with
  | inl j => exact allocatedPartitionedInput_frozen_bound B U basis S x u j
  | inr j => simp only [allocatedProfileFrozenNoise, Sum.elim_inr, abs_zero, zero_le_one]

variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)

omit [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
theorem allocatedTailProfileJet_eq {t : ℝ} (ht : t ≠ 0)
    (r : activeCoefficient → ℝ) (y : activeInput → ℝ) :
    partitionedAllocatedProfileJet degree grid extra (fun a : {a // ¬grid a} => rows a.val.1)
        (fun a => R a.1) t
        (profileNoiseWithActive degree grid (allocatedProfileFrozenNoise B U basis S x u)
          (activeTailRescale degree grid (fun a => σ a.1 / t) r)) y =
      allocatedNormalizedLongJetMap B U basis S x u rows y r := by
  let z := profileNoiseWithActive degree grid (allocatedProfileFrozenNoise B U basis S x u)
    (activeTailRescale degree grid (fun a => σ a.1 / t) r)
  have hcube (v : Finset α) :
      normalizedCubeTuple (partitionedProfileInput grid extra) z y v =
        normalizedCubeTuple (partitionedPrincipalInput grid extra) fixedReal y v := by
    funext k
    rw [partitionedProfileInput_source]
    rfl
  have htail (j : Fin m) (N : ℕ) : tailProfileSize (R j) (σ j) N =
      σ j * tailProfileSize (R j) 1 N := by
    unfold tailProfileSize
    ring
  have hpoly (a : {a // ¬grid a}) :
      monomialArrayPolynomial Subtype.val (fun e : SamplerCoefficientSlot G B degree a.val =>
        coefficientProfileCenter (principalCoefficientSlots degree a.val)
            (principalProfileSize (R a.val.1) (Fintype.card (B a.val))) e +
          coefficientProfileWidth (principalCoefficientSlots degree a.val) (constantCoefficientSlot _ _)
            (R a.val.1 / 4) (principalProfileSize (R a.val.1) (Fintype.card (B a.val)))
            (t * tailProfileSize (R a.val.1) 1 (Fintype.card (SamplerCoefficientSlot G B degree a.val))) e *
              z (.inr ⟨a.val, e⟩)) =
        allocatedAxisProfilePolynomial B R σ a.val (fun e => r ⟨a, e⟩) := by
    rw [allocatedAxisProfilePolynomial_eq]
    apply congrArg (monomialArrayPolynomial Subtype.val)
    funext e
    dsimp only [z]
    rw [profileNoiseWithActive_active, htail]
    unfold activeTailRescale
    congr 1
    exact boundedProfileWidth_noise_rescale degree a.val (R a.val.1 / 4)
      (principalProfileSize (R a.val.1) (Fintype.card (B a.val)))
      (tailProfileSize (R a.val.1) 1 (Fintype.card (SamplerCoefficientSlot G B degree a.val)))
      (σ a.val.1) t (r ⟨a, e⟩) ht e
  change partitionedAllocatedProfileJet degree grid extra (fun a : {a // ¬grid a} => rows a.val.1)
    (fun a => R a.1) t z y = _
  funext o
  unfold partitionedAllocatedProfileJet partitionedProfileJet
  simp_rw [hcube, hpoly]
  rfl

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ActiveTailSlicedProfileComparison
namespace OAI

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators ContDiff NNReal Classical

theorem exists_active_tail_sliced_profile_comparison_with_scales
    {W D G Z α : Type*} [MeasurableSpace W]
    [Fintype D] [Fintype G] [Fintype Z] [Fintype α] [DecidableEq α]
    {B : D → Type*} [∀ d, Fintype (B d)]
    (h : D → ℕ) (hh : ∀ d, 0 < h d) (P : D → Prop) [DecidablePred P]
    (extra : G → Option α → Z)
    {O : {d // ¬P d} → Type*} [∀ d, Fintype (O d)] [∀ d, Nonempty (O d)]
    (sets : ∀ d, O d → Finset α) (hsets : ∀ d, Function.Injective (sets d))
    (hcard : ∀ d o, (sets d o).card ≤ h d.val)
    (block : ∀ d, O d → B d.val) (hblock : ∀ d, Function.Injective (block d))
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    {degree : ℕ} (hdegree : ∀ d, h d ≤ degree)
    {δ E : ℝ} (hδ : 0 < δ) (hδone : δ ≤ 1) (hE : 0 < E) :
    ∃ ρ : ℝ≥0, 0 < ρ ∧ ρ ≤ 1 ∧
    (ρ : ℝ) = partitionedAffineSourceRadius (B := B) (O := O) (α := α) h P A T δ E ∧
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
    t = partitionedAffineSourceTolerance (G := G) (Z := Z) (B := B) (O := O) (α := α)
      h P A T degree δ E ∧
    ∀ τ : D → ℝ, (∀ d, |τ d| ≤ 1) →
    ∀ z : W → PartitionedProfileNoiseIndex G Z α B h P → ℝ,
    (∀ j, Measurable (fun a => z a j)) →
    ∀ (center width : PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d) → ℝ),
    (∀ i, δ ≤ |width i|) → (∀ i, |center i| + |width i| ≤ 1) →
    ∀ μ : Measure W, IsProbabilityMeasure μ → (∀ᵐ a ∂μ, ∀ j, |z a j| ≤ 1) →
    ∀ (R : D → ℝ) (f : W × ((Σ d, O d) → ℝ) → ℝ),
    Measurable f → (∀ p, ‖f p‖ ≤ 1) →
    |(∫ p, activeAveragedSlicedProfileIdeal (G := G) (B := B) Z h P sets ρ center width p.2 *
        f (p.1, fun o => R o.1.val * p.2 o) ∂μ.prod volume) -
      ∫ p, f (p.1.1, partitionedAllocatedProfileJet h P extra sets R t
          (profileNoiseWithActive h P (z p.1.1) (activeTailRescale h P τ p.1.2))
          (fun i => center i + width i * p.2 i))
        ∂(μ.prod (unitCoefficientSource (ActiveProfileCoefficientIndex G B h P))).prod
          (jointBooleanSource (B := fun d : {d // ¬P d} => B d.val) (α := α) (fun d => h d.val))| ≤ E := by
  classical
  obtain ⟨ρ, hρ, hρone, hρeq, t, ht, htone, hteq, hs⟩ := exists_partitioned_sliced_density_comparison_with_scales_s2
    (Ω := W × (ActiveProfileCoefficientIndex G B h P → ℝ))
    h hh P extra sets hsets hcard block hblock ψ hψ hrange hzero hone A T hLip hTransition
    hdegree hδ hδone hE
  refine ⟨ρ, hρ, hρone, hρeq, t, ht, htone, hteq, ?_⟩
  intro τ hτ z hz center width hwidth hcenter μ hμ hbox R f hf hbound
  let : IsProbabilityMeasure μ := hμ
  let ζ := fun p : W × (ActiveProfileCoefficientIndex G B h P → ℝ) =>
    profileNoiseWithActive h P (z p.1) (activeTailRescale h P τ p.2)
  have hζ (j : PartitionedProfileNoiseIndex G Z α B h P) : Measurable (fun p => ζ p j) :=
    profileNoiseWithActive_measurable h P
      (fun p : W × (ActiveProfileCoefficientIndex G B h P → ℝ) => z p.1)
      (fun p => activeTailRescale h P τ p.2)
      (fun i => (hz i).comp measurable_fst)
      (activeTailRescale_measurable_comp h P τ Prod.snd
        (fun i => (measurable_pi_apply i).comp measurable_snd)) j
  have hgood : ∀ᵐ p ∂μ.prod (unitCoefficientSource (ActiveProfileCoefficientIndex G B h P)),
      (∀ j, |ζ p j| ≤ 1) ∧ (∀ i, δ ≤ |width i|) ∧ (∀ i, |center i| + |width i| ≤ 1) := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hbox,
      Measure.quasiMeasurePreserving_snd.ae
        (unitCoefficientSource_abs_le (ActiveProfileCoefficientIndex G B h P))] with p hp hr
    exact ⟨profileNoiseWithActive_abs_le h P (z p.1) (activeTailRescale h P τ p.2) hp
      (activeTailRescale_abs_le h P τ hτ p.2 hr), hwidth, hcenter⟩
  let f' := fun p : (W × (ActiveProfileCoefficientIndex G B h P → ℝ)) ×
      ((Σ d, O d) → ℝ) => f (p.1.1, p.2)
  have hf' : Measurable f' := hf.comp (measurable_fst.fst.prodMk measurable_snd)
  have he := hs ζ hζ (fun _ => center) (fun _ => width)
    (fun _ => measurable_const) (fun _ => measurable_const)
    (μ.prod (unitCoefficientSource (ActiveProfileCoefficientIndex G B h P))) inferInstance hgood
    R f' hf' (fun p => hbound (p.1.1, p.2))
  dsimp only at he
  simp only [ζ, partitionedSlicedRegularizedIdeal_activeTailRescale] at he
  let Φ := fun p : W × ((Σ d, O d) → ℝ) => f (p.1, fun o => R o.1.val * p.2 o)
  have hΦ : Measurable Φ := hf.comp (measurable_fst.prodMk (measurable_pi_iff.mpr
    (fun o => measurable_const.mul ((measurable_pi_apply o).comp measurable_snd))))
  have havg := retained_coefficient_density_average μ
    (unitCoefficientSource (ActiveProfileCoefficientIndex G B h P)) volume
    (activeSlicedProfileIdeal Z h P sets ρ center width)
    (activeSlicedProfileIdeal_measurable Z h P sets ρ center width)
    (fun r => partitionedSlicedRegularizedIdeal_probability h P sets ρ hρ center width
      (profileNoiseWithActive (Z := Z) h P (fun _ => 0) r)) Φ hΦ
    (fun p => hbound (p.1, fun o => R o.1.val * p.2 o))
  change |(∫ p : (W × (ActiveProfileCoefficientIndex G B h P → ℝ)) × ((Σ d, O d) → ℝ),
      activeSlicedProfileIdeal Z h P sets ρ center width p.1.2 p.2 * Φ (p.1.1, p.2)
      ∂(μ.prod (unitCoefficientSource (ActiveProfileCoefficientIndex G B h P))).prod volume) - _| ≤ E at he
  rw [havg] at he
  exact he

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedAffineRadiusLog
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped ContDiff NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Nonempty (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (hrows : ∀ j, Function.Injective (rows j)) (hcard : ∀ j o, (rows j o).card ≤ j.val + 1)

include hrows hcard in
theorem exists_early_allocated_affine_tail_test_comparison_with_scales_s2_oai
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    (block : ∀ a : LayerSamplerAxis I n, O a.1 → B a)
    (hblock : ∀ a, Function.Injective (block a))
    {δ ε : ℝ} (hδ : 0 < δ) (hδone : δ ≤ 1) (hε : 0 < ε) :
    ∃ ρmin : ℝ≥0, 0 < ρmin ∧ ∃ ρ : (LayerSamplerAxis I n → Prop) → ℝ≥0,
      (∀ P, ρmin ≤ ρ P ∧ ρ P ≤ 1) ∧
      (∀ P, (ρ P : ℝ) = partitionedAffineSourceRadius (B := B)
        (O := fun a : {a // ¬P a} => O a.val.1) (α := α) (layerSamplerDegree I n) P A T δ ε) ∧
      ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
      t = allocatedAffineSourceTolerance (G := G) (O := O) (α := α) B A T δ ε ∧
      ∀ {J : Fin m → Type*} [∀ j, Fintype (J j)]
        (U : ∀ j, Submodule ℝ (J j → ℝ))
        (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
        {R σ : Fin m → ℝ} (_hσ : ∀ j, 0 < σ j)
        (S : LayerSamplerScale (G := G) B U basis R σ),
      (∀ j, σ j ≤ t) →
      ∀ (x : G → IntegerScalarCubeBox α S.value)
        (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value) (allocatedPrincipalSides B U basis S))
        (center width : (PrincipalAxisParameter (B := B) (h := (layerSamplerDegree I n)) (α := α) (fun a => ¬(allocatedGridAxis (I := I) U basis S.value) a)) → ℝ),
      (∀ i, δ ≤ |width i|) → (∀ i, |center i| + |width i| ≤ 1) →
      ∀ f : ((Σ a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a}, O (Sigma.fst (Subtype.val a))) → ℝ) → ℝ, Measurable f → (∀ v, ‖f v‖ ≤ 1) →
      |(∫ v, activeAveragedSlicedProfileIdeal (G := G) (B := B) (G × Option α)
          (layerSamplerDegree I n) (allocatedGridAxis (I := I) U basis S.value) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => rows (Sigma.fst (Subtype.val a))) (ρ (allocatedGridAxis (I := I) U basis S.value)) center width v * f (fun o => R o.1.val.1 * v o)) -
        ∫ p, f (allocatedNormalizedLongJetMap B U basis S x u rows
          (fun i => center i + width i * p.2 i) p.1)
          ∂(unitCoefficientSource (ActiveProfileCoefficientIndex G B (layerSamplerDegree I n) (allocatedGridAxis (I := I) U basis S.value))).prod
            (jointBooleanSource (B := fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (α := α) (fun a => (layerSamplerDegree I n) a.val))| ≤ ε := by
  have hh (a : LayerSamplerAxis I n) : 0 < (layerSamplerDegree I n) a := Nat.zero_lt_succ _
  have hdeg (a : LayerSamplerAxis I n) : (layerSamplerDegree I n) a ≤ m := Nat.succ_le_of_lt a.1.isLt
  have hall (P : LayerSamplerAxis I n → Prop) := exists_active_tail_sliced_profile_comparison_with_scales
    (W := Unit) (G := G) (Z := G × Option α) (layerSamplerDegree I n) hh P (fun g a => (g, a))
    (fun a : {a // ¬P a} => rows a.val.1) (fun a => hrows a.val.1)
    (fun a => hcard a.val.1) (fun a => block a.val) (fun a => hblock a.val)
    ψ hψ hrange hzero hone A T hLip hTransition hdeg hδ hδone hε
  choose ρ hρ hρone hρeq tp htp htpone htpeq hcomp using hall
  let t := Finset.univ.inf' Finset.univ_nonempty tp
  have ht : 0 < t := (Finset.lt_inf'_iff _).mpr (fun P _ => htp P)
  have htP (P) : t ≤ tp P := Finset.inf'_le _ (Finset.mem_univ P)
  let ρmin := Finset.univ.inf' Finset.univ_nonempty ρ
  have hρmin : 0 < ρmin := (Finset.lt_inf'_iff _).mpr (fun P _ => hρ P)
  refine ⟨ρmin, hρmin, ρ, (fun P => ⟨Finset.inf'_le _ (Finset.mem_univ P), hρone P⟩),
    hρeq, t, ht, (htP (fun _ => False)).trans (htpone _), ?_, ?_⟩
  · change Finset.univ.inf' Finset.univ_nonempty tp = _
    simp only [htpeq]
    rfl
  intro J _ U basis R σ hσ S hsmall x u center width hwidth hcenter f hf hfb
  let τ : LayerSamplerAxis I n → ℝ := fun a => σ a.1 / tp (allocatedGridAxis (I := I) U basis S.value)
  have hτ (a : LayerSamplerAxis I n) : |τ a| ≤ 1 := by
    dsimp only [τ]
    rw [abs_div, abs_of_pos (hσ a.1), abs_of_pos (htp (allocatedGridAxis (I := I) U basis S.value))]
    exact (div_le_one (htp (allocatedGridAxis (I := I) U basis S.value))).mpr ((hsmall a.1).trans (htP (allocatedGridAxis (I := I) U basis S.value)))
  let z := fun _ : Unit => allocatedProfileFrozenNoise B U basis S x u
  have hbox : ∀ᵐ a ∂Measure.dirac (), ∀ j, |z a j| ≤ 1 :=
    Filter.Eventually.of_forall (fun _ => allocatedProfileFrozenNoise_abs_le B U basis S x u)
  have herr := hcomp (allocatedGridAxis (I := I) U basis S.value) τ hτ z (fun _ => measurable_const) center width hwidth hcenter
    (Measure.dirac ()) inferInstance hbox (fun a => R a.1)
    (fun p => f p.2) (hf.comp measurable_snd) (fun p => hfb p.2)
  have heq (p : (Unit × ((ActiveProfileCoefficientIndex G B (layerSamplerDegree I n) (allocatedGridAxis (I := I) U basis S.value)) → ℝ)) × ((PrincipalAxisParameter (B := B) (h := (layerSamplerDegree I n)) (α := α) (fun a => ¬(allocatedGridAxis (I := I) U basis S.value) a)) → ℝ)) :
      partitionedAllocatedProfileJet (layerSamplerDegree I n) (allocatedGridAxis (I := I) U basis S.value) (fun g a => (g, a)) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => rows (Sigma.fst (Subtype.val a))) (fun a => R a.1) (tp (allocatedGridAxis (I := I) U basis S.value))
        (profileNoiseWithActive (layerSamplerDegree I n) (allocatedGridAxis (I := I) U basis S.value) (z p.1.1) (activeTailRescale (layerSamplerDegree I n) (allocatedGridAxis (I := I) U basis S.value) τ p.1.2))
        (fun i => center i + width i * p.2 i) =
      allocatedNormalizedLongJetMap B U basis S x u rows
        (fun i => center i + width i * p.2 i) p.1.2 :=
    allocatedTailProfileJet_eq B U basis S x u rows (htp (allocatedGridAxis (I := I) U basis S.value)).ne' p.1.2 _
  simp only [heq] at herr
  have hD : Measurable (activeAveragedSlicedProfileIdeal (G := G) (B := B) (G × Option α)
      (layerSamplerDegree I n) (allocatedGridAxis (I := I) U basis S.value) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => rows (Sigma.fst (Subtype.val a))) (ρ (allocatedGridAxis (I := I) U basis S.value)) center width) :=
    (activeAveragedSlicedProfileIdeal_spec (G × Option α) (layerSamplerDegree I n) (allocatedGridAxis (I := I) U basis S.value) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => rows (Sigma.fst (Subtype.val a))) (ρ (allocatedGridAxis (I := I) U basis S.value)) (hρ (allocatedGridAxis (I := I) U basis S.value)) center width).2.1.continuous.measurable
  have hscale : Measurable (fun v : (Σ a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a}, O (Sigma.fst (Subtype.val a))) → ℝ => fun o => R o.1.val.1 * v o) :=
    measurable_pi_iff.mpr (fun o => measurable_const.mul (measurable_pi_apply o))
  have hfirst := integral_dirac_first volume ()
    (fun p : Unit × ((Σ a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a}, O (Sigma.fst (Subtype.val a))) → ℝ) =>
      activeAveragedSlicedProfileIdeal (G := G) (B := B) (G × Option α) (layerSamplerDegree I n) (allocatedGridAxis (I := I) U basis S.value) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => rows (Sigma.fst (Subtype.val a))) (ρ (allocatedGridAxis (I := I) U basis S.value)) center width p.2 *
        f (fun o => R o.1.val.1 * p.2 o))
    ((hD.comp measurable_snd).mul (hf.comp (hscale.comp measurable_snd)))
  have hin : Measurable (fun p : (Unit × ((ActiveProfileCoefficientIndex G B (layerSamplerDegree I n) (allocatedGridAxis (I := I) U basis S.value)) → ℝ)) × ((PrincipalAxisParameter (B := B) (h := (layerSamplerDegree I n)) (α := α) (fun a => ¬(allocatedGridAxis (I := I) U basis S.value) a)) → ℝ) =>
      ((fun i => center i + width i * p.2 i), p.1.2)) := by
    apply Measurable.prodMk
    · apply measurable_pi_iff.mpr
      intro i
      exact measurable_const.add (measurable_const.mul ((measurable_pi_apply i).comp measurable_snd))
    · exact measurable_snd.comp measurable_fst
  have hmap : Measurable (fun p : (Unit × ((ActiveProfileCoefficientIndex G B (layerSamplerDegree I n) (allocatedGridAxis (I := I) U basis S.value)) → ℝ)) × ((PrincipalAxisParameter (B := B) (h := (layerSamplerDegree I n)) (α := α) (fun a => ¬(allocatedGridAxis (I := I) U basis S.value) a)) → ℝ) =>
      allocatedNormalizedLongJetMap B U basis S x u rows
        (fun i => center i + width i * p.2 i) p.1.2) :=
    (allocatedNormalizedLongJetMap_measurable B U basis S x u rows).comp
      (f := fun p : (Unit × ((ActiveProfileCoefficientIndex G B (layerSamplerDegree I n) (allocatedGridAxis (I := I) U basis S.value)) → ℝ)) × ((PrincipalAxisParameter (B := B) (h := (layerSamplerDegree I n)) (α := α) (fun a => ¬(allocatedGridAxis (I := I) U basis S.value) a)) → ℝ) =>
        ((fun i => center i + width i * p.2 i), p.1.2)) hin
  have hsecond := integral_dirac_first_nested (unitCoefficientSource (ActiveProfileCoefficientIndex G B (layerSamplerDegree I n) (allocatedGridAxis (I := I) U basis S.value)))
    (jointBooleanSource (B := fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (α := α) (fun a => (layerSamplerDegree I n) a.val)) ()
    (fun p : (Unit × ((ActiveProfileCoefficientIndex G B (layerSamplerDegree I n) (allocatedGridAxis (I := I) U basis S.value)) → ℝ)) × ((PrincipalAxisParameter (B := B) (h := (layerSamplerDegree I n)) (α := α) (fun a => ¬(allocatedGridAxis (I := I) U basis S.value) a)) → ℝ) =>
      f (allocatedNormalizedLongJetMap B U basis S x u rows
        (fun i => center i + width i * p.2 i) p.1.2)) (hf.comp hmap)
  rw [hfirst, hsecond] at herr
  exact herr

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4, u_5, u_6} : type_of% @OAI.Erdos3.VectorPolynomial.exists_early_allocated_affine_tail_test_comparison_with_scales_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6} := @OAI.Erdos3.VectorPolynomial.exists_early_allocated_affine_tail_test_comparison_with_scales_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6}
