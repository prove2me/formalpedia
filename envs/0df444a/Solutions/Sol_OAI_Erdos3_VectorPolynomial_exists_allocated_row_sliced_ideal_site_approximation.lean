-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.exists_allocated_row_sliced_ideal_site_approximation
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T23:29:24.98636+00:00
-- url     : https://prove2.me/submissions/28104f98-eaec-4682-b1c3-daa2170a6e6f

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B144

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BufferedSiteExpansion
namespace OAI

section

namespace Erdos3

open scoped NNReal

end Erdos3

end

section

open scoped NNReal BigOperators

namespace Erdos3

end Erdos3

end

section

namespace Erdos3
open scoped NNReal

end Erdos3

end

section

namespace Erdos3
open scoped Classical BigOperators NNReal

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators NNReal

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

variable {S T U D : Type*} [Fintype S] [Fintype T]

theorem bufferedSiteExpansion_identity (y : S → U → D → ℝ) (χ : S → U → ℂ)
    (c : T → ℂ) (f : T → S → (D → ℝ) → ℂ) (u : S → U) :
    (∑ k, c k*∏ s, bufferedSiteFactor y χ f k s (u s)) =
      (∏ s, χ s (u s))*(∑ k, c k*∏ s, f k s (y s (u s))) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  simp only [bufferedSiteFactor, Finset.prod_mul_distrib]
  ring

omit [Fintype S] [Fintype T] in
theorem bufferedSiteFactor_bound (y : S → U → D → ℝ) (χ : S → U → ℂ)
    (f : T → S → (D → ℝ) → ℂ) (hχ : ∀ s u, ‖χ s u‖ ≤ 1)
    (hf : ∀ k s x, ‖f k s x‖ ≤ 1) (k : T) (s : S) (u : U) :
    ‖bufferedSiteFactor y χ f k s u‖ ≤ 1 := by
  unfold bufferedSiteFactor
  rw [norm_mul]
  exact (mul_le_mul (hχ s u) (hf k s _) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)

omit [Fintype S] [Fintype T] in
theorem bufferedSiteFactor_lipschitz [Fintype D] [PseudoMetricSpace U]
    (y : S → U → D → ℝ) (χ : S → U → ℂ) (f : T → S → (D → ℝ) → ℂ)
    {K L C : ℝ≥0} (hy : ∀ s, LipschitzWith L (y s)) (hχ : ∀ s, LipschitzWith C (χ s))
    (hf : ∀ k s, LipschitzWith K (f k s))
    (hχ1 : ∀ s u, ‖χ s u‖ ≤ 1) (hf1 : ∀ k s x, ‖f k s x‖ ≤ 1) (k : T) (s : S) :
    LipschitzWith (K*L+C) (bufferedSiteFactor y χ f k s) := by
  unfold bufferedSiteFactor
  simpa only [one_mul, Function.comp_def] using
    lipschitz_mul_of_bounds (χ s) (f k s ∘ y s) (hχ s) ((hf k s).comp (hy s))
      (Bf := 1) (Bg := 1) (hχ1 s) (fun u => hf1 k s (y s u))

theorem bufferedSiteExpansion_error (y : S → U → D → ℝ) (χ : S → U → ℂ)
    (F : (S → D → ℝ) → ℂ) (c : T → ℂ) (f : T → S → (D → ℝ) → ℂ)
    {R ε : ℝ} (hε : 0 ≤ ε) (hχ : ∀ s u, ‖χ s u‖ ≤ 1)
    (hsupport : ∀ s u, χ s u ≠ 0 → ∀ d, |y s u d| ≤ R)
    (herr : ∀ x : S → D → ℝ, (∀ s d, |x s d| ≤ R) →
      ‖F x-∑ k, c k*∏ s, f k s (x s)‖ ≤ ε) (u : S → U) :
    ‖(∏ s, χ s (u s))*F (fun s => y s (u s))-
      ∑ k, c k*∏ s, bufferedSiteFactor y χ f k s (u s)‖ ≤ ε := by
  classical
  rw [bufferedSiteExpansion_identity, ← mul_sub, norm_mul]
  by_cases hz : ∃ s, χ s (u s) = 0
  · obtain ⟨s, hs⟩ := hz
    rw [Finset.prod_eq_zero (Finset.mem_univ s) hs, norm_zero, zero_mul]
    exact hε
  · have hbox : ∀ s d, |y s (u s) d| ≤ R := fun s => hsupport s (u s) (fun hs => hz ⟨s, hs⟩)
    have hp : ‖∏ s, χ s (u s)‖ ≤ 1 := siteFactorTensor_factor_bound χ hχ u
    exact (mul_le_mul hp (herr _ hbox) (norm_nonneg _) zero_le_one).trans_eq (one_mul ε)

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

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel

open _root_.MvPolynomial
open scoped BigOperators

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3

open scoped BigOperators NNReal

theorem booleanCoefficient_sub_bound {α : Type*} [DecidableEq α]
    (f g : Finset α → ℝ) (s : Finset α) {H : ℝ}
    (h : ∀ t ∈ s.powerset, |f t-g t| ≤ H) :
    |booleanCoefficient f s-booleanCoefficient g s| ≤ (2 : ℝ)^s.card*H := by
  unfold booleanCoefficient
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ t ∈ s.powerset, |(-1 : ℝ)^(s\t).card*f t-(-1 : ℝ)^(s\t).card*g t| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ t ∈ s.powerset, |f t-g t| := by
      apply Finset.sum_congr rfl
      intro t _
      rw [← mul_sub, abs_mul, abs_pow]
      norm_num
    _ ≤ ∑ _t ∈ s.powerset, H := Finset.sum_le_sum h
    _ = _ := by simp

theorem booleanSiteJets_lipschitz {D α : Type*} [Fintype D] [Fintype α] [DecidableEq α]
    {O : D → Type*} [∀ d, Fintype (O d)] (sets : ∀ d, O d → Finset α) :
    LipschitzWith ((2 : ℝ≥0)^Fintype.card α) (booleanSiteJets sets) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  apply (dist_pi_le_iff (by positivity)).mpr
  intro o
  change |booleanCoefficient (fun s => x s o.1) (sets o.1 o.2)-
    booleanCoefficient (fun s => y s o.1) (sets o.1 o.2)| ≤ _
  apply (booleanCoefficient_sub_bound _ _ _ (H := dist x y) ?_).trans
  · simp only [NNReal.coe_pow, NNReal.coe_ofNat]
    gcongr
    · norm_num
    · exact Finset.card_le_univ _
  · intro s _
    exact (show |x s o.1-y s o.1| ≤ dist (x s) (y s) from dist_le_pi_dist (x s) (y s) o.1).trans
      (dist_le_pi_dist x y s)

end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {α β R : Type*} [DecidableEq α] [CommRing R]

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel

open _root_.MvPolynomial
open scoped Classical

variable {α β R : Type*} [DecidableEq α] [CommRing R]

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {α β R : Type*} [Fintype α] [DecidableEq α] [CommRing R]

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open _root_.MvPolynomial
open scoped Classical

variable {α β R V : Type*} [Fintype α] [DecidableEq α] [CommRing R]
  [AddCommGroup V] [Module R V]

end Erdos3.BooleanCubeKernel

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

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

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

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

variable {T G : Type*} [MeasurableSpace T] [AddCommGroup G]
  [MeasurableSpace G] [MeasurableAdd₂ G] [MeasurableNeg G]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

variable {T : Type*} [MeasurableSpace T]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

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
open scoped NNReal BigOperators

variable {I J : Type*} [Fintype I] [Fintype J]

end Erdos3

end

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
open scoped NNReal BigOperators

variable {I J : Type*} [Fintype I] [Fintype J]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {D : Type*} [Fintype D] {I : D → Type*} [∀ d, Fintype (I d)]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal ContDiff BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

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

end Erdos3

end

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

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

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

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped ContDiff

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

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

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

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

section

namespace Erdos3

open MeasureTheory

variable (ι : Type*) [Fintype ι]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ResidualErrorAllocation
namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3.NativeModelingNumerics

end Erdos3.NativeModelingNumerics

end

section

namespace Erdos3

theorem regularizationRadius_spec {L ε : ℝ} (hL : 0 ≤ L) (hε : 0 < ε) :
    0 < regularizationRadius L ε ∧ regularizationRadius L ε ≤ 1 ∧
      L*regularizationRadius L ε ≤ ε/2 := by
  have hp : 0 < regularizationRadius L ε := by unfold regularizationRadius; positivity
  refine ⟨hp, min_le_left _ _, ?_⟩
  have hs := (le_div_iff₀ (show 0 < 2*(1+L) by positivity)).mp
    (show regularizationRadius L ε ≤ ε/(2*(1+L)) from min_le_right _ _)
  nlinarith

theorem regularizationRadius_inverse_le_exp {L ε P : ℝ}
    (hL : 0 ≤ L) (hε : 0 < ε) (hP : 0 ≤ P)
    (hLP : L ≤ Real.exp P) (hεP : ε⁻¹ ≤ Real.exp P) :
    (regularizationRadius L ε)⁻¹ ≤ Real.exp (2*P+2) := by
  apply inv_min_le_of_inv_le
  · simpa only [inv_one] using Real.one_le_exp_iff.mpr (by positivity : 0 ≤ 2*P+2)
  · have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    calc
      (ε/(2*(1+L)))⁻¹ = 2*(1+L)*ε⁻¹ := by rw [inv_div, div_eq_mul_inv]
      _ ≤ Real.exp 1*Real.exp (P+1)*Real.exp P := by
        gcongr
        exact one_add_le_exp_succ hP hLP
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

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

open scoped ContDiff NNReal

variable {D : Type*} [Fintype D] {I O : D → Type*}
  [∀ d, Fintype (I d)] [∀ d, Fintype (O d)]

end Erdos3

end

section

namespace Erdos3

open scoped ContDiff

variable {D α : Type*} [Fintype D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)]

end Erdos3

end

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

section

namespace Erdos3

open scoped BigOperators

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
open scoped ContDiff

end Erdos3

end

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

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped Matrix

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.JointPivotProfileBudget
namespace OAI

section

namespace Erdos3

open scoped NNReal

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem profileWidthPower_le_exp (n : ℕ) {δ t : ℝ} (hδ : 0 < δ)
    (hi : δ⁻¹ ≤ Real.exp t) : δ⁻¹ ^ n ≤ Real.exp ((n : ℝ) * t) := by
  calc
    _ ≤ (Real.exp t)^n := by gcongr
    _ = _ := (Real.exp_nat_mul _ _).symm

theorem affineProductProfileLip_le_exp (I : Type*) [Fintype I]
    {δ : ℝ≥0} {t : ℝ} (hi : (δ : ℝ)⁻¹ ≤ Real.exp t) :
    (affineProductProfileLip I δ : ℝ) ≤ Real.exp (affineProfileLogBound (Fintype.card I) t) := by
  have hn : (Fintype.card I : ℝ) ≤ Real.exp (Fintype.card I : ℝ) := by
    linarith [Real.add_one_le_exp (Fintype.card I : ℝ)]
  have hA : (probabilityProfileLipschitz : ℝ) ≤ Real.exp (probabilityProfileLipschitz : ℝ) := by
    linarith [Real.add_one_le_exp (probabilityProfileLipschitz : ℝ)]
  simp only [affineProductProfileLip, NNReal.coe_mul, NNReal.coe_natCast,
    NNReal.coe_pow, NNReal.coe_inv]
  calc
    _ ≤ Real.exp (Fintype.card I : ℝ) * Real.exp (probabilityProfileLipschitz : ℝ) *
        (Real.exp t)^(Fintype.card I + 1) := by gcongr
    _ = _ := by
      rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
      congr 1
      simp only [affineProfileLogBound, Nat.cast_add, Nat.cast_one]

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

variable {D : Type*} [Fintype D] {O J : D → Type*}
  [∀ d, Fintype (O d)] [∀ d, Fintype (J d)]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RepresentativeWindowPatch
namespace OAI

section

namespace Erdos3

open scoped NNReal

variable {X I : Type*} [PseudoMetricSpace X] [Fintype I]

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem intervalSiteWeight_sum {B r : ℝ} (hB : 0 < B) (hr : 0 < r) (x : ℝ) (hx : |x| ≤ B) :
    ∑ i, intervalSiteWeight B r i x = 1 := by
  apply regularizedTentPartition_sum _ hr
  obtain ⟨i, hi⟩ := exists_uniformIntervalGrid_approx hB (boxCoverMeshCount_pos B 1 r) x hx
  refine ⟨i, ?_⟩
  have he := boxCoverMeshCount_error (1 : ℝ≥0) hr (B := B)
  simp only [NNReal.coe_one, one_mul] at he
  exact (show dist x (intervalSiteCenter B r i) ≤ 2 * B / boxCoverMeshCount B 1 r from hi).trans he

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

variable {X I : Type*} [PseudoMetricSpace X] [Fintype I]

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {X : Type*} [Fintype X] (p : FiniteProbabilityWeights X)

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open scoped NNReal

namespace FiniteProbabilityWeights

end FiniteProbabilityWeights

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open scoped BigOperators NNReal

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped NNReal

namespace RepresentativeWindow

end RepresentativeWindow
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

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Matrix

end Erdos3

end

section

namespace Erdos3

open MeasureTheory ProbabilityTheory

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

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

end Erdos3

end

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

section

namespace Erdos3
open MeasureTheory
open scoped NNReal

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeBoundedVariablePatchExpansion
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {α : Type*} [Fintype α] {κ X : α → Type*}
  (ψ : ∀ a, κ a → X a → ℝ)

variable [DecidableEq α] [∀ a, Fintype (κ a)]

variable [∀ a, PseudoMetricSpace (X a)]

end Erdos3

end

section

namespace Erdos3

open scoped NNReal BigOperators

theorem intervalTensorWeight_nonneg {S : Type*} [Fintype S] (B : ℝ) {r : ℝ} (hr : 0 < r)
    (k : S → Fin (intervalSiteCount B r)) (x : S → ℝ) : 0 ≤ intervalTensorWeight B r k x :=
  Finset.prod_nonneg (fun i _ => (intervalSiteWeight_range B hr (k i) (x i)).1)

theorem intervalTensorWeight_sum {S : Type*} [Fintype S] [DecidableEq S]
    {B r : ℝ} (hB : 0 < B) (hr : 0 < r) (x : S → ℝ) (hx : ∀ i, |x i| ≤ B) :
    ∑ k : S → Fin (intervalSiteCount B r), intervalTensorWeight B r k x = 1 := by
  unfold intervalTensorWeight
  rw [← Fintype.prod_sum (fun i k => intervalSiteWeight B r k (x i))]
  simp only [intervalSiteWeight_sum hB hr _ (hx _), Finset.prod_const_one]

theorem intervalTensorWeight_near {S : Type*} [Fintype S] {B r : ℝ} (hr : 0 < r)
    (k : S → Fin (intervalSiteCount B r)) (x : S → ℝ) (hx : 0 < intervalTensorWeight B r k x) :
    dist x (fun i => intervalSiteCenter B r (k i)) ≤ 2 * r := by
  apply (dist_pi_le_iff (by positivity)).mpr
  intro i
  have hp := productPartitionWeight_pos_coordinate (fun _ : S => intervalSiteWeight B r)
    (fun _ j x => (intervalSiteWeight_range B hr j x).1) k x hx i
  exact (intervalSiteWeight_near B r (k i) (x i) hp).le

theorem intervalTensorApprox_error {S : Type*} [Fintype S] [DecidableEq S]
    {B r : ℝ} (hB : 0 < B) (hr : 0 < r) (F : (S → ℝ) → ℂ) {K : ℝ≥0}
    (hF : LipschitzWith K F) (x : S → ℝ) (hx : ∀ i, |x i| ≤ B) :
    ‖F x - intervalTensorApprox B r F x‖ ≤ 2 * K * r := by
  apply norm_sub_positive_sum_le (fun k => intervalTensorWeight B r k x)
    (fun k => F (fun i => intervalSiteCenter B r (k i))) (F x) _
    (fun k => intervalTensorWeight_nonneg B hr k x) (intervalTensorWeight_sum hB hr x hx)
  intro k hk
  have h := hF.dist_le_mul x (fun i => intervalSiteCenter B r (k i))
  rw [dist_eq_norm] at h
  exact h.trans ((mul_le_mul_of_nonneg_left (intervalTensorWeight_near hr k x hk) K.coe_nonneg).trans_eq (by ring))

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct NNReal BigOperators

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct NNReal BigOperators

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.GroupedSiteTensor
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

variable {S D : Type*} [Fintype S] [Fintype D]

theorem siteCurry_lipschitz :
    LipschitzWith 1 (fun x : S × D → ℝ => fun s d => x (s, d)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul]
  apply (dist_pi_le_iff dist_nonneg).mpr
  intro s
  apply (dist_pi_le_iff dist_nonneg).mpr
  intro d
  exact dist_le_pi_dist x y (s, d)

theorem groupedSiteApprox_eq_interval [DecidableEq S] [DecidableEq D]
    (B r : ℝ) (F : (S → D → ℝ) → ℂ) (x : S → D → ℝ) :
    groupedSiteApprox B r F x =
      intervalTensorApprox B r (fun y : S × D → ℝ => F (fun s d => y (s, d)))
        (fun p => x p.1 p.2) := by
  unfold groupedSiteApprox intervalTensorApprox groupedSiteCoefficient
  apply Finset.sum_congr rfl
  intro k _
  simp only [groupedSiteFactor, vectorIntervalSiteWeight, intervalTensorWeight,
    Complex.ofReal_prod, Fintype.prod_prod_type]
  ring

theorem groupedSiteApprox_error [DecidableEq S] [DecidableEq D]
    {B r : ℝ} (hB : 0 < B) (hr : 0 < r) (F : (S → D → ℝ) → ℂ)
    {K : ℝ≥0} (hF : LipschitzWith K F) (x : S → D → ℝ)
    (hx : ∀ s d, |x s d| ≤ B) :
    ‖F x-groupedSiteApprox B r F x‖ ≤ 2*K*r := by
  rw [groupedSiteApprox_eq_interval]
  exact intervalTensorApprox_error hB hr _
    (by simpa only [mul_one] using hF.comp (siteCurry_lipschitz (S := S) (D := D)))
    (fun p : S × D => x p.1 p.2) (fun p : S × D => hx p.1 p.2)

theorem groupedSiteCoefficient_sum [DecidableEq S] [DecidableEq D]
    (B r : ℝ) (F : (S → D → ℝ) → ℂ)
    {A : ℝ} (hF : ∀ x, ‖F x‖ ≤ A) :
    (∑ k : S × D → Fin (intervalSiteCount B r), ‖groupedSiteCoefficient B r F k‖) ≤
      (intervalSiteCount B r : ℝ)^(Fintype.card S*Fintype.card D)*A := by
  calc
    _ ≤ ∑ _k : S × D → Fin (intervalSiteCount B r), A := Finset.sum_le_sum (fun k _ => hF _)
    _ = _ := by simp [Fintype.card_prod]

omit [Fintype S] in
theorem groupedSiteFactor_bound (B : ℝ) {r : ℝ} (hr : 0 < r)
    (k : S × D → Fin (intervalSiteCount B r)) (s : S) (x : D → ℝ) :
    ‖groupedSiteFactor B r k s x‖ ≤ 1 :=
  vectorIntervalSiteWeight_bound B hr _ _

omit [Fintype S] in
theorem groupedSiteFactor_lipschitz (B : ℝ) {r : ℝ≥0} (hr : 0 < r)
    (k : S × D → Fin (intervalSiteCount B r)) (s : S) :
    LipschitzWith (Fintype.card D*((2*intervalSiteCount B r+1)/r))
      (groupedSiteFactor B r k s) :=
  vectorIntervalSiteWeight_lipschitz B hr _

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.VectorSiteBudget
namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

theorem exists_grouped_site_approximation {S D : Type*} [Fintype S] [Fintype D]
    [DecidableEq S] [DecidableEq D]
    (F : (S → D → ℝ) → ℂ) (A K : ℝ≥0) (hA : ∀ x, ‖F x‖ ≤ A)
    (hK : LipschitzWith K F) {B ε P : ℝ} (hB : 0 < B) (hε : 0 < ε) (hP : 0 ≤ P)
    (hBP : B ≤ Real.exp P) (hAP : (A : ℝ) ≤ Real.exp P) (hKP : (K : ℝ) ≤ Real.exp P)
    (hεP : ε⁻¹ ≤ Real.exp P) :
    ∃ n : ℕ, (n : ℝ) ≤ Real.exp (4*P+8) ∧
      ∃ (c : (S × D → Fin n) → ℂ) (f : (S × D → Fin n) → S → (D → ℝ) → ℂ),
        (∑ k, ‖c k‖) ≤ Real.exp ((Fintype.card S*Fintype.card D : ℕ)*(4*P+8)+P) ∧
        (∀ k s x, ‖f k s x‖ ≤ 1) ∧
        (∀ k s, LipschitzWith ⟨Real.exp (Fintype.card D+6*P+12), Real.exp_nonneg _⟩ (f k s)) ∧
        ∀ x : S → D → ℝ, (∀ s d, |x s d| ≤ B) →
          ‖F x-∑ k, c k*∏ s, f k s (x s)‖ ≤ ε := by
  let r := regularizationRadius K ε
  have hs := regularizationRadius_spec K.coe_nonneg hε
  have hr : 0 < r := hs.1
  have hi : r⁻¹ ≤ Real.exp (2*P+2) :=
    regularizationRadius_inverse_le_exp K.coe_nonneg hε hP hKP hεP
  have hP' : 0 ≤ 2*P+2 := by positivity
  have hPP' : P ≤ 2*P+2 := by linarith
  have hB' : B ≤ Real.exp (2*P+2) := hBP.trans (Real.exp_le_exp.mpr hPP')
  have hn : (intervalSiteCount B r : ℝ) ≤ Real.exp (4*P+8) := by
    have hb := intervalSiteCount_le_exp hB.le hr hP' hB' (by simpa only [one_div] using hi)
    have he : 2*(2*P+2)+4 = 4*P+8 := by ring
    simpa only [he] using hb
  have hf : (Fintype.card D : ℝ)*((2*(intervalSiteCount B r : ℝ)+1)/r) ≤
      Real.exp (Fintype.card D+6*P+12) := by
    have hb := intervalSiteLipschitz_le_exp hB.le hr hP' hB' (by simpa only [one_div] using hi)
    have hd : (Fintype.card D : ℝ) ≤ Real.exp (Fintype.card D : ℝ) := by
      linarith [Real.add_one_le_exp (Fintype.card D : ℝ)]
    calc
      _ ≤ Real.exp (Fintype.card D : ℝ)*Real.exp (3*(2*P+2)+6) := by gcongr
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  refine ⟨intervalSiteCount B r, hn, groupedSiteCoefficient B r F, groupedSiteFactor B r, ?_,
    (fun k s x => groupedSiteFactor_bound B hr k s x), ?_, ?_⟩
  · apply (groupedSiteCoefficient_sum B r F hA).trans
    calc
      _ ≤ (Real.exp (4*P+8))^(Fintype.card S*Fintype.card D)*Real.exp P := by gcongr
      _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]
  · intro k s
    have hl := groupedSiteFactor_lipschitz B (r := ⟨r, hr.le⟩) hr k s
    apply hl.weaken
    exact_mod_cast hf
  · intro x hx
    apply (groupedSiteApprox_error hB hr F hK x hx).trans
    have hs' : (K : ℝ)*r ≤ ε/2 := hs.2.2
    nlinarith

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ActiveProfileNoise
namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open VectorPolynomial
open scoped BigOperators

variable {D G : Type*} [Fintype D] [Fintype G] {B : D → Type*}
variable [∀ d, Fintype (B d)] (h : D → ℕ) (d : D)

end Erdos3

end

section

namespace Erdos3

open VectorPolynomial
open scoped BigOperators

variable {D G Z α : Type*} [Fintype D] [Fintype G] [Fintype α] [DecidableEq α]
variable {B : D → Type*} [∀ d, Fintype (B d)] (h : D → ℕ)
variable (P : D → Prop) [DecidablePred P] (extra : G → Option α → Z)
variable {O : {d // ¬P d} → Type*} (sets : ∀ d, O d → Finset α)

end Erdos3

end

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

open scoped BigOperators

variable {D : Type*} [Fintype D] (B : D → Type*) [∀ d, Fintype (B d)]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators ContDiff NNReal

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

open MeasureTheory
open scoped BigOperators ContDiff NNReal

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

open scoped BigOperators Classical

variable {S R T U : Type*} [Fintype S] [Fintype R] [Fintype T]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

theorem unitCoefficientSource_abs_le (I : Type*) [Fintype I] :
    ∀ᵐ r ∂unitCoefficientSource I, ∀ i, |r i| ≤ 1 := by
  filter_upwards [unitCoefficientSource_norm_le I] with r hr i
  exact (Real.norm_eq_abs (r i)).symm.trans_le ((norm_le_pi_norm r i).trans hr)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem idealSiteProfile_bounds (I : Type*) [Fintype I] (q : ℕ)
    (η : ℝ≥0) (hη : 0 < η) {P : ℝ} (hP : 0 ≤ P) (hηP : (η : ℝ)⁻¹ ≤ Real.exp P) :
    ((η⁻¹^Fintype.card I : ℝ≥0) : ℝ) ≤ Real.exp (idealSiteLogBudget (Fintype.card I) q P) ∧
    ((affineProductProfileLip I η*(2 : ℝ≥0)^q : ℝ≥0) : ℝ) ≤
      Real.exp (idealSiteLogBudget (Fintype.card I) q P) := by
  have hb := idealSiteLogBudget_bounds (Fintype.card I) q hP
  constructor
  · apply le_trans _ (Real.exp_le_exp.mpr hb.2.2.1)
    simpa only [NNReal.coe_pow, NNReal.coe_inv] using
      profileWidthPower_le_exp (Fintype.card I) (show (0 : ℝ) < η from hη) hηP
  · have hp := affineProductProfileLip_le_exp I hηP
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have hq : (2 : ℝ)^q ≤ Real.exp q := by
      calc
        _ ≤ (Real.exp 1)^q := by gcongr
        _ = _ := by rw [← Real.exp_nat_mul]; simp
    apply le_trans _ (Real.exp_le_exp.mpr hb.2.2.2)
    simp only [NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_ofNat]
    calc
      _ ≤ Real.exp (affineProfileLogBound (Fintype.card I) P)*Real.exp q := by gcongr
      _ = _ := (Real.exp_add _ _).symm

section Ideal

variable {D G α : Type*} [Fintype D] [Fintype α] [DecidableEq α]
  {B O J N : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  [∀ d, Fintype (J d)] [∀ d, Fintype (N d)]
  (h : D → ℕ) (e : ∀ d, J d ⊕ N d → SamplerTupleIndex G B h →₀ ℕ)
  (index : ∀ d, B d → J d ⊕ N d) (c w : ∀ d, J d ⊕ N d → ℝ)
  (sets : ∀ d, O d → Finset α)

end Ideal

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

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

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff NNReal

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

variable {D G : Type*} [Fintype D] [Fintype G]
  {B : D → Type*} [∀ d, Fintype (B d)] (h : D → ℕ) (P : D → Prop)

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

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff NNReal

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

variable {D G Z α : Type*} [Fintype D] [Fintype G] [Fintype Z]
  [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  (h : D → ℕ) (P : D → Prop) [DecidablePred P]
  (sets : ∀ d : {d // ¬P d}, O d.val → Finset α)
  (center width : PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d) → ℝ)

theorem activeAveragedSlicedIdealSiteFunction_bound (δ : ℝ≥0) (hδ : 0 < δ)
    (x : Finset α → D → ℝ) :
    ‖activeAveragedSlicedIdealSiteFunction (G := G) (Z := Z) (B := B) h P sets center width δ x‖ ≤
      (δ⁻¹ ^ Fintype.card (Σ d : {d // ¬P d}, O d.val) : ℝ≥0) := by
  have hx := (activeAveragedSlicedProfileIdeal_spec (G := G) (B := B) Z h P sets δ hδ center width).1
    (booleanSiteJets sets (fun s d => x s d.val))
  simpa only [activeAveragedSlicedIdealSiteFunction, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hx.1] using hx.2

theorem activeAveragedSlicedIdealSiteFunction_lipschitz (δ : ℝ≥0) (hδ : 0 < δ) :
    LipschitzWith
      (affineProductProfileLip (Σ d : {d // ¬P d}, O d.val) δ * (2 : ℝ≥0)^Fintype.card α)
      (activeAveragedSlicedIdealSiteFunction (G := G) (Z := Z) (B := B) h P sets center width δ) := by
  have hrestrict : LipschitzWith 1
      (fun x : Finset α → D → ℝ => fun s (d : {d // ¬P d}) => x s d.val) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [NNReal.coe_one, one_mul]
    apply (dist_pi_le_iff dist_nonneg).mpr
    intro s
    apply (dist_pi_le_iff dist_nonneg).mpr
    intro d
    exact (dist_le_pi_dist (x s) (y s) d.val).trans (dist_le_pi_dist x y s)
  have hi := (activeAveragedSlicedProfileIdeal_spec (G := G) (B := B) Z h P sets δ hδ center width).2.1
  change LipschitzWith _ (fun x : Finset α → D → ℝ =>
    (activeAveragedSlicedProfileIdeal (G := G) (B := B) Z h P sets δ center width
      (booleanSiteJets sets (fun s d => x s d.val)) : ℂ))
  simpa only [one_mul, mul_one, Function.comp_def] using
    Complex.isometry_ofReal.lipschitz.comp
      (hi.comp ((booleanSiteJets_lipschitz sets).comp hrestrict))

theorem exists_active_sliced_ideal_site_approximation (δ : ℝ≥0) (hδ : 0 < δ)
    {R ε p : ℝ} (hR : 0 < R) (hε : 0 < ε) (hp : 0 ≤ p)
    (hRp : R ≤ Real.exp p) (hεp : ε⁻¹ ≤ Real.exp p) (hδp : (δ : ℝ)⁻¹ ≤ Real.exp p) :
    let Q := idealSiteLogBudget (Fintype.card (Σ d, O d)) (Fintype.card α) p
    ∃ n : ℕ, (n : ℝ) ≤ Real.exp (4*Q+8) ∧
      ∃ (a : (Finset α × D → Fin n) → ℂ)
        (f : (Finset α × D → Fin n) → Finset α → (D → ℝ) → ℂ),
        (∑ k, ‖a k‖) ≤ Real.exp ((Fintype.card (Finset α)*Fintype.card D : ℕ)*(4*Q+8)+Q) ∧
        (∀ k s x, ‖f k s x‖ ≤ 1) ∧
        (∀ k s, LipschitzWith ⟨Real.exp (Fintype.card D+6*Q+12), Real.exp_nonneg _⟩ (f k s)) ∧
        ∀ x : Finset α → D → ℝ, (∀ s d, |x s d| ≤ R) →
          ‖(activeAveragedSlicedProfileIdeal (G := G) (B := B) Z h P sets δ center width
              (booleanSiteJets sets (fun s d => x s d.val)) : ℂ) -
            ∑ k, a k*∏ s, f k s (x s)‖ ≤ ε := by
  intro Q
  have hcard : Fintype.card (Σ d : {d // ¬P d}, O d.val) ≤ Fintype.card (Σ d, O d) := by
    apply Fintype.card_le_of_injective (fun a : (Σ d : {d // ¬P d}, O d.val) =>
      (⟨a.1.val, a.2⟩ : Σ d, O d))
    rintro ⟨⟨a, ha⟩, x⟩ ⟨⟨b, hb⟩, y⟩ heq
    cases heq
    rfl
  have hcardR : (Fintype.card (Σ d : {d // ¬P d}, O d.val) : ℝ) ≤
      Fintype.card (Σ d, O d) := by exact_mod_cast hcard
  have hQle : idealSiteLogBudget (Fintype.card (Σ d : {d // ¬P d}, O d.val))
      (Fintype.card α) p ≤ Q := by
    dsimp only [Q, idealSiteLogBudget, affineProfileLogBound]
    gcongr
  have hb := idealSiteLogBudget_bounds (Fintype.card (Σ d, O d)) (Fintype.card α) hp
  have hprof := idealSiteProfile_bounds (Σ d : {d // ¬P d}, O d.val)
    (Fintype.card α) δ hδ hp hδp
  exact exists_grouped_site_approximation
    (activeAveragedSlicedIdealSiteFunction (G := G) (Z := Z) (B := B) h P sets center width δ)
    (δ⁻¹ ^ Fintype.card (Σ d : {d // ¬P d}, O d.val))
    (affineProductProfileLip (Σ d : {d // ¬P d}, O d.val) δ * (2 : ℝ≥0)^Fintype.card α)
    (activeAveragedSlicedIdealSiteFunction_bound h P sets center width δ hδ)
    (activeAveragedSlicedIdealSiteFunction_lipschitz h P sets center width δ hδ)
    hR hε hb.1 (hRp.trans (Real.exp_le_exp.mpr hb.2.1))
    (hprof.1.trans (Real.exp_le_exp.mpr hQle))
    (hprof.2.trans (Real.exp_le_exp.mpr hQle))
    (hεp.trans (Real.exp_le_exp.mpr hb.2.1))

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

variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.BufferedActiveSlicedIdealSiteSupport
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

theorem exists_supported_buffered_active_sliced_ideal_site_approximation
    {D G Z α U : Type*} [Fintype D] [Fintype G] [Fintype Z] [Fintype α] [DecidableEq α]
    [PseudoMetricSpace U] {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
    (h : D → ℕ) (P : D → Prop) [DecidablePred P]
    (sets : ∀ d : {d // ¬P d}, O d.val → Finset α)
    (center width : PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d) → ℝ)
    (δ : ℝ≥0) (hδ : 0 < δ)
    {R ε p : ℝ} (hR : 0 < R) (hε : 0 < ε) (hp : 0 ≤ p)
    (hRp : R ≤ Real.exp p) (hεp : ε⁻¹ ≤ Real.exp p) (hδp : (δ : ℝ)⁻¹ ≤ Real.exp p)
    (y : Finset α → U → D → ℝ) (χ : Finset α → U → ℂ) {L C : ℝ≥0}
    (hy : ∀ s, LipschitzWith L (y s)) (hχ : ∀ s, LipschitzWith C (χ s))
    (hχ1 : ∀ s u, ‖χ s u‖ ≤ 1) (hsupport : ∀ s u, χ s u ≠ 0 → ∀ d, |y s u d| ≤ R) :
    let Q := idealSiteLogBudget (Fintype.card (Σ d, O d)) (Fintype.card α) p
    ∃ n : ℕ, (n : ℝ) ≤ Real.exp (4 * Q + 8) ∧
      ∃ (a : (Finset α × D → Fin n) → ℂ) (f : (Finset α × D → Fin n) → Finset α → U → ℂ),
        (∑ k, ‖a k‖) ≤ Real.exp ((Fintype.card (Finset α) * Fintype.card D : ℕ) * (4 * Q + 8) + Q) ∧
        (∀ k s u, ‖f k s u‖ ≤ 1) ∧
        (∀ k s, LipschitzWith (⟨Real.exp (Fintype.card D + 6 * Q + 12), Real.exp_nonneg _⟩ * L + C) (f k s)) ∧
        (∀ k s u, χ s u = 0 → f k s u = 0) ∧
        ∀ u : Finset α → U,
          ‖(∏ s, χ s (u s)) * (activeAveragedSlicedProfileIdeal (G := G) (B := B) Z h P sets δ center width
              (booleanSiteJets sets (fun s d => y s (u s) d.val)) : ℂ) -
            ∑ k, a k * ∏ s, f k s (u s)‖ ≤ ε := by
  obtain ⟨n, hn, a, f, ha, hf, hLip, herr⟩ :=
    exists_active_sliced_ideal_site_approximation (G := G) (Z := Z) (B := B) h P sets center width δ hδ hR hε hp hRp hεp hδp
  dsimp only
  refine ⟨n, hn, a, bufferedSiteFactor y χ f, ha, ?_, ?_, ?_, ?_⟩
  · exact bufferedSiteFactor_bound y χ f hχ1 hf
  · exact bufferedSiteFactor_lipschitz y χ f hy hχ hLip hχ1 hf
  · intro k s u hu
    simp only [bufferedSiteFactor, hu, zero_mul]
  · intro u
    exact bufferedSiteExpansion_error y χ
      (activeAveragedSlicedIdealSiteFunction (G := G) (Z := Z) (B := B) h P sets center width δ)
      a f hε.le hχ1 hsupport herr u

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedScalarStructuralBasePower
namespace OAI

section

namespace Erdos3

open scoped NNReal ContDiff

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

theorem exists_normalized_active_sliced_ideal_site_approximation
    {D G Z α : Type*} [Fintype D] [Fintype G] [Fintype Z] [Fintype α] [DecidableEq α]
    {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
    (h : D → ℕ) (P : D → Prop) [DecidablePred P]
    (sets : ∀ d : {d // ¬P d}, O d.val → Finset α)
    (center width : PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d) → ℝ)
    (δ : ℝ≥0) (hδ : 0 < δ)
    (radius : ℝ≥0) (hradius : 0 < radius) {ε p : ℝ} (hε : 0 < ε) (hp : 0 ≤ p)
    (hbox : 2 * (radius : ℝ) ≤ Real.exp p) (hεp : ε⁻¹ ≤ Real.exp p) (hδp : (δ : ℝ)⁻¹ ≤ Real.exp p) :
    let C : ℝ≥0 := Fintype.card D * normalizedSiteCutoffBound / (2 * radius)
    let Q := idealSiteLogBudget (Fintype.card (Σ d, O d)) (Fintype.card α) p
    ∃ χ : (D → ℝ) → ℝ, (∀ v, (∀ d, |v d| ≤ (radius : ℝ)) → χ v = 1) ∧
      ∃ k : ℕ, (k : ℝ) ≤ Real.exp (4 * Q + 8) ∧
        (Fintype.card (Finset α × D → Fin k) : ℝ) ≤
          Real.exp ((Fintype.card (Finset α) * Fintype.card D : ℕ) * (4 * Q + 8)) ∧
        ∃ (a : (Finset α × D → Fin k) → ℂ) (f : (Finset α × D → Fin k) → Finset α → (D → ℝ) → ℂ),
          (∑ i, ‖a i‖) ≤ Real.exp ((Fintype.card (Finset α) * Fintype.card D : ℕ) * (4 * Q + 8) + Q) ∧
          (∀ i s v, ‖f i s v‖ ≤ 1) ∧
          (∀ i s, LipschitzWith (⟨Real.exp (Fintype.card D + 6 * Q + 12), Real.exp_nonneg _⟩ + C) (f i s)) ∧
          (∀ i s v, (∃ d, 2 * (radius : ℝ) < |v d|) → f i s v = 0) ∧
          ∀ v : Finset α → D → ℝ,
            ‖(∏ s, (χ (v s) : ℂ)) * (activeAveragedSlicedProfileIdeal (G := G) (B := B) Z h P sets δ center width
                (booleanSiteJets sets (fun s d => v s d.val)) : ℂ) -
              ∑ i, a i * ∏ s, f i s (v s)‖ ≤ ε := by
  intro C Q
  obtain ⟨χ, _hsmooth, _hcompact, hχ, hone, hsupport, hLip⟩ := exists_normalized_site_cutoff (D := D) radius hradius
  have hχC : LipschitzWith C (fun v => (χ v : ℂ)) := by
    simpa only [one_mul, Function.comp_def] using Complex.isometry_ofReal.lipschitz.comp hLip
  obtain ⟨k, hk, a, f, ha, hf, hLf, hfsupport, herr⟩ :=
    exists_supported_buffered_active_sliced_ideal_site_approximation (G := G) (Z := Z) (B := B) (O := O)
      h P sets center width δ hδ (mul_pos (by norm_num : (0 : ℝ) < 2) hradius) hε hp hbox hεp hδp
      (fun (_ : Finset α) (v : D → ℝ) => v) (fun _ v => (χ v : ℂ))
      (fun _ => LipschitzWith.id) (fun _ => hχC)
      (fun _ v => by simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hχ v).1] using (hχ v).2)
      (fun _ v hv d => hsupport v (by exact_mod_cast hv) d)
  have hcard : (Fintype.card (Finset α × D → Fin k) : ℝ) ≤
      Real.exp ((Fintype.card (Finset α) * Fintype.card D : ℕ) * (4 * Q + 8)) := by
    simp only [Fintype.card_fun, Fintype.card_prod, Fintype.card_fin, Nat.cast_pow]
    calc
      _ ≤ (Real.exp (4 * Q + 8)) ^ (Fintype.card (Finset α) * Fintype.card D) :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) hk _
      _ = _ := (Real.exp_nat_mul _ _).symm
  refine ⟨χ, hone, k, hk, hcard, a, f, ha, hf, ?_, ?_, herr⟩
  · intro i s
    let L : ℝ≥0 := ⟨Real.exp (Fintype.card D + 6 * Q + 12), Real.exp_nonneg _⟩
    have h : LipschitzWith (L * 1 + C) (f i s) := hLf i s
    simpa only [mul_one] using h
  · intro i s v hv
    apply hfsupport
    have hzero : χ v = 0 := by
      by_contra hn
      obtain ⟨d, hd⟩ := hv
      exact (not_lt_of_ge (hsupport v hn d)) hd
    simp only [hzero, Complex.ofReal_zero]

end Erdos3

end

section

namespace Erdos3

open scoped NNReal ContDiff

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedProductIdealCutoff
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical Matrix

variable {α : Type*} [DecidableEq α]

theorem rowRestrictedSiteMatrix_real_bound (rows : Finset (Finset α))
    (v : rows → ℝ) {T : ℝ} (hT : 0 ≤ T) (hv : ∀ t, |v t| ≤ T) (s : Finset α) :
    |∑ t : rows, (rowRestrictedSiteMatrix rows s t : ℝ) * v t| ≤ rows.card * T := by
  calc
    _ ≤ ∑ t : rows, |(rowRestrictedSiteMatrix rows s t : ℝ) * v t| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _t : rows, T := by
      apply Finset.sum_le_sum
      intro t _
      by_cases ht : t.val ⊆ s
      · simpa only [rowRestrictedSiteMatrix, booleanReconstructionMatrix, if_pos ht,
          Int.cast_one, one_mul] using hv t
      · simpa only [rowRestrictedSiteMatrix, booleanReconstructionMatrix, if_neg ht,
          Int.cast_zero, zero_mul, abs_zero] using hT
    _ = _ := by simp

namespace VectorPolynomial

variable {m : ℕ} {I J E : Fin m → Type*} {n : Fin m → ℕ}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
variable (rowSets : Fin m → Finset (Finset α))
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R : Fin m → ℝ} (hR : ∀ j, 0 < R j) (d : ℕ)

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d] (r : ℝ≥0) (hr : 0 < r)

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset α))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "split" => coefficientJetAxisSplit rowTypes I n grid
local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (E := E) U o b d
  (fun j (_ : rowTypes j) => standardLatticeClosedQuarterBox (J j))

variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (T : Fin m → ℝ) (hT : ∀ j, 0 ≤ T j)
variable (hsource : ∀ j, (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
  ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ (j.val + 1)) ≤ T j)
variable (hradius : ∀ j, (rowSets j).card * T j ≤ (r : ℝ))
variable (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
variable (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)) ≤ 1 / 4)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α]
variable (rowSets : Fin m → Finset (Finset α))

variable [DecidableEq α]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset α))

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

omit [Fintype α] in
theorem realRowsSiteValue_bound (rows : Finset (Finset α))
    (v : rows → ℝ) {T : ℝ} (hT : 0 ≤ T) (hv : ∀ t, |v t| ≤ T) (s : Finset α) :
    |realRowsSiteValue rows v s| ≤ rows.card * T := by
  simpa only [realRowsSiteValue, rowRestrictedSiteMatrix, booleanReconstructionMatrix, Int.cast_ite, Int.cast_one, Int.cast_zero, mul_comm]
    using rowRestrictedSiteMatrix_real_bound rows v hT hv s

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

omit [DecidableEq α] in
theorem allocatedRowSlicedSiteRadius_pos : 0 < allocatedRowSlicedSiteRadius rowSets := by
  change (0 : ℝ) < 1 + ∑ j : Fin m, (rowSets j).card * (partitionedIdealRadius α m + 1)
  have := partitionedIdealRadius_nonneg α m
  positivity

omit [DecidableEq α] in
theorem allocatedRowSlicedSiteRadius_dominates (j : Fin m) :
    (rowSets j).card * (partitionedIdealRadius α m + 1) ≤ allocatedRowSlicedSiteRadius rowSets := by
  change _ ≤ 1 + ∑ k : Fin m, (rowSets k).card * (partitionedIdealRadius α m + 1)
  have hT : 0 ≤ partitionedIdealRadius α m + 1 := by
    have := partitionedIdealRadius_nonneg α m
    positivity
  exact (Finset.single_le_sum (f := fun k : Fin m =>
    (rowSets k).card * (partitionedIdealRadius α m + 1))
    (fun k _ => mul_nonneg (Nat.cast_nonneg _) hT) (Finset.mem_univ j)).trans
    (le_add_of_nonneg_left zero_le_one)

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

theorem allocatedRowSlicedIdealCoordinates_bound
    (ρ : ℝ≥0) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (center width : input → ℝ) (hw : ∀ i, |center i| + |width i| ≤ 1)
    (z : AllocatedLongJetRows B U b S jets)
    (hz : allocatedRowSlicedIdeal B U b S rowSets ρ center width
      (allocatedLongJetRealCoordinates B U b S z) ≠ 0)
    (s : Finset α) (a : LayerSamplerAxis I n) :
    |allocatedRowIdealCoordinates B U b S rowSets z s a| ≤
      (allocatedRowSlicedSiteRadius rowSets : ℝ) := by
  have hT : 0 ≤ partitionedIdealRadius α m + 1 := by
    have := partitionedIdealRadius_nonneg α m
    positivity
  have hv : ‖fun q : output => allocatedLongJetRealCoordinates B U b S z q / R q.1.val.1‖ ≤
      partitionedIdealRadius α m + 1 := by
    by_contra hn
    apply hz
    unfold allocatedRowSlicedIdeal diagonalImageDensity
    rw [activeAveragedSlicedProfileIdeal_zero_outside (G := G) (B := B) (G × Option α)
      (layerSamplerDegree I n) grid (fun a : {a // ¬grid a} => (Subtype.val : jets a.val.1 → Finset α))
      (fun a => Nat.succ_le_of_lt a.1.isLt) ρ hρ hρ1 center width hw _ (lt_of_not_ge hn), mul_zero]
  unfold allocatedRowIdealCoordinates
  apply (realRowsSiteValue_bound (rowSets a.1) _ hT ?_ s).trans
    (allocatedRowSlicedSiteRadius_dominates rowSets a.1)
  intro t
  by_cases ha : ¬grid a
  · rw [dif_pos ha]
    exact (norm_le_pi_norm (fun q : output =>
      allocatedLongJetRealCoordinates B U b S z q / R q.1.val.1) ⟨⟨a, ha⟩, t⟩).trans hv
  · rw [dif_neg ha, abs_zero]
    exact hT

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedRowSlicedIdealApproximation
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
local notation "siteRadius" => allocatedRowSlicedSiteRadius rowSets
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "hLayer" => layerSamplerDegree I n

variable (center width : PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n)
  (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a) → ℝ)

theorem allocatedRowSlicedIdealCutoff_complex_mul
    (δ : ℝ≥0) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hw : ∀ i, |center i| + |width i| ≤ 1)
    (χ : (LayerSamplerAxis I n → ℝ) → ℝ)
    (hone : ∀ v, (∀ a, |v a| ≤ (siteRadius : ℝ)) → χ v = 1)
    (z : AllocatedLongJetRows B U b S jets) :
    (∏ s : Finset α, (χ (allocatedRowIdealCoordinates B U b S rowSets z s) : ℂ)) *
      (allocatedRowSlicedIdeal B U b S rowSets δ center width (allocatedLongJetRealCoordinates B U b S z) : ℂ) =
      (allocatedRowSlicedIdeal B U b S rowSets δ center width (allocatedLongJetRealCoordinates B U b S z) : ℂ) := by
  by_cases hz : allocatedRowSlicedIdeal B U b S rowSets δ center width
      (allocatedLongJetRealCoordinates B U b S z) = 0
  · rw [hz, Complex.ofReal_zero, mul_zero]
  · have hp : (∏ s : Finset α, (χ (allocatedRowIdealCoordinates B U b S rowSets z s) : ℂ)) = 1 := by
      apply Finset.prod_eq_one
      intro s _
      rw [hone _ (allocatedRowSlicedIdealCoordinates_bound B U b S rowSets δ hδ hδ1 center width hw z hz s),
        Complex.ofReal_one]
    rw [hp, one_mul]

theorem allocatedRowSlicedIdealApproximation_error {T : Type*} [Fintype T]
    (hR : ∀ j, 0 < R j) (δ : ℝ≥0) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hw : ∀ i, |center i| + |width i| ≤ 1)
    (χ : (LayerSamplerAxis I n → ℝ) → ℝ)
    (hone : ∀ v, (∀ a, |v a| ≤ (siteRadius : ℝ)) → χ v = 1)
    (a : T → ℂ) (f : T → Finset α → (LayerSamplerAxis I n → ℝ) → ℂ) (ε : ℝ)
    (herr : ∀ v : Finset α → LayerSamplerAxis I n → ℝ,
      ‖(∏ s, (χ (v s) : ℂ)) * (activeAveragedSlicedProfileIdeal (G := G) (B := B) (G × Option α) hLayer grid
          (fun a => (Subtype.val : jets a.val.1 → Finset α)) δ center width
          (booleanSiteJets (fun a : {a // ¬grid a} => (Subtype.val : jets a.val.1 → Finset α))
            (fun s d => v s d.val)) : ℂ) - ∑ i, a i * ∏ s, f i s (v s)‖ ≤ ε)
    (z : AllocatedLongJetRows B U b S jets) :
    let volume : ℝ := ∏ q : (Σ a : {a // ¬grid a}, jets a.val.1), R q.1.val.1
    ‖(volume : ℂ) * (allocatedRowSlicedIdeal B U b S rowSets δ center width (allocatedLongJetRealCoordinates B U b S z) : ℂ) -
      ∑ i, a i * ∏ s, f i s (allocatedRowIdealCoordinates B U b S rowSets z s)‖ ≤ ε ∧
    ‖(allocatedRowSlicedIdeal B U b S rowSets δ center width (allocatedLongJetRealCoordinates B U b S z) : ℂ) -
      (∑ i, a i * ∏ s, f i s (allocatedRowIdealCoordinates B U b S rowSets z s)) / (volume : ℂ)‖ ≤ ε / volume := by
  intro volume
  have hdensity := congrArg Complex.ofReal (allocatedRowSlicedIdealCoordinates_density B U b S rowSets hR δ center width z)
  simp only [Complex.ofReal_mul] at hdensity
  have hcutoff := allocatedRowSlicedIdealCutoff_complex_mul B U b S rowSets center width δ hδ hδ1 hw χ hone z
  have hpoint := herr (allocatedRowIdealCoordinates B U b S rowSets z)
  rw [← hdensity] at hpoint
  have hproduct : (∏ s : Finset α, (χ (allocatedRowIdealCoordinates B U b S rowSets z s) : ℂ)) *
      ((volume : ℂ) * (allocatedRowSlicedIdeal B U b S rowSets δ center width
        (allocatedLongJetRealCoordinates B U b S z) : ℂ)) =
      (volume : ℂ) * (allocatedRowSlicedIdeal B U b S rowSets δ center width
        (allocatedLongJetRealCoordinates B U b S z) : ℂ) := by
    rw [mul_left_comm, hcutoff]
  rw [hproduct] at hpoint
  refine ⟨hpoint, ?_⟩
  have hvolume : 0 < volume := Finset.prod_pos (fun q _ => hR q.1.val.1)
  have hvolumeC : (volume : ℂ) ≠ 0 := by exact_mod_cast hvolume.ne'
  calc
    _ = ‖((volume : ℂ) * (allocatedRowSlicedIdeal B U b S rowSets δ center width
          (allocatedLongJetRealCoordinates B U b S z) : ℂ) -
        ∑ i, a i * ∏ s, f i s (allocatedRowIdealCoordinates B U b S rowSets z s)) / (volume : ℂ)‖ := by
      congr 1
      field_simp [hvolumeC]
    _ = _ := by rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hvolume]
    _ ≤ _ := div_le_div_of_nonneg_right hpoint hvolume.le

theorem exists_allocated_row_sliced_ideal_site_approximation (hR : ∀ j, 0 < R j)
    (δ : ℝ≥0) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hw : ∀ i, |center i| + |width i| ≤ 1)
    {ε p : ℝ} (hε : 0 < ε) (hp : 0 ≤ p)
    (hbox : 2 * (siteRadius : ℝ) ≤ Real.exp p)
    (hεp : ε⁻¹ ≤ Real.exp p) (hδp : (δ : ℝ)⁻¹ ≤ Real.exp p) :
    let radius : ℝ≥0 := allocatedRowSlicedSiteRadius rowSets
    let C : ℝ≥0 := Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound / (2 * radius)
    let Q := idealSiteLogBudget (Fintype.card (Σ a : LayerSamplerAxis I n, jets a.1)) (Fintype.card α) p
    let volume : ℝ := ∏ q : (Σ a : {a // ¬grid a}, jets a.val.1), R q.1.val.1
    ∃ k : ℕ, (k : ℝ) ≤ Real.exp (4 * Q + 8) ∧
      (Fintype.card (Finset α × LayerSamplerAxis I n → Fin k) : ℝ) ≤
        Real.exp ((Fintype.card (Finset α) * Fintype.card (LayerSamplerAxis I n) : ℕ) * (4 * Q + 8)) ∧
      ∃ (a : (Finset α × LayerSamplerAxis I n → Fin k) → ℂ)
        (f : (Finset α × LayerSamplerAxis I n → Fin k) → Finset α → (LayerSamplerAxis I n → ℝ) → ℂ),
        (∑ i, ‖a i‖) ≤ Real.exp ((Fintype.card (Finset α) * Fintype.card (LayerSamplerAxis I n) : ℕ) * (4 * Q + 8) + Q) ∧
        (∀ i s v, ‖f i s v‖ ≤ 1) ∧
        (∀ i s, LipschitzWith (⟨Real.exp (Fintype.card (LayerSamplerAxis I n) + 6 * Q + 12), Real.exp_nonneg _⟩ + C) (f i s)) ∧
        (∀ i s v, (∃ d, 2 * (radius : ℝ) < |v d|) → f i s v = 0) ∧
        ∀ z : AllocatedLongJetRows B U b S jets,
          ‖(volume : ℂ) * (allocatedRowSlicedIdeal B U b S rowSets δ center width (allocatedLongJetRealCoordinates B U b S z) : ℂ) -
            ∑ i, a i * ∏ s, f i s (allocatedRowIdealCoordinates B U b S rowSets z s)‖ ≤ ε ∧
          ‖(allocatedRowSlicedIdeal B U b S rowSets δ center width (allocatedLongJetRealCoordinates B U b S z) : ℂ) -
            (∑ i, a i * ∏ s, f i s (allocatedRowIdealCoordinates B U b S rowSets z s)) / (volume : ℂ)‖ ≤ ε / volume := by
  intro radius C Q volume
  obtain ⟨χ, hone, k, hk, hcard, a, f, ha, hf, hLf, hfsupport, herr⟩ :=
    exists_normalized_active_sliced_ideal_site_approximation (G := G) (Z := G × Option α) (B := B)
      (O := fun a : LayerSamplerAxis I n => jets a.1)
      hLayer grid (fun a => (Subtype.val : jets a.val.1 → Finset α)) center width δ hδ
      radius (allocatedRowSlicedSiteRadius_pos rowSets) hε hp hbox hεp hδp
  let alternateUniverse : Finset (Finset α × LayerSamplerAxis I n → Fin k) :=
    @Finset.univ _ (@Pi.instFintype (Finset α × LayerSamplerAxis I n) (fun _ => Fin k)
      (@instDecidableEqProd (Finset α) (LayerSamplerAxis I n) inferInstance
        (fun a b => Classical.propDecidable (a = b)))
      inferInstance (fun _ => Fin.fintype k))
  have huniv : (Finset.univ : Finset (Finset α × LayerSamplerAxis I n → Fin k)) =
      alternateUniverse := by
    ext i
    simp only [alternateUniverse, Finset.mem_univ]
  have hcard' : (Fintype.card (Finset α × LayerSamplerAxis I n → Fin k) : ℝ) ≤
      Real.exp ((Fintype.card (Finset α) * Fintype.card (LayerSamplerAxis I n) : ℕ) * (4 * Q + 8)) := by
    simpa only [Q, Fintype.card_eq_nat_card] using hcard
  refine ⟨k, hk, hcard', a, f, ?_, hf, ?_, hfsupport, ?_⟩
  · calc
      (∑ i, ‖a i‖) = alternateUniverse.sum (fun i => ‖a i‖) := by rw [huniv]
      _ ≤ _ := ha
  · simpa only [Q] using hLf
  · intro z
    refine allocatedRowSlicedIdealApproximation_error B U b S rowSets center width hR δ hδ hδ1 hw χ hone a f ε ?_ z
    intro v
    rw [huniv]
    exact herr v

end Erdos3.VectorPolynomial

end

end OAI

end

theorem solution.{u_1, u_2, u_3, u_4, u_5} : type_of% @OAI.Erdos3.VectorPolynomial.exists_allocated_row_sliced_ideal_site_approximation.{u_1, u_2, u_3, u_4, u_5} := @OAI.Erdos3.VectorPolynomial.exists_allocated_row_sliced_ideal_site_approximation.{u_1, u_2, u_3, u_4, u_5}
