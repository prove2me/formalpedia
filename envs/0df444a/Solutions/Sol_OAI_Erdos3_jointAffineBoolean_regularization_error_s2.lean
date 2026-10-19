-- Prove2me | solution 1 for OAI.Erdos3.jointAffineBoolean_regularization_error_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-17T10:50:41.544711+00:00
-- url     : https://prove2.me/submissions/493f0890-b469-43cd-bc38-9f859b5e5ee5

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B112
import Definitions.Def_OAIE3v2B113
import Theorems.Thm_OAI_Erdos3_imageTranslationBound_of_inverse_budget_s2
import Theorems.Thm_OAI_Erdos3_jointAffineBooleanGoodWeight_derivative_budget_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SmoothedImageTest
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem mappedTest_integrable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) [IsFiniteMeasure μ] (U : Ω → X) (hU : Measurable U)
    (φ : X → ℝ) (hφ : Measurable φ) (hbound : ∀ x, ‖φ x‖ ≤ 1) :
    Integrable (fun a => φ (U a)) μ :=
  (integrable_const (1 : ℝ)).mono' (hφ.comp hU).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun a => hbound (U a)))

theorem mappedTest_norm_le {Ω X : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (U : Ω → X) (φ : X → ℝ)
    (hbound : ∀ x, ‖φ x‖ ≤ 1) : ‖mappedTest μ U φ‖ ≤ μ.real Set.univ := by
  have h := norm_integral_le_of_norm_le (integrable_const (1 : ℝ) (μ := μ))
    (Filter.Eventually.of_forall (fun a => hbound (U a)))
  simp only [integral_const, smul_eq_mul, mul_one] at h
  exact h

theorem mappedTest_shift_measurable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [SFinite μ] (U : Ω → (ι → ℝ)) (hU : Measurable U)
    (φ : (ι → ℝ) → ℝ) (hφ : Measurable φ) :
    Measurable (fun z => mappedTest μ U (fun x => φ (x + z))) := by
  have hm : Measurable (fun p : Ω × (ι → ℝ) => φ (U p.1 + p.2)) :=
    hφ.comp ((hU.comp measurable_fst).add measurable_snd)
  exact hm.stronglyMeasurable.integral_prod_left'.measurable

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CutoffImageTest
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem cutoff_integrable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (w : Ω → ℝ) (hw : Measurable w) (hbound : ∀ a, w a ∈ Set.Icc (0 : ℝ) 1) : Integrable w μ := by
  apply (integrable_const (1 : ℝ)).mono' hw.aestronglyMeasurable
  filter_upwards [] with a
  rw [Real.norm_of_nonneg (hbound a).1]
  exact (hbound a).2

theorem mappedTest_cutoff_error {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) [IsFiniteMeasure μ] (w : Ω → ℝ) (hw : Measurable w)
    (hbound : ∀ a, w a ∈ Set.Icc (0 : ℝ) 1)
    (U : Ω → X) (hU : Measurable U) (φ : X → ℝ) (hφ : Measurable φ)
    (hφbound : ∀ x, ‖φ x‖ ≤ 1) :
    |mappedTest μ U φ - mappedTest (realDensityMeasure μ w) U φ| ≤ ∫ a, 1 - w a ∂μ := by
  have hwi := cutoff_integrable μ w hw hbound
  have hgi := mappedTest_integrable μ U hU φ hφ hφbound
  have hwgi : Integrable (fun a => w a * φ (U a)) μ :=
    hwi.mul_bdd (hφ.comp hU).aestronglyMeasurable (Filter.Eventually.of_forall (fun a => hφbound _))
  change |(∫ a, φ (U a) ∂μ) - ∫ a, φ (U a) ∂realDensityMeasure μ w| ≤ _
  rw [realDensityMeasure_integral μ w hw (fun a => (hbound a).1), ← integral_sub hgi hwgi]
  have hrem : Integrable (fun a => 1 - w a) μ := (integrable_const (1 : ℝ)).sub hwi
  have hp (a : Ω) : ‖φ (U a) - w a * φ (U a)‖ ≤ 1 - w a := by
    rw [show φ (U a) - w a * φ (U a) = (1 - w a) * φ (U a) by ring, norm_mul,
      Real.norm_of_nonneg (sub_nonneg.mpr (hbound a).2)]
    exact (mul_le_mul_of_nonneg_left (hφbound _) (sub_nonneg.mpr (hbound a).2)).trans_eq (mul_one _)
  have h := norm_integral_le_of_norm_le hrem (Filter.Eventually.of_forall hp)
  rw [Real.norm_eq_abs] at h
  exact h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ProductCutoffBudget
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem product_cutoff_range {ι : Type*} [Fintype ι] (f : ι → ℝ)
    (hf : ∀ i, f i ∈ Set.Icc (0 : ℝ) 1) : (∏ i, f i) ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨Finset.prod_nonneg (fun i _ => (hf i).1),
    Finset.prod_le_one (fun i _ => (hf i).1) (fun i _ => (hf i).2)⟩

theorem product_cutoff_tsupport_subset {ι E : Type*} [Fintype ι] [TopologicalSpace E]
    (f : ι → E → ℝ) (i : ι) : tsupport (fun x => ∏ j, f j x) ⊆ tsupport (f i) := by
  classical
  apply closure_mono
  intro x hx
  change f i x ≠ 0
  intro hz
  exact hx (Finset.prod_eq_zero (Finset.mem_univ i) hz)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SmoothSublevelCutoff
namespace OAI

section

namespace Erdos3

open scoped NNReal ContDiff

theorem sublevelCutoff_range {E : Type*} (ψ : ℝ → ℝ)
    (hψ : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1) (r : ℝ) (d : E → ℝ) (x : E) :
    sublevelCutoff ψ r d x ∈ Set.Icc (0 : ℝ) 1 := hψ _

theorem sublevelCutoff_eq_zero {E : Type*} (ψ : ℝ → ℝ)
    (hψ : ∀ t, |t| ≤ 1 → ψ t = 0) {r : ℝ} (hr : 0 < r)
    (d : E → ℝ) {x : E} (hx : |d x| ≤ r) : sublevelCutoff ψ r d x = 0 := by
  apply hψ
  rw [abs_div, abs_of_pos hr]
  exact (div_le_one hr).mpr hx

theorem sublevelCutoff_tsupport_subset {E : Type*} [TopologicalSpace E]
    (ψ : ℝ → ℝ) (hψ : ∀ t, |t| ≤ 1 → ψ t = 0) {r : ℝ} (hr : 0 < r)
    (d : E → ℝ) (hd : Continuous d) :
    tsupport (sublevelCutoff ψ r d) ⊆ {x | r ≤ |d x|} := by
  apply closure_minimal _ (isClosed_le continuous_const hd.abs)
  intro x hx
  change r ≤ |d x|
  by_contra! h
  exact hx (sublevelCutoff_eq_zero ψ hψ hr d h.le)

theorem contDiff_sublevelCutoff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (r : ℝ) (d : E → ℝ)
    (hd : ContDiff ℝ ∞ d) : ContDiff ℝ ∞ (sublevelCutoff ψ r d) :=
  hψ.comp (hd.div_const r)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SigmaAxisCoordinates
namespace OAI

section

namespace Erdos3

open MeasureTheory

variable {D : Type*} [Fintype D] (I : D → Type*) [∀ d, Fintype (I d)]

theorem sigmaAxisCoordinates_symm_measurePreserving :
    MeasurePreserving (sigmaAxisCoordinates I).symm volume volume := by
  refine ⟨(sigmaAxisCoordinates I).symm.continuous.measurable, ?_⟩
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply (sigmaAxisCoordinates I).symm.continuous.measurable (MeasurableSet.univ_pi hs)]
  have he : (sigmaAxisCoordinates I).symm ⁻¹' Set.univ.pi s =
      Set.univ.pi (fun d => Set.univ.pi (fun i : I d => s ⟨d, i⟩)) := by
    ext x
    constructor
    · intro hx d _ i _
      exact hx ⟨d, i⟩ (Set.mem_univ _)
    · intro hx t _
      exact hx t.1 (Set.mem_univ _) t.2 (Set.mem_univ _)
  rw [he, volume_pi_pi]
  simp only [volume_pi_pi, Fintype.prod_sigma]

theorem sigmaAxisCoordinates_measurePreserving :
    MeasurePreserving (sigmaAxisCoordinates I) volume volume :=
  (sigmaAxisCoordinates_symm_measurePreserving I).symm
    (sigmaAxisCoordinates I).symm.toHomeomorph.toMeasurableEquiv

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

theorem tensorCutoffWeight_contDiff {ι : Type*} {E : ι → Type*} [Fintype ι]
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    (w : ∀ i, E i → ℝ) (hw : ∀ i, ContDiff ℝ 1 (w i)) :
    ContDiff ℝ 1 (tensorCutoffWeight w) :=
  contDiff_prod (fun i _ => (hw i).comp
    (ContinuousLinearMap.proj i : (∀ j, E j) →L[ℝ] E i).contDiff)

theorem tensorCutoffWeight_abs_mass {ι : Type*} {E : ι → Type*} [Fintype ι] [∀ i, MeasureSpace (E i)]
    [∀ i, SigmaFinite (volume : Measure (E i))] (w : ∀ i, E i → ℝ) :
    (∫ x, |tensorCutoffWeight w x|) = ∏ i, ∫ y, |w i y| := by
  simp only [tensorCutoffWeight, Finset.abs_prod]
  exact integral_fintype_prod_volume_eq_prod (fun i y => |w i y|)

theorem tensorCutoffWeight_abs_mass_le_one {ι : Type*} {E : ι → Type*} [Fintype ι] [∀ i, MeasureSpace (E i)]
    [∀ i, SigmaFinite (volume : Measure (E i))] (w : ∀ i, E i → ℝ)
    (hw : ∀ i, (∫ y, |w i y|) ≤ 1) : (∫ x, |tensorCutoffWeight w x|) ≤ 1 := by
  rw [tensorCutoffWeight_abs_mass]
  exact Finset.prod_le_one (fun i _ => integral_nonneg (fun y => abs_nonneg _)) (fun i _ => hw i)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {D : Type*} [Fintype D] {I : D → Type*} [∀ d, Fintype (I d)]

theorem sigmaAxisWeight_contDiff (w : ∀ d, (I d → ℝ) → ℝ)
    (hw : ∀ d, ContDiff ℝ 1 (w d)) : ContDiff ℝ 1 (sigmaAxisWeight w) :=
  (tensorCutoffWeight_contDiff w hw).comp (sigmaAxisCoordinates I).contDiff

omit [∀ d, Fintype (I d)] in
theorem sigmaAxisWeight_compact (w : ∀ d, (I d → ℝ) → ℝ)
    (hw : ∀ d, HasCompactSupport (w d)) : HasCompactSupport (sigmaAxisWeight w) :=
  (tensorCutoffWeight_compact w hw).comp_homeomorph (sigmaAxisCoordinates I).toHomeomorph

omit [∀ d, Fintype (I d)] in
theorem sigmaAxisWeight_tsupport (w : ∀ d, (I d → ℝ) → ℝ)
    {x : (Σ d, I d) → ℝ} (hx : x ∈ tsupport (sigmaAxisWeight w)) (d : D) :
    sigmaAxisProjection I d x ∈ tsupport (w d) := by
  have he : tsupport (sigmaAxisWeight w) =
      (sigmaAxisCoordinates I) ⁻¹' tsupport (tensorCutoffWeight w) :=
    tsupport_comp_eq_preimage _ (sigmaAxisCoordinates I).toHomeomorph
  rw [he] at hx
  exact tensorCutoffWeight_tsupport w hx d

omit [∀ d, Fintype (I d)] in
theorem sigmaAxisWeight_nonneg (w : ∀ d, (I d → ℝ) → ℝ)
    (hw : ∀ d y, 0 ≤ w d y) (x : (Σ d, I d) → ℝ) : 0 ≤ sigmaAxisWeight w x :=
  tensorCutoffWeight_nonneg w hw _

theorem sigmaAxisWeight_integral (w : ∀ d, (I d → ℝ) → ℝ) :
    (∫ x, sigmaAxisWeight w x) = ∏ d, ∫ y, w d y := by
  calc
    _ = ∫ x, tensorCutoffWeight w x :=
      (sigmaAxisCoordinates_measurePreserving I).integral_comp
        (sigmaAxisCoordinates I).toHomeomorph.toMeasurableEquiv.measurableEmbedding _
    _ = _ := tensorCutoffWeight_integral w

theorem sigmaAxisWeight_abs_mass (w : ∀ d, (I d → ℝ) → ℝ) :
    (∫ x, |sigmaAxisWeight w x|) = ∏ d, ∫ y, |w d y| := by
  have he (x : (Σ d, I d) → ℝ) : |sigmaAxisWeight w x| =
      sigmaAxisWeight (fun d y => |w d y|) x := by
    simp only [sigmaAxisWeight, tensorCutoffWeight, Finset.abs_prod]
  simp_rw [he]
  exact sigmaAxisWeight_integral _

theorem sigmaAxisWeight_abs_mass_le_one (w : ∀ d, (I d → ℝ) → ℝ)
    (hm : ∀ d, (∫ y, |w d y|) ≤ 1) : (∫ x, |sigmaAxisWeight w x|) ≤ 1 := by
  rw [sigmaAxisWeight_abs_mass]
  exact Finset.prod_le_one (fun d _ => integral_nonneg (fun _ => abs_nonneg _)) (fun d _ => hm d)

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.OperatorCoordinateBound
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem clm_norm_le_card_mul_of_entries {I O : Type*}
    [Fintype I] [DecidableEq I] [Fintype O]
    (A : (I → ℝ) →L[ℝ] (O → ℝ)) {M : ℝ} (hM : 0 ≤ M)
    (hA : ∀ i o, |A (Pi.single i 1) o| ≤ M) : ‖A‖ ≤ Fintype.card I * M := by
  apply clm_norm_le_card_mul_of_basis A hM
  intro i
  apply (pi_norm_le_iff_of_nonneg hM).mpr
  intro o
  simpa only [Real.norm_eq_abs] using hA i o

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

theorem pderiv_prod_zero {α ι : Type*} (j : α) (s : Finset ι)
    (p : ι → MvPolynomial α ℝ) (hp : ∀ i ∈ s, MvPolynomial.pderiv j (p i) = 0) :
    MvPolynomial.pderiv j (∏ i ∈ s, p i) = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, MvPolynomial.pderiv_mul, hp i (Finset.mem_insert_self i s),
      ih (fun k hk => hp k (Finset.mem_insert_of_mem hk))]
    simp

theorem pderiv_prod_one_active {α ι : Type*} [DecidableEq ι] (j : α) (s : Finset ι)
    (p : ι → MvPolynomial α ℝ) (i : ι) (hi : i ∈ s)
    (hp : ∀ k ∈ s.erase i, MvPolynomial.pderiv j (p k) = 0) :
    MvPolynomial.pderiv j (∏ k ∈ s, p k) =
      MvPolynomial.pderiv j (p i) * ∏ k ∈ s.erase i, p k := by
  rw [← Finset.mul_prod_erase s p hi, MvPolynomial.pderiv_mul, pderiv_prod_zero j _ p hp]
  simp

theorem pderiv_booleanCoefficient {α ι : Type*} [DecidableEq α]
    (j : ι) (f : Finset α → MvPolynomial ι ℝ) (s : Finset α) :
    MvPolynomial.pderiv j (booleanCoefficient f s) =
      booleanCoefficient (fun t => MvPolynomial.pderiv j (f t)) s := by
  classical
  unfold booleanCoefficient
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro t _
  have hc : (-1 : MvPolynomial ι ℝ) ^ (s \ t).card =
      MvPolynomial.C ((-1 : ℝ) ^ (s \ t).card) := by simp
  rw [hc, MvPolynomial.pderiv_C_mul]

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

theorem booleanAffinePolynomial_pderiv {B F α : Type*} [Fintype α] [DecidableEq α]
    [DecidableEq B] [DecidableEq F]
    (b b₀ : B) (v v₀ : F) (r : Option α) (t : Finset α) :
    MvPolynomial.pderiv (b₀, v₀, r) (booleanAffinePolynomial b v t) =
      if b = b₀ ∧ v = v₀ then MvPolynomial.C (booleanFeature r t : ℝ) else 0 := by
  classical
  simp only [booleanAffinePolynomial, map_sum, MvPolynomial.pderiv_C_mul, MvPolynomial.pderiv_X,
    Pi.single_apply, Prod.mk.injEq, mul_ite, mul_one, mul_zero]
  by_cases hb : b = b₀ <;> by_cases hv : v = v₀
  · subst b
    subst v
    simp
  · simp [hb, hv]
  · simp [hb, hv]
  · simp [hb, hv]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem mvPolynomial_prod_pderiv_eval_abs_le {I K : Type*} (s : Finset K)
    (p : K → MvPolynomial I ℝ) (j : I) (a : I → ℝ) {L : ℝ} (hL : 1 ≤ L)
    (hp : ∀ k ∈ s, |MvPolynomial.eval a (p k)| ≤ L)
    (hd : ∀ k ∈ s, |MvPolynomial.eval a (MvPolynomial.pderiv j (p k))| ≤ 1) :
    |MvPolynomial.eval a (MvPolynomial.pderiv j (∏ k ∈ s, p k))| ≤ s.card * L ^ s.card := by
  have h := mvPolynomial_prod_pderiv_eval_abs_le_of_bound s p j a hL zero_le_one hp hd
  simpa only [mul_one] using h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.BooleanProductSampler
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {B F α : Type*} [Fintype B] [Fintype F] [Fintype α]
  [DecidableEq B] [DecidableEq F] [DecidableEq α]

omit [Fintype B] in
theorem booleanBlockPolynomial_pderiv (b b₀ : B) (v₀ : F) (r : Option α) (t : Finset α) :
    MvPolynomial.pderiv (b₀, v₀, r) (booleanBlockPolynomial (F := F) b t) =
      if b = b₀ then MvPolynomial.C (booleanFeature r t : ℝ) *
        ∏ k ∈ Finset.univ.erase v₀, booleanAffinePolynomial b k t else 0 := by
  by_cases hb : b = b₀
  · subst b
    rw [if_pos rfl, booleanBlockPolynomial, pderiv_prod_one_active
      (b₀, v₀, r) Finset.univ (fun k => booleanAffinePolynomial b₀ k t) v₀ (Finset.mem_univ _)]
    · simp only [booleanAffinePolynomial_pderiv, and_self, ite_true]
    · intro k hk
      simp only [booleanAffinePolynomial_pderiv, true_and]
      exact if_neg (Finset.ne_of_mem_erase hk)
  · rw [if_neg hb, booleanBlockPolynomial]
    apply pderiv_prod_zero
    intro k _
    simp only [booleanAffinePolynomial_pderiv, hb, false_and, ite_false]

theorem booleanSamplerPolynomial_pderiv (c : B → ℝ) (s : Finset α) (b₀ : B) (v₀ : F) (r : Option α) :
    MvPolynomial.pderiv (b₀, v₀, r) (booleanSamplerPolynomial (F := F) c s) =
      booleanSelectedColumn c b₀ v₀ r s := by
  rw [booleanSamplerPolynomial, pderiv_booleanCoefficient]
  have hinner (t : Finset α) :
      MvPolynomial.pderiv (b₀, v₀, r)
        (∑ b : B, MvPolynomial.C (c b) * booleanBlockPolynomial (F := F) b t) =
      MvPolynomial.C (c b₀) * (MvPolynomial.C (booleanFeature r t : ℝ) *
        ∏ k ∈ Finset.univ.erase v₀, booleanAffinePolynomial b₀ k t) := by
    simp only [map_sum, MvPolynomial.pderiv_C_mul, booleanBlockPolynomial_pderiv, mul_ite, mul_zero]
    simp
  simp_rw [hinner]
  rw [booleanCoefficient_const_mul]
  rfl

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
theorem booleanSamplerMap_contDiff [Fintype O] (c : B → ℝ) (sets : O → Finset α) :
    ContDiff ℝ ∞ (booleanSamplerMap (F := F) c sets) :=
  contDiff_pi.mpr (fun o => mvPolynomial_contDiff_eval (booleanSamplerPolynomial c (sets o)))

theorem booleanSelectedMinor_fderiv [Fintype O] [DecidableEq O]
    (c : B → ℝ) (sets : O → Finset α) (block : O → B) (v : F) (r : O → Option α)
    (a : BlockParameter B F α → ℝ) (row col : O) :
    (fderiv ℝ (booleanSamplerMap (F := F) c sets) a (Pi.single (block col, v, r col) 1)) row =
      MvPolynomial.eval a (booleanSelectedMinor c sets block v r row col) := by
  have hd := (booleanSamplerMap_contDiff (F := F) c sets).differentiable (by norm_num)
  have h := mvPolynomial_fderiv_coordinate (booleanSamplerPolynomial (F := F) c (sets row)) a
    (block col, v, r col)
  change fderiv ℝ (fun x => booleanSamplerMap c sets x row) a (Pi.single (block col, v, r col) 1) = _ at h
  rw [fderiv_apply (hd a) row] at h
  exact h

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

theorem booleanCoefficient_abs_le {α : Type*} [DecidableEq α]
    (f : Finset α → ℝ) (s : Finset α) {M : ℝ}
    (hf : ∀ t ∈ s.powerset, |f t| ≤ M) :
    |booleanCoefficient f s| ≤ (2 : ℝ) ^ s.card * M := by
  unfold booleanCoefficient
  calc
    _ ≤ ∑ t ∈ s.powerset, |(-1 : ℝ) ^ (s \ t).card * f t| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _t ∈ s.powerset, M := by
      apply Finset.sum_le_sum
      intro t ht
      simpa only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul] using hf t ht
    _ = _ := by simp

theorem booleanAffinePolynomial_eval_abs_le {B F α : Type*} [Fintype α] [DecidableEq α]
    (a : BlockParameter B F α → ℝ) (b : B) (v : F) (t : Finset α) {R : ℝ}
    (ha : ∀ j, |a j| ≤ R) :
    |MvPolynomial.eval a (booleanAffinePolynomial b v t)| ≤ ((Fintype.card α : ℝ) + 1) * R := by
  rw [booleanAffinePolynomial_eval]
  calc
    _ ≤ ∑ r : Option α, |(booleanFeature r t : ℝ) * a (b, v, r)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _r : Option α, R := by
      apply Finset.sum_le_sum
      intro r _
      rw [abs_mul]
      simpa only [one_mul] using mul_le_mul (booleanFeature_abs_le_one r t)
        (ha (b, v, r)) (abs_nonneg _) zero_le_one
    _ = _ := by simp

theorem booleanSelectedColumn_eval_abs_le {B F α : Type*}
    [Fintype F] [Fintype α] [DecidableEq F] [DecidableEq α]
    (c : B → ℝ) (b : B) (v : F) (r : Option α) (s : Finset α)
    (a : BlockParameter B F α → ℝ) {R : ℝ} (ha : ∀ j, |a j| ≤ R) :
    |MvPolynomial.eval a (booleanSelectedColumn c b v r s)| ≤
      |c b| * ((2 : ℝ) ^ s.card *
        (((Fintype.card α : ℝ) + 1) * R) ^ (Fintype.card F - 1)) := by
  rw [booleanSelectedColumn, map_mul, MvPolynomial.eval_C, abs_mul, booleanCoefficient_map]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  apply booleanCoefficient_abs_le
  intro t _
  simp only [map_mul, MvPolynomial.eval_C, map_prod, abs_mul, Finset.abs_prod]
  calc
    _ ≤ 1 * ∏ _k ∈ Finset.univ.erase v, (((Fintype.card α : ℝ) + 1) * R) := by
      apply mul_le_mul (booleanFeature_abs_le_one r t)
      · exact Finset.prod_le_prod (fun _ _ => abs_nonneg _)
          (fun k _ => booleanAffinePolynomial_eval_abs_le a b k t ha)
      · exact Finset.prod_nonneg (fun _ _ => abs_nonneg _)
      · exact zero_le_one
    _ = _ := by simp

theorem productMinorEntryBound_nonneg (q h : ℕ) {C R : ℝ} (hC : 0 ≤ C) (hR : 0 ≤ R) :
    0 ≤ productMinorEntryBound q h C R := by
  unfold productMinorEntryBound
  positivity

theorem booleanSelectedMinor_entry_bound {B O α : Type*}
    [Fintype B] [Fintype α] [DecidableEq B] [DecidableEq α]
    (c : B → ℝ) (sets : O → Finset α) (block : O → B) {h : ℕ}
    (v : Fin h) (r : O → Option α) (hcard : ∀ o, (sets o).card ≤ h)
    (a : BlockParameter B (Fin h) α → ℝ) {C R : ℝ} (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hc : ∀ o, |c (block o)| ≤ C) (ha : ∀ j, |a j| ≤ R) (row col : O) :
    |MvPolynomial.eval a (booleanSelectedMinor c sets block v r row col)| ≤
      productMinorEntryBound (Fintype.card α) h C R := by
  unfold booleanSelectedMinor
  rw [booleanSamplerPolynomial_pderiv]
  have hcol := booleanSelectedColumn_eval_abs_le c (block col) v (r col) (sets row) a ha
  simp only [Fintype.card_fin] at hcol
  have htwo : (2 : ℝ) ^ (sets row).card ≤ 2 ^ h :=
    pow_le_pow_right₀ (by norm_num) (hcard row)
  have hpower : 0 ≤ (((Fintype.card α : ℝ) + 1) * R) ^ (h - 1) := by positivity
  exact hcol.trans (mul_le_mul (hc col) (mul_le_mul_of_nonneg_right htwo hpower)
    (mul_nonneg (by positivity) hpower) hC)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem booleanAffinePolynomial_pderiv_eval_abs_le {B F α : Type*}
    [Fintype α] [DecidableEq B] [DecidableEq F] [DecidableEq α]
    (a : BlockParameter B F α → ℝ) (b : B) (v : F) (t : Finset α)
    (j : BlockParameter B F α) :
    |MvPolynomial.eval a (MvPolynomial.pderiv j (booleanAffinePolynomial b v t))| ≤ 1 := by
  rcases j with ⟨b₀, v₀, r⟩
  rw [booleanAffinePolynomial_pderiv]
  split_ifs
  · simpa only [MvPolynomial.eval_C] using booleanFeature_abs_le_one r t
  · simp

theorem booleanSelectedColumn_pderiv_eval_abs_le {B F α : Type*}
    [Fintype F] [Fintype α] [DecidableEq B] [DecidableEq F] [DecidableEq α]
    (c : B → ℝ) (b : B) (v : F) (r : Option α) (s : Finset α)
    (a : BlockParameter B F α → ℝ) {R : ℝ} (hR : 1 ≤ R) (ha : ∀ j, |a j| ≤ R)
    (j : BlockParameter B F α) :
    |MvPolynomial.eval a (MvPolynomial.pderiv j (booleanSelectedColumn c b v r s))| ≤
      |c b| * ((2 : ℝ) ^ s.card *
        (Fintype.card F * (((Fintype.card α : ℝ) + 1) * R) ^ Fintype.card F)) := by
  let L : ℝ := ((Fintype.card α : ℝ) + 1) * R
  have hL : 1 ≤ L := by
    dsimp [L]
    have hq : 0 ≤ (Fintype.card α : ℝ) := Nat.cast_nonneg _
    nlinarith [mul_nonneg hq (zero_le_one.trans hR)]
  rw [booleanSelectedColumn, MvPolynomial.pderiv_C_mul, map_mul, MvPolynomial.eval_C,
    abs_mul, pderiv_booleanCoefficient, booleanCoefficient_map]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  apply booleanCoefficient_abs_le
  intro t _
  rw [MvPolynomial.pderiv_C_mul, map_mul, MvPolynomial.eval_C, abs_mul]
  have hd := mvPolynomial_prod_pderiv_eval_abs_le (Finset.univ.erase v)
    (fun k => booleanAffinePolynomial b k t) j a hL
    (fun k _ => booleanAffinePolynomial_eval_abs_le a b k t ha)
    (fun k _ => booleanAffinePolynomial_pderiv_eval_abs_le a b k t j)
  have hn : (Finset.univ.erase v).card ≤ Fintype.card F :=
    (Finset.card_erase_le).trans_eq (Finset.card_univ)
  have hpow := pow_le_pow_right₀ hL hn
  calc
    _ ≤ 1 * ((Finset.univ.erase v).card * L ^ (Finset.univ.erase v).card) :=
      mul_le_mul (booleanFeature_abs_le_one r t) hd (abs_nonneg _) zero_le_one
    _ ≤ Fintype.card F * L ^ Fintype.card F := by
      rw [one_mul]
      exact mul_le_mul (Nat.cast_le.mpr hn) hpow (pow_nonneg (zero_le_one.trans hL) _) (by positivity)

theorem productMinorPartialBound_nonneg (q h : ℕ) {C R : ℝ} (hC : 0 ≤ C) (hR : 0 ≤ R) :
    0 ≤ productMinorPartialBound q h C R := by
  unfold productMinorPartialBound
  positivity

theorem booleanSelectedMinor_partial_bound {B O α : Type*}
    [Fintype B] [Fintype α] [DecidableEq B] [DecidableEq α]
    (c : B → ℝ) (sets : O → Finset α) (block : O → B) {h : ℕ}
    (v : Fin h) (r : O → Option α) (hcard : ∀ o, (sets o).card ≤ h)
    (a : BlockParameter B (Fin h) α → ℝ) {C R : ℝ} (hC : 0 ≤ C) (hR : 1 ≤ R)
    (hc : ∀ o, |c (block o)| ≤ C) (ha : ∀ j, |a j| ≤ R)
    (row col : O) (j : BlockParameter B (Fin h) α) :
    |MvPolynomial.eval a (MvPolynomial.pderiv j (booleanSelectedMinor c sets block v r row col))| ≤
      productMinorPartialBound (Fintype.card α) h C R := by
  unfold booleanSelectedMinor
  rw [booleanSamplerPolynomial_pderiv]
  have hd := booleanSelectedColumn_pderiv_eval_abs_le c (block col) v (r col) (sets row) a hR ha j
  simp only [Fintype.card_fin] at hd
  have htwo : (2 : ℝ) ^ (sets row).card ≤ 2 ^ h :=
    pow_le_pow_right₀ (by norm_num) (hcard row)
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  have hpos : 0 ≤ (h : ℝ) * (((Fintype.card α : ℝ) + 1) * R) ^ h := by positivity
  exact hd.trans (mul_le_mul (hc col) (mul_le_mul_of_nonneg_right htwo hpos)
    (mul_nonneg (by positivity) hpos) hC)

end Erdos3

end

section

namespace Erdos3

open scoped ContDiff

theorem booleanMinorDeterminant_contDiff {B O F α : Type*}
    [Fintype B] [Fintype O] [Fintype F] [Fintype α]
    [DecidableEq B] [DecidableEq O] [DecidableEq F] [DecidableEq α]
    (c : B → ℝ) (sets : O → Finset α) (block : O → B) (v : F) (r : O → Option α) :
    ContDiff ℝ ∞ (booleanMinorDeterminant c sets block v r) := by
  change ContDiff ℝ ∞ (fun a => ((booleanSelectedMinor c sets block v r).map (MvPolynomial.eval a)).det)
  rw [polynomial_det_eval_function]
  exact mvPolynomial_contDiff_eval _

theorem productMinorDeterminantDerivativeBound_nonneg (n j q h : ℕ) {C R : ℝ}
    (hC : 0 ≤ C) (hR : 0 ≤ R) :
    0 ≤ productMinorDeterminantDerivativeBound n j q h C R := by
  have he := productMinorEntryBound_nonneg q h hC hR
  have hd := productMinorPartialBound_nonneg q h hC hR
  unfold productMinorDeterminantDerivativeBound
  positivity

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SmoothHalfspaceCutoff
namespace OAI

section

namespace Erdos3

open scoped NNReal ContDiff

theorem halfspaceCutoff_range {E : Type*} (r : ℝ) (d : E → ℝ) (x : E) :
    halfspaceCutoff r d x ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

theorem halfspaceCutoff_eq_zero {E : Type*} {r : ℝ} (hr : 0 < r)
    (d : E → ℝ) {x : E} (hx : d x ≤ r) : halfspaceCutoff r d x = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  exact sub_nonpos.mpr ((div_le_one hr).mpr hx)

theorem halfspaceCutoff_tsupport_subset {E : Type*} [TopologicalSpace E]
    {r : ℝ} (hr : 0 < r) (d : E → ℝ) (hd : Continuous d) :
    tsupport (halfspaceCutoff r d) ⊆ {x | r ≤ d x} := by
  apply closure_minimal _ (isClosed_le continuous_const hd)
  intro x hx
  change r ≤ d x
  by_contra! h
  exact hx (halfspaceCutoff_eq_zero hr d h.le)

theorem contDiff_halfspaceCutoff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r : ℝ) (d : E → ℝ) (hd : ContDiff ℝ ∞ d) : ContDiff ℝ ∞ (halfspaceCutoff r d) :=
  Real.smoothTransition.contDiff.comp ((hd.div_const r).sub contDiff_const)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ScalarCubeDomain
namespace OAI

section

namespace Erdos3

open scoped BigOperators ContDiff NNReal

theorem inequalityBoundaryCutoff_range {I E : Type*} [Fintype I]
    (r : I → ℝ) (d : I → E → ℝ) (x : E) :
    inequalityBoundaryCutoff r d x ∈ Set.Icc (0 : ℝ) 1 :=
  product_cutoff_range _ (fun i => halfspaceCutoff_range (r i) (d i) x)

theorem inequalityBoundaryCutoff_smooth {I E : Type*} [Fintype I]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (r : I → ℝ) (d : I → E → ℝ)
    (hd : ∀ i, ContDiff ℝ ∞ (d i)) : ContDiff ℝ ∞ (inequalityBoundaryCutoff r d) :=
  contDiff_prod (fun i _ => contDiff_halfspaceCutoff (r i) (d i) (hd i))

theorem inequalityBoundaryCutoff_tsupport_subset {I E : Type*} [Fintype I]
    [TopologicalSpace E] (r : I → ℝ) (hr : ∀ i, 0 < r i)
    (d : I → E → ℝ) (hd : ∀ i, Continuous (d i)) :
    tsupport (inequalityBoundaryCutoff r d) ⊆ {x | ∀ i, r i ≤ d i x} := by
  intro x hx i
  exact halfspaceCutoff_tsupport_subset (hr i) (d i) (hd i)
    (product_cutoff_tsupport_subset (fun j => halfspaceCutoff (r j) (d j)) i hx)

theorem inequalityBoundaryCutoff_tsupport_domain {I E : Type*} [Fintype I]
    [TopologicalSpace E] (r : I → ℝ) (hr : ∀ i, 0 < r i)
    (d : I → E → ℝ) (hd : ∀ i, Continuous (d i)) :
    tsupport (inequalityBoundaryCutoff r d) ⊆ positiveInequalityDomain d := by
  intro x hx i
  exact (hr i).trans_le (inequalityBoundaryCutoff_tsupport_subset r hr d hd hx i)

theorem inequalityBoundaryCutoff_compact {I E : Type*} [Fintype I]
    [MetricSpace E] [ProperSpace E] (r : I → ℝ) (hr : ∀ i, 0 < r i)
    (d : I → E → ℝ) (hd : ∀ i, Continuous (d i))
    (hbounded : Bornology.IsBounded (positiveInequalityDomain d)) :
    HasCompactSupport (inequalityBoundaryCutoff r d) := by
  apply Metric.isCompact_of_isClosed_isBounded (isClosed_tsupport _)
  exact hbounded.subset (inequalityBoundaryCutoff_tsupport_domain r hr d hd)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ScalarCubeBoundaryCost
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

theorem scalarCubeBoundaryCutoff_compact (α : Type*) [Fintype α] [DecidableEq α]
    {r : ℝ} (hr : 0 < r) :
    HasCompactSupport (inequalityBoundaryCutoff (fun _ : Bool × Finset α => r) scalarCubeFace) := by
  apply inequalityBoundaryCutoff_compact _ (fun _ => hr) _ (fun i => (scalarCubeFace_contDiff i).continuous)
  rw [positiveInequalityDomain_scalarCubeFace]
  exact scalarCubeDomain_isBounded α

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

theorem scalarCubeMeasure_integral {α : Type*} [Fintype α] [DecidableEq α]
    (f : (Option α → ℝ) → ℝ) :
    (∫ a, f a ∂scalarCubeMeasure α) = scalarCubeDomainDensity α * ∫ a in scalarCubeDomain α, f a := by
  rw [scalarCubeMeasure, integral_smul_measure, ENNReal.toReal_inv, smul_eq_mul]
  rfl

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

theorem scalarCubeProductMeasure_eq_smul_restrict (ι α : Type*) [Fintype ι] [Fintype α]
    [DecidableEq α] :
    scalarCubeProductMeasure ι α =
      (volume (scalarCubeDomain α))⁻¹ ^ Fintype.card ι •
        volume.restrict (scalarCubeProductDomain ι α) := by
  unfold scalarCubeProductMeasure
  apply Measure.pi_eq
  intro s hs
  rw [Measure.smul_apply, Measure.restrict_apply (MeasurableSet.univ_pi hs)]
  change _ * volume (Set.univ.pi s ∩ Set.univ.pi (fun _ : ι => scalarCubeDomain α)) = _
  rw [← Set.pi_inter_distrib, volume_pi_pi]
  simp only [scalarCubeMeasure, Measure.smul_apply, Measure.restrict_apply (hs _),
    smul_eq_mul, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]

theorem scalarCubeProductMeasure_integral {ι α : Type*} [Fintype ι] [Fintype α]
    [DecidableEq α] (f : (ι → Option α → ℝ) → ℝ) :
    (∫ x, f x ∂scalarCubeProductMeasure ι α) =
      scalarCubeDomainDensity α ^ Fintype.card ι *
        ∫ x in scalarCubeProductDomain ι α, f x := by
  rw [scalarCubeProductMeasure_eq_smul_restrict, integral_smul_measure,
    ENNReal.toReal_pow, ENNReal.toReal_inv, smul_eq_mul]
  rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProductCutoffLipschitz
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff BigOperators

theorem scalarCubeCutoffWeight_contDiff {α : Type*} [Fintype α] [DecidableEq α]
    (b : (Option α → ℝ) → ℝ) (hb : ContDiff ℝ 1 b) :
    ContDiff ℝ 1 (scalarCubeCutoffWeight b) := contDiff_const.mul hb

theorem scalarCubeCutoffWeight_compact {α : Type*} [Fintype α] [DecidableEq α]
    (b : (Option α → ℝ) → ℝ) (hb : HasCompactSupport b) :
    HasCompactSupport (scalarCubeCutoffWeight b) := hb.mul_left

theorem scalarCubeCutoffWeight_tsupport_subset {α : Type*} [Fintype α] [DecidableEq α]
    (b : (Option α → ℝ) → ℝ) : tsupport (scalarCubeCutoffWeight b) ⊆ tsupport b :=
  tsupport_mul_subset_right

theorem scalarCubeCutoffWeight_integral {α : Type*} [Fintype α] [DecidableEq α]
    (b : (Option α → ℝ) → ℝ) (hb : tsupport b ⊆ scalarCubeDomain α) :
    (∫ a, scalarCubeCutoffWeight b a) = ∫ a, b a ∂scalarCubeMeasure α := by
  rw [scalarCubeMeasure_integral]
  change (∫ a, scalarCubeDomainDensity α * b a) = _
  rw [integral_const_mul]
  congr 1
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro a ha
  exact image_eq_zero_of_notMem_tsupport (fun h => ha (hb h))

theorem scalarCubeCutoffWeight_abs_mass_le_one {α : Type*} [Fintype α] [DecidableEq α]
    (b : (Option α → ℝ) → ℝ) (hb : Measurable b) (hs : tsupport b ⊆ scalarCubeDomain α)
    (hrange : ∀ a, b a ∈ Set.Icc (0 : ℝ) 1) :
    (∫ a, |scalarCubeCutoffWeight b a|) ≤ 1 := by
  have heq : (fun a => |scalarCubeCutoffWeight b a|) = scalarCubeCutoffWeight b := by
    funext a
    exact abs_of_nonneg (mul_nonneg (scalarCubeDomainDensity_pos α).le (hrange a).1)
  rw [heq, scalarCubeCutoffWeight_integral b hs]
  have h := integral_mono (cutoff_integrable (scalarCubeMeasure α) b hb hrange)
    (integrable_const (1 : ℝ)) (fun a => (hrange a).2)
  simpa only [integral_const, probReal_univ, one_smul] using h

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

theorem scalarCubeBoundaryCutoff_tsupport_domain (α : Type*) [Fintype α] [DecidableEq α]
    {r : ℝ} (hr : 0 < r) :
    tsupport (inequalityBoundaryCutoff (fun _ : Bool × Finset α => r) scalarCubeFace) ⊆
      scalarCubeDomain α := by
  rw [← positiveInequalityDomain_scalarCubeFace α]
  exact inequalityBoundaryCutoff_tsupport_domain _ (fun _ => hr) _
    (fun i => (scalarCubeFace_contDiff i).continuous)

theorem scalarCubeBoundaryWeight_spec (α : Type*) [Fintype α] [DecidableEq α]
    {r : ℝ} (hr : 0 < r) :
    ContDiff ℝ 1 (scalarCubeBoundaryWeight α r) ∧ HasCompactSupport (scalarCubeBoundaryWeight α r) ∧
      tsupport (scalarCubeBoundaryWeight α r) ⊆ scalarCubeDomain α ∧
      (∀ a, 0 ≤ scalarCubeBoundaryWeight α r a) ∧ (∫ a, |scalarCubeBoundaryWeight α r a|) ≤ 1 := by
  let b := inequalityBoundaryCutoff (fun _ : Bool × Finset α => r) scalarCubeFace
  have hb : ContDiff ℝ 1 b :=
    (inequalityBoundaryCutoff_smooth _ _ scalarCubeFace_contDiff).of_le (by norm_num)
  have hs : tsupport b ⊆ scalarCubeDomain α := scalarCubeBoundaryCutoff_tsupport_domain α hr
  refine ⟨scalarCubeCutoffWeight_contDiff b hb,
    scalarCubeCutoffWeight_compact b (scalarCubeBoundaryCutoff_compact α hr),
    (scalarCubeCutoffWeight_tsupport_subset b).trans hs, ?_, ?_⟩
  · intro a
    exact mul_nonneg (scalarCubeDomainDensity_pos α).le (inequalityBoundaryCutoff_range _ _ a).1
  · exact scalarCubeCutoffWeight_abs_mass_le_one b hb.continuous.measurable hs
      (inequalityBoundaryCutoff_range _ _)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

theorem scalarCubeProductWeight_spec {ι α : Type*} [Fintype ι] [Fintype α]
    [DecidableEq α] (r : ι → ℝ) (hr : ∀ i, 0 < r i) :
    ContDiff ℝ 1 (scalarCubeProductWeight α r) ∧
      HasCompactSupport (scalarCubeProductWeight α r) ∧
      tsupport (scalarCubeProductWeight α r) ⊆ scalarCubeProductDomain ι α ∧
      (∀ x, 0 ≤ scalarCubeProductWeight α r x) ∧
      (∫ x, |scalarCubeProductWeight α r x|) ≤ 1 := by
  have h := fun i => scalarCubeBoundaryWeight_spec α (hr i)
  refine ⟨tensorCutoffWeight_contDiff _ (fun i => (h i).1),
    tensorCutoffWeight_compact _ (fun i => (h i).2.1), ?_,
    tensorCutoffWeight_nonneg _ (fun i => (h i).2.2.2.1),
    tensorCutoffWeight_abs_mass_le_one _ (fun i => (h i).2.2.2.2)⟩
  intro x hx i _
  exact (h i).2.2.1 (tensorCutoffWeight_tsupport _ hx i)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators ContDiff

theorem scalarCubeProductCutoff_range {ι α : Type*} [Fintype ι] [Fintype α]
    [DecidableEq α] (r : ι → ℝ) (x : ι → Option α → ℝ) :
    scalarCubeProductCutoff α r x ∈ Set.Icc (0 : ℝ) 1 :=
  product_cutoff_range _ (fun i => inequalityBoundaryCutoff_range _ _ (x i))

theorem scalarCubeProductCutoff_smooth {ι α : Type*} [Fintype ι] [Fintype α]
    [DecidableEq α] (r : ι → ℝ) : ContDiff ℝ ∞ (scalarCubeProductCutoff α r) :=
  contDiff_prod (fun i _ => (inequalityBoundaryCutoff_smooth _ _ scalarCubeFace_contDiff).comp
    (contDiff_apply ℝ (Option α → ℝ) i))

theorem scalarCubeProductCutoff_tsupport {ι α : Type*} [Fintype ι] [Fintype α]
    [DecidableEq α] (r : ι → ℝ) (hr : ∀ i, 0 < r i) :
    tsupport (scalarCubeProductCutoff α r) ⊆ scalarCubeProductDomain ι α := by
  intro x hx i _
  exact scalarCubeBoundaryCutoff_tsupport_domain α (hr i) (tensorCutoffWeight_tsupport _ hx i)

theorem scalarCubeProductWeight_eq_mul {ι α : Type*} [Fintype ι] [Fintype α]
    [DecidableEq α] (r : ι → ℝ) (x : ι → Option α → ℝ) :
    scalarCubeProductWeight α r x =
      scalarCubeDomainDensity α ^ Fintype.card ι * scalarCubeProductCutoff α r x := by
  simp only [scalarCubeProductWeight, scalarCubeBoundaryWeight, scalarCubeCutoffWeight,
    tensorCutoffWeight, scalarCubeProductCutoff, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ]

theorem scalarCubeProductWeight_integral_test {ι α : Type*} [Fintype ι] [Fintype α]
    [DecidableEq α] (r : ι → ℝ) (hr : ∀ i, 0 < r i) (f : (ι → Option α → ℝ) → ℝ) :
    (∫ x, scalarCubeProductWeight α r x * f x) =
      ∫ x, scalarCubeProductCutoff α r x * f x ∂scalarCubeProductMeasure ι α := by
  simp_rw [scalarCubeProductWeight_eq_mul, mul_assoc]
  rw [integral_const_mul, scalarCubeProductMeasure_integral]
  congr 1
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  have hz : scalarCubeProductCutoff α r x = 0 := image_eq_zero_of_notMem_tsupport
    (fun h => hx (scalarCubeProductCutoff_tsupport r hr h))
  rw [hz, zero_mul]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoordinateInjection
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem coordinateInjection_apply {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (f : ι → κ) (x : ι → ℝ) :
    coordinateInjection f x = ∑ i, Pi.single (f i) (x i) := by
  simp only [coordinateInjection, sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.single_apply, ContinuousLinearMap.proj_apply]

theorem coordinateInjection_at_image {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (f : ι → κ) (hf : Function.Injective f) (x : ι → ℝ) (i : ι) :
    coordinateInjection f x (f i) = x i := by
  classical
  simp only [coordinateInjection_apply, Finset.sum_apply, Pi.single_apply]
  simp [hf.eq_iff]

theorem coordinateInjection_off_image {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (f : ι → κ) (x : ι → ℝ) (j : κ) (hj : ∀ i, f i ≠ j) :
    coordinateInjection f x j = 0 := by
  have hji : ∀ i, j ≠ f i := fun i => (hj i).symm
  simp only [coordinateInjection_apply, Finset.sum_apply, Pi.single_apply, hji, ite_false,
    Finset.sum_const_zero]

theorem coordinateInjection_norm_le {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (f : ι → κ) (hf : Function.Injective f) : ‖coordinateInjection f‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [one_mul]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr
  intro j
  by_cases hj : ∃ i, f i = j
  · obtain ⟨i, rfl⟩ := hj
    rw [coordinateInjection_at_image f hf]
    exact norm_le_pi_norm x i
  · rw [coordinateInjection_off_image f x j (not_exists.mp hj), norm_zero]
    exact norm_nonneg x

theorem coordinateInjection_single {ι κ : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq κ]
    (f : ι → κ) (i : ι) :
    coordinateInjection f (Pi.single i 1) = Pi.single (f i) 1 := by
  rw [coordinateInjection_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [hji]
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.SelectedCoordinateMatrix
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem clm_coordinateInjection_matrix {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq κ]
    (A : (κ → ℝ) →L[ℝ] (ι → ℝ)) (f : ι → κ) :
    A.comp (coordinateInjection f) =
      matrixSupCLM (fun row col => A (Pi.single (f col) 1) row) := by
  ext x row
  change A (coordinateInjection f x) row = _
  rw [coordinateInjection_apply, map_sum, Finset.sum_apply]
  change (∑ i, A (Pi.single (f i) (x i)) row) = ∑ i, A (Pi.single (f i) 1) row * x i
  apply Finset.sum_congr rfl
  intro i _
  have hs : Pi.single (f i) (x i) = (x i) • (Pi.single (f i) (1 : ℝ) : κ → ℝ) := by
    rw [← Pi.single_smul]
    simp
  rw [hs, map_smul]
  simp only [Pi.smul_apply, smul_eq_mul, mul_comm]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineSliceC2Difference
namespace OAI

section

namespace Erdos3

variable {E X Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem affineSlice_fderiv (F : X → Y) (c : X) (J : E →L[ℝ] X) (x : E)
    (hF : DifferentiableAt ℝ F (c + J x)) :
    fderiv ℝ (fun y => F (c + J y)) x = (fderiv ℝ F (c + J x)).comp J := by
  exact (hF.hasFDerivAt.comp x (J.hasFDerivAt.const_add c)).fderiv

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialParameterContinuity
namespace OAI

section

namespace Erdos3

theorem polynomialOperator_fderiv_entry {I J O : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype O] [DecidableEq O]
    (A : (I → ℝ) → (J → ℝ) →L[ℝ] (O → ℝ)) (p : Matrix O J (MvPolynomial I ℝ))
    (hentry : ∀ y row col, A y (Pi.single col 1) row = MvPolynomial.eval y (p row col))
    (x : I → ℝ) (hA : DifferentiableAt ℝ A x) (j : I) (row : O) (col : J) :
    (fderiv ℝ A x (Pi.single j 1)) (Pi.single col 1) row =
      MvPolynomial.eval x (MvPolynomial.pderiv j (p row col)) := by
  have hscalar : (fun y => A y (Pi.single col 1) row) =
      (fun y => MvPolynomial.eval y (p row col)) := funext (fun y => hentry y row col)
  have hB : DifferentiableAt ℝ (fun y => A y (Pi.single col 1)) x :=
    hA.clm_apply (differentiableAt_const _)
  have hp := mvPolynomial_fderiv_coordinate (p row col) x j
  rw [← hscalar, fderiv_apply hB row, fderiv_clm_apply hA (differentiableAt_const _)] at hp
  simp only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, ContinuousLinearMap.flip_apply] at hp
  exact hp

theorem polynomialOperator_fderiv_norm_le {I J O : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype O] [DecidableEq O]
    (A : (I → ℝ) → (J → ℝ) →L[ℝ] (O → ℝ)) (p : Matrix O J (MvPolynomial I ℝ))
    (hentry : ∀ y row col, A y (Pi.single col 1) row = MvPolynomial.eval y (p row col))
    (x : I → ℝ) (hA : DifferentiableAt ℝ A x) {M : ℝ} (hM : 0 ≤ M)
    (hp : ∀ row col j, |MvPolynomial.eval x (MvPolynomial.pderiv j (p row col))| ≤ M) :
    ‖fderiv ℝ A x‖ ≤ Fintype.card I * (Fintype.card J * M) := by
  apply clm_norm_le_card_mul_of_basis _ (mul_nonneg (Nat.cast_nonneg _) hM)
  intro j
  apply clm_norm_le_card_mul_of_entries _ hM
  intro col row
  rw [polynomialOperator_fderiv_entry A p hentry x hA j row col]
  exact hp row col j

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BooleanSelectedDerivativeBound
namespace OAI

section

namespace Erdos3

theorem booleanSelectedInjection_norm_le {B O F α : Type*}
    [Fintype B] [Fintype O] [Fintype F] [Fintype α]
    [DecidableEq B] [DecidableEq F] [DecidableEq α]
    (block : O → B) (hblock : Function.Injective block) (v : F) (r : O → Option α) :
    ‖booleanSelectedInjection block v r‖ ≤ 1 := by
  apply coordinateInjection_norm_le
  intro i j hij
  exact hblock (congrArg Prod.fst hij)

theorem booleanSelectedDerivative_eq {B O F α : Type*}
    [Fintype B] [Fintype O] [Fintype F] [Fintype α]
    [DecidableEq B] [DecidableEq O] [DecidableEq F] [DecidableEq α]
    (c : B → ℝ) (sets : O → Finset α) (block : O → B) (v : F) (r : O → Option α)
    (a : BlockParameter B F α → ℝ) :
    selectedDerivative (booleanSamplerMap (F := F) c sets) (booleanSelectedInjection block v r) a =
      matrixSupCLM ((booleanSelectedMinor c sets block v r).map (MvPolynomial.eval a)) := by
  unfold selectedDerivative booleanSelectedInjection
  rw [clm_coordinateInjection_matrix]
  apply congrArg matrixSupCLM
  funext row col
  exact booleanSelectedMinor_fderiv c sets block v r a row col

theorem boolean_selected_inverse_bound {B O α : Type*}
    [Fintype B] [Fintype O] [Fintype α]
    [DecidableEq B] [DecidableEq O] [DecidableEq α]
    (c : B → ℝ) (sets : O → Finset α) (block : O → B) {h : ℕ}
    (v : Fin h) (r : O → Option α) (hcard : ∀ o, (sets o).card ≤ h)
    (a : BlockParameter B (Fin h) α → ℝ) {C R κ : ℝ}
    (hC : 0 ≤ C) (hR : 0 ≤ R) (hc : ∀ o, |c (block o)| ≤ C) (ha : ∀ j, |a j| ≤ R)
    (hκ : 0 < κ)
    (hdet : κ ≤ |((booleanSelectedMinor c sets block v r).map (MvPolynomial.eval a)).det|) :
    (selectedDerivative (booleanSamplerMap c sets) (booleanSelectedInjection block v r) a).IsInvertible ∧
      ‖(selectedDerivative (booleanSamplerMap c sets) (booleanSelectedInjection block v r) a).inverse‖ ≤
        productMinorInverseBound (Fintype.card O) (Fintype.card α) h C R κ := by
  rw [booleanSelectedDerivative_eq]
  exact matrixSupCLM_inverse_norm_le _ (productMinorEntryBound_nonneg _ _ hC hR)
    (booleanSelectedMinor_entry_bound c sets block v r hcard a hC hR hc ha) hκ hdet

end Erdos3

end

section

namespace Erdos3

open scoped ContDiff

theorem booleanSelectedInjection_single {B O F α : Type*}
    [Fintype O] [DecidableEq O] [DecidableEq B] [DecidableEq F] [DecidableEq α]
    (block : O → B) (v : F) (r : O → Option α) (col : O) :
    booleanSelectedInjection block v r (Pi.single col 1) = Pi.single (block col, v, r col) 1 :=
  coordinateInjection_single _ col

theorem booleanSelectedDerivative_entry {B O F α : Type*}
    [Fintype B] [Fintype O] [Fintype F] [Fintype α]
    [DecidableEq B] [DecidableEq O] [DecidableEq F] [DecidableEq α]
    (c : B → ℝ) (sets : O → Finset α) (block : O → B) (v : F) (r : O → Option α)
    (a : BlockParameter B F α → ℝ) (row col : O) :
    selectedDerivative (booleanSamplerMap c sets) (booleanSelectedInjection block v r) a
      (Pi.single col 1) row = MvPolynomial.eval a (booleanSelectedMinor c sets block v r row col) := by
  change fderiv ℝ (booleanSamplerMap c sets) a
    (booleanSelectedInjection block v r (Pi.single col 1)) row = _
  rw [booleanSelectedInjection_single]
  exact booleanSelectedMinor_fderiv c sets block v r a row col

theorem booleanSelectedDerivative_contDiff {B O F α : Type*}
    [Fintype B] [Fintype O] [Fintype F] [Fintype α]
    [DecidableEq B] [DecidableEq O] [DecidableEq F] [DecidableEq α]
    (c : B → ℝ) (sets : O → Finset α) (block : O → B) (v : F) (r : O → Option α) :
    ContDiff ℝ 1 (selectedDerivative (booleanSamplerMap c sets) (booleanSelectedInjection block v r)) := by
  have hU : ContDiff ℝ 2 (booleanSamplerMap (F := F) c sets) :=
    contDiff_infty.mp (booleanSamplerMap_contDiff (F := F) c sets) 2
  exact (hU.fderiv_right (by norm_num)).clm_comp contDiff_const

theorem boolean_selected_derivative_bound {B O α : Type*}
    [Fintype B] [Fintype O] [Fintype α]
    [DecidableEq B] [DecidableEq O] [DecidableEq α]
    (c : B → ℝ) (sets : O → Finset α) (block : O → B) {h : ℕ}
    (v : Fin h) (r : O → Option α) (hcard : ∀ o, (sets o).card ≤ h)
    (a : BlockParameter B (Fin h) α → ℝ) {C R : ℝ} (hC : 0 ≤ C) (hR : 1 ≤ R)
    (hc : ∀ o, |c (block o)| ≤ C) (ha : ∀ j, |a j| ≤ R) :
    ‖fderiv ℝ (selectedDerivative (booleanSamplerMap c sets) (booleanSelectedInjection block v r)) a‖ ≤
      productMinorDerivativeBound (Fintype.card (BlockParameter B (Fin h) α))
        (Fintype.card O) (Fintype.card α) h C R := by
  have hA := (booleanSelectedDerivative_contDiff c sets block v r).differentiable (by norm_num)
  exact polynomialOperator_fderiv_norm_le
    (selectedDerivative (booleanSamplerMap c sets) (booleanSelectedInjection block v r))
    (booleanSelectedMinor c sets block v r) (booleanSelectedDerivative_entry c sets block v r)
    a (hA a) (productMinorPartialBound_nonneg _ _ hC (zero_le_one.trans hR))
    (booleanSelectedMinor_partial_bound c sets block v r hcard a hC hR hc ha)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BoundedInequalityGoodCutoff
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal ContDiff BigOperators

theorem goodDomainCutoff_range {ι E : Type*} [Fintype ι]
    (ψ : ℝ → ℝ) (hψ : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (r : ι → ℝ) (d : ι → E → ℝ) (b : E → ℝ)
    (hb : ∀ x, b x ∈ Set.Icc (0 : ℝ) 1) (x : E) :
    goodDomainCutoff ψ r d b x ∈ Set.Icc (0 : ℝ) 1 := by
  have hp := product_cutoff_range (fun i => sublevelCutoff ψ (r i) (d i) x)
    (fun i => sublevelCutoff_range ψ hψ (r i) (d i) x)
  exact ⟨mul_nonneg (hb x).1 hp.1, (mul_le_mul (hb x).2 hp.2 hp.1 zero_le_one).trans_eq (by ring)⟩

theorem goodDomainCutoff_smooth {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (r : ι → ℝ)
    (d : ι → E → ℝ) (hd : ∀ i, ContDiff ℝ ∞ (d i))
    (b : E → ℝ) (hb : ContDiff ℝ ∞ b) : ContDiff ℝ ∞ (goodDomainCutoff ψ r d b) :=
  hb.mul (contDiff_prod (fun i _ => contDiff_sublevelCutoff ψ hψ (r i) (d i) (hd i)))

theorem goodDomainCutoff_tsupport_subset {ι E : Type*} [Fintype ι] [TopologicalSpace E]
    (ψ : ℝ → ℝ) (hzero : ∀ t, |t| ≤ 1 → ψ t = 0)
    (r : ι → ℝ) (hr : ∀ i, 0 < r i) (d : ι → E → ℝ) (hd : ∀ i, Continuous (d i))
    (b : E → ℝ) :
    tsupport (goodDomainCutoff ψ r d b) ⊆ tsupport b ∩ {x | ∀ i, r i ≤ |d i x|} := by
  intro x hx
  refine ⟨tsupport_mul_subset_left hx, ?_⟩
  intro i
  exact sublevelCutoff_tsupport_subset ψ hzero (hr i) (d i) (hd i)
    (product_cutoff_tsupport_subset (fun j => sublevelCutoff ψ (r j) (d j)) i
      (tsupport_mul_subset_right hx))

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal ContDiff BigOperators

theorem sublevelCutoffProduct_range {J E : Type*} [Fintype J]
    (ψ : ℝ → ℝ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (κ : J → ℝ) (d : J → E → ℝ) (x : E) :
    sublevelCutoffProduct ψ κ d x ∈ Set.Icc (0 : ℝ) 1 :=
  product_cutoff_range _ (fun i => sublevelCutoff_range ψ hrange (κ i) (d i) x)

theorem sublevelCutoffProduct_smooth {J E : Type*} [Fintype J]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (κ : J → ℝ)
    (d : J → E → ℝ) (hd : ∀ i, ContDiff ℝ ∞ (d i)) :
    ContDiff ℝ ∞ (sublevelCutoffProduct ψ κ d) :=
  contDiff_prod (fun i _ => contDiff_sublevelCutoff ψ hψ (κ i) (d i) (hd i))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.BlockCubeCoordinates
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem blockCubeFlatten_measurePreserving (B F α : Type*) [Fintype B] [Fintype F] [Fintype α] :
    MeasurePreserving (blockCubeFlatten B F α) volume volume := by
  refine ⟨(blockCubeFlatten B F α).continuous.measurable, ?_⟩
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply (blockCubeFlatten B F α).continuous.measurable (MeasurableSet.univ_pi hs)]
  have he : blockCubeFlatten B F α ⁻¹' Set.univ.pi s =
      Set.univ.pi (fun bf : B × F => Set.univ.pi (fun r => s (bf.1, bf.2, r))) := by
    ext x
    constructor
    · intro hx bf _ r _
      exact hx (bf.1, bf.2, r) (Set.mem_univ _)
    · intro hx z _
      exact hx (z.1, z.2.1) (Set.mem_univ _) z.2.2 (Set.mem_univ _)
  rw [he, volume_pi_pi]
  simp only [volume_pi_pi, Fintype.prod_prod_type]

theorem blockCubeFlatten_symm_measurePreserving (B F α : Type*) [Fintype B] [Fintype F]
    [Fintype α] : MeasurePreserving (blockCubeFlatten B F α).symm volume volume :=
  (blockCubeFlatten_measurePreserving B F α).symm
    (blockCubeFlatten B F α).toHomeomorph.toMeasurableEquiv

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SigmaAxisOperator
namespace OAI

section

namespace Erdos3

variable {D : Type*} [Fintype D] {I O P : D → Type*}
  [∀ d, Fintype (I d)] [∀ d, Fintype (O d)] [∀ d, Fintype (P d)]

omit [Fintype D] [∀ d, Fintype (I d)] [∀ d, Fintype (O d)] [∀ d, Fintype (P d)] in
theorem sigmaAxisOperator_comp (A : ∀ d, (I d → ℝ) →L[ℝ] (O d → ℝ))
    (B : ∀ d, (O d → ℝ) →L[ℝ] (P d → ℝ)) :
    (sigmaAxisOperator B).comp (sigmaAxisOperator A) =
      sigmaAxisOperator (fun d => (B d).comp (A d)) := by
  ext x s
  rfl

omit [Fintype D] [∀ d, Fintype (I d)] in
theorem sigmaAxisOperator_inverse_spec (A : ∀ d, (I d → ℝ) →L[ℝ] (I d → ℝ))
    (hA : ∀ d, (A d).IsInvertible) :
    (sigmaAxisOperator A).IsInvertible ∧
      (sigmaAxisOperator A).inverse = sigmaAxisOperator (fun d => (A d).inverse) := by
  have hr : (sigmaAxisOperator A).comp (sigmaAxisOperator (fun d => (A d).inverse)) =
      ContinuousLinearMap.id ℝ ((Σ d, I d) → ℝ) := by
    ext x s
    change A s.1 ((A s.1).inverse (sigmaAxisProjection I s.1 x)) s.2 = x s
    rw [(hA s.1).self_apply_inverse]
    rfl
  have hl : (sigmaAxisOperator (fun d => (A d).inverse)).comp (sigmaAxisOperator A) =
      ContinuousLinearMap.id ℝ ((Σ d, I d) → ℝ) := by
    ext x s
    change (A s.1).inverse (A s.1 (sigmaAxisProjection I s.1 x)) s.2 = x s
    rw [(hA s.1).inverse_apply_self]
    rfl
  exact ⟨ContinuousLinearMap.IsInvertible.of_inverse hr hl, ContinuousLinearMap.inverse_eq hr hl⟩

theorem sigmaAxisOperator_inverse_norm_le (A : ∀ d, (I d → ℝ) →L[ℝ] (I d → ℝ))
    (hA : ∀ d, (A d).IsInvertible) {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ d, ‖(A d).inverse‖ ≤ K) :
    (sigmaAxisOperator A).IsInvertible ∧ ‖(sigmaAxisOperator A).inverse‖ ≤ K := by
  obtain ⟨hi, he⟩ := sigmaAxisOperator_inverse_spec A hA
  refine ⟨hi, ?_⟩
  rw [he]
  exact sigmaAxisOperator_norm_le _ hK hbound

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

theorem sigmaAxisSampler_contDiff (U : ∀ d, (I d → ℝ) → (O d → ℝ))
    (hU : ∀ d, ContDiff ℝ ∞ (U d)) : ContDiff ℝ ∞ (sigmaAxisSampler U) :=
  contDiff_pi.mpr (fun s => ((contDiff_apply ℝ ℝ s.2).comp (hU s.1)).comp
    (sigmaAxisProjection I s.1).contDiff)

theorem sigmaAxisSampler_hasFDerivAt (U : ∀ d, (I d → ℝ) → (O d → ℝ))
    (x : (Σ d, I d) → ℝ)
    (hU : ∀ d, DifferentiableAt ℝ (U d) (sigmaAxisProjection I d x)) :
    HasFDerivAt (sigmaAxisSampler U)
      (sigmaAxisOperator (fun d => fderiv ℝ (U d) (sigmaAxisProjection I d x))) x := by
  apply hasFDerivAt_pi.mpr
  intro s
  exact (hasFDerivAt_apply s.2 _).comp x
    ((hU s.1).hasFDerivAt.comp x (sigmaAxisProjection I s.1).hasFDerivAt)

theorem sigmaAxisSampler_fderiv (U : ∀ d, (I d → ℝ) → (O d → ℝ))
    (x : (Σ d, I d) → ℝ)
    (hU : ∀ d, DifferentiableAt ℝ (U d) (sigmaAxisProjection I d x)) :
    fderiv ℝ (sigmaAxisSampler U) x =
      sigmaAxisOperator (fun d => fderiv ℝ (U d) (sigmaAxisProjection I d x)) :=
  (sigmaAxisSampler_hasFDerivAt U x hU).fderiv

theorem sigmaAxisSampler_selectedDerivative (U : ∀ d, (I d → ℝ) → (O d → ℝ))
    (J : ∀ d, (O d → ℝ) →L[ℝ] (I d → ℝ)) (x : (Σ d, I d) → ℝ)
    (hU : ∀ d, DifferentiableAt ℝ (U d) (sigmaAxisProjection I d x)) :
    selectedDerivative (sigmaAxisSampler U) (sigmaAxisOperator J) x =
      sigmaAxisOperator (fun d => selectedDerivative (U d) (J d) (sigmaAxisProjection I d x)) := by
  unfold selectedDerivative
  rw [sigmaAxisSampler_fderiv U x hU, sigmaAxisOperator_comp]

theorem sigmaAxisSampler_inverse_bound (U : ∀ d, (I d → ℝ) → (O d → ℝ))
    (J : ∀ d, (O d → ℝ) →L[ℝ] (I d → ℝ)) (x : (Σ d, I d) → ℝ)
    (hU : ∀ d, DifferentiableAt ℝ (U d) (sigmaAxisProjection I d x))
    (hinv : ∀ d, (selectedDerivative (U d) (J d) (sigmaAxisProjection I d x)).IsInvertible)
    {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ d, ‖(selectedDerivative (U d) (J d) (sigmaAxisProjection I d x)).inverse‖ ≤ K) :
    (selectedDerivative (sigmaAxisSampler U) (sigmaAxisOperator J) x).IsInvertible ∧
      ‖(selectedDerivative (sigmaAxisSampler U) (sigmaAxisOperator J) x).inverse‖ ≤ K := by
  rw [sigmaAxisSampler_selectedDerivative U J x hU]
  exact sigmaAxisOperator_inverse_norm_le _ hinv hK hbound

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.JointBooleanGoodWeight
namespace OAI

section

namespace Erdos3

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem weightedCutoff_abs_mass_le [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [IsFiniteMeasureOnCompacts μ]
    (w θ : E → ℝ) (hw : ContDiff ℝ 1 w) (hs : HasCompactSupport w)
    (hθ : ContDiff ℝ 1 θ) (hrange : ∀ x, θ x ∈ Set.Icc (0 : ℝ) 1) :
    (∫ x, |w x * θ x| ∂μ) ≤ ∫ x, |w x| ∂μ := by
  have hwθ : Integrable (fun x => w x * θ x) μ :=
    (hw.mul hθ).continuous.integrable_of_hasCompactSupport hs.mul_right
  have hwi : Integrable w μ := hw.continuous.integrable_of_hasCompactSupport hs
  have hleft : Integrable (fun x => |w x * θ x|) μ := by
    simpa only [Real.norm_eq_abs] using hwθ.norm
  have hright : Integrable (fun x => |w x|) μ := by
    simpa only [Real.norm_eq_abs] using hwi.norm
  apply integral_mono hleft hright
  intro x
  change |w x * θ x| ≤ |w x|
  rw [abs_mul, abs_of_nonneg (hrange x).1]
  exact mul_le_of_le_one_right (abs_nonneg _) (hrange x).2

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem blockCubeWeight_contDiff {B F α : Type*} [Fintype B] [Fintype F] [Fintype α]
    (w : ((B × F) → Option α → ℝ) → ℝ) (hw : ContDiff ℝ 1 w) :
    ContDiff ℝ 1 (blockCubeWeight w) := hw.comp (blockCubeFlatten B F α).symm.contDiff

theorem blockCubeWeight_compact {B F α : Type*} [Fintype B] [Fintype F] [Fintype α]
    (w : ((B × F) → Option α → ℝ) → ℝ) (hw : HasCompactSupport w) :
    HasCompactSupport (blockCubeWeight w) :=
  hw.comp_homeomorph (blockCubeFlatten B F α).symm.toHomeomorph

theorem blockCubeWeight_tsupport {B F α : Type*} [Fintype B] [Fintype F] [Fintype α]
    (w : ((B × F) → Option α → ℝ) → ℝ) :
    tsupport (blockCubeWeight w) = (blockCubeFlatten B F α).symm ⁻¹' tsupport w :=
  tsupport_comp_eq_preimage w (blockCubeFlatten B F α).symm.toHomeomorph

theorem blockCubeWeight_integral {B F α : Type*} [Fintype B] [Fintype F] [Fintype α]
    (w : ((B × F) → Option α → ℝ) → ℝ) :
    (∫ a, blockCubeWeight w a) = ∫ x, w x :=
  (blockCubeFlatten_symm_measurePreserving B F α).integral_comp
    (blockCubeFlatten B F α).symm.toHomeomorph.toMeasurableEquiv.measurableEmbedding w

theorem blockCubeWeight_abs_integral {B F α : Type*} [Fintype B] [Fintype F] [Fintype α]
    (w : ((B × F) → Option α → ℝ) → ℝ) :
    (∫ a, |blockCubeWeight w a|) = ∫ x, |w x| :=
  blockCubeWeight_integral (fun x => |w x|)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

theorem blockCubeMeasure_integral {B F α : Type*} [Fintype B] [Fintype F] [Fintype α]
    [DecidableEq α] (f : (BlockParameter B F α → ℝ) → ℝ) :
    (∫ a, f a ∂blockCubeMeasure B F α) =
      ∫ x, f (blockCubeFlatten B F α x) ∂scalarCubeProductMeasure (B × F) α :=
  (blockCubeFlatten B F α).toHomeomorph.toMeasurableEquiv.measurableEmbedding.integral_map f

theorem blockCubeFlatten_box {B F α : Type*} [Fintype B] [Fintype F] [Fintype α]
    [DecidableEq α] {x : (B × F) → Option α → ℝ} (hx : x ∈ scalarCubeProductDomain (B × F) α)
    (z : BlockParameter B F α) : |blockCubeFlatten B F α x z| ≤ 1 :=
  (scalarCubeDomain_coordinate_abs_lt_one (hx (z.1, z.2.1) (Set.mem_univ _)) z.2.2).le

theorem blockCubeWeight_box {B F α : Type*} [Fintype B] [Fintype F] [Fintype α]
    [DecidableEq α] (w : ((B × F) → Option α → ℝ) → ℝ)
    (hs : tsupport w ⊆ scalarCubeProductDomain (B × F) α)
    {a : BlockParameter B F α → ℝ} (ha : a ∈ tsupport (blockCubeWeight w))
    (z : BlockParameter B F α) : |a z| ≤ 1 := by
  rw [blockCubeWeight_tsupport] at ha
  have hx := blockCubeFlatten_box (hs ha) z
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using hx

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

theorem blockCubeWeight_integral_test {B F α : Type*} [Fintype B] [Fintype F] [Fintype α]
    (w : ((B × F) → Option α → ℝ) → ℝ) (f : (BlockParameter B F α → ℝ) → ℝ) :
    (∫ a, blockCubeWeight w a * f a) =
      ∫ x, w x * f (blockCubeFlatten B F α x) := by
  have h := (blockCubeFlatten_measurePreserving B F α).integral_comp
    (blockCubeFlatten B F α).toHomeomorph.toMeasurableEquiv.measurableEmbedding
    (fun a => blockCubeWeight w a * f a)
  simp only [blockCubeWeight, ContinuousLinearEquiv.symm_apply_apply] at h
  exact h.symm

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff BigOperators

theorem scalarCubeGoodWeight_spec {I J α : Type*} [Fintype I] [Fintype J]
    [Fintype α] [DecidableEq α] (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1) (hzero : ∀ t, |t| ≤ 1 → ψ t = 0)
    (r : I → ℝ) (hr : ∀ i, 0 < r i) (κ : J → ℝ) (hκ : ∀ i, 0 < κ i)
    (d : J → (I → Option α → ℝ) → ℝ) (hd : ∀ i, ContDiff ℝ ∞ (d i)) :
    ContDiff ℝ 1 (scalarCubeGoodWeight α ψ r κ d) ∧
      HasCompactSupport (scalarCubeGoodWeight α ψ r κ d) ∧
      tsupport (scalarCubeGoodWeight α ψ r κ d) ⊆
        scalarCubeProductDomain I α ∩ {x | ∀ i, κ i ≤ |d i x|} ∧
      (∀ x, 0 ≤ scalarCubeGoodWeight α ψ r κ d x) ∧
      (∫ x, |scalarCubeGoodWeight α ψ r κ d x|) ≤ 1 := by
  have hb := scalarCubeProductWeight_spec (α := α) r hr
  have hθ : ContDiff ℝ 1 (sublevelCutoffProduct ψ κ d) :=
    (sublevelCutoffProduct_smooth ψ hψ κ d hd).of_le (by norm_num)
  refine ⟨hb.1.mul hθ, hb.2.1.mul_right, ?_, ?_, ?_⟩
  · intro x hx
    have h := goodDomainCutoff_tsupport_subset ψ hzero κ hκ d
      (fun i => (hd i).continuous) (scalarCubeProductWeight α r) hx
    exact ⟨hb.2.2.1 h.1, h.2⟩
  · intro x
    exact mul_nonneg (hb.2.2.2.1 x) (sublevelCutoffProduct_range ψ hrange κ d x).1
  · exact (weightedCutoff_abs_mass_le volume _ _ hb.1 hb.2.1 hθ
      (sublevelCutoffProduct_range ψ hrange κ d)).trans hb.2.2.2.2

theorem scalarCubeGoodWeight_integral_test {I J α : Type*} [Fintype I] [Fintype J]
    [Fintype α] [DecidableEq α] (ψ : ℝ → ℝ) (r : I → ℝ) (hr : ∀ i, 0 < r i)
    (κ : J → ℝ) (d : J → (I → Option α → ℝ) → ℝ) (f : (I → Option α → ℝ) → ℝ) :
    (∫ x, scalarCubeGoodWeight α ψ r κ d x * f x) =
      ∫ x, goodDomainCutoff ψ κ d (scalarCubeProductCutoff α r) x * f x
        ∂scalarCubeProductMeasure I α := by
  have h := scalarCubeProductWeight_integral_test r hr
    (fun x => sublevelCutoffProduct ψ κ d x * f x)
  simpa only [scalarCubeGoodWeight, sublevelCutoffProduct, goodDomainCutoff, mul_assoc] using h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.JointBooleanWeightBudget
namespace OAI

section

namespace Erdos3

open scoped NNReal BigOperators

variable {D α : Type*} [Fintype D] [Fintype α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]

theorem jointBooleanWeightBudget_nonneg (h : D → ℕ) (C : D → ℝ) (hC : ∀ d, 0 ≤ C d)
    (A T : ℝ≥0) (r : ∀ d, B d × Fin (h d) → ℝ) (hr : ∀ d i, 0 ≤ r d i)
    (κ : D → ℝ) (hκ : ∀ d, 0 ≤ κ d) :
    0 ≤ jointBooleanWeightBudget (O := O) (α := α) h C A T r κ := by
  apply Finset.sum_nonneg
  intro d _
  exact add_nonneg (Finset.sum_nonneg (fun i _ => div_nonneg (by positivity) (hr d i)))
    (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (div_nonneg A.coe_nonneg (hκ d))
      (productMinorDeterminantDerivativeBound_nonneg _ _ _ _ (hC d) zero_le_one)))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.SlicedRemainderDensityFamily
namespace OAI

section

namespace Erdos3

open MeasureTheory

variable {D : Type*} [Fintype D] {I : D → Type*} [∀ d, Fintype (I d)]

theorem sigmaAxisMeasure_withDensity (μ : ∀ d, Measure (I d → ℝ)) [∀ d, SigmaFinite (μ d)]
    (f : ∀ d, (I d → ℝ) → ℝ) (hf : ∀ d, Integrable (f d) (μ d)) (hf0 : ∀ d x, 0 ≤ f d x) :
    sigmaAxisMeasure (fun d => realDensityMeasure (μ d) (f d)) =
      realDensityMeasure (sigmaAxisMeasure μ) (sigmaAxisWeight f) := by
  unfold sigmaAxisMeasure
  rw [realDensityMeasure_pi μ f hf hf0]
  exact realDensityMeasure_map_equiv
    (sigmaAxisCoordinates I).symm.toHomeomorph.toMeasurableEquiv _ _

theorem sigmaAxisMeasure_volume :
    sigmaAxisMeasure (fun d => (volume : Measure (I d → ℝ))) = volume :=
  (sigmaAxisCoordinates_symm_measurePreserving I).map_eq

theorem sigmaAxisMeasure_density (f : ∀ d, (I d → ℝ) → ℝ)
    (hf : ∀ d, Integrable (f d)) (hf0 : ∀ d x, 0 ≤ f d x) :
    sigmaAxisMeasure (fun d => realDensityMeasure volume (f d)) =
      realDensityMeasure volume (sigmaAxisWeight f) := by
  rw [sigmaAxisMeasure_withDensity _ f hf hf0, sigmaAxisMeasure_volume]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.JointBooleanCutoffLaw
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem cutoff_loss_of_density_mass {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) [IsProbabilityMeasure μ] (χ w : X → ℝ)
    (hχ : Measurable χ) (hχ01 : ∀ x, χ x ∈ Set.Icc (0 : ℝ) 1)
    (hwi : Integrable w ν) (hw0 : ∀ x, 0 ≤ w x)
    (hlaw : realDensityMeasure ν w = realDensityMeasure μ χ)
    {η : ℝ} (hmass : 1 - η ≤ ∫ x, w x ∂ν) : (∫ x, 1 - χ x ∂μ) ≤ η := by
  have hi := cutoff_integrable μ χ hχ hχ01
  have hm : (∫ x, χ x ∂μ) = ∫ x, w x ∂ν := by
    rw [← realDensityMeasure_real_univ μ χ hi (fun x => (hχ01 x).1),
      ← hlaw, realDensityMeasure_real_univ ν w hwi hw0]
  rw [integral_sub (integrable_const (1 : ℝ)) hi, hm]
  simpa only [integral_const, probReal_univ, one_smul] using sub_le_iff_le_add.mpr
    (show (1 : ℝ) ≤ η + ∫ x, w x ∂ν by linarith)

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

section

namespace Erdos3

open MeasureTheory

theorem affineProbabilityProfile_integral_test (c : ℝ) {w : ℝ} (hw : 0 < w) (φ : ℝ → ℝ) :
    (∫ x, affineProbabilityProfile c w x * φ x) =
      ∫ y, smoothProbabilityProfile y * φ (c + w*y) := by
  let g := fun y => smoothProbabilityProfile y * φ (c+w*y)
  have he (x : ℝ) : affineProbabilityProfile c w x * φ x = w⁻¹ * g ((x-c)/w) := by
    have hx : c + w*((x-c)/w) = x := by field_simp [hw.ne']; ring
    simp only [affineProbabilityProfile, g, hx]
    ring
  simp_rw [he]
  rw [integral_const_mul, integral_sub_right_eq_self (fun x => g (x/w)) c,
    Measure.integral_comp_div, smul_eq_mul, abs_of_pos hw, ← mul_assoc,
    inv_mul_cancel₀ hw.ne', one_mul]

theorem affineProbabilityProfile_law (c : ℝ) {w : ℝ} (hw : 0 < w) :
    (realDensityMeasure volume smoothProbabilityProfile).map (fun y => c + w*y) =
      realDensityMeasure volume (affineProbabilityProfile c w) := by
  have hψ : Integrable smoothProbabilityProfile :=
    smoothProbabilityProfile_contDiff.continuous.integrable_of_hasCompactSupport smoothProbabilityProfile_compact
  let : IsFiniteMeasure (realDensityMeasure volume smoothProbabilityProfile) :=
    realDensityMeasure_finite _ _ hψ (fun y => (smoothProbabilityProfile_range y).1)
  let : IsFiniteMeasure (realDensityMeasure volume (affineProbabilityProfile c w)) :=
    realDensityMeasure_finite _ _ (affineProbabilityProfile_integrable c hw) (affineProbabilityProfile_nonneg c hw)
  have hmap : Measurable (fun y : ℝ => c+w*y) := by fun_prop
  apply finiteMeasure_eq_of_integrals
  intro φ hφ
  rw [integral_map hmap.aemeasurable hφ.aestronglyMeasurable,
    realDensityMeasure_integral volume smoothProbabilityProfile
      smoothProbabilityProfile_contDiff.continuous.measurable (fun y => (smoothProbabilityProfile_range y).1),
    realDensityMeasure_integral volume (affineProbabilityProfile c w)
      (affineProbabilityProfile_contDiff c w).continuous.measurable (affineProbabilityProfile_nonneg c hw)]
  exact (affineProbabilityProfile_integral_test c hw φ).symm

theorem affineProductProfile_law {I : Type*} [Fintype I]
    (c w : I → ℝ) (hw : ∀ i, 0 < w i) :
    (realDensityMeasure volume (smoothProductProfile I)).map (fun y i => c i + w i * y i) =
      realDensityMeasure volume (affineProductProfile c w) := by
  have hψ : Integrable smoothProbabilityProfile :=
    smoothProbabilityProfile_contDiff.continuous.integrable_of_hasCompactSupport smoothProbabilityProfile_compact
  let : IsFiniteMeasure (realDensityMeasure volume smoothProbabilityProfile) :=
    realDensityMeasure_finite _ _ hψ (fun y => (smoothProbabilityProfile_range y).1)
  have hsrc := realDensityMeasure_pi (fun _ : I => (volume : Measure ℝ))
    (fun _ => smoothProbabilityProfile) (fun _ => hψ) (fun _ y => (smoothProbabilityProfile_range y).1)
  have hdst := realDensityMeasure_pi (fun _ : I => (volume : Measure ℝ))
    (fun i => affineProbabilityProfile (c i) (w i))
    (fun i => affineProbabilityProfile_integrable (c i) (hw i))
    (fun i => affineProbabilityProfile_nonneg (c i) (hw i))
  change (Measure.pi (fun _ : I => realDensityMeasure volume smoothProbabilityProfile)) =
    realDensityMeasure volume (smoothProductProfile I) at hsrc
  change (Measure.pi (fun i : I => realDensityMeasure volume (affineProbabilityProfile (c i) (w i)))) =
    realDensityMeasure volume (affineProductProfile c w) at hdst
  rw [← hsrc, Measure.pi_map_pi (fun i =>
    (show Measurable (fun y : ℝ => c i + w i * y) by fun_prop).aemeasurable)]
  simp_rw [affineProbabilityProfile_law _ (hw _)]
  exact hdst

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

theorem unitCoefficientSource_affine_law {I : Type*} [Fintype I]
    (c w : I → ℝ) (hw : ∀ i, 0 < w i) :
    (unitCoefficientSource I).map (fun r i => c i+w i*r i) =
      realDensityMeasure volume (affineProductProfile c w) :=
  affineProductProfile_law c w hw

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

theorem regularizedImageMap_measurable {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (δ : ℝ≥0) (U : Ω → I → ℝ) (hU : Measurable U) : Measurable (regularizedImageMap δ U) :=
  (hU.comp measurable_fst).add (measurable_snd.const_smul (δ : ℝ))

theorem regularizedImageDensity_joint_measurable {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (U : Ω → I → ℝ) (hU : Measurable U) (δ : ℝ≥0) :
    Measurable (fun p : Ω × (I → ℝ) => affineProductProfile (U p.1) (fun _ => (δ : ℝ)) p.2) :=
  affineProductProfile_measurable_center _ _ _
    (fun i => (measurable_pi_apply i).comp (hU.comp measurable_fst))
    (fun i => (measurable_pi_apply i).comp measurable_snd)

theorem regularizedImageDensity_measurable {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (μ : Measure Ω) [SFinite μ] (U : Ω → I → ℝ) (hU : Measurable U) (δ : ℝ≥0) :
    Measurable (regularizedImageDensity μ U δ) :=
  (regularizedImageDensity_joint_measurable U hU δ).stronglyMeasurable.integral_prod_left'.measurable

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

theorem regularizedImageDensity_image_law {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : Ω → I → ℝ) (hU : Measurable U)
    (δ : ℝ≥0) (hδ : 0 < δ) :
    (μ.prod (unitCoefficientSource I)).map (regularizedImageMap δ U) =
      realDensityMeasure volume (regularizedImageDensity μ U δ) := by
  apply densityMixture_image_law μ (unitCoefficientSource I) volume _
    (regularizedImageMap_measurable δ U hU)
    (fun a => affineProductProfile (U a) (fun _ => (δ : ℝ)))
    (regularizedImageDensity_joint_measurable U hU δ)
  · intro a
    exact ⟨affineProductProfile_nonneg (U a) _ (fun _ => hδ),
      affineProductProfile_integrable (U a) _ (fun _ => hδ),
      affineProductProfile_integral (U a) _ (fun _ => hδ)⟩
  · intro a
    exact unitCoefficientSource_affine_law (U a) (fun _ => (δ : ℝ)) (fun _ => hδ)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.JointBooleanRegularization
namespace OAI

section

namespace Erdos3

variable {D : Type*} [Fintype D] {I O : D → Type*}
  [∀ d, Fintype (I d)] [∀ d, Fintype (O d)]

theorem sigmaAxisOperatorMap_norm_le_one :
    ‖sigmaAxisOperatorMap (I := I) (O := O)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro A
  rw [one_mul]
  exact sigmaAxisOperator_norm_le A (norm_nonneg A) (norm_le_pi_norm A)

theorem sigmaAxisFamily_fderiv_norm_le {E : D → Type*}
    [∀ d, NormedAddCommGroup (E d)] [∀ d, NormedSpace ℝ (E d)]
    (f : ∀ d, (I d → ℝ) → E d) (x : (Σ d, I d) → ℝ)
    (hf : ∀ d, DifferentiableAt ℝ (f d) (sigmaAxisProjection I d x))
    {H : ℝ} (hH : 0 ≤ H)
    (hbound : ∀ d, ‖fderiv ℝ (f d) (sigmaAxisProjection I d x)‖ ≤ H) :
    ‖fderiv ℝ (fun y d => f d (sigmaAxisProjection I d y)) x‖ ≤ H := by
  have hd := hasFDerivAt_pi.mpr (fun d =>
    (hf d).hasFDerivAt.comp x (sigmaAxisProjection I d).hasFDerivAt)
  simp only [Function.comp_def] at hd
  rw [hd.fderiv]
  apply ContinuousLinearMap.opNorm_le_bound _ hH
  intro v
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hH (norm_nonneg v))).mpr
  intro d
  change ‖fderiv ℝ (f d) (sigmaAxisProjection I d x) (sigmaAxisProjection I d v)‖ ≤ H * ‖v‖
  exact ((fderiv ℝ (f d) (sigmaAxisProjection I d x)).le_opNorm _).trans
    (mul_le_mul (hbound d) (sigmaAxisProjection_norm_apply_le I d v) (norm_nonneg _) hH)

theorem sigmaAxisOperatorFamily_fderiv_norm_le
    (A : ∀ d, (I d → ℝ) → ((O d → ℝ) →L[ℝ] (O d → ℝ))) (x : (Σ d, I d) → ℝ)
    (hA : ∀ d, DifferentiableAt ℝ (A d) (sigmaAxisProjection I d x))
    {H : ℝ} (hH : 0 ≤ H)
    (hbound : ∀ d, ‖fderiv ℝ (A d) (sigmaAxisProjection I d x)‖ ≤ H) :
    ‖fderiv ℝ (fun y => sigmaAxisOperator (fun d => A d (sigmaAxisProjection I d y))) x‖ ≤ H := by
  let F := fun y d => A d (sigmaAxisProjection I d y)
  let L : (∀ d, (O d → ℝ) →L[ℝ] (O d → ℝ)) →L[ℝ]
      (((Σ d, O d) → ℝ) →L[ℝ] ((Σ d, O d) → ℝ)) := sigmaAxisOperatorMap
  have hF : DifferentiableAt ℝ F x := differentiableAt_pi.mpr (fun d =>
    (hA d).comp x (sigmaAxisProjection I d).differentiableAt)
  have he : (fun y => sigmaAxisOperator (fun d => A d (sigmaAxisProjection I d y))) =
      L ∘ F := rfl
  rw [he, fderiv_comp x L.differentiableAt hF, L.fderiv]
  have hL : ‖L‖ ≤ 1 := sigmaAxisOperatorMap_norm_le_one
  have hfbound : ‖fderiv ℝ F x‖ ≤ H := sigmaAxisFamily_fderiv_norm_le A x hA hH hbound
  have hnF : 0 ≤ ‖fderiv ℝ F x‖ := norm_nonneg (fderiv ℝ F x)
  calc
    _ ≤ ‖L‖ * ‖fderiv ℝ F x‖ := L.opNorm_comp_le _
    _ ≤ 1 * H := mul_le_mul hL hfbound hnF zero_le_one
    _ = H := one_mul H

theorem sigmaAxisSampler_selected_fderiv_norm_le
    (U : ∀ d, (I d → ℝ) → (O d → ℝ)) (hU : ∀ d, ContDiff ℝ 2 (U d))
    (J : ∀ d, (O d → ℝ) →L[ℝ] (I d → ℝ)) (x : (Σ d, I d) → ℝ)
    {H : ℝ} (hH : 0 ≤ H)
    (hbound : ∀ d, ‖fderiv ℝ (selectedDerivative (U d) (J d)) (sigmaAxisProjection I d x)‖ ≤ H) :
    ‖fderiv ℝ (selectedDerivative (sigmaAxisSampler U) (sigmaAxisOperator J)) x‖ ≤ H := by
  have he : selectedDerivative (sigmaAxisSampler U) (sigmaAxisOperator J) =
      fun y => sigmaAxisOperator (fun d => selectedDerivative (U d) (J d) (sigmaAxisProjection I d y)) := by
    funext y
    exact sigmaAxisSampler_selectedDerivative U J y (fun d => (hU d).differentiable (by norm_num) _)
  rw [he]
  apply sigmaAxisOperatorFamily_fderiv_norm_le _ x _ hH hbound
  intro d
  have hc : ContDiff ℝ 1 (selectedDerivative (U d) (J d)) :=
    ((hU d).fderiv_right (by norm_num)).clm_comp contDiff_const
  exact hc.differentiable one_ne_zero _

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem regularizedImageMap_mappedTest {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (μ : Measure Ω) [IsFiniteMeasure μ] (U : Ω → I → ℝ) (hU : Measurable U) (δ : ℝ≥0)
    (φ : (I → ℝ) → ℝ) (hφ : Measurable φ) (hbound : ∀ x, ‖φ x‖ ≤ 1) :
    mappedTest (μ.prod (unitCoefficientSource I)) (regularizedImageMap δ U) φ =
      ∫ r, mappedTest μ U (fun x => φ (x+(δ : ℝ) • r)) ∂unitCoefficientSource I := by
  have hi := mappedTest_integrable (μ.prod (unitCoefficientSource I)) (regularizedImageMap δ U)
    (regularizedImageMap_measurable δ U hU) φ hφ hbound
  change (∫ p, φ (U p.1+(δ : ℝ) • p.2) ∂μ.prod (unitCoefficientSource I)) = _
  exact (integral_prod _ hi).trans (integral_integral_swap hi)

theorem regularizedImageMap_error {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : Ω → I → ℝ) (hU : Measurable U)
    (δ H : ℝ≥0) (η : ℝ) (φ : (I → ℝ) → ℝ) (hφ : Measurable φ)
    (hbound : ∀ x, ‖φ x‖ ≤ 1)
    (hmove : ∀ z, |mappedTest μ U (fun x => φ (x+z))-mappedTest μ U φ| ≤ η+H*dist z 0) :
    |mappedTest (μ.prod (unitCoefficientSource I)) (regularizedImageMap δ U) φ - mappedTest μ U φ| ≤
      η+H*δ := by
  let F := fun r : I → ℝ => mappedTest μ U (fun x => φ (x+(δ : ℝ) • r))
  have hfm : Measurable F := (mappedTest_shift_measurable μ U hU φ hφ).comp
    (measurable_id.const_smul (δ : ℝ))
  have hfi : Integrable F (unitCoefficientSource I) :=
    (integrable_const (μ.real Set.univ)).mono' hfm.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun r => mappedTest_norm_le μ U _ (fun x => hbound _)))
  have heq : mappedTest (μ.prod (unitCoefficientSource I)) (regularizedImageMap δ U) φ - mappedTest μ U φ =
      ∫ r, F r-mappedTest μ U φ ∂unitCoefficientSource I := by
    rw [regularizedImageMap_mappedTest μ U hU δ φ hφ hbound,
      integral_sub hfi (integrable_const _)]
    simp only [integral_const, probReal_univ, one_smul, F]
  have hb : ∀ᵐ r ∂unitCoefficientSource I, ‖F r-mappedTest μ U φ‖ ≤ η+(H : ℝ)*δ := by
    filter_upwards [unitCoefficientSource_norm_le I] with r hr
    have hd : dist ((δ : ℝ) • r) 0 ≤ (δ : ℝ) := by
      rw [dist_zero_right, norm_smul, Real.norm_of_nonneg δ.coe_nonneg]
      exact mul_le_of_le_one_right δ.coe_nonneg hr
    exact (hmove ((δ : ℝ) • r)).trans
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left hd H.coe_nonneg))
  have hi := norm_integral_le_of_norm_le (integrable_const (η+(H : ℝ)*δ)) hb
  rw [integral_const, probReal_univ, one_smul, Real.norm_eq_abs] at hi
  rw [heq]
  exact hi

theorem regularizedImageDensity_test_error {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : Ω → I → ℝ) (hU : Measurable U)
    (δ : ℝ≥0) (hδ : 0 < δ) (H : ℝ≥0) (η : ℝ)
    (φ : (I → ℝ) → ℝ) (hφ : Measurable φ) (hbound : ∀ x, ‖φ x‖ ≤ 1)
    (hmove : ∀ z, |mappedTest μ U (fun x => φ (x+z))-mappedTest μ U φ| ≤ η+H*dist z 0) :
    |(∫ x, regularizedImageDensity μ U δ x*φ x)-mappedTest μ U φ| ≤ η+H*δ := by
  have he := mappedTest_eq_density (μ.prod (unitCoefficientSource I)) volume (regularizedImageMap δ U)
    (regularizedImageMap_measurable δ U hU) (regularizedImageDensity μ U δ)
    (regularizedImageDensity_measurable μ U hU δ) (regularizedImageDensity_probability μ U hU δ hδ).1
    (regularizedImageDensity_image_law μ U hU δ hδ) φ hφ
  rw [← he]
  exact regularizedImageMap_error μ U hU δ H η φ hφ hbound hmove

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem cutoff_translation_error {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (w : Ω → ℝ) (hw : Measurable w) (hw01 : ∀ a, w a ∈ Set.Icc (0 : ℝ) 1)
    (U : Ω → I → ℝ) (hU : Measurable U) (H : ℝ≥0)
    (hmove : ImageTranslationBound (realDensityMeasure μ w) U H)
    {η : ℝ} (hcut : (∫ a, 1-w a ∂μ) ≤ η)
    (φ : (I → ℝ) → ℝ) (hφ : Measurable φ) (hbound : ∀ x, ‖φ x‖ ≤ 1) (z : I → ℝ) :
    |mappedTest μ U (fun x => φ (x+z))-mappedTest μ U φ| ≤ 2*η+H*dist z 0 := by
  have hshift := (mappedTest_cutoff_error μ w hw hw01 U hU (fun x => φ (x+z))
    (hφ.comp (measurable_id.add_const z)) (fun x => hbound (x+z))).trans hcut
  have hbase := (mappedTest_cutoff_error μ w hw hw01 U hU φ hφ hbound).trans hcut
  have hmiddle := hmove φ hφ hbound z
  have ht := abs_sub_le (mappedTest μ U (fun x => φ (x+z)))
    (mappedTest (realDensityMeasure μ w) U (fun x => φ (x+z))) (mappedTest μ U φ)
  have hu := abs_sub_le (mappedTest (realDensityMeasure μ w) U (fun x => φ (x+z)))
    (mappedTest (realDensityMeasure μ w) U φ) (mappedTest μ U φ)
  rw [abs_sub_comm (mappedTest (realDensityMeasure μ w) U φ) (mappedTest μ U φ)] at hu
  linarith

theorem regularizedImageDensity_cutoff_error {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (w : Ω → ℝ) (hw : Measurable w) (hw01 : ∀ a, w a ∈ Set.Icc (0 : ℝ) 1)
    (U : Ω → I → ℝ) (hU : Measurable U) (H : ℝ≥0)
    (hmove : ImageTranslationBound (realDensityMeasure μ w) U H)
    {η : ℝ} (hcut : (∫ a, 1-w a ∂μ) ≤ η) (δ : ℝ≥0) (hδ : 0 < δ)
    (φ : (I → ℝ) → ℝ) (hφ : Measurable φ) (hbound : ∀ x, ‖φ x‖ ≤ 1) :
    |(∫ x, regularizedImageDensity μ U δ x*φ x)-mappedTest μ U φ| ≤ 2*η+H*δ :=
  regularizedImageDensity_test_error μ U hU δ hδ H (2*η) φ hφ hbound
    (cutoff_translation_error μ w hw hw01 U hU H hmove hcut φ hφ hbound)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineCubeMinorGoodMass
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff BigOperators

variable {B O J α : Type*} [Fintype B] [Fintype O] [Fintype J] [Fintype α]
  [DecidableEq B] [DecidableEq O] [DecidableEq α] {h : ℕ}

theorem affineBooleanCubeDeterminant_contDiff
    (c : B → ℝ) (sets : O → Finset α) (block : O → B)
    (v : Fin h) (sel : O → Option α)
    (L : (BlockParameter B (Fin h) α → ℝ) →L[ℝ] (BlockParameter B (Fin h) α → ℝ))
    (b : BlockParameter B (Fin h) α → ℝ) :
    ContDiff ℝ ∞ (affineBooleanCubeDeterminant c sets block v sel L b) :=
  (booleanMinorDeterminant_contDiff c sets block v sel).comp
    (contDiff_const.add (L.contDiff.comp (blockCubeFlatten B (Fin h) α).contDiff))

variable (c : J → B → ℝ) (sets : O → Finset α) (block : J → O → B)
  (v : Fin h) (sel : J → O → Option α)
  (L : (BlockParameter B (Fin h) α → ℝ) →L[ℝ] (BlockParameter B (Fin h) α → ℝ))
  (b : BlockParameter B (Fin h) α → ℝ)
  (ψ : ℝ → ℝ) (r : B × Fin h → ℝ) (κ : J → ℝ)

theorem affineBooleanCubeCutoff_contDiff (hψ : ContDiff ℝ ∞ ψ) :
    ContDiff ℝ ∞ (affineBooleanCubeCutoff c sets block v sel L b ψ r κ) :=
  (goodDomainCutoff_smooth ψ hψ κ _
    (fun j => affineBooleanCubeDeterminant_contDiff (c j) sets (block j) v (sel j) L b) _
    (scalarCubeProductCutoff_smooth r)).comp (blockCubeFlatten B (Fin h) α).symm.contDiff

theorem affineBooleanCubeCutoff_range (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (x : BlockParameter B (Fin h) α → ℝ) :
    affineBooleanCubeCutoff c sets block v sel L b ψ r κ x ∈ Set.Icc (0 : ℝ) 1 :=
  goodDomainCutoff_range ψ hrange κ _ _ (scalarCubeProductCutoff_range r) _

theorem affineBooleanCubeGoodWeight_spec
    (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hr : ∀ i, 0 < r i) (hκ : ∀ j, 0 < κ j) :
    let w := affineBooleanCubeGoodWeight c sets block v sel L b ψ r κ
    ContDiff ℝ 1 w ∧ HasCompactSupport w ∧ (∀ a, 0 ≤ w a) ∧ (∫ a, |w a|) ≤ 1 ∧
      ∀ a ∈ tsupport w, (∀ z, |a z| ≤ 1) ∧
        ∀ j, κ j ≤ |booleanMinorDeterminant (c j) sets (block j) v (sel j) (b + L a)| := by
  let d := fun j => affineBooleanCubeDeterminant (c j) sets (block j) v (sel j) L b
  have hs := scalarCubeGoodWeight_spec ψ hψ hrange hzero r hr κ hκ d
    (fun j => affineBooleanCubeDeterminant_contDiff (c j) sets (block j) v (sel j) L b)
  refine ⟨blockCubeWeight_contDiff _ hs.1, blockCubeWeight_compact _ hs.2.1,
    fun a => hs.2.2.2.1 _, ?_, ?_⟩
  · change (∫ a, |blockCubeWeight (scalarCubeGoodWeight α ψ r κ d) a|) ≤ 1
    rw [blockCubeWeight_abs_integral]
    exact hs.2.2.2.2
  · intro a ha
    refine ⟨blockCubeWeight_box _ (fun x hx => (hs.2.2.1 hx).1) ha, ?_⟩
    change a ∈ tsupport (blockCubeWeight (scalarCubeGoodWeight α ψ r κ d)) at ha
    rw [blockCubeWeight_tsupport] at ha
    intro j
    simpa only [d, affineBooleanCubeDeterminant, ContinuousLinearEquiv.apply_symm_apply] using
      (hs.2.2.1 ha).2 j

theorem affineBooleanCubeGoodWeight_integral_test (hr : ∀ i, 0 < r i)
    (f : (BlockParameter B (Fin h) α → ℝ) → ℝ) :
    (∫ a, affineBooleanCubeGoodWeight c sets block v sel L b ψ r κ a * f a) =
      ∫ a, affineBooleanCubeCutoff c sets block v sel L b ψ r κ a * f a
        ∂blockCubeMeasure B (Fin h) α := by
  unfold affineBooleanCubeGoodWeight
  rw [blockCubeWeight_integral_test, blockCubeMeasure_integral]
  simp only [affineBooleanCubeCutoff, ContinuousLinearEquiv.symm_apply_apply]
  exact scalarCubeGoodWeight_integral_test ψ r hr κ _ _

theorem affineBooleanCubeGoodWeight_measure
    (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hr : ∀ i, 0 < r i) (hκ : ∀ j, 0 < κ j) :
    realDensityMeasure volume (affineBooleanCubeGoodWeight c sets block v sel L b ψ r κ) =
      realDensityMeasure (blockCubeMeasure B (Fin h) α)
        (affineBooleanCubeCutoff c sets block v sel L b ψ r κ) := by
  let w := affineBooleanCubeGoodWeight c sets block v sel L b ψ r κ
  let χ := affineBooleanCubeCutoff c sets block v sel L b ψ r κ
  have hw := affineBooleanCubeGoodWeight_spec c sets block v sel L b ψ r κ hψ hrange hzero hr hκ
  have hm : Measurable χ :=
    (affineBooleanCubeCutoff_contDiff c sets block v sel L b ψ r κ hψ).continuous.measurable
  have h01 := affineBooleanCubeCutoff_range c sets block v sel L b ψ r κ hrange
  let : IsFiniteMeasure (realDensityMeasure volume w) :=
    realDensityMeasure_finite volume w (hw.1.continuous.integrable_of_hasCompactSupport hw.2.1) hw.2.2.1
  let : IsFiniteMeasure (realDensityMeasure (blockCubeMeasure B (Fin h) α) χ) :=
    realDensityMeasure_finite _ χ (cutoff_integrable _ χ hm h01) (fun a => (h01 a).1)
  apply finiteMeasure_eq_of_integrals
  intro f _
  rw [realDensityMeasure_integral volume w hw.1.continuous.measurable hw.2.2.1,
    realDensityMeasure_integral _ χ hm (fun a => (h01 a).1)]
  exact affineBooleanCubeGoodWeight_integral_test c sets block v sel L b ψ r κ hr f

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineBooleanCubeComparison
namespace OAI

section

namespace Erdos3

variable {I O : Type*} [Fintype I] [fintypeO : Fintype O]

theorem affineSelectedInjection_norm_le (L : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (J : (O → ℝ) →L[ℝ] (I → ℝ)) {δ : ℝ} (hδ : 0 ≤ δ)
    (hL : δ * ‖L.symm.toContinuousLinearMap‖ ≤ 1) (hJ : ‖J‖ ≤ 1) :
    ‖affineSelectedInjection L J δ‖ ≤ 1 := by
  unfold affineSelectedInjection
  rw [norm_smul, Real.norm_of_nonneg hδ]
  calc
    _ ≤ δ * (‖L.symm.toContinuousLinearMap‖ * ‖J‖) :=
      mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) hδ
    _ = (δ * ‖L.symm.toContinuousLinearMap‖) * ‖J‖ := by ring
    _ ≤ 1 * 1 := mul_le_mul hL hJ (norm_nonneg _) zero_le_one
    _ = 1 := one_mul _

theorem selectedDerivative_affine (U : (I → ℝ) → (O → ℝ))
    (L : (I → ℝ) ≃L[ℝ] (I → ℝ)) (b : I → ℝ)
    (J : (O → ℝ) →L[ℝ] (I → ℝ)) (δ : ℝ) (x : I → ℝ)
    (hU : DifferentiableAt ℝ U (b + L x)) :
    selectedDerivative (fun y => U (b + L y)) (affineSelectedInjection L J δ) x =
      δ • selectedDerivative U J (b + L x) := by
  unfold selectedDerivative
  change (fderiv ℝ (fun y => U (b + L.toContinuousLinearMap y)) x).comp _ = _
  rw [affineSlice_fderiv U b L.toContinuousLinearMap x hU]
  ext y i
  simp [affineSelectedInjection]

omit fintypeO in
theorem invertible_smul_inverse [Fintype O] {A : (O → ℝ) →L[ℝ] (O → ℝ)}
    (hA : A.IsInvertible) {δ : ℝ} (hδ : δ ≠ 0) :
    (δ • A).IsInvertible ∧ (δ • A).inverse = δ⁻¹ • A.inverse := by
  have hr : (δ • A).comp (δ⁻¹ • A.inverse) = ContinuousLinearMap.id ℝ (O → ℝ) := by
    ext x i
    simp [smul_smul, hA.self_apply_inverse, hδ]
  have hl : (δ⁻¹ • A.inverse).comp (δ • A) = ContinuousLinearMap.id ℝ (O → ℝ) := by
    ext x i
    simp [smul_smul, hA.inverse_apply_self, hδ]
  exact ⟨ContinuousLinearMap.IsInvertible.of_inverse hr hl, ContinuousLinearMap.inverse_eq hr hl⟩

theorem selectedDerivative_affine_inverse_bound (U : (I → ℝ) → (O → ℝ))
    (L : (I → ℝ) ≃L[ℝ] (I → ℝ)) (b : I → ℝ)
    (J : (O → ℝ) →L[ℝ] (I → ℝ)) {δ K : ℝ} (hδ : 0 < δ) (x : I → ℝ)
    (hU : DifferentiableAt ℝ U (b + L x))
    (hinv : (selectedDerivative U J (b + L x)).IsInvertible)
    (hK : ‖(selectedDerivative U J (b + L x)).inverse‖ ≤ K) :
    (selectedDerivative (fun y => U (b + L y)) (affineSelectedInjection L J δ) x).IsInvertible ∧
      ‖(selectedDerivative (fun y => U (b + L y))
        (affineSelectedInjection L J δ) x).inverse‖ ≤ δ⁻¹ * K := by
  rw [selectedDerivative_affine U L b J δ x hU]
  obtain ⟨hi, he⟩ := invertible_smul_inverse hinv hδ.ne'
  refine ⟨hi, ?_⟩
  rw [he, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hδ.le)]
  exact mul_le_mul_of_nonneg_left hK (inv_nonneg.mpr hδ.le)

theorem selectedDerivative_affine_derivative_bound (U : (I → ℝ) → (O → ℝ))
    (hU : ContDiff ℝ 2 U) (L : (I → ℝ) ≃L[ℝ] (I → ℝ)) (b : I → ℝ)
    (J : (O → ℝ) →L[ℝ] (I → ℝ)) {δ H : ℝ} (hδ : 0 ≤ δ) (x : I → ℝ)
    (hH : ‖fderiv ℝ (selectedDerivative U J) (b + L x)‖ ≤ H) :
    ‖fderiv ℝ (selectedDerivative (fun y => U (b + L y))
      (affineSelectedInjection L J δ)) x‖ ≤ δ * H * ‖L.toContinuousLinearMap‖ := by
  let : NormedSpace ℝ ((O → ℝ) →L[ℝ] (O → ℝ)) := ContinuousLinearMap.toNormedSpace
  let : NormedSpace ℝ ((I → ℝ) →L[ℝ] ((O → ℝ) →L[ℝ] (O → ℝ))) :=
    ContinuousLinearMap.toNormedSpace
  have hA : ContDiff ℝ 1 (selectedDerivative U J) :=
    (hU.fderiv_right (by norm_num)).clm_comp contDiff_const
  have he : selectedDerivative (fun y => U (b + L y)) (affineSelectedInjection L J δ) =
      fun y => δ • selectedDerivative U J (b + L y) := by
    funext y
    exact selectedDerivative_affine U L b J δ y (hU.differentiable (by norm_num) _)
  rw [he]
  have hd := ((hA.differentiable one_ne_zero (b + L x)).hasFDerivAt.comp x
    (L.toContinuousLinearMap.hasFDerivAt.const_add b)).const_smul δ
  change ‖fderiv ℝ (δ • selectedDerivative U J ∘
    (fun y => b + L.toContinuousLinearMap y)) x‖ ≤ _
  rw [hd.fderiv]
  calc
    _ ≤ δ * ‖(fderiv ℝ (selectedDerivative U J) (b + L x)).comp L.toContinuousLinearMap‖ := by
      simpa only [Real.norm_of_nonneg hδ] using norm_smul_le δ
        ((fderiv ℝ (selectedDerivative U J) (b + L x)).comp L.toContinuousLinearMap)
    _ ≤ δ * (‖fderiv ℝ (selectedDerivative U J) (b + L x)‖ * ‖L.toContinuousLinearMap‖) :=
      mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) hδ
    _ ≤ δ * (H * ‖L.toContinuousLinearMap‖) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hH (norm_nonneg _)) hδ
    _ = _ := by ring

end Erdos3

end

section

namespace Erdos3

open scoped ContDiff

variable {D α : Type*} [Fintype D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  [decidableEqB : ∀ d, DecidableEq (B d)] [decidableEqO : ∀ d, DecidableEq (O d)] {h : D → ℕ}

variable (c : ∀ d, B d → ℝ) (sets : ∀ d, O d → Finset α)
  (block : ∀ d, O d → B d) (v : ∀ d, Fin (h d)) (sel : ∀ d, O d → Option α)
  (L : ∀ d, (BlockParameter (B d) (Fin (h d)) α → ℝ) ≃L[ℝ]
    (BlockParameter (B d) (Fin (h d)) α → ℝ))
  (b : ∀ d, BlockParameter (B d) (Fin (h d)) α → ℝ) (δ : D → ℝ)

omit decidableEqB decidableEqO in
theorem jointAffineBooleanSampler_contDiff
    [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)] :
    ContDiff ℝ ∞ (jointAffineBooleanSampler c sets L b) :=
  sigmaAxisSampler_contDiff _ (fun d =>
    (booleanSamplerMap_contDiff (c d) (sets d)).comp (contDiff_const.add (L d).contDiff))

omit decidableEqO in
theorem jointAffineBooleanInjection_norm_le [∀ d, DecidableEq (O d)]
    (hblock : ∀ d, Function.Injective (block d)) (hδ : ∀ d, 0 ≤ δ d)
    (hL : ∀ d, δ d * ‖(L d).symm.toContinuousLinearMap‖ ≤ 1) :
    ‖jointAffineBooleanInjection block v sel L δ‖ ≤ 1 :=
  sigmaAxisOperator_norm_le _ zero_le_one (fun d => affineSelectedInjection_norm_le
    (L d) _ (hδ d) (hL d) (booleanSelectedInjection_norm_le (block d) (hblock d) (v d) (sel d)))

theorem jointAffineBoolean_selected_inverse_bound
    (hcard : ∀ d o, (sets d o).card ≤ h d) (x : JointBlockParameter B h α → ℝ)
    (C κ : D → ℝ) (hC : ∀ d, 0 ≤ C d) (hκ : ∀ d, 0 < κ d) (hδ : ∀ d, 0 < δ d)
    (hc : ∀ d o, |c d (block d o)| ≤ C d)
    (hx : ∀ d z, |(b d + L d (fun i => x ⟨d, i⟩)) z| ≤ 1)
    (hdet : ∀ d, κ d ≤ |booleanMinorDeterminant (c d) (sets d) (block d) (v d) (sel d)
      (b d + L d (fun i => x ⟨d, i⟩))|)
    {K : ℝ} (hK : 0 ≤ K)
    (hcap : ∀ d, (δ d)⁻¹ * productMinorInverseBound (Fintype.card (O d)) (Fintype.card α)
      (h d) (C d) 1 (κ d) ≤ K) :
    (selectedDerivative (jointAffineBooleanSampler c sets L b)
      (jointAffineBooleanInjection block v sel L δ) x).IsInvertible ∧
    ‖(selectedDerivative (jointAffineBooleanSampler c sets L b)
      (jointAffineBooleanInjection block v sel L δ) x).inverse‖ ≤ K := by
  have haxis (d) := boolean_selected_inverse_bound (c d) (sets d) (block d) (v d) (sel d)
    (hcard d) (b d + L d (fun i => x ⟨d, i⟩)) (hC d) zero_le_one (hc d) (hx d) (hκ d) (hdet d)
  have hi (d) := selectedDerivative_affine_inverse_bound (booleanSamplerMap (c d) (sets d))
    (L d) (b d) (booleanSelectedInjection (block d) (v d) (sel d)) (hδ d) (fun i => x ⟨d, i⟩)
    ((booleanSamplerMap_contDiff (c d) (sets d)).differentiable (by norm_num) _) (haxis d).1 (haxis d).2
  exact sigmaAxisSampler_inverse_bound _ _ x
    (fun d => ((booleanSamplerMap_contDiff (c d) (sets d)).comp
      (contDiff_const.add (L d).contDiff)).differentiable (by norm_num) _)
    (fun d => (hi d).1) hK (fun d => (hi d).2.trans (hcap d))

theorem jointAffineBoolean_selected_derivative_bound
    (hcard : ∀ d o, (sets d o).card ≤ h d) (x : JointBlockParameter B h α → ℝ)
    (C : D → ℝ) (hC : ∀ d, 0 ≤ C d) (hδ : ∀ d, 0 ≤ δ d) (hδone : ∀ d, δ d ≤ 1)
    (hL : ∀ d, ‖(L d).toContinuousLinearMap‖ ≤ 1)
    (hc : ∀ d o, |c d (block d o)| ≤ C d)
    (hx : ∀ d z, |(b d + L d (fun i => x ⟨d, i⟩)) z| ≤ 1)
    {H : ℝ} (hH : 0 ≤ H)
    (hcap : ∀ d, productMinorDerivativeBound (Fintype.card (BlockParameter (B d) (Fin (h d)) α))
      (Fintype.card (O d)) (Fintype.card α) (h d) (C d) 1 ≤ H) :
    ‖fderiv ℝ (selectedDerivative (jointAffineBooleanSampler c sets L b)
      (jointAffineBooleanInjection block v sel L δ)) x‖ ≤ H := by
  apply sigmaAxisSampler_selected_fderiv_norm_le _
    (fun d => ((booleanSamplerMap_contDiff (c d) (sets d)).comp
      (contDiff_const.add (L d).contDiff)).of_le (WithTop.coe_le_coe.2 le_top)) _ x hH
  intro d
  have hd := selectedDerivative_affine_derivative_bound (booleanSamplerMap (c d) (sets d))
    ((booleanSamplerMap_contDiff (c d) (sets d)).of_le (WithTop.coe_le_coe.2 le_top)) (L d) (b d)
    (booleanSelectedInjection (block d) (v d) (sel d)) (hδ d) (fun i => x ⟨d, i⟩)
    ((boolean_selected_derivative_bound (c d) (sets d) (block d) (v d) (sel d)
      (hcard d) (b d + L d (fun i => x ⟨d, i⟩)) (hC d) le_rfl (hc d) (hx d)).trans (hcap d))
  exact hd.trans ((mul_le_mul (mul_le_of_le_one_left hH (hδone d)) (hL d)
    (norm_nonneg _) hH).trans_eq (mul_one _))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.JointAffineBooleanSource
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff BigOperators

variable {D α : Type*} [Fintype D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)] {h : D → ℕ}
  (c : ∀ d, B d → ℝ) (sets : ∀ d, O d → Finset α) (block : ∀ d, O d → B d)
  (v : ∀ d, Fin (h d)) (sel : ∀ d, O d → Option α)
  (L : ∀ d, (BlockParameter (B d) (Fin (h d)) α → ℝ) →L[ℝ]
    (BlockParameter (B d) (Fin (h d)) α → ℝ))
  (b : ∀ d, BlockParameter (B d) (Fin (h d)) α → ℝ)
  (ψ : ℝ → ℝ) (r : ∀ d, B d × Fin (h d) → ℝ) (κ : D → ℝ)

theorem jointAffineBooleanCutoff_contDiff (hψ : ContDiff ℝ ∞ ψ) :
    ContDiff ℝ 1 (jointAffineBooleanCutoff c sets block v sel L b ψ r κ) :=
  sigmaAxisWeight_contDiff _ (fun d =>
    (affineBooleanCubeCutoff_contDiff (fun _ : Unit => c d) (sets d)
      (fun _ => block d) (v d) (fun _ => sel d) (L d) (b d) ψ (r d) (fun _ => κ d) hψ).of_le
        (by norm_num))

theorem jointAffineBooleanCutoff_range (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (x : JointBlockParameter B h α → ℝ) :
    jointAffineBooleanCutoff c sets block v sel L b ψ r κ x ∈ Set.Icc (0 : ℝ) 1 :=
  product_cutoff_range _ (fun d => affineBooleanCubeCutoff_range (fun _ : Unit => c d) (sets d)
    (fun _ => block d) (v d) (fun _ => sel d) (L d) (b d) ψ (r d) (fun _ => κ d) hrange _)

theorem jointAffineBooleanGoodWeight_spec
    (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hr : ∀ d i, 0 < r d i) (hκ : ∀ d, 0 < κ d) :
    let w := jointAffineBooleanGoodWeight c sets block v sel L b ψ r κ
    ContDiff ℝ 1 w ∧ HasCompactSupport w ∧ (∀ x, 0 ≤ w x) ∧ (∫ x, |w x|) ≤ 1 ∧
      ∀ x ∈ tsupport w, (∀ s, |x s| ≤ 1) ∧ ∀ d, κ d ≤
        |booleanMinorDeterminant (c d) (sets d) (block d) (v d) (sel d)
          (b d + L d (fun i => x ⟨d, i⟩))| := by
  have hs (d) := affineBooleanCubeGoodWeight_spec (fun _ : Unit => c d) (sets d)
    (fun _ => block d) (v d) (fun _ => sel d) (L d) (b d) ψ (r d) (fun _ => κ d)
    hψ hrange hzero (hr d) (fun _ => hκ d)
  refine ⟨sigmaAxisWeight_contDiff _ (fun d => (hs d).1),
    sigmaAxisWeight_compact _ (fun d => (hs d).2.1),
    sigmaAxisWeight_nonneg _ (fun d => (hs d).2.2.1),
    sigmaAxisWeight_abs_mass_le_one _ (fun d => (hs d).2.2.2.1), ?_⟩
  intro x hx
  have hp (d) := (hs d).2.2.2.2 _ (sigmaAxisWeight_tsupport _ hx d)
  exact ⟨fun s => (hp s.1).1 s.2, fun d => (hp d).2 ()⟩

theorem jointAffineBooleanGoodWeight_measure
    (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hr : ∀ d i, 0 < r d i) (hκ : ∀ d, 0 < κ d) :
    realDensityMeasure volume (jointAffineBooleanGoodWeight c sets block v sel L b ψ r κ) =
      realDensityMeasure (jointBooleanSource h) (jointAffineBooleanCutoff c sets block v sel L b ψ r κ) := by
  let w := fun d => affineBooleanCubeGoodWeight (fun _ : Unit => c d) (sets d)
    (fun _ => block d) (v d) (fun _ => sel d) (L d) (b d) ψ (r d) (fun _ => κ d)
  let χ := fun d => affineBooleanCubeCutoff (fun _ : Unit => c d) (sets d)
    (fun _ => block d) (v d) (fun _ => sel d) (L d) (b d) ψ (r d) (fun _ => κ d)
  have hw (d) := affineBooleanCubeGoodWeight_spec (fun _ : Unit => c d) (sets d)
    (fun _ => block d) (v d) (fun _ => sel d) (L d) (b d) ψ (r d) (fun _ => κ d)
    hψ hrange hzero (hr d) (fun _ => hκ d)
  have hm (d) : Measurable (χ d) := (affineBooleanCubeCutoff_contDiff (fun _ : Unit => c d) (sets d)
    (fun _ => block d) (v d) (fun _ => sel d) (L d) (b d) ψ (r d) (fun _ => κ d) hψ).continuous.measurable
  have h01 (d) := affineBooleanCubeCutoff_range (fun _ : Unit => c d) (sets d)
    (fun _ => block d) (v d) (fun _ => sel d) (L d) (b d) ψ (r d) (fun _ => κ d) hrange
  change realDensityMeasure volume (sigmaAxisWeight w) =
    realDensityMeasure (sigmaAxisMeasure _) (sigmaAxisWeight χ)
  rw [← sigmaAxisMeasure_density w (fun d =>
    (hw d).1.continuous.integrable_of_hasCompactSupport (hw d).2.1) (fun d => (hw d).2.2.1)]
  have hlaw (d) : realDensityMeasure volume (w d) =
      realDensityMeasure (blockCubeMeasure (B d) (Fin (h d)) α) (χ d) :=
    affineBooleanCubeGoodWeight_measure (fun _ : Unit => c d) (sets d)
      (fun _ => block d) (v d) (fun _ => sel d) (L d) (b d) ψ (r d) (fun _ => κ d)
      hψ hrange hzero (hr d) (fun _ => hκ d)
  simp_rw [hlaw]
  exact sigmaAxisMeasure_withDensity _ χ (fun d => cutoff_integrable _ _ (hm d) (h01 d))
    (fun d x => (h01 d x).1)

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped ContDiff NNReal BigOperators

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)] {h : D → ℕ}

theorem jointAffineBoolean_translation_bound
    (c : ∀ d, B d → ℝ) (sets : ∀ d, O d → Finset α) (block : ∀ d, O d → B d)
    (hblock : ∀ d, Function.Injective (block d))
    (v : ∀ d, Fin (h d)) (sel : ∀ d, O d → Option α) (hcard : ∀ d o, (sets d o).card ≤ h d)
    (L : ∀ d, (BlockParameter (B d) (Fin (h d)) α → ℝ) ≃L[ℝ]
      (BlockParameter (B d) (Fin (h d)) α → ℝ))
    (b : ∀ d, BlockParameter (B d) (Fin (h d)) α → ℝ)
    (δ : D → ℝ) (hδ : ∀ d, 0 < δ d) (hδone : ∀ d, δ d ≤ 1)
    (hL : ∀ d, ‖(L d).toContinuousLinearMap‖ ≤ 1)
    (hLinv : ∀ d, δ d * ‖(L d).symm.toContinuousLinearMap‖ ≤ 1)
    (hbox : ∀ d x, (∀ z, |x z| ≤ 1) → ∀ z, |(b d + L d x) z| ≤ 1)
    (C : D → ℝ) (hC : ∀ d, 0 ≤ C d) (hc : ∀ d o, |c d (block d o)| ≤ C d)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    (r : ∀ d, B d × Fin (h d) → ℝ) (hr : ∀ d i, 0 < r d i)
    (κ : D → ℝ) (hκ : ∀ d, 0 < κ d) (K H : ℝ≥0)
    (hK : ∀ d, (δ d)⁻¹ * productMinorInverseBound (Fintype.card (O d)) (Fintype.card α)
      (h d) (C d) 1 (κ d) ≤ K)
    (hH : ∀ d, productMinorDerivativeBound (Fintype.card (BlockParameter (B d) (Fin (h d)) α))
      (Fintype.card (O d)) (Fintype.card α) (h d) (C d) 1 ≤ H)
    : ImageTranslationBound
      (realDensityMeasure (jointBooleanSource h)
        (jointAffineBooleanCutoff c sets block v sel (fun d => (L d).toContinuousLinearMap) b ψ r κ))
      (jointAffineBooleanSampler c sets L b)
      (jointAffineBooleanTranslationBudget (O := O) (α := α) C A T r κ K H) := by
  let w := jointAffineBooleanGoodWeight c sets block v sel (fun d => (L d).toContinuousLinearMap) b ψ r κ
  let U := jointAffineBooleanSampler c sets L b
  let J := jointAffineBooleanInjection block v sel L δ
  let S : ℝ≥0 := ⟨jointBooleanWeightBudget (O := O) (α := α) h C A T r κ,
    jointBooleanWeightBudget_nonneg h C hC A T r (fun d i => (hr d i).le) κ (fun d => (hκ d).le)⟩
  have hU : ContDiff ℝ 2 U := (jointAffineBooleanSampler_contDiff c sets L b).of_le (WithTop.coe_le_coe.2 le_top)
  have hJ : ‖J‖ ≤ 1 := jointAffineBooleanInjection_norm_le block v sel L δ hblock
    (fun d => (hδ d).le) hLinv
  have hw := jointAffineBooleanGoodWeight_spec c sets block v sel (fun d => (L d).toContinuousLinearMap)
    b ψ r κ hψ hrange hzero hr hκ
  have hb (x) (hx : x ∈ tsupport w) : ∀ z, |x z| ≤ 1 := (hw.2.2.2.2 x hx).1
  have hbx (x) (hx : x ∈ tsupport w) (d) (z) :
      |(b d + L d (fun i => x ⟨d, i⟩)) z| ≤ 1 := hbox d _ (fun i => hb x hx ⟨d, i⟩) z
  have hi (x) (hx : x ∈ tsupport w) := jointAffineBoolean_selected_inverse_bound c sets block v sel L b δ
    hcard x C κ hC hκ hδ hc (hbx x hx) ((hw.2.2.2.2 x hx).2) K.coe_nonneg hK
  have hHU₀ (x) (hx : x ∈ tsupport w) : ‖fderiv ℝ (selectedDerivative U J) x‖ ≤ H :=
    jointAffineBoolean_selected_derivative_bound c sets block v sel L b δ hcard x C hC
      (fun d => (hδ d).le) hδone hL hc (hbx x hx) H.coe_nonneg hH
  have hS := jointAffineBooleanGoodWeight_derivative_budget_s2 c sets block v sel hcard
    (fun d => (L d).toContinuousLinearMap) b hL
    (fun d x hx => hbox d _ (blockCubeFlatten_box hx)) C hC hc ψ hψ hrange hzero
    A T hLip hTransition r hr κ hκ
  let Q : ℝ≥0 := K * S + (Fintype.card (JointBlockParameter B h α) : ℝ≥0) * (K ^ 2 * H)
  have ht := imageTranslationBound_of_inverse_budget_s2 U hU J hJ w hw.1 hw.2.1 hw.2.2.1
    hw.2.2.2.1 K H S Q (fun x hx => (hi x hx).1) (fun x hx => (hi x hx).2)
    hHU₀ hS (by simp only [Q, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_pow]; exact le_rfl)
  have hSdef : S = Real.toNNReal (jointBooleanWeightBudget (O := O) (α := α) h C A T r κ) := by
    ext
    exact (Real.coe_toNNReal _ S.coe_nonneg).symm
  rw [jointAffineBooleanGoodWeight_measure c sets block v sel
    (fun d => (L d).toContinuousLinearMap) b ψ r κ hψ hrange hzero hr hκ] at ht
  simpa only [Q, hSdef, jointAffineBooleanTranslationBudget] using ht

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped ContDiff NNReal BigOperators

theorem jointAffineBooleanCutoff_loss {D α : Type*}
    [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
    {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)]
    [∀ d, Fintype (O d)] [∀ d, DecidableEq (O d)] {h : D → ℕ}
    (c : ∀ d, B d → ℝ) (sets : ∀ d, O d → Finset α) (block : ∀ d, O d → B d)
    (v : ∀ d, Fin (h d)) (sel : ∀ d, O d → Option α)
    (L : ∀ d, (BlockParameter (B d) (Fin (h d)) α → ℝ) →L[ℝ]
      (BlockParameter (B d) (Fin (h d)) α → ℝ))
    (b : ∀ d, BlockParameter (B d) (Fin (h d)) α → ℝ)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0)
    (r : ∀ d, B d × Fin (h d) → ℝ) (hr : ∀ d i, 0 < r d i)
    (κ : D → ℝ) (hκ : ∀ d, 0 < κ d) {η : ℝ}
    (hmass : 1-η ≤ ∫ x, jointAffineBooleanGoodWeight c sets block v sel L b ψ r κ x) :
    (∫ x, 1-jointAffineBooleanCutoff c sets block v sel L b ψ r κ x ∂jointBooleanSource h) ≤ η := by
  let : IsProbabilityMeasure (jointBooleanSource (B := B) (α := α) h) := jointBooleanSource_probability h
  have hs := jointAffineBooleanGoodWeight_spec c sets block v sel L b ψ r κ hψ hrange hzero hr hκ
  have hwi : Integrable (jointAffineBooleanGoodWeight c sets block v sel L b ψ r κ) :=
    hs.1.continuous.integrable_of_hasCompactSupport hs.2.1
  have hw0 : ∀ x, 0 ≤ jointAffineBooleanGoodWeight c sets block v sel L b ψ r κ x := hs.2.2.1
  have hχ : Measurable (jointAffineBooleanCutoff c sets block v sel L b ψ r κ) :=
    (jointAffineBooleanCutoff_contDiff c sets block v sel L b ψ r κ hψ).continuous.measurable
  have hχ01 : ∀ x, jointAffineBooleanCutoff c sets block v sel L b ψ r κ x ∈ Set.Icc (0 : ℝ) 1 :=
    jointAffineBooleanCutoff_range c sets block v sel L b ψ r κ hrange
  have hlaw : realDensityMeasure volume (jointAffineBooleanGoodWeight c sets block v sel L b ψ r κ) =
      realDensityMeasure (jointBooleanSource (B := B) (α := α) h) (jointAffineBooleanCutoff c sets block v sel L b ψ r κ) :=
    jointAffineBooleanGoodWeight_measure c sets block v sel L b ψ r κ hψ hrange hzero hr hκ
  exact cutoff_loss_of_density_mass (X := JointBlockParameter B h α → ℝ)
    (jointBooleanSource (B := B) (α := α) h) volume
    (jointAffineBooleanCutoff c sets block v sel L b ψ r κ) (jointAffineBooleanGoodWeight c sets block v sel L b ψ r κ)
    hχ hχ01 hwi hw0 hlaw hmass

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)] {h : D → ℕ}

theorem jointAffineBoolean_regularization_error_s2_oai
    (c : ∀ d, B d → ℝ) (sets : ∀ d, O d → Finset α) (block : ∀ d, O d → B d)
    (hblock : ∀ d, Function.Injective (block d))
    (v : ∀ d, Fin (h d)) (sel : ∀ d, O d → Option α) (hcard : ∀ d o, (sets d o).card ≤ h d)
    (L : ∀ d, (BlockParameter (B d) (Fin (h d)) α → ℝ) ≃L[ℝ]
      (BlockParameter (B d) (Fin (h d)) α → ℝ))
    (b : ∀ d, BlockParameter (B d) (Fin (h d)) α → ℝ)
    (δ : D → ℝ) (hδ : ∀ d, 0 < δ d) (hδone : ∀ d, δ d ≤ 1)
    (hL : ∀ d, ‖(L d).toContinuousLinearMap‖ ≤ 1)
    (hLinv : ∀ d, δ d * ‖(L d).symm.toContinuousLinearMap‖ ≤ 1)
    (hbox : ∀ d x, (∀ z, |x z| ≤ 1) → ∀ z, |(b d + L d x) z| ≤ 1)
    (C : D → ℝ) (hC : ∀ d, 0 ≤ C d) (hc : ∀ d o, |c d (block d o)| ≤ C d)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    (r : ∀ d, B d × Fin (h d) → ℝ) (hr : ∀ d i, 0 < r d i)
    (κ : D → ℝ) (hκ : ∀ d, 0 < κ d) (K H : ℝ≥0)
    (hK : ∀ d, (δ d)⁻¹ * productMinorInverseBound (Fintype.card (O d)) (Fintype.card α)
      (h d) (C d) 1 (κ d) ≤ K)
    (hH : ∀ d, productMinorDerivativeBound (Fintype.card (BlockParameter (B d) (Fin (h d)) α))
      (Fintype.card (O d)) (Fintype.card α) (h d) (C d) 1 ≤ H)
    {η : ℝ}
    (hmass : 1 - η ≤ ∫ x, jointAffineBooleanGoodWeight c sets block v sel
      (fun d => (L d).toContinuousLinearMap) b ψ r κ x)
    (ρ : ℝ≥0) (hρ : 0 < ρ) (φ : ((Σ d, O d) → ℝ) → ℝ)
    (hφ : Measurable φ) (hbound : ∀ x, ‖φ x‖ ≤ 1) :
    |(∫ x, regularizedImageDensity (jointBooleanSource h)
        (jointAffineBooleanSampler c sets L b) ρ x * φ x) -
      mappedTest (jointBooleanSource h) (jointAffineBooleanSampler c sets L b) φ| ≤
      2 * η + jointAffineBooleanTranslationBudget (O := O) (α := α) C A T r κ K H * ρ := by
  have htrans := jointAffineBoolean_translation_bound c sets block hblock v sel hcard L b δ
    hδ hδone hL hLinv hbox C hC hc ψ hψ hrange hzero A T hLip hTransition r hr κ hκ K H hK hH
  have hcut := jointAffineBooleanCutoff_loss c sets block v sel (fun d => (L d).toContinuousLinearMap)
    b ψ hψ hrange hzero r hr κ hκ hmass
  exact regularizedImageDensity_cutoff_error (jointBooleanSource h)
    (jointAffineBooleanCutoff c sets block v sel (fun d => (L d).toContinuousLinearMap) b ψ r κ)
    (jointAffineBooleanCutoff_contDiff _ _ _ _ _ _ _ _ _ _ hψ).continuous.measurable
    (jointAffineBooleanCutoff_range _ _ _ _ _ _ _ _ _ _ hrange)
    (jointAffineBooleanSampler c sets L b) (jointAffineBooleanSampler_contDiff c sets L b).continuous.measurable
    (jointAffineBooleanTranslationBudget (O := O) (α := α) C A T r κ K H) htrans hcut ρ hρ φ hφ hbound

end Erdos3

end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4} : type_of% @OAI.Erdos3.jointAffineBoolean_regularization_error_s2_oai.{u_1, u_2, u_3, u_4} := @OAI.Erdos3.jointAffineBoolean_regularization_error_s2_oai.{u_1, u_2, u_3, u_4}
