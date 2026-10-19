-- Prove2me | solution 1 for OAI.Erdos3.box_smooth_pair_correlation_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-17T11:11:51.920979+00:00
-- url     : https://prove2.me/submissions/09a4c5a5-7b62-48af-8772-bd04248c2246

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B116
import Definitions.Def_OAIE3v2B126
import Theorems.Thm_OAI_Erdos3_smooth_affinePair_probability_law_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.FiniteConditionedMass
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

theorem eventProbability_nonneg {Ω : Type*} [Fintype Ω] (p : FiniteProbabilityWeights Ω)
    (E : Ω → Prop) : 0 ≤ p.eventProbability E := by
  classical
  exact p.mean_nonneg (fun x => by split_ifs <;> norm_num)

end Erdos3.FiniteProbabilityWeights

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.TranslatedMixtureL1
namespace OAI

section

namespace Erdos3

open MeasureTheory

variable {I J : Type*} [Fintype I] [Fintype J]

omit [Fintype I] in
theorem pivotOutputDensity_formula (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (B : (J → ℝ) →L[ℝ] (I → ℝ)) (f : (J → ℝ) × (I → ℝ) → ℝ) (v : I → ℝ) :
    pivotOutputDensity A B f v = inverseJacobian A * ∫ y, f (y, A.symm (v - B y)) := by
  exact integral_const_mul _ _

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PivotJacobianBound
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

variable {I J : Type*} [Fintype I] [Fintype J]

theorem pivotSliceProfile_zero_outside (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (B : (J → ℝ) →L[ℝ] (I → ℝ)) {f : (J → ℝ) × (I → ℝ) → ℝ} {R : ℝ}
    (hf : ∀ p, R < ‖p‖ → f p = 0) (v : I → ℝ) (y : J → ℝ) (hy : R < ‖y‖) :
    pivotSliceProfile A B f v y = 0 :=
  hf _ (hy.trans_le (norm_fst_le (y, A.symm (v - B y))))

omit [Fintype I] in
theorem pivotOutputDensity_slice_formula (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (B : (J → ℝ) →L[ℝ] (I → ℝ)) (f : (J → ℝ) × (I → ℝ) → ℝ) (v : I → ℝ) :
    pivotOutputDensity A B f v = inverseJacobian A * ∫ y, pivotSliceProfile A B f v y :=
  pivotOutputDensity_formula A B f v

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

omit [DecidableEq I] in
theorem coordinateMatrix_entry_le_norm (f : (J → ℝ) →L[ℝ] (I → ℝ)) (i : I) (j : J) :
    |(LinearMap.toMatrix' f.toLinearMap) i j| ≤ ‖f‖ := by
  rw [LinearMap.toMatrix'_apply]
  calc
    |f (Pi.single j 1) i| ≤ ‖f (Pi.single j 1)‖ := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm (f (Pi.single j 1)) i
    _ ≤ ‖f‖ * ‖(Pi.single j 1 : J → ℝ)‖ := f.le_opNorm (Pi.single j 1)
    _ = ‖f‖ := by rw [Pi.norm_single, norm_one, mul_one]

theorem inverseJacobian_le_norm_bound (A : (I → ℝ) ≃L[ℝ] (I → ℝ)) {U : ℝ}
    (hA : ‖A.symm.toContinuousLinearMap‖ ≤ U) :
    inverseJacobian A ≤ (Fintype.card I).factorial * U ^ Fintype.card I := by
  have h := matrix_det_abs_le_uniform_bound
    (LinearMap.toMatrix' A.symm.toContinuousLinearMap.toLinearMap)
    (fun i j => (coordinateMatrix_entry_le_norm A.symm.toContinuousLinearMap i j).trans hA)
  rw [LinearMap.det_toMatrix'] at h
  exact h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueSliceCountingCost
namespace OAI

section

namespace Erdos3

theorem scalarResidue_card_mul_le (a b r v : ℤ) (hab : a ≤ b) (hr : 0 < r) :
    ((Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)).card : ℤ) * r ≤ b - a + r := by
  have hrQ : (0 : ℚ) < r := by exact_mod_cast hr
  have hc := Int.Ico_filter_modEq_card a b hr v
  have hcQ := congrArg (fun n : ℤ => (n : ℚ)) hc
  simp only [Int.cast_natCast, Int.cast_max, Int.cast_sub, Int.cast_zero] at hcQ
  have hn : (0 : ℚ) ≤ ((b - a : ℤ) : ℚ) / r :=
    div_nonneg (by exact_mod_cast sub_nonneg.mpr hab) hrQ.le
  have hbound : ((Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)).card : ℚ) ≤
      ((b - a : ℤ) : ℚ) / r + 1 := by
    rw [hcQ]
    apply max_le
    · have hx := Int.ceil_lt_add_one (((b : ℚ) - v) / r)
      have hy := Int.le_ceil (((a : ℚ) - v) / r)
      have heq : ((b : ℚ) - v) / r - ((a : ℚ) - v) / r = ((b - a : ℤ) : ℚ) / r := by
        push_cast
        ring
      linarith
    · linarith
  have hm := mul_le_mul_of_nonneg_right hbound hrQ.le
  have heq : (((b - a : ℤ) : ℚ) / r + 1) * r = (b - a : ℤ) + (r : ℚ) := by
    field_simp
  rw [heq] at hm
  exact_mod_cast hm

theorem scalarResidue_card_real_le (a b r v : ℤ) (hab : a ≤ b) (hr : 0 < r) :
    ((Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)).card : ℝ) ≤
      ((b - a : ℤ) : ℝ) / r + 1 := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have h := scalarResidue_card_mul_le a b r v hab hr
  have hR : ((Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)).card : ℝ) * r ≤
      ((b - a : ℤ) : ℝ) + r := by exact_mod_cast h
  have heq : ((b - a : ℤ) : ℝ) + r = (((b - a : ℤ) : ℝ) / r + 1) * r := by
    field_simp
  rw [heq] at hR
  exact (mul_le_mul_iff_left₀ hrR).mp hR

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.IndependentProductTransport
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem independentProductPMF_map {D X Y : Type*} [Fintype D]
    [Countable X] [MeasurableSpace X] [MeasurableSingletonClass X]
    [Countable Y] [MeasurableSpace Y] [MeasurableSingletonClass Y]
    (p : D → PMF X) (f : D → X → Y) :
    (independentProductPMF p).map (fun x i => f i (x i)) =
      independentProductPMF (fun i => (p i).map (f i)) := by
  apply PMF.toMeasure_injective
  rw [← PMF.toMeasure_map (fun (x : D → X) i => f i (x i)) _ (measurable_of_countable _)]
  simp only [independentProductPMF, Measure.toPMF_toMeasure]
  rw [Measure.pi_map_pi (fun i => (measurable_of_countable (f i)).aemeasurable)]
  congr 1
  funext i
  exact PMF.toMeasure_map (f i) (p i) (measurable_of_countable _)

theorem independentArrayRows_injective {J I X : Type*} :
    Function.Injective (independentArrayRows (J := J) (I := I) (X := X)) := by
  intro x y h
  funext ji
  exact congrFun (congrFun h ji.2) ji.1

theorem independentProductPMF_rows {J I X : Type*} [Fintype J] [Fintype I]
    [Countable X] [MeasurableSpace X] [MeasurableSingletonClass X]
    (p : J × I → PMF X) :
    (independentProductPMF p).map independentArrayRows =
      independentProductPMF (fun i => independentProductPMF (fun j => p (j, i))) := by
  ext y
  let z : J × I → X := fun ji => y ji.2 ji.1
  change (independentProductPMF p).map independentArrayRows (independentArrayRows z) = _
  rw [pmf_map_injective_at _ _ independentArrayRows_injective]
  simp only [independentProductPMF_apply, Fintype.prod_prod_type, z]
  exact Finset.prod_comm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerFiberUniformBound
namespace OAI

section

namespace Erdos3

open scoped Matrix

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

theorem normalizedPivotEquiv_coe (A : Matrix I I ℤ) (hA : A.det ≠ 0)
    (S P : I → ℝ) (hS : ∀ i, 0 < S i) (hP : ∀ i, 0 < P i) :
    (normalizedPivotEquiv A hA S P hS hP).toContinuousLinearMap =
      matrixSupCLM (normalizedIntegerPivot A S P) :=
  (matrixSupCLM_inverse_spec (normalizedIntegerPivot A S P)
    (normalizedIntegerPivot_det_ne_zero A hA S P hS hP)).1.choose_spec

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
open scoped BigOperators NNReal

theorem splitSmoothProductProfile_join (J I : Type*) [Fintype J] [Fintype I] :
    splitInputProfile (splitSmoothProductProfile J I) = smoothProductProfile (J ⊕ I) := by
  funext x
  simp [splitInputProfile, splitSmoothProductProfile, smoothProductProfile, Fintype.prod_sum_type]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SpatialPivotNormalization
namespace OAI

section

namespace Erdos3

theorem normalizedPivotEquiv_inverse_eq {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℤ) (hA : A.det ≠ 0) (S P : I → ℝ)
    (hS : ∀ i, 0 < S i) (hP : ∀ i, 0 < P i) :
    (normalizedPivotEquiv A hA S P hS hP).symm.toContinuousLinearMap =
      (matrixSupCLM (normalizedIntegerPivot A S P)).inverse := by
  rw [← normalizedPivotEquiv_coe A hA S P hS hP, ContinuousLinearMap.inverse_equiv]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.PivotDensityCap
namespace OAI

section

namespace Erdos3

open MeasureTheory

variable {I J : Type*} [Fintype I] [Fintype J]

theorem pivotOutputDensity_abs_le (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (B : (J → ℝ) →L[ℝ] (I → ℝ)) (f : (J → ℝ) × (I → ℝ) → ℝ)
    {R H : ℝ} (hR : 0 ≤ R) (hsupport : ∀ p, R < ‖p‖ → f p = 0)
    (hbound : ∀ p, ‖f p‖ ≤ H) (v : I → ℝ) :
    |pivotOutputDensity A B f v| ≤ inverseJacobian A * H * (2 * R) ^ Fintype.card J := by
  have hi := integral_norm_le_box (pivotSliceProfile A B f v) hR
    (pivotSliceProfile_zero_outside A B hsupport v) (fun y _ => hbound _)
  have hb := (norm_integral_le_integral_norm (f := pivotSliceProfile A B f v)).trans hi
  rw [pivotOutputDensity_slice_formula, abs_mul, abs_of_pos (inverseJacobian_pos A)]
  have h := mul_le_mul_of_nonneg_left hb (inverseJacobian_pos A).le
  simpa only [Real.norm_eq_abs, mul_assoc] using h

theorem pivotOutputDensity_abs_le_uniform [DecidableEq I]
    (A : (I → ℝ) ≃L[ℝ] (I → ℝ)) (B : (J → ℝ) →L[ℝ] (I → ℝ))
    (f : (J → ℝ) × (I → ℝ) → ℝ) {R H U : ℝ} (hR : 0 ≤ R) (hH : 0 ≤ H)
    (hsupport : ∀ p, R < ‖p‖ → f p = 0) (hbound : ∀ p, ‖f p‖ ≤ H)
    (hinv : ‖A.symm.toContinuousLinearMap‖ ≤ U) (v : I → ℝ) :
    |pivotOutputDensity A B f v| ≤
      ((Fintype.card I).factorial * U ^ Fintype.card I) * H * (2 * R) ^ Fintype.card J :=
  (pivotOutputDensity_abs_le A B f hR hsupport hbound v).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (inverseJacobian_le_norm_bound A hinv) hH) (by positivity))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ScaledInputProbability
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped Matrix BigOperators

variable {I J : Type*} [Fintype I] [Fintype J]

theorem scaledInputPMF_apply (f : (J → ℝ) × (I → ℝ) → ℝ) (hf0 : ∀ p, 0 ≤ f p)
    (S : I → ℝ) (T : J → ℝ) (hS : ∀ i, 0 < S i) (hT : ∀ j, 0 < T j)
    {R : ℝ} (hsupport : ∀ p, R < ‖p‖ → f p = 0) (hM : 0 < scaledInputMass f S T)
    (p : (I → ℤ) × (J → ℤ)) :
    (scaledInputPMF f hf0 S T hS hT hsupport hM p).toReal =
      scaledIntegerWeight f S T p / scaledInputWeightSum f S T :=
  realWeightPMF_apply _ _ _ _ p

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.SmoothSplitSampling
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

theorem smoothCoefficientPMF_apply (S : ℝ) (hS : 0 < S) (k : ℤ) :
    (smoothCoefficientPMF S hS k).toReal = smoothProbabilityProfile ((k : ℝ) / S) / smoothSampleSum S :=
  realWeightPMF_apply _ _ _ _ k

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem smoothProductPMF_apply {I : Type*} [Fintype I]
    (S : I → ℝ) (hS : ∀ i, 0 < S i) (z : I → ℤ) :
    (smoothProductPMF S hS z).toReal = ∏ i, (smoothCoefficientPMF (S i) (hS i) (z i)).toReal := by
  rw [smoothProductPMF, realWeightPMF_apply, smoothProductSamples_sum S hS]
  simp only [smoothProductProfile, smoothCoefficientPMF_apply, Finset.prod_div_distrib]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem scaledInputWeightSum_splitSmoothProductProfile {I J : Type*}
    [Fintype I] [Fintype J] (S : I → ℝ) (T : J → ℝ)
    (hS : ∀ i, 0 < S i) (hT : ∀ j, 0 < T j) :
    scaledInputWeightSum (splitSmoothProductProfile J I) S T =
      (∏ i, smoothSampleSum (S i)) * ∏ j, smoothSampleSum (T j) := by
  have hscale : ∀ k, 0 < Sum.elim T S k := by intro k; cases k <;> simp [hS, hT]
  unfold scaledInputWeightSum
  rw [← splitInputProfile_sample_sum, splitSmoothProductProfile_join,
    smoothProductSamples_sum _ hscale]
  simp [Fintype.prod_sum_type, mul_comm]

theorem scaledInputPMF_splitSmoothProductProfile {I J : Type*}
    [Fintype I] [Fintype J] (S : I → ℝ) (T : J → ℝ)
    (hS : ∀ i, 0 < S i) (hT : ∀ j, 0 < T j)
    (hM : 0 < scaledInputMass (splitSmoothProductProfile J I) S T)
    (p : (I → ℤ) × (J → ℤ)) :
    (scaledInputPMF (splitSmoothProductProfile J I) (fun z => (splitSmoothProductProfile_range J I z).1)
      S T hS hT (splitSmoothProductProfile_zero_outside J I) hM p).toReal =
      (smoothProductPMF S hS p.1).toReal * (smoothProductPMF T hT p.2).toReal := by
  rw [scaledInputPMF_apply, scaledInputWeightSum_splitSmoothProductProfile S T hS hT]
  simp only [smoothProductPMF, realWeightPMF_apply, smoothProductSamples_sum S hS,
    smoothProductSamples_sum T hT,
    scaledIntegerWeight, splitSmoothProductProfile]
  ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ShiftedSmoothSelectedMarginal
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem pmf_map_finite_sum {X Y : Type*} [DecidableEq Y]
    (p : PMF X) (S : Finset X) (hp : ∀ x ∉ S, (p x).toReal = 0)
    (F : X → Y) (y : Y) :
    (p.map F y).toReal = ∑ x ∈ S, (p x).toReal * (if F x = y then 1 else 0) := by
  rw [pmf_map_toReal_indicator]
  exact (hasSum_sum_of_ne_finset_zero (fun x hx => by rw [hp x hx, zero_mul])).tsum_eq

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem pmf_image_finite_real_mean {X Y : Type*} [DecidableEq Y]
    (p : PMF X) (S : Finset X) (hp : ∀ x ∉ S, (p x).toReal = 0)
    (F : X → Y) (T : Finset Y) (hT : ∀ x ∈ S, F x ∈ T) (φ : Y → ℝ) :
    (∑' x, (p x).toReal * φ (F x)) = ∑ y ∈ T, (p.map F y).toReal * φ y := by
  have hs : (∑' x, (p x).toReal * φ (F x)) = ∑ x ∈ S, (p x).toReal * φ (F x) :=
    (hasSum_sum_of_ne_finset_zero (fun x hx => by rw [hp x hx, zero_mul])).tsum_eq
  rw [hs]
  simp_rw [pmf_map_finite_sum p S hp F, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.sum_eq_single (F x)]
  · simp
  · intro y _ hy
    simp [Ne.symm hy]
  · intro hn
    exact (hn (hT x hx)).elim

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem smoothProductPMF_eq_independent {I : Type*} [Fintype I]
    (S : I → ℝ) (hS : ∀ i, 0 < S i) :
    smoothProductPMF S hS = independentProductPMF (fun i => smoothCoefficientPMF (S i) (hS i)) := by
  ext z
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [smoothProductPMF_apply, independentProductPMF_toReal]

theorem smoothProductPMF_rows {J I : Type*} [Fintype J] [Fintype I]
    (S : J × I → ℝ) (hS : ∀ i, 0 < S i) :
    (smoothProductPMF S hS).map independentArrayRows =
      independentProductPMF (fun i => smoothProductPMF (fun j => S (j, i)) (fun j => hS (j, i))) := by
  simp only [smoothProductPMF_eq_independent]
  exact independentProductPMF_rows _

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem smoothInputSplit_join {I J D X : Type*} (e : (I ⊕ J) ≃ D) (p : (I → X) × (J → X)) :
    smoothInputSplit e (smoothInputJoin e p) = p := by
  ext <;> simp [smoothInputSplit, smoothInputJoin]

theorem smoothInputJoin_split {I J D X : Type*} (e : (I ⊕ J) ≃ D) (z : D → X) :
    smoothInputJoin e (smoothInputSplit e z) = z := by
  funext d
  obtain ⟨c, rfl⟩ := e.surjective d
  cases c <;> simp [smoothInputSplit, smoothInputJoin]

theorem smoothInputSplit_injective {I J D X : Type*} (e : (I ⊕ J) ≃ D) :
    Function.Injective (smoothInputSplit (X := X) e) := by
  intro x y h
  have h' := congrArg (smoothInputJoin e) h
  simpa only [smoothInputJoin_split] using h'

theorem smoothInputSplit_law {I J D : Type*} [Fintype I] [Fintype J] [Fintype D]
    (e : (I ⊕ J) ≃ D) (S : D → ℝ) (hS : ∀ d, 0 < S d)
    (hM : 0 < scaledInputMass (splitSmoothProductProfile J I)
      (fun i => S (e (.inl i))) (fun j => S (e (.inr j)))) :
    (smoothProductPMF S hS).map (smoothInputSplit e) =
      scaledInputPMF (splitSmoothProductProfile J I)
        (fun z => (splitSmoothProductProfile_range J I z).1)
        (fun i => S (e (.inl i))) (fun j => S (e (.inr j)))
        (fun i => hS (e (.inl i))) (fun j => hS (e (.inr j)))
        (splitSmoothProductProfile_zero_outside J I) hM := by
  ext p
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  nth_rw 1 [← smoothInputSplit_join e p]
  rw [pmf_map_injective_at _ _ (smoothInputSplit_injective e),
    scaledInputPMF_splitSmoothProductProfile, smoothProductPMF_apply,
    smoothProductPMF_apply, smoothProductPMF_apply]
  rw [← e.prod_comp]
  simp only [Fintype.prod_sum_type, smoothInputJoin, Equiv.symm_apply_apply, Sum.elim_inl,
    Sum.elim_inr]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.IntegerBoxCharacterBound
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem integerInterval_indicator_expect (a b : ℤ) (hab : a ≤ b) (E : ℤ → Prop)
    [DecidablePred E] :
    (𝔼 x : Finset.Ico a b, if E x then (1 : ℝ) else 0) =
      ((Finset.filter E (Finset.Ico a b)).card : ℝ) / ((b - a : ℤ) : ℝ) := by
  classical
  rw [Fintype.expect_eq_sum_div_card,
    Finset.sum_coe_sort (Finset.Ico a b) (fun x : ℤ => if E x then (1 : ℝ) else 0),
    Fintype.card_coe]
  have hcard : ((Finset.Ico a b).card : ℝ) = ((b - a : ℤ) : ℝ) := by
    exact_mod_cast Int.card_Ico_of_le a b hab
  rw [hcard]
  congr 1
  simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SmoothAffinePairLaw
namespace OAI


namespace Erdos3

open scoped BigOperators Matrix Classical

theorem affinePairMatrix_mulVec {J : Type*} [Fintype J] (t u : J → ℤ)
    (w : Option J → ℤ) :
    affinePairMatrix t u *ᵥ w =
      ![w none + ∑ j, t j * w (some j), w none + ∑ j, u j * w (some j)] := by
  ext i
  fin_cases i <;> simp [affinePairMatrix, Matrix.mulVec, dotProduct, Fintype.sum_option]

theorem mem_affinePairImage_iff {J : Type*} [Fintype J] (t u : J → ℤ) (v : Fin 2 → ℤ) :
    v ∈ affinePairImage t u ↔ ∃ x : ℤ, ∃ V : J → ℤ,
      x + ∑ j, t j * V j = v 0 ∧ x + ∑ j, u j * V j = v 1 := by
  constructor
  · rintro ⟨w, hw⟩
    change affinePairMatrix t u *ᵥ w = v at hw
    rw [affinePairMatrix_mulVec] at hw
    exact ⟨w none, (fun j => w (some j)), congrFun hw 0, congrFun hw 1⟩
  · rintro ⟨x, V, h0, h1⟩
    refine ⟨(fun c => Option.elim c x V), ?_⟩
    change affinePairMatrix t u *ᵥ (fun c => Option.elim c x V) = v
    rw [affinePairMatrix_mulVec]
    ext i
    fin_cases i
    · exact h0
    · exact h1

theorem affinePairImage_iff_content_dvd {J : Type*} [Fintype J]
    (t u : J → ℤ) (v : Fin 2 → ℤ) :
    v ∈ affinePairImage t u ↔ BohrLattice.Primitive.content (fun j => u j - t j) ∣ v 1 - v 0 := by
  rw [mem_affinePairImage_iff]
  constructor
  · rintro ⟨x, V, h0, h1⟩
    have he : v 1 - v 0 = ∑ j, (u j - t j) * V j := by
      rw [← h0, ← h1]
      simp only [sub_mul, Finset.sum_sub_distrib]
      ring
    rw [he]
    exact Finset.dvd_sum (fun j _ => dvd_mul_of_dvd_left
      (BohrLattice.Primitive.content_dvd (fun j => u j - t j) j) (V j))
  · rintro ⟨c, hc⟩
    obtain ⟨b, hb⟩ := BohrLattice.Primitive.exists_bezout_finset Finset.univ (fun j => u j - t j)
    have hb' : ∑ j, b j * (u j - t j) = BohrLattice.Primitive.content (fun j => u j - t j) := hb
    have he : (∑ j, u j * (c * b j)) - (∑ j, t j * (c * b j)) =
        BohrLattice.Primitive.content (fun j => u j - t j) * c := by
      calc
        _ = ∑ j, (u j * (c * b j) - t j * (c * b j)) := by rw [Finset.sum_sub_distrib]
        _ = c * ∑ j, b j * (u j - t j) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring
        _ = _ := by rw [hb']; ring
    refine ⟨v 0 - ∑ j, t j * (c * b j), (fun j => c * b j), ?_, ?_⟩
    · ring
    · linarith

end Erdos3


namespace Erdos3

open scoped Matrix Classical

theorem affinePairPivot_columns {J : Type*} [DecidableEq J] (t u : J → ℤ) (k : J) :
    Matrix.fromCols (affinePairPivot t u k) (affinePairFree t u k) =
      (affinePairMatrix t u).submatrix id (affinePairColumnEquiv k) := by
  ext i c
  rcases c with j | j
  · fin_cases i <;> fin_cases j <;>
      simp [affinePairPivot, affinePairMatrix, affinePairColumnEquiv, Matrix.submatrix]
  · rfl

end Erdos3


namespace Erdos3

open scoped Matrix

theorem normalized_affinePairPivot {J : Type*} (t u : J → ℤ) (k : J)
    {H L : ℝ} (hH : H ≠ 0) (hL : L ≠ 0) :
    normalizedIntegerPivot (affinePairPivot t u k) (affinePairScale H L) (fun _ => H) =
      !![1, (t k : ℝ) / L; 1, (u k : ℝ) / L] := by
  ext i j
  rw [normalizedIntegerPivot_entry]
  fin_cases i <;> fin_cases j <;> simp [affinePairPivot, affinePairScale, hH] <;> field_simp

theorem normalized_affinePairPivot_det {J : Type*} (t u : J → ℤ) (k : J)
    {H L : ℝ} (hH : H ≠ 0) (hL : L ≠ 0) :
    (normalizedIntegerPivot (affinePairPivot t u k) (affinePairScale H L) (fun _ => H)).det =
      ((u k - t k : ℤ) : ℝ) / L := by
  rw [normalized_affinePairPivot t u k hH hL]
  simp [Matrix.det_fin_two, sub_div]

theorem normalized_affinePairPivot_inverse {J : Type*} (t u : J → ℤ) (k : J)
    {H L C κ : ℝ} (hH : H ≠ 0) (hL : L ≠ 0) (hC : 1 ≤ C) (hκ : 0 < κ)
    (ht : |(t k : ℝ) / L| ≤ C) (hu : |(u k : ℝ) / L| ≤ C)
    (hgap : κ ≤ |((u k - t k : ℤ) : ℝ) / L|) :
    ‖(matrixSupCLM (normalizedIntegerPivot (affinePairPivot t u k)
      (affinePairScale H L) (fun _ => H))).inverse‖ ≤ 4 * C / κ := by
  have hentry : ∀ i j, |normalizedIntegerPivot (affinePairPivot t u k)
      (affinePairScale H L) (fun _ => H) i j| ≤ C := by
    rw [normalized_affinePairPivot t u k hH hL]
    intro i j
    fin_cases i <;> fin_cases j
    · simpa using hC
    · exact ht
    · simpa using hC
    · exact hu
  have hd : κ ≤ |(normalizedIntegerPivot (affinePairPivot t u k)
      (affinePairScale H L) (fun _ => H)).det| := by
    rwa [normalized_affinePairPivot_det t u k hH hL]
  have h := (matrixSupCLM_inverse_norm_le _ (zero_le_one.trans hC) hentry hκ hd).2
  norm_num [mul_div_assoc, ← mul_assoc] at h
  simpa only [mul_div_assoc] using h

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.IntervalDivisorProbability
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem intervalUniformWeights_mean (a b : ℤ) (hab : a < b) (f : Finset.Ico a b → ℝ) :
    (intervalUniformWeights a b hab).mean f = 𝔼 x, f x := by
  let : Nonempty (Finset.Ico a b) := ⟨⟨a, Finset.mem_Ico.mpr ⟨le_rfl, hab⟩⟩⟩
  unfold intervalUniformWeights
  exact FiniteProbabilityWeights.uniform_mean f

theorem interval_mod_probability (a b m v : ℤ) (hab : a < b) (hm : 0 < m) :
    (intervalUniformWeights a b hab).eventProbability (fun x => (x : ℤ) ≡ v [ZMOD m]) ≤
      1 / (m : ℝ) + 1 / ((b - a : ℤ) : ℝ) := by
  have hL : (0 : ℝ) < ((b - a : ℤ) : ℝ) := by exact_mod_cast sub_pos.mpr hab
  unfold FiniteProbabilityWeights.eventProbability
  rw [intervalUniformWeights_mean,
    @integerInterval_indicator_expect a b hab.le (fun x : ℤ => x ≡ v [ZMOD m])
      (fun _ => Classical.propDecidable _)]
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have heq : (((b - a : ℤ) : ℝ) / (m : ℝ) + 1) / ((b - a : ℤ) : ℝ) =
      1 / (m : ℝ) + 1 / ((b - a : ℤ) : ℝ) := by
    field_simp
  have hdiv := div_le_div_of_nonneg_right
    (scalarResidue_card_real_le a b m v hab.le hm) hL.le
  refine le_of_eq_of_le ?_ (hdiv.trans_eq heq)
  rw [div_eq_mul_inv, div_eq_mul_inv]
  congr 2
  apply congrArg Finset.card
  ext x
  simp

theorem interval_divisor_probability (a b m v : ℤ) (hab : a < b) (hm : 0 < m) :
    (intervalUniformWeights a b hab).eventProbability (fun x => m ∣ (x : ℤ) - v) ≤
      1 / (m : ℝ) + 1 / ((b - a : ℤ) : ℝ) := by
  have heq : (fun x : Finset.Ico a b => m ∣ (x : ℤ) - v) =
      (fun x : Finset.Ico a b => (x : ℤ) ≡ v [ZMOD m]) := by
    funext x
    exact propext (by rw [Int.modEq_iff_dvd, dvd_sub_comm])
  rw [heq]
  exact interval_mod_probability a b m v hab hm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ScalarDominatedSlack
namespace OAI

section

namespace Erdos3

open scoped BigOperators

namespace FiniteProbabilityWeights

theorem mean_mul_const {X : Type*} [Fintype X] (p : FiniteProbabilityWeights X)
    (f : X → ℝ) (c : ℝ) : p.mean (fun x => f x * c) = p.mean f * c := by
  simp only [mean, ← mul_assoc, Finset.sum_mul]

end FiniteProbabilityWeights

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CellResidueCorrelation
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem finite_fiber_mean_square {Ω R : Type*} [Fintype Ω] [DecidableEq R]
    (p : FiniteProbabilityWeights Ω) (F : Ω → R) (e : Ω → ℝ) (r : R) :
    (p.mean (fun x => if F x = r then e x else 0)) ^ 2 ≤
      p.eventProbability (fun x => F x = r) *
        p.mean (fun x => if F x = r then e x ^ 2 else 0) := by
  have h := p.mean_mul_sq_le (fun x => if F x = r then (1 : ℝ) else 0)
    (fun x => if F x = r then e x else 0)
  have h1 : (fun x => (if F x = r then (1 : ℝ) else 0) *
      (if F x = r then e x else 0)) = (fun x => if F x = r then e x else 0) := by
    funext x; split_ifs <;> simp
  have h2 : (fun x => (if F x = r then (1 : ℝ) else 0) ^ 2) =
      (fun x => if F x = r then (1 : ℝ) else 0) := by
    funext x; split_ifs <;> norm_num
  have h3 : (fun x => (if F x = r then e x else 0) ^ 2) =
      (fun x => if F x = r then e x ^ 2 else 0) := by
    funext x; split_ifs <;> norm_num
  rw [h1, h2, h3] at h
  have hmass : p.mean (fun x => if F x = r then (1 : ℝ) else 0) =
      p.eventProbability (fun x => F x = r) := by
    unfold FiniteProbabilityWeights.eventProbability
    apply congrArg p.mean
    funext x
    split_ifs <;> rfl
  rw [hmass] at h
  exact h

theorem finite_fiber_energy_sum {Ω R : Type*} [Fintype Ω] [Fintype R] [DecidableEq R]
    (p : FiniteProbabilityWeights Ω) (F : Ω → R) (e : Ω → ℝ) :
    (∑ r, p.mean (fun x => if F x = r then e x ^ 2 else 0)) =
      p.mean (fun x => e x ^ 2) := by
  rw [← p.mean_sum]
  congr 1
  funext x
  simp

theorem finite_fiber_square_sum_le {Ω R : Type*}
    [Fintype Ω] [Fintype R] [DecidableEq R]
    (p : FiniteProbabilityWeights Ω) (F : Ω → R) (e : Ω → ℝ) {c : ℝ}
    (hmass : ∀ r, p.eventProbability (fun x => F x = r) ≤ c) :
    (∑ r, (p.mean (fun x => if F x = r then e x else 0)) ^ 2) ≤
      c * p.mean (fun x => e x ^ 2) := by
  calc
    _ ≤ ∑ r, c * p.mean (fun x => if F x = r then e x ^ 2 else 0) := by
      apply Finset.sum_le_sum
      intro r _
      apply (finite_fiber_mean_square p F e r).trans
      exact mul_le_mul_of_nonneg_right (hmass r)
        (p.mean_nonneg (fun x => by split_ifs; exact sq_nonneg _; exact le_rfl))
    _ = _ := by rw [← Finset.mul_sum, finite_fiber_energy_sum]

theorem finite_residue_energy_bound {Ω R : Type*}
    [Fintype Ω] [Fintype R] [Nonempty R] [DecidableEq R]
    (p : FiniteProbabilityWeights Ω) (F : Ω → R) (e : Ω → ℝ) {K : ℝ}
    (hmass : ∀ r, p.eventProbability (fun x => F x = r) ≤ K / Fintype.card R) :
    (Fintype.card R : ℝ) *
        (∑ r, (p.mean (fun x => if F x = r then |e x| else 0)) ^ 2) ≤
      K * p.mean (fun x => e x ^ 2) := by
  have hcard : (0 : ℝ) < Fintype.card R := by exact_mod_cast Fintype.card_pos
  have h := finite_fiber_square_sum_le p F (fun x => |e x|) hmass
  simp only [sq_abs] at h
  calc
    _ ≤ (Fintype.card R : ℝ) * ((K / Fintype.card R) * p.mean (fun x => e x ^ 2)) :=
      mul_le_mul_of_nonneg_left h hcard.le
    _ = _ := by field_simp

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem finite_matching_residue_mean {X Y R : Type*}
    [Fintype X] [Fintype Y] [Fintype R] [DecidableEq R]
    (p : FiniteProbabilityWeights X) (q : FiniteProbabilityWeights Y)
    (F : X → R) (G : Y → R) (e : X → ℝ) (d : Y → ℝ) :
    p.mean (fun x => q.mean (fun y => if F x = G y then |e x| * |d y| else 0)) =
      ∑ r, p.mean (fun x => if F x = r then |e x| else 0) *
        q.mean (fun y => if G y = r then |d y| else 0) := by
  have hpoint (x : X) (y : Y) :
      (if F x = G y then |e x| * |d y| else 0) =
        ∑ r, (if F x = r then |e x| else 0) * (if G y = r then |d y| else 0) := by
    symm
    rw [Finset.sum_eq_single (F x)]
    · by_cases h : F x = G y <;> simp [h, eq_comm]
    · intro r _ hr
      simp [Ne.symm hr]
    · simp
  simp_rw [hpoint, q.mean_sum, p.mean_sum]
  apply Finset.sum_congr rfl
  intro r _
  simp_rw [q.mean_const_mul, p.mean_mul_const]

theorem finite_matching_residue_energy {X Y R : Type*}
    [Fintype X] [Fintype Y] [Fintype R] [Nonempty R] [DecidableEq R]
    (p : FiniteProbabilityWeights X) (q : FiniteProbabilityWeights Y)
    (F : X → R) (G : Y → R) (e : X → ℝ) (d : Y → ℝ) {K : ℝ}
    (hp : ∀ r, p.eventProbability (fun x => F x = r) ≤ K / Fintype.card R)
    (hq : ∀ r, q.eventProbability (fun y => G y = r) ≤ K / Fintype.card R) :
    (Fintype.card R : ℝ) *
        p.mean (fun x => q.mean (fun y => if F x = G y then |e x| * |d y| else 0)) ≤
      K / 2 * (p.mean (fun x => e x ^ 2) + q.mean (fun y => d y ^ 2)) := by
  rw [finite_matching_residue_mean]
  have he := finite_residue_energy_bound p F e hp
  have hd := finite_residue_energy_bound q G d hq
  have hs : 2 * (∑ r, p.mean (fun x => if F x = r then |e x| else 0) *
      q.mean (fun y => if G y = r then |d y| else 0)) ≤
      (∑ r, (p.mean (fun x => if F x = r then |e x| else 0)) ^ 2) +
      (∑ r, (q.mean (fun y => if G y = r then |d y| else 0)) ^ 2) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro r _
    nlinarith [sq_nonneg (p.mean (fun x => if F x = r then |e x| else 0) -
      q.mean (fun y => if G y = r then |d y| else 0))]
  have hscaled := mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg (α := ℝ) (Fintype.card R))
  nlinarith only [hscaled, he, hd]

theorem finite_matching_kernel_error {X Y R : Type*}
    [Fintype X] [Fintype Y] [Fintype R] [Nonempty R] [DecidableEq R]
    (p : FiniteProbabilityWeights X) (q : FiniteProbabilityWeights Y)
    (F : X → R) (G : Y → R) (e : X → ℝ) (d : Y → ℝ) (k : X → Y → ℝ)
    {K epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (hp : ∀ r, p.eventProbability (fun x => F x = r) ≤ K / Fintype.card R)
    (hq : ∀ r, q.eventProbability (fun y => G y = r) ≤ K / Fintype.card R)
    (hk : ∀ x y, F x = G y → |k x y| ≤ epsilon) :
    (Fintype.card R : ℝ) *
        |p.mean (fun x => q.mean (fun y => if F x = G y then k x y * e x * d y else 0))| ≤
      epsilon * (K / 2 * (p.mean (fun x => e x ^ 2) + q.mean (fun y => d y ^ 2))) := by
  have ha : |p.mean (fun x => q.mean (fun y => if F x = G y then k x y * e x * d y else 0))| ≤
      epsilon * p.mean (fun x => q.mean (fun y => if F x = G y then |e x| * |d y| else 0)) := by
    apply (p.abs_mean_le_mean_abs _).trans
    rw [← p.mean_const_mul]
    apply p.mean_mono
    intro x
    apply (q.abs_mean_le_mean_abs _).trans
    rw [← q.mean_const_mul]
    apply q.mean_mono
    intro y
    by_cases h : F x = G y
    · simp only [h, ite_true, abs_mul]
      calc
        _ = |k x y| * (|e x| * |d y|) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (hk x y h) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    · simp [h]
  calc
    _ ≤ (Fintype.card R : ℝ) * (epsilon *
        p.mean (fun x => q.mean (fun y => if F x = G y then |e x| * |d y| else 0))) :=
      mul_le_mul_of_nonneg_left ha (Nat.cast_nonneg _)
    _ = epsilon * ((Fintype.card R : ℝ) *
        p.mean (fun x => q.mean (fun y => if F x = G y then |e x| * |d y| else 0))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (finite_matching_residue_energy p q F G e d hp hq) hepsilon

theorem finite_matching_kernel_approximation {X Y R : Type*}
    [Fintype X] [Fintype Y] [Fintype R] [Nonempty R] [DecidableEq R]
    (p : FiniteProbabilityWeights X) (q : FiniteProbabilityWeights Y)
    (F : X → R) (G : Y → R) (e : X → ℝ) (d : Y → ℝ) (k l : X → Y → ℝ)
    {K epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (hp : ∀ r, p.eventProbability (fun x => F x = r) ≤ K / Fintype.card R)
    (hq : ∀ r, q.eventProbability (fun y => G y = r) ≤ K / Fintype.card R)
    (hk : ∀ x y, F x = G y → |k x y - l x y| ≤ epsilon) :
    |(Fintype.card R : ℝ) *
        p.mean (fun x => q.mean (fun y => if F x = G y then k x y * e x * d y else 0)) -
      (Fintype.card R : ℝ) *
        p.mean (fun x => q.mean (fun y => if F x = G y then l x y * e x * d y else 0))| ≤
      epsilon * (K / 2 * (p.mean (fun x => e x ^ 2) + q.mean (fun y => d y ^ 2))) := by
  have hid : p.mean (fun x => q.mean (fun y =>
      if F x = G y then (k x y - l x y) * e x * d y else 0)) =
      p.mean (fun x => q.mean (fun y => if F x = G y then k x y * e x * d y else 0)) -
      p.mean (fun x => q.mean (fun y => if F x = G y then l x y * e x * d y else 0)) := by
    rw [← p.mean_sub]
    apply congrArg p.mean
    funext x
    rw [← q.mean_sub]
    apply congrArg q.mean
    funext y
    split_ifs <;> ring
  rw [← mul_sub, ← hid, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
  exact finite_matching_kernel_error p q F G e d (fun x y => k x y - l x y) hepsilon hp hq hk

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem finite_cell_residue_kernel_expand {X Y A B R : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B] [Fintype R]
    [DecidableEq A] [DecidableEq B] [DecidableEq R]
    (p : FiniteProbabilityWeights X) (q : FiniteProbabilityWeights Y)
    (C : X → A) (D : Y → B) (F : X → R) (G : Y → R)
    (e : X → ℝ) (d : Y → ℝ) (k : A → B → R → ℝ) :
    p.mean (fun x => q.mean (fun y => if F x = G y then k (C x) (D y) (F x) * e x * d y else 0)) =
      ∑ r, ∑ a, ∑ b, k a b r * finiteCellResidueMean p C F e a r * finiteCellResidueMean q D G d b r := by
  have hpoint (x : X) (y : Y) :
      (if F x = G y then k (C x) (D y) (F x) * e x * d y else 0) =
      ∑ r, ∑ a, ∑ b, k a b r * (if C x = a ∧ F x = r then e x else 0) *
        (if D y = b ∧ G y = r then d y else 0) := by
    symm
    rw [Finset.sum_eq_single (F x)]
    · rw [Finset.sum_eq_single (C x)]
      · rw [Finset.sum_eq_single (D y)]
        · by_cases h : F x = G y <;> simp [h, eq_comm]
        · intro b _ hb
          simp [Ne.symm hb]
        · simp
      · intro a _ ha
        simp [Ne.symm ha]
      · simp
    · intro r _ hr
      simp [Ne.symm hr]
    · simp
  simp_rw [hpoint, q.mean_sum, p.mean_sum]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  simp only [finiteCellResidueMean, q.mean_const_mul, p.mean_mul_const, p.mean_const_mul]

theorem weighted_cell_residue_cancellation {A B R : Type*}
    [Fintype A] [Fintype B] [Fintype R] [Nonempty R]
    (p : FiniteProbabilityWeights A) (q : FiniteProbabilityWeights B)
    (e : A → R → ℝ) (d : B → R → ℝ) (k : A → B → R → ℝ)
    {delta gamma L : ℝ} (hdelta : 0 ≤ delta) (hL : 0 ≤ L)
    (he : ∀ a r, |e a r| ≤ p.weight a * delta / Fintype.card R)
    (hd : ∀ b r, |d b r| ≤ q.weight b * gamma / Fintype.card R)
    (hk : ∀ a b r, |k a b r| ≤ L) :
    |(Fintype.card R : ℝ) * ∑ r, ∑ a, ∑ b, k a b r * e a r * d b r| ≤ L * delta * gamma := by
  let N : ℝ := Fintype.card R
  have hN : 0 < N := by dsimp only [N]; exact_mod_cast Fintype.card_pos
  have hterm (a : A) (b : B) (r : R) :
      |k a b r * e a r * d b r| ≤ (L * delta * gamma / N ^ 2) * (p.weight a * q.weight b) := by
    rw [abs_mul, abs_mul]
    have h := mul_le_mul (mul_le_mul (hk a b r) (he a r) (abs_nonneg _) hL)
      (hd b r) (abs_nonneg _) (mul_nonneg hL (div_nonneg (mul_nonneg (p.nonneg a) hdelta) hN.le))
    apply h.trans_eq
    dsimp only [N]
    ring
  have hs : |∑ r, ∑ a, ∑ b, k a b r * e a r * d b r| ≤
      ∑ _r : R, ∑ a, ∑ b, (L * delta * gamma / N ^ 2) * (p.weight a * q.weight b) := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro r _
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro a _
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    exact Finset.sum_le_sum (fun b _ => hterm a b r)
  have hsum : (∑ _r : R, ∑ a, ∑ b, (L * delta * gamma / N ^ 2) * (p.weight a * q.weight b)) =
      N * (L * delta * gamma / N ^ 2) := by
    simp only [← mul_assoc, ← Finset.mul_sum, q.total, p.total, mul_one,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, N]
  change |N * _| ≤ _
  rw [abs_mul, abs_of_pos hN]
  calc
    _ ≤ N * (N * (L * delta * gamma / N ^ 2)) :=
      mul_le_mul_of_nonneg_left (hs.trans_eq hsum) hN.le
    _ = _ := by field_simp

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem finite_cell_kernel_cancellation {X Y A B R : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B] [Fintype R] [Nonempty R]
    [DecidableEq A] [DecidableEq B] [DecidableEq R]
    (p : FiniteProbabilityWeights X) (q : FiniteProbabilityWeights Y)
    (C : X → A) (D : Y → B) (F : X → R) (G : Y → R)
    (e : X → ℝ) (d : Y → ℝ) (k : A → B → R → ℝ)
    {delta gamma L : ℝ} (hdelta : 0 ≤ delta) (hL : 0 ≤ L)
    (he : ∀ a r, |finiteCellResidueMean p C F e a r| ≤
      (finiteCellWeights p C).weight a * delta / Fintype.card R)
    (hd : ∀ b r, |finiteCellResidueMean q D G d b r| ≤
      (finiteCellWeights q D).weight b * gamma / Fintype.card R)
    (hk : ∀ a b r, |k a b r| ≤ L) :
    |(Fintype.card R : ℝ) * p.mean
      (fun x => q.mean (fun y => if F x = G y then k (C x) (D y) (F x) * e x * d y else 0))| ≤
      L * delta * gamma := by
  rw [finite_cell_residue_kernel_expand]
  exact weighted_cell_residue_cancellation (finiteCellWeights p C) (finiteCellWeights q D)
    (finiteCellResidueMean p C F e) (finiteCellResidueMean q D G d) k hdelta hL he hd hk

theorem finite_cell_kernel_correlation {X Y A B R : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B] [Fintype R] [Nonempty R]
    [DecidableEq A] [DecidableEq B] [DecidableEq R]
    (p : FiniteProbabilityWeights X) (q : FiniteProbabilityWeights Y)
    (C : X → A) (D : Y → B) (F : X → R) (G : Y → R)
    (e : X → ℝ) (d : Y → ℝ) (k : X → Y → ℝ) (cell : A → B → R → ℝ)
    {delta gamma L K zeta : ℝ} (hdelta : 0 ≤ delta) (hL : 0 ≤ L) (hzeta : 0 ≤ zeta)
    (hp : ∀ r, p.eventProbability (fun x => F x = r) ≤ K / Fintype.card R)
    (hq : ∀ r, q.eventProbability (fun y => G y = r) ≤ K / Fintype.card R)
    (he : ∀ a r, |finiteCellResidueMean p C F e a r| ≤
      (finiteCellWeights p C).weight a * delta / Fintype.card R)
    (hd : ∀ b r, |finiteCellResidueMean q D G d b r| ≤
      (finiteCellWeights q D).weight b * gamma / Fintype.card R)
    (hcell : ∀ a b r, |cell a b r| ≤ L)
    (hgrid : ∀ x y, F x = G y → |k x y - cell (C x) (D y) (F x)| ≤ zeta) :
    |(Fintype.card R : ℝ) * p.mean
      (fun x => q.mean (fun y => if F x = G y then k x y * e x * d y else 0))| ≤
      L * delta * gamma + zeta * (K / 2 * (p.mean (fun x => e x ^ 2) + q.mean (fun y => d y ^ 2))) := by
  have herror := finite_matching_kernel_approximation p q F G e d k
    (fun x y => cell (C x) (D y) (F x)) hzeta hp hq hgrid
  have hmain := finite_cell_kernel_cancellation p q C D F G e d cell hdelta hL he hd hcell
  have htriangle := abs_add_le
    ((Fintype.card R : ℝ) * p.mean
      (fun x => q.mean (fun y => if F x = G y then k x y * e x * d y else 0)) -
      (Fintype.card R : ℝ) * p.mean
      (fun x => q.mean (fun y => if F x = G y then cell (C x) (D y) (F x) * e x * d y else 0)))
    ((Fintype.card R : ℝ) * p.mean
      (fun x => q.mean (fun y => if F x = G y then cell (C x) (D y) (F x) * e x * d y else 0)))
  rw [sub_add_cancel] at htriangle
  exact (htriangle.trans (add_le_add herror hmain)).trans_eq (add_comm _ _)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PMFSupportedMean
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem pmf_image_supported_real_mean {X Y : Type*} [DecidableEq Y]
    (p : PMF X) (S : Finset X) (hp : ∀ x ∉ S, (p x).toReal = 0)
    (F : X → Y) (T : Finset Y) (f : Y → ℝ) (hf : ∀ y ∉ T, f y = 0) :
    (∑' x, (p x).toReal * f (F x)) = ∑ y ∈ T, (p.map F y).toReal * f y := by
  let U := T ∪ S.image F
  have hU : ∀ x ∈ S, F x ∈ U :=
    fun x hx => Finset.mem_union_right _ (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
  rw [pmf_image_finite_real_mean p S hp F U hU f]
  symm
  apply Finset.sum_subset Finset.subset_union_left
  intro y _ hy
  rw [hf y hy, mul_zero]

theorem pmf_pair_supported_real_mean {X Y Z : Type*} [DecidableEq Y] [DecidableEq Z]
    (p : PMF X) (S : Finset X) (hp : ∀ x ∉ S, (p x).toReal = 0)
    (F : X → Y) (G : X → Z) (T : Finset Y) (U : Finset Z)
    (e : Y → ℝ) (d : Z → ℝ) (he : ∀ y ∉ T, e y = 0) (hd : ∀ z ∉ U, d z = 0) :
    (∑' x, (p x).toReal * (e (F x) * d (G x))) =
      ∑ y ∈ T, ∑ z ∈ U, (p.map (fun x => (F x, G x)) (y, z)).toReal * (e y * d z) := by
  have hoff (yz : Y × Z) (h : yz ∉ T ×ˢ U) : e yz.1 * d yz.2 = 0 := by
    by_cases hy : yz.1 ∈ T
    · have hz : yz.2 ∉ U := fun hz => h (Finset.mem_product.mpr ⟨hy, hz⟩)
      rw [hd _ hz, mul_zero]
    · rw [he _ hy, zero_mul]
  rw [pmf_image_supported_real_mean p S hp (fun x => (F x, G x)) (T ×ˢ U)
    (fun yz => e yz.1 * d yz.2) hoff, Finset.sum_product]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SmoothIntegerTranslation
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

theorem smoothAffinePairRows_apply {K I : Type*} [Fintype K]
    (t u : K → ℤ) (z : Option K × I → ℤ) (i : I) :
    smoothAffinePairRows t u z i = ![smoothAffineSample t z i, smoothAffineSample u z i] := by
  rw [smoothAffinePairRows, affinePairMatrix_mulVec]
  rfl

end Erdos3

end

section

namespace Erdos3

open scoped Matrix

theorem smoothAffinePairRows_congruence {J I : Type*} [Fintype J]
    (t u : J → ℤ) (z : Option J × I → ℤ) (i : I) :
    BohrLattice.Primitive.content (fun j => u j - t j) ∣
      smoothAffinePairRows t u z i 1 - smoothAffinePairRows t u z i 0 := by
  apply (affinePairImage_iff_content_dvd t u _).mp
  exact ⟨independentArrayRows z i, rfl⟩

theorem affinePairPMF_zero_off_congruence {J I : Type*} [Fintype J]
    (p : PMF (Option J × I → ℤ)) (t u : J → ℤ) (v : I → Fin 2 → ℤ)
    (hv : ¬ ∀ i, BohrLattice.Primitive.content (fun j => u j - t j) ∣ v i 1 - v i 0) :
    p.map (smoothAffinePairRows t u) v = 0 := by
  apply pmf_map_zero_off_range
  rintro ⟨z, rfl⟩
  exact hv (smoothAffinePairRows_congruence t u z)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Matrix

theorem shiftedSmoothSampleSum_integer (b : ℤ) (S : ℝ) :
    shiftedSmoothSampleSum (b : ℝ) S = smoothSampleSum S := by
  have h := (Equiv.addRight b).tsum_eq
    (fun k : ℤ => smoothProbabilityProfile (((k : ℝ) - b) / S))
  simpa only [Equiv.coe_addRight, Int.cast_add, add_sub_cancel_right,
    shiftedSmoothSampleSum, smoothSampleSum] using h.symm

theorem shiftedSmoothCoefficientPMF_integer (b : ℤ) (S : ℝ) (hS : 0 < S)
    (hZ : 0 < shiftedSmoothSampleSum (b : ℝ) S) :
    shiftedSmoothCoefficientPMF (b : ℝ) S hS hZ =
      (smoothCoefficientPMF S hS).map (fun z => z + b) := by
  ext z
  have hmap := pmf_map_injective_at (smoothCoefficientPMF S hS) (fun z => z + b)
    (fun _ _ h => add_right_cancel h) (z - b)
  rw [sub_add_cancel] at hmap
  rw [hmap]
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [shiftedSmoothCoefficientPMF_apply, smoothCoefficientPMF_apply, shiftedSmoothSampleSum_integer]
  simp only [Int.cast_sub]

theorem shiftedSmoothProductPMF_integer {I : Type*} [Fintype I]
    (b : I → ℤ) (S : I → ℝ) (hS : ∀ i, 0 < S i)
    (hZ : 0 < shiftedSmoothProductMass (fun i => (b i : ℝ)) S) :
    shiftedSmoothProductPMF (fun i => (b i : ℝ)) S hS hZ =
      (smoothProductPMF S hS).map (fun z => z + b) := by
  change _ = (smoothProductPMF S hS).map (fun z i => z i + b i)
  rw [shiftedSmoothProductPMF_eq_independent, smoothProductPMF_eq_independent,
    independentProductPMF_map (fun i => smoothCoefficientPMF (S i) (hS i)) (fun i z => z + b i)]
  congr 1
  funext i
  exact shiftedSmoothCoefficientPMF_integer (b i) (S i) (hS i) _

theorem smoothAffinePairRows_add {K I : Type*} [Fintype K]
    (t u : K → ℤ) (z b : Option K × I → ℤ) :
    smoothAffinePairRows t u (z + b) = smoothAffinePairRows t u z + smoothAffinePairRows t u b := by
  funext i
  change affinePairMatrix t u *ᵥ (independentArrayRows z i + independentArrayRows b i) = _
  exact Matrix.mulVec_add _ _ _

theorem shiftedSmoothAffinePairRows_integer {K I : Type*} [Fintype K] [Fintype I]
    (b : Option K × I → ℤ) (S : Option K × I → ℝ) (hS : ∀ i, 0 < S i)
    (hZ : 0 < shiftedSmoothProductMass (fun i => (b i : ℝ)) S) (t u : K → ℤ) :
    (shiftedSmoothProductPMF (fun i => (b i : ℝ)) S hS hZ).map (smoothAffinePairRows t u) =
      ((smoothProductPMF S hS).map (smoothAffinePairRows t u)).map
        (fun v => v + smoothAffinePairRows t u b) := by
  rw [shiftedSmoothProductPMF_integer, PMF.map_comp, PMF.map_comp]
  congr 1
  funext z
  exact smoothAffinePairRows_add t u z b

theorem shiftedSmoothAffinePairRows_integer_apply {K I : Type*} [Fintype K] [Fintype I]
    (b : Option K × I → ℤ) (S : Option K × I → ℝ) (hS : ∀ i, 0 < S i)
    (hZ : 0 < shiftedSmoothProductMass (fun i => (b i : ℝ)) S) (t u : K → ℤ)
    (v : I → Fin 2 → ℤ) :
    ((shiftedSmoothProductPMF (fun i => (b i : ℝ)) S hS hZ).map (smoothAffinePairRows t u)) v =
      ((smoothProductPMF S hS).map (smoothAffinePairRows t u)) (v - smoothAffinePairRows t u b) := by
  rw [shiftedSmoothAffinePairRows_integer]
  have h := pmf_map_injective_at ((smoothProductPMF S hS).map (smoothAffinePairRows t u))
    (fun v => v + smoothAffinePairRows t u b) (fun _ _ h => add_right_cancel h)
    (v - smoothAffinePairRows t u b)
  simpa only [sub_add_cancel] using h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SmoothWindowChange
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem smoothSourceFiniteWeights_mean {J : Type*} [Fintype J]
    (a S : J → ℝ) (hS : ∀ j, 0 < S j) (hZ : 0 < shiftedSmoothProductMass a S)
    (f : (J → ℤ) → ℝ) :
    (smoothSourceFiniteWeights a S hS hZ).mean (fun z => f z.val) =
      ∑' z, (shiftedSmoothProductPMF a S hS hZ z).toReal * f z := by
  unfold FiniteProbabilityWeights.mean
  change (∑ z : rectangularWeightIndices a S 1,
    (shiftedSmoothProductPMF a S hS hZ z.val).toReal * f z.val) = _
  rw [Finset.sum_coe_sort (rectangularWeightIndices a S 1)
    (fun z => (shiftedSmoothProductPMF a S hS hZ z).toReal * f z)]
  exact (hasSum_sum_of_ne_finset_zero (fun z hz => by
    rw [shiftedSmoothProductPMF_toReal_zero_off a S hS hZ z hz, zero_mul])).tsum_eq.symm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.BoxPairDivisibility
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem integer_box_divisor_probability {J : Type*} [Fintype J] [DecidableEq J]
    (lo hi : J → ℤ) (hlen : ∀ j, lo j < hi j) (m : ℤ) (hm : 0 < m) (v : J → ℤ) :
    (integerBoxUniformWeights lo hi hlen).eventProbability
        (fun y => ∀ j, m ∣ (y j : ℤ) - v j) ≤
      ∏ j, (1 / (m : ℝ) + 1 / ((hi j - lo j : ℤ) : ℝ)) := by
  rw [integerBoxUniformWeights, FiniteProbabilityWeights.eventProbability_pi
    (fun j => intervalUniformWeights (lo j) (hi j) (hlen j))
    (fun j (y : Finset.Ico (lo j) (hi j)) => m ∣ (y : ℤ) - v j)]
  apply Finset.prod_le_prod
  · intro j _
    exact FiniteProbabilityWeights.eventProbability_nonneg _ _
  · intro j _
    exact interval_divisor_probability (lo j) (hi j) m (v j) (hlen j) hm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineMeshRetention
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem integerBoxUniformWeights_mean {J : Type*} [Fintype J] [DecidableEq J]
    (lo hi : J → ℤ) (hlen : ∀ j, lo j < hi j)
    (f : (∀ j, Finset.Ico (lo j) (hi j)) → ℝ) :
    (integerBoxUniformWeights lo hi hlen).mean f = 𝔼 x, f x := by
  let : ∀ j, Nonempty (Finset.Ico (lo j) (hi j)) :=
    fun j => ⟨⟨lo j, Finset.mem_Ico.mpr ⟨le_rfl, hlen j⟩⟩⟩
  have he : integerBoxUniformWeights lo hi hlen =
      FiniteProbabilityWeights.uniform (∀ j, Finset.Ico (lo j) (hi j)) := by
    apply FiniteProbabilityWeights.eq_of_weight_eq
    intro x
    change (∏ j, (Fintype.card (Finset.Ico (lo j) (hi j)) : ℝ)⁻¹) =
      (Fintype.card (∀ j, Finset.Ico (lo j) (hi j)) : ℝ)⁻¹
    rw [Fintype.card_pi, Nat.cast_prod, Finset.prod_inv_distrib]
  rw [he, FiniteProbabilityWeights.uniform_mean]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.UniformBoxResidueMass
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

theorem affinePairLocations_rows {I : Type*} (xy : (I → ℤ) × (I → ℤ)) :
    affinePairLocations (affinePairRowsOfLocations xy) = xy := rfl

theorem affinePairRows_locations {I : Type*} (v : I → Fin 2 → ℤ) :
    affinePairRowsOfLocations (affinePairLocations v) = v := by
  funext i j
  fin_cases j <;> rfl

theorem affinePairLocations_injective {I : Type*} :
    Function.Injective (affinePairLocations (I := I)) := by
  intro x y h
  have he := congrArg affinePairRowsOfLocations h
  simpa only [affinePairRows_locations] using he

theorem smoothAffinePairRows_locations {J I : Type*} [Fintype J]
    (t u : J → ℤ) (z : Option J × I → ℤ) :
    affinePairLocations (smoothAffinePairRows t u z) = (smoothAffineSample t z, smoothAffineSample u z) := by
  apply Prod.ext
  · funext i
    change smoothAffinePairRows t u z i 0 = _
    rw [smoothAffinePairRows_apply]
    rfl
  · funext i
    change smoothAffinePairRows t u z i 1 = _
    rw [smoothAffinePairRows_apply]
    rfl

theorem affinePair_joint_probability {J I : Type*} [Fintype J]
    (p : PMF (Option J × I → ℤ)) (t u : J → ℤ) (x y : I → ℤ) :
    p.map (fun z => (smoothAffineSample t z, smoothAffineSample u z)) (x, y) =
      p.map (smoothAffinePairRows t u) (affinePairRowsOfLocations (x, y)) := by
  have he : (p.map (smoothAffinePairRows t u)).map affinePairLocations =
      p.map (fun z => (smoothAffineSample t z, smoothAffineSample u z)) := by
    rw [PMF.map_comp]
    congr 1
    funext z
    exact smoothAffinePairRows_locations t u z
  rw [← he]
  have h := pmf_map_injective_at (p.map (smoothAffinePairRows t u)) affinePairLocations
    affinePairLocations_injective (affinePairRowsOfLocations (x, y))
  simpa only [affinePairLocations_rows] using h

theorem smoothSource_pair_correlation {J I : Type*} [Fintype J] [Fintype I]
    (a S : Option J × I → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S)
    (t u : J → ℤ) (T U : Finset (I → ℤ)) (e d : (I → ℤ) → ℝ)
    (he : ∀ x ∉ T, e x = 0) (hd : ∀ y ∉ U, d y = 0) :
    (smoothSourceFiniteWeights a S hS hZ).mean
        (fun z => e (smoothAffineSample t z.val) * d (smoothAffineSample u z.val)) =
      ∑ x ∈ T, ∑ y ∈ U,
        ((shiftedSmoothProductPMF a S hS hZ).map (smoothAffinePairRows t u)
          (affinePairRowsOfLocations (x, y))).toReal * (e x * d y) := by
  classical
  rw [smoothSourceFiniteWeights_mean a S hS hZ
    (fun z => e (smoothAffineSample t z) * d (smoothAffineSample u z))]
  rw [pmf_pair_supported_real_mean (shiftedSmoothProductPMF a S hS hZ)
    (rectangularWeightIndices a S 1) (shiftedSmoothProductPMF_toReal_zero_off a S hS hZ)
    (smoothAffineSample t) (smoothAffineSample u) T U e d he hd]
  simp_rw [affinePair_joint_probability]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem integerVectorResidue_eq_iff {I : Type*} (m : ℕ) (x y : I → ℤ) :
    integerVectorResidue m x = integerVectorResidue m y ↔ ∀ i, (m : ℤ) ∣ y i - x i := by
  simp only [funext_iff, integerVectorResidue, ZMod.intCast_eq_intCast_iff_dvd_sub]

theorem integerVectorResidue_surjective {I : Type*} (m : ℕ) :
    Function.Surjective (integerVectorResidue (I := I) m) := by
  intro r
  choose x hx using fun i => ZMod.intCast_surjective (r i)
  exact ⟨x, funext hx⟩

theorem integerVectorResidue_card (I : Type*) [Fintype I] [DecidableEq I] (m : ℕ) [NeZero m] :
    Fintype.card (I → ZMod m) = m ^ Fintype.card I := by simp

theorem affinePairModulus_pos {J : Type*} [Fintype J] (t u : J → ℤ) (k : J)
    (hne : u k - t k ≠ 0) : 0 < affinePairModulus t u := by
  apply Int.natAbs_pos.mpr
  apply BohrLattice.Primitive.content_ne_zero
  intro h
  exact hne (congrFun h k)

theorem affinePairModulus_residue_iff {J I : Type*} [Fintype J]
    (t u : J → ℤ) (x y : I → ℤ) :
    integerVectorResidue (affinePairModulus t u) x = integerVectorResidue (affinePairModulus t u) y ↔
      ∀ i, BohrLattice.Primitive.content (fun j => u j - t j) ∣ y i - x i := by
  rw [integerVectorResidue_eq_iff]
  simp only [affinePairModulus, Int.natAbs_dvd]

theorem affinePairPMF_zero_off_residue {J I : Type*} [Fintype J]
    (p : PMF (Option J × I → ℤ)) (t u : J → ℤ) (x y : I → ℤ)
    (hxy : integerVectorResidue (affinePairModulus t u) x ≠
      integerVectorResidue (affinePairModulus t u) y) :
    p.map (smoothAffinePairRows t u) (affinePairRowsOfLocations (x, y)) = 0 := by
  apply affinePairPMF_zero_off_congruence
  intro h
  apply hxy
  apply (affinePairModulus_residue_iff t u x y).mpr
  simpa only [affinePairRowsOfLocations, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] using h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem integer_box_residue_probability {I : Type*} [Fintype I] [DecidableEq I]
    (lo hi : I → ℤ) (hlen : ∀ i, lo i < hi i) (m : ℕ) (hm : 0 < m) (r : I → ZMod m) :
    (integerBoxUniformWeights lo hi hlen).eventProbability
      (fun x => integerVectorResidue m (fun i => (x i).val) = r) ≤
      ∏ i, (1 / (m : ℝ) + 1 / ((hi i - lo i : ℤ) : ℝ)) := by
  obtain ⟨v, hv⟩ := integerVectorResidue_surjective m r
  have heq : (fun x : ∀ i, Finset.Ico (lo i) (hi i) =>
      integerVectorResidue m (fun i => (x i).val) = r) =
      (fun x => ∀ i, (m : ℤ) ∣ (x i).val - v i) := by
    funext x
    apply propext
    rw [← hv, eq_comm, integerVectorResidue_eq_iff]
  rw [heq]
  exact integer_box_divisor_probability lo hi hlen (m : ℤ) (by exact_mod_cast hm) v

theorem integer_box_residue_probability_of_lengths {I : Type*} [Fintype I] [DecidableEq I]
    (lo hi : I → ℤ) (hlen : ∀ i, lo i < hi i) (m : ℕ) (hm : 0 < m)
    (hwidth : ∀ i, (m : ℝ) ≤ ((hi i - lo i : ℤ) : ℝ)) (r : I → ZMod m) :
    (integerBoxUniformWeights lo hi hlen).eventProbability
      (fun x => integerVectorResidue m (fun i => (x i).val) = r) ≤
      (2 : ℝ) ^ Fintype.card I / (m : ℝ) ^ Fintype.card I := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  apply (integer_box_residue_probability lo hi hlen m hm r).trans
  calc
    _ ≤ ∏ _i : I, 2 / (m : ℝ) := by
      apply Finset.prod_le_prod
      · intro i _
        exact add_nonneg (one_div_nonneg.mpr hmR.le)
          (one_div_nonneg.mpr (hmR.le.trans (hwidth i)))
      · intro i _
        have h := one_div_le_one_div_of_le hmR (hwidth i)
        calc
          _ ≤ 1 / (m : ℝ) + 1 / (m : ℝ) := add_le_add le_rfl h
          _ = _ := by ring
    _ = _ := by simp only [Finset.prod_const, Finset.card_univ, div_pow]

theorem uniform_interval_box_residue_bound {I : Type*} [Fintype I] [DecidableEq I]
    (lo hi : I → ℤ) (hlen : ∀ i, lo i < hi i)
    [Nonempty (Fintype.piFinset (fun i => Finset.Ico (lo i) (hi i)))]
    (m : ℕ) (hm : 0 < m) (hwidth : ∀ i, (m : ℝ) ≤ ((hi i - lo i : ℤ) : ℝ))
    (r : I → ZMod m) :
    (FiniteProbabilityWeights.uniform (Fintype.piFinset (fun i => Finset.Ico (lo i) (hi i)))).eventProbability
      (fun x => integerVectorResidue m x.val = r) ≤
      (2 : ℝ) ^ Fintype.card I / (m : ℝ) ^ Fintype.card I := by
  classical
  have h := integer_box_residue_probability_of_lengths lo hi hlen m hm hwidth r
  unfold FiniteProbabilityWeights.eventProbability at h ⊢
  rw [FiniteProbabilityWeights.uniform_mean]
  rw [integerBoxUniformWeights_mean] at h
  apply le_of_eq_of_le ?_ h
  apply Fintype.expect_equiv (finiteBoxPointsEquiv (fun i => Finset.Ico (lo i) (hi i))).symm
  intro x
  split_ifs <;> first | rfl | contradiction

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AnisotropicSmoothPairLaw
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem independent_row_density_error {I X : Type*} [Fintype I] [Countable X]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (p : I → PMF X) (A : I → ℝ) (f : I → X → ℝ) {B epsilon : ℝ}
    (hB : 1 ≤ B) (hepsilon : 0 ≤ epsilon)
    (hcap : ∀ i x, |f i x| ≤ B)
    (herror : ∀ i x, |A i * (p i x).toReal - f i x| ≤ epsilon) (x : I → X) :
    |(∏ i, A i) * (independentProductPMF p x).toReal - ∏ i, f i (x i)| ≤
      Fintype.card I * epsilon * (B + epsilon) ^ Fintype.card I := by
  rw [independentProductPMF_toReal, ← Finset.prod_mul_distrib]
  apply abs_finset_prod_sub_prod_le Finset.univ _ _ (by linarith) hepsilon
  · intro i _
    have h := abs_add_le (A i * (p i (x i)).toReal - f i (x i)) (f i (x i))
    have he := herror i (x i)
    have hc := hcap i (x i)
    rw [sub_add_cancel] at h
    linarith
  · intro i _
    exact (hcap i (x i)).trans (by linarith)
  · intro i _
    exact herror i (x i)

theorem product_masked_scalars {I : Type*} [Fintype I]
    (P : I → Prop) (f : I → ℝ) (m : ℝ) :
    (∏ i, if P i then m * f i else 0) =
      if ∀ i, P i then m ^ Fintype.card I * ∏ i, f i else 0 := by
  by_cases h : ∀ i, P i
  · simp [h, Finset.prod_mul_distrib]
  · have hn : ∃ i, ¬ P i := by simpa only [not_forall] using h
    obtain ⟨i, hi⟩ := hn
    rw [if_neg h]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

theorem independent_masked_row_density_error {I X : Type*} [Fintype I] [Countable X]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (p : I → PMF X) (A : I → ℝ) (P : I → X → Prop) (f : I → X → ℝ) (m : ℝ)
    {B epsilon : ℝ} (hB : 1 ≤ B) (hepsilon : 0 ≤ epsilon)
    (hcap : ∀ i x, |m * f i x| ≤ B)
    (herror : ∀ i x, |A i * (p i x).toReal - (if P i x then m * f i x else 0)| ≤ epsilon)
    (x : I → X) :
    |(∏ i, A i) * (independentProductPMF p x).toReal -
      (if ∀ i, P i (x i) then m ^ Fintype.card I * ∏ i, f i (x i) else 0)| ≤
      Fintype.card I * epsilon * (B + epsilon) ^ Fintype.card I := by
  have hc (i : I) (y : X) : |(if P i y then m * f i y else 0)| ≤ B := by
    split_ifs
    · exact hcap i y
    · simpa only [abs_zero] using zero_le_one.trans hB
  have h := independent_row_density_error p A (fun i y => if P i y then m * f i y else 0)
    hB hepsilon hc herror x
  rwa [product_masked_scalars] at h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Matrix

theorem affinePair_split_mulVec {J : Type*} [Fintype J] [DecidableEq J]
    (t u : J → ℤ) (k : J) (z : Option J → ℤ) :
    affinePairMatrix t u *ᵥ z =
      affinePairPivot t u k *ᵥ (smoothInputSplit (affinePairColumnEquiv k) z).1 +
      affinePairFree t u k *ᵥ (smoothInputSplit (affinePairColumnEquiv k) z).2 := by
  calc
    _ = Matrix.fromCols (affinePairPivot t u k) (affinePairFree t u k) *ᵥ
        (z ∘ affinePairColumnEquiv k) := by
      rw [affinePairPivot_columns, Matrix.submatrix_mulVec_equiv]
      simp only [Function.comp_def, Equiv.apply_symm_apply, id_eq]
    _ = _ := by
      ext i
      fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, smoothInputSplit, Matrix.fromCols]

theorem smooth_pair_input_law {J : Type*} [Fintype J] [DecidableEq J]
    (k : J) {H L : ℝ} (hH : 0 < H) (hL : 0 < L)
    (hM : 0 < scaledInputMass (splitSmoothProductProfile {j : J // j ≠ k} (Fin 2))
      (affinePairScale H L) (fun _ => H / L)) :
    (smoothProductPMF (smoothPairCoefficientScale H L) (smoothPairCoefficientScale_pos hH hL)).map
        (smoothInputSplit (affinePairColumnEquiv k)) =
      scaledInputPMF (splitSmoothProductProfile {j : J // j ≠ k} (Fin 2))
        (fun z => (splitSmoothProductProfile_range _ _ z).1)
        (affinePairScale H L) (fun _ => H / L) (affinePairScale_pos hH hL)
        (fun _ => div_pos hH hL) (splitSmoothProductProfile_zero_outside _ _) hM := by
  have hs : (fun i => smoothPairCoefficientScale H L (affinePairColumnEquiv k (.inl i))) =
      affinePairScale H L := by
    funext i
    fin_cases i <;> rfl
  have ht : (fun j => smoothPairCoefficientScale H L (affinePairColumnEquiv k (.inr j))) =
      (fun _ : {j : J // j ≠ k} => H / L) := rfl
  have hm : 0 < scaledInputMass (splitSmoothProductProfile {j : J // j ≠ k} (Fin 2))
      (fun i => smoothPairCoefficientScale H L (affinePairColumnEquiv k (.inl i)))
      (fun j => smoothPairCoefficientScale H L (affinePairColumnEquiv k (.inr j))) := by
    simpa only [hs, ht] using hM
  have h := smoothInputSplit_law (affinePairColumnEquiv k) (smoothPairCoefficientScale H L)
    (smoothPairCoefficientScale_pos hH hL) hm
  simpa only [hs, ht] using h

theorem smooth_pair_row_law {J : Type*} [Fintype J] [DecidableEq J]
    (t u : J → ℤ) (k : J) {H L : ℝ} (hH : 0 < H) (hL : 0 < L)
    (hM : 0 < scaledInputMass (splitSmoothProductProfile {j : J // j ≠ k} (Fin 2))
      (affinePairScale H L) (fun _ => H / L)) :
    (smoothProductPMF (smoothPairCoefficientScale H L) (smoothPairCoefficientScale_pos hH hL)).map
        (fun z => affinePairMatrix t u *ᵥ z) =
      integerImagePMF (affinePairPivot t u k) (affinePairFree t u k)
        (splitSmoothProductProfile {j : J // j ≠ k} (Fin 2))
        (fun z => (splitSmoothProductProfile_range _ _ z).1)
        (affinePairScale H L) (fun _ => H / L) (affinePairScale_pos hH hL)
        (fun _ => div_pos hH hL) (splitSmoothProductProfile_zero_outside _ _) hM := by
  rw [integerImagePMF, ← smooth_pair_input_law k hH hL hM, PMF.map_comp]
  congr 1
  funext z
  exact affinePair_split_mulVec t u k z

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem smooth_affinePairRowDensity_cap {J : Type*} [Fintype J] [DecidableEq J]
    (t u : J → ℤ) (k : J) (hne : u k - t k ≠ 0)
    {H L C κ : ℝ} (hH : 0 < H) (hL : 0 < L) (hC : 1 ≤ C) (hκ : 0 < κ)
    (ht : |(t k : ℝ) / L| ≤ C) (hu : |(u k : ℝ) / L| ≤ C)
    (hgap : κ ≤ |((u k - t k : ℤ) : ℝ) / L|) (y : Fin 2 → ℝ) :
    |affinePairRowDensity t u k hne H L hH hL
      (splitSmoothProductProfile {j : J // j ≠ k} (Fin 2)) y| ≤
      2 * (4 * C / κ) ^ 2 * (2 : ℝ) ^ Fintype.card {j : J // j ≠ k} := by
  have hA : (affinePairPivot t u k).det ≠ 0 := by rwa [affinePairPivot_det]
  let e := normalizedPivotEquiv (affinePairPivot t u k) hA (affinePairScale H L)
    (fun _ => H) (affinePairScale_pos hH hL) (fun _ => hH)
  let b := matrixSupCLM (normalizedIntegerColumns (affinePairFree t u k) (fun _ => H / L) (fun _ => H))
  have hinv : ‖e.symm.toContinuousLinearMap‖ ≤ 4 * C / κ := by
    dsimp only [e]
    rw [normalizedPivotEquiv_inverse_eq]
    exact normalized_affinePairPivot_inverse t u k hH.ne' hL.ne' hC hκ ht hu hgap
  have hb (z : ({j : J // j ≠ k} → ℝ) × (Fin 2 → ℝ)) :
      ‖splitSmoothProductProfile {j : J // j ≠ k} (Fin 2) z‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (splitSmoothProductProfile_range _ _ z).1]
    exact (splitSmoothProductProfile_range _ _ z).2
  have h := pivotOutputDensity_abs_le_uniform e b _ zero_le_one zero_le_one
    (splitSmoothProductProfile_zero_outside _ _) hb hinv y
  norm_num at h
  simpa [affinePairRowDensity, normalizedFiberDensity, e, b] using h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Matrix NNReal

theorem smooth_pair_actual_row_error {J : Type*} [Fintype J] [DecidableEq J]
    (t u : J → ℤ) (k : J) (hne : u k - t k ≠ 0)
    {H L C κ δ : ℝ} (Q : ℕ) (hH : 0 < H) (hL : 1 ≤ L) (hC : 1 ≤ C) (hκ : 0 < κ)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (ht : ∀ j, |(t j : ℝ) / L| ≤ C) (hu : ∀ j, |(u j : ℝ) / L| ≤ C)
    (hgap : κ ≤ |((u k - t k : ℤ) : ℝ) / L|)
    (hQ : (BohrLattice.Primitive.content (fun j => u j - t j)).natAbs ≤ Q)
    (hmesh : ((u k - t k).natAbs : ℝ) * L / H ≤ δ)
    (hsmall : (4 : ℝ) ^ (2 + Fintype.card {j : J // j ≠ k}) *
      smoothPairRowLipschitz k * δ ≤ 1 / 2) (v : Fin 2 → ℤ) :
    |H ^ 2 * ((smoothProductPMF (smoothPairCoefficientScale H L)
          (smoothPairCoefficientScale_pos hH (zero_lt_one.trans_le hL))).map
          (fun z => affinePairMatrix t u *ᵥ z) v).toReal -
      (if BohrLattice.Primitive.content (fun j => u j - t j) ∣ v 1 - v 0 then
        ((BohrLattice.Primitive.content (fun j => u j - t j)).natAbs : ℝ) *
          affinePairRowDensity t u k hne H L hH (zero_lt_one.trans_le hL)
            (splitSmoothProductProfile {j : J // j ≠ k} (Fin 2))
            (fun i => (v i : ℝ) / H) else 0)| ≤
      smoothPairProbabilityError k Q C κ δ := by
  obtain ⟨hM, he⟩ := smooth_affinePair_probability_law_s2 t u k hne Q hH hL hC hκ
    hδ hδ1 ht hu hgap hQ hmesh hsmall
  rw [smooth_pair_row_law t u k hH (zero_lt_one.trans_le hL) hM]
  exact he v

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Matrix NNReal

theorem affine_pair_shift_divisibility {J : Type*} [Fintype J]
    (t u : J → ℤ) (b : Option J → ℤ) (v : Fin 2 → ℤ) :
    (BohrLattice.Primitive.content (fun j => u j - t j) ∣
      (v 1 - (affinePairMatrix t u *ᵥ b) 1) - (v 0 - (affinePairMatrix t u *ᵥ b) 0)) ↔
      BohrLattice.Primitive.content (fun j => u j - t j) ∣ v 1 - v 0 := by
  have hb : affinePairMatrix t u *ᵥ b ∈ affinePairImage t u := ⟨b, rfl⟩
  have hd := (affinePairImage_iff_content_dvd t u _).mp hb
  rw [show (v 1 - (affinePairMatrix t u *ᵥ b) 1) - (v 0 - (affinePairMatrix t u *ᵥ b) 0) =
    (v 1 - v 0) - ((affinePairMatrix t u *ᵥ b) 1 - (affinePairMatrix t u *ᵥ b) 0) by ring]
  exact dvd_sub_left hd

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Matrix NNReal

theorem centeredSmoothAffinePairRows_variable {J I : Type*} [Fintype J] [Fintype I]
    (S : Option J × I → ℝ) (hS : ∀ z, 0 < S z) (t u : J → ℤ) :
    (smoothProductPMF S hS).map (smoothAffinePairRows t u) =
      independentProductPMF (fun i => (smoothProductPMF (fun j => S (j, i))
        (fun j => hS (j, i))).map (fun z => affinePairMatrix t u *ᵥ z)) := by
  have h := congrArg (fun p : PMF (I → Option J → ℤ) =>
    p.map (fun rows i => affinePairMatrix t u *ᵥ rows i)) (smoothProductPMF_rows S hS)
  rw [PMF.map_comp, independentProductPMF_map] at h
  exact h

theorem anisotropic_smooth_pair_product_probability_law {J I : Type*}
    [Fintype J] [DecidableEq J] [Fintype I]
    (t u : J → ℤ) (k : J) (hne : u k - t k ≠ 0)
    (H : I → ℝ) {L C κ δ : ℝ} (Q : ℕ) (hH : ∀ i, 0 < H i) (hL : 1 ≤ L) (hC : 1 ≤ C) (hκ : 0 < κ)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (ht : ∀ j, |(t j : ℝ) / L| ≤ C) (hu : ∀ j, |(u j : ℝ) / L| ≤ C)
    (hgap : κ ≤ |((u k - t k : ℤ) : ℝ) / L|)
    (hQ : (BohrLattice.Primitive.content (fun j => u j - t j)).natAbs ≤ Q)
    (hmesh : ∀ i, ((u k - t k).natAbs : ℝ) * L / H i ≤ δ)
    (hsmall : (4 : ℝ) ^ (2 + Fintype.card {j : J // j ≠ k}) *
      smoothPairRowLipschitz k * δ ≤ 1 / 2) (v : I → Fin 2 → ℤ) :
    |(∏ i, H i ^ 2) *
        ((smoothProductPMF (fun z : Option J × I => smoothPairCoefficientScale (H z.2) L z.1)
          (fun z => smoothPairCoefficientScale_pos (hH z.2) (zero_lt_one.trans_le hL) z.1)).map
          (smoothAffinePairRows t u) v).toReal -
      (if ∀ i, BohrLattice.Primitive.content (fun j => u j - t j) ∣ v i 1 - v i 0 then
        ((BohrLattice.Primitive.content (fun j => u j - t j)).natAbs : ℝ) ^ Fintype.card I *
          ∏ i, affinePairRowDensity t u k hne (H i) L (hH i) (zero_lt_one.trans_le hL)
            (splitSmoothProductProfile {j : J // j ≠ k} (Fin 2))
            (fun j => (v i j : ℝ) / H i) else 0)| ≤
      Fintype.card I * smoothPairProbabilityError k Q C κ δ *
        (smoothPairProbabilityCap k Q C κ + smoothPairProbabilityError k Q C κ δ) ^ Fintype.card I := by
  classical
  let density : I → (Fin 2 → ℤ) → ℝ := fun i v =>
    affinePairRowDensity t u k hne (H i) L (hH i) (zero_lt_one.trans_le hL)
      (splitSmoothProductProfile {j : J // j ≠ k} (Fin 2)) (fun j => (v j : ℝ) / H i)
  let m : ℝ := (BohrLattice.Primitive.content (fun j => u j - t j)).natAbs
  have hrow (i : I) := smooth_pair_actual_row_error t u k hne Q (hH i) hL hC hκ hδ hδ1 ht hu hgap hQ (hmesh i) hsmall
  have hepsilon : 0 ≤ smoothPairProbabilityError k Q C κ δ := smoothPairProbabilityError_nonneg k Q C κ δ hδ
  have hbound (i : I) (v : Fin 2 → ℤ) : |density i v| ≤
      2 * (4 * C / κ) ^ 2 * 2 ^ Fintype.card {j : J // j ≠ k} :=
    smooth_affinePairRowDensity_cap t u k hne (hH i) (zero_lt_one.trans_le hL) hC hκ (ht k) (hu k) hgap _
  have hm : 0 ≤ m := Nat.cast_nonneg _
  have hmQ : m ≤ Q := by
    dsimp only [m]
    exact_mod_cast hQ
  have hcap0 : 0 ≤ 2 * (4 * C / κ) ^ 2 * 2 ^ Fintype.card {j : J // j ≠ k} := by positivity
  have hB : 1 ≤ smoothPairProbabilityCap k Q C κ := by
    unfold smoothPairProbabilityCap
    exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hcap0)
  have hcap (i : I) (v : Fin 2 → ℤ) : |m * density i v| ≤ smoothPairProbabilityCap k Q C κ := by
    rw [abs_mul, abs_of_nonneg hm]
    apply (mul_le_mul hmQ (hbound i v) (abs_nonneg _) (Nat.cast_nonneg _)).trans
    change (Q : ℝ) * _ ≤ 1 + (Q : ℝ) * _
    linarith
  rw [centeredSmoothAffinePairRows_variable]
  have h := independent_masked_row_density_error
    (fun i : I => (smoothProductPMF (smoothPairCoefficientScale (H i) L)
      (smoothPairCoefficientScale_pos (hH i) (zero_lt_one.trans_le hL))).map
        (fun z => affinePairMatrix t u *ᵥ z))
    (fun i => H i ^ 2) (fun _ v => BohrLattice.Primitive.content (fun j => u j - t j) ∣ v 1 - v 0)
    density m hB hepsilon hcap (fun i x => by
      by_cases hx : BohrLattice.Primitive.content (fun j => u j - t j) ∣ x 1 - x 0
      · simpa only [hx, ite_true, m, density] using hrow i x
      · simpa only [hx, ite_false] using hrow i x) v
  simpa only [density, m] using h

theorem shifted_anisotropic_smooth_pair_product_probability_law {J I : Type*}
    [Fintype J] [DecidableEq J] [Fintype I]
    (t u : J → ℤ) (k : J) (hne : u k - t k ≠ 0)
    (H : I → ℝ) {L C κ δ : ℝ} (Q : ℕ) (hH : ∀ i, 0 < H i) (hL : 1 ≤ L) (hC : 1 ≤ C) (hκ : 0 < κ)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (ht : ∀ j, |(t j : ℝ) / L| ≤ C) (hu : ∀ j, |(u j : ℝ) / L| ≤ C)
    (hgap : κ ≤ |((u k - t k : ℤ) : ℝ) / L|)
    (hQ : (BohrLattice.Primitive.content (fun j => u j - t j)).natAbs ≤ Q)
    (hmesh : ∀ i, ((u k - t k).natAbs : ℝ) * L / H i ≤ δ)
    (hsmall : (4 : ℝ) ^ (2 + Fintype.card {j : J // j ≠ k}) *
      smoothPairRowLipschitz k * δ ≤ 1 / 2)
    (b : Option J × I → ℤ)
    (hZ : 0 < shiftedSmoothProductMass (fun z => (b z : ℝ))
      (fun z : Option J × I => smoothPairCoefficientScale (H z.2) L z.1))
    (v : I → Fin 2 → ℤ) :
    |(∏ i, H i ^ 2) *
        ((shiftedSmoothProductPMF (fun z => (b z : ℝ))
          (fun z : Option J × I => smoothPairCoefficientScale (H z.2) L z.1)
          (fun z => smoothPairCoefficientScale_pos (hH z.2) (zero_lt_one.trans_le hL) z.1) hZ).map
          (smoothAffinePairRows t u) v).toReal -
      (if ∀ i, BohrLattice.Primitive.content (fun j => u j - t j) ∣ v i 1 - v i 0 then
        ((BohrLattice.Primitive.content (fun j => u j - t j)).natAbs : ℝ) ^ Fintype.card I *
          ∏ i, affinePairRowDensity t u k hne (H i) L (hH i) (zero_lt_one.trans_le hL)
            (splitSmoothProductProfile {j : J // j ≠ k} (Fin 2))
            (fun j => ((v i j - smoothAffinePairRows t u b i j : ℤ) : ℝ) / H i) else 0)| ≤
      Fintype.card I * smoothPairProbabilityError k Q C κ δ *
        (smoothPairProbabilityCap k Q C κ + smoothPairProbabilityError k Q C κ δ) ^ Fintype.card I := by
  classical
  rw [shiftedSmoothAffinePairRows_integer_apply]
  have h := anisotropic_smooth_pair_product_probability_law t u k hne H Q hH hL hC hκ hδ hδ1 ht hu hgap
    hQ hmesh hsmall (v - smoothAffinePairRows t u b)
  have hm : (∀ i, BohrLattice.Primitive.content (fun j => u j - t j) ∣
      (v i 1 - smoothAffinePairRows t u b i 1) - (v i 0 - smoothAffinePairRows t u b i 0)) ↔
      (∀ i, BohrLattice.Primitive.content (fun j => u j - t j) ∣ v i 1 - v i 0) :=
    forall_congr' (fun i => affine_pair_shift_divisibility t u (independentArrayRows b i) (v i))
  simpa only [Pi.sub_apply, hm] using h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.CanonicalPairPointLaw
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

theorem canonical_pair_point_error {J I : Type*}
    [Fintype J] [DecidableEq J] [Fintype I]
    (t u : J → ℤ) (k : J) (hne : u k - t k ≠ 0)
    (H : I → ℝ) {L C κ δ : ℝ} (Q : ℕ) (hH : ∀ i, 0 < H i)
    (hL : 1 ≤ L) (hC : 1 ≤ C) (hκ : 0 < κ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (ht : ∀ j, |(t j : ℝ) / L| ≤ C) (hu : ∀ j, |(u j : ℝ) / L| ≤ C)
    (hgap : κ ≤ |((u k - t k : ℤ) : ℝ) / L|)
    (hQ : affinePairModulus t u ≤ Q)
    (hmesh : ∀ i, ((u k - t k).natAbs : ℝ) * L / H i ≤ δ)
    (hsmall : (4 : ℝ) ^ (2 + Fintype.card {j : J // j ≠ k}) * smoothPairRowLipschitz k * δ ≤ 1 / 2)
    (b : Option J × I → ℤ)
    (hZ : 0 < shiftedSmoothProductMass (fun z => (b z : ℝ))
      (fun z : Option J × I => smoothPairCoefficientScale (H z.2) L z.1))
    (x y : I → ℤ)
    (hxy : integerVectorResidue (affinePairModulus t u) x = integerVectorResidue (affinePairModulus t u) y) :
    |(∏ i, H i ^ 2) *
        ((shiftedSmoothProductPMF (fun z => (b z : ℝ))
          (fun z : Option J × I => smoothPairCoefficientScale (H z.2) L z.1)
          (fun z => smoothPairCoefficientScale_pos (hH z.2) (zero_lt_one.trans_le hL) z.1) hZ).map
          (smoothAffinePairRows t u) (affinePairRowsOfLocations (x, y))).toReal -
      (affinePairModulus t u : ℝ) ^ Fintype.card I *
        shiftedPairLocationKernel t u k hne H L hH (zero_lt_one.trans_le hL) b x y| ≤
      (affinePairModulus t u : ℝ) ^ Fintype.card I * fullSmoothPairError (Fintype.card I) k Q C κ δ := by
  have hraw := shifted_anisotropic_smooth_pair_product_probability_law t u k hne H Q hH hL hC hκ
    hδ hδ1 ht hu hgap hQ hmesh hsmall b hZ (affinePairRowsOfLocations (x, y))
  have hmask : ∀ i, BohrLattice.Primitive.content (fun j => u j - t j) ∣
      affinePairRowsOfLocations (x, y) i 1 - affinePairRowsOfLocations (x, y) i 0 :=
    (affinePairModulus_residue_iff t u x y).mp hxy
  rw [if_pos hmask] at hraw
  have h : |(∏ i, H i ^ 2) *
        ((shiftedSmoothProductPMF (fun z => (b z : ℝ))
          (fun z : Option J × I => smoothPairCoefficientScale (H z.2) L z.1)
          (fun z => smoothPairCoefficientScale_pos (hH z.2) (zero_lt_one.trans_le hL) z.1) hZ).map
          (smoothAffinePairRows t u) (affinePairRowsOfLocations (x, y))).toReal -
      (affinePairModulus t u : ℝ) ^ Fintype.card I *
        shiftedPairLocationKernel t u k hne H L hH (zero_lt_one.trans_le hL) b x y| ≤
      fullSmoothPairError (Fintype.card I) k Q C κ δ := by
    simpa only [fullSmoothPairError, affinePairModulus, shiftedPairLocationKernel, smoothPairProductDensity] using hraw
  have hE : 0 ≤ fullSmoothPairError (Fintype.card I) k Q C κ δ := (abs_nonneg _).trans h
  have hbase : (1 : ℝ) ≤ affinePairModulus t u := by
    exact_mod_cast Nat.succ_le_of_lt (affinePairModulus_pos t u k hne)
  have hN : (1 : ℝ) ≤ (affinePairModulus t u : ℝ) ^ Fintype.card I := one_le_pow₀ hbase
  apply h.trans
  nlinarith [mul_nonneg (sub_nonneg.mpr hN) hE]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SmoothPairErrorLogBounds
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem uniform_pair_sum {X Y : Type*} [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
    (f : X → Y → ℝ) :
    (Fintype.card X : ℝ) * Fintype.card Y *
        (FiniteProbabilityWeights.uniform X).mean
          (fun x => (FiniteProbabilityWeights.uniform Y).mean (f x)) = ∑ x, ∑ y, f x y := by
  simp_rw [FiniteProbabilityWeights.uniform_mean, Fintype.expect_eq_sum_div_card, ← Finset.sum_div]
  have hX : (Fintype.card X : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hY : (Fintype.card Y : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp [hX, hY]

theorem uniform_joint_residual_bound {X Y A B R : Type*}
    [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
    [Fintype A] [Fintype B] [Fintype R] [Nonempty R]
    [DecidableEq A] [DecidableEq B] [DecidableEq R]
    (C : X → A) (D : Y → B) (F : X → R) (G : Y → R)
    (e : X → ℝ) (d : Y → ℝ) (joint k : X → Y → ℝ) (cell : A → B → R → ℝ)
    {V delta gamma L K epsilon zeta : ℝ} (hV : 0 < V)
    (hdelta : 0 ≤ delta) (hL : 0 ≤ L) (hepsilon : 0 ≤ epsilon) (hzeta : 0 ≤ zeta)
    (hp : ∀ r, (FiniteProbabilityWeights.uniform X).eventProbability (fun x => F x = r) ≤
      K / Fintype.card R)
    (hq : ∀ r, (FiniteProbabilityWeights.uniform Y).eventProbability (fun y => G y = r) ≤
      K / Fintype.card R)
    (he : ∀ a r, |finiteCellResidueMean (FiniteProbabilityWeights.uniform X) C F e a r| ≤
      (finiteCellWeights (FiniteProbabilityWeights.uniform X) C).weight a * delta / Fintype.card R)
    (hd : ∀ b r, |finiteCellResidueMean (FiniteProbabilityWeights.uniform Y) D G d b r| ≤
      (finiteCellWeights (FiniteProbabilityWeights.uniform Y) D).weight b * gamma / Fintype.card R)
    (hcell : ∀ a b r, |cell a b r| ≤ L)
    (hoff : ∀ x y, F x ≠ G y → joint x y = 0)
    (hpoint : ∀ x y, F x = G y →
      |V * joint x y - (Fintype.card R : ℝ) * k x y| ≤ Fintype.card R * epsilon)
    (hgrid : ∀ x y, F x = G y → |k x y - cell (C x) (D y) (F x)| ≤ zeta) :
    |∑ x, ∑ y, joint x y * e x * d y| ≤
      ((Fintype.card X : ℝ) * Fintype.card Y / V) *
        (L * delta * gamma + (epsilon + zeta) * (K / 2 *
          ((FiniteProbabilityWeights.uniform X).mean (fun x => e x ^ 2) +
           (FiniteProbabilityWeights.uniform Y).mean (fun y => d y ^ 2)))) := by
  let p := FiniteProbabilityWeights.uniform X
  let q := FiniteProbabilityWeights.uniform Y
  let N : ℝ := Fintype.card R
  let a : X → Y → ℝ := fun x y => V * joint x y / N
  have hN : 0 < N := by dsimp only [N]; exact_mod_cast Fintype.card_pos
  have hnear (x : X) (y : Y) (h : F x = G y) : |a x y - k x y| ≤ epsilon := by
    have hid : a x y - k x y = (V * joint x y - N * k x y) / N := by
      dsimp only [a]
      field_simp [hN.ne']
    rw [hid, abs_div, abs_of_pos hN]
    apply (div_le_iff₀ hN).mpr
    exact (hpoint x y h).trans_eq (mul_comm _ _)
  have happrox (x : X) (y : Y) (h : F x = G y) :
      |a x y - cell (C x) (D y) (F x)| ≤ epsilon + zeta :=
    (abs_sub_le (a x y) (k x y) (cell (C x) (D y) (F x))).trans
      (add_le_add (hnear x y h) (hgrid x y h))
  have hmain := finite_cell_kernel_correlation p q C D F G e d a cell
    hdelta hL (add_nonneg hepsilon hzeta) hp hq he hd hcell happrox
  have hpoint' (x : X) (y : Y) :
      N * (if F x = G y then a x y * e x * d y else 0) = V * (joint x y * e x * d y) := by
    by_cases h : F x = G y
    · simp only [h, ite_true, a]
      field_simp
    · simp [h, hoff x y h]
  have hscaled : N * p.mean (fun x => q.mean (fun y => if F x = G y then a x y * e x * d y else 0)) =
      V * p.mean (fun x => q.mean (fun y => joint x y * e x * d y)) := by
    calc
      _ = p.mean (fun x => q.mean (fun y => N *
          (if F x = G y then a x y * e x * d y else 0))) := by
        simp only [q.mean_const_mul, p.mean_const_mul]
      _ = _ := by simp only [hpoint', q.mean_const_mul, p.mean_const_mul]
  have hsum := uniform_pair_sum (fun x y => joint x y * e x * d y)
  have hid : (∑ x, ∑ y, joint x y * e x * d y) =
      ((Fintype.card X : ℝ) * Fintype.card Y / V) *
        (N * p.mean (fun x => q.mean (fun y => if F x = G y then a x y * e x * d y else 0))) := by
    rw [hscaled]
    change _ = _ * (V * (FiniteProbabilityWeights.uniform X).mean
      (fun x => (FiniteProbabilityWeights.uniform Y).mean (fun y => joint x y * e x * d y)))
    rw [← mul_assoc, div_mul_cancel₀ _ hV.ne']
    exact hsum.symm
  rw [hid, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (Fintype.card X : ℝ) * Fintype.card Y / V)]
  exact mul_le_mul_of_nonneg_left hmain (by positivity)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem smoothSource_pair_kernel_reduction {J I A B R : Type*}
    [Fintype J] [Fintype I] [Fintype A] [Fintype B] [Fintype R] [Nonempty R]
    [DecidableEq A] [DecidableEq B] [DecidableEq R]
    (a S : Option J × I → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S)
    (t u : J → ℤ) (T U : Finset (I → ℤ)) [Nonempty T] [Nonempty U]
    (e d : (I → ℤ) → ℝ) (heoff : ∀ x ∉ T, e x = 0) (hdoff : ∀ y ∉ U, d y = 0)
    (C : T → A) (D : U → B) (F : T → R) (G : U → R)
    (k : T → U → ℝ) (cell : A → B → R → ℝ)
    {V delta gamma L K epsilon zeta : ℝ} (hV : 0 < V)
    (hdelta : 0 ≤ delta) (hL : 0 ≤ L) (hepsilon : 0 ≤ epsilon) (hzeta : 0 ≤ zeta)
    (hp : ∀ r, (FiniteProbabilityWeights.uniform T).eventProbability (fun x => F x = r) ≤
      K / Fintype.card R)
    (hq : ∀ r, (FiniteProbabilityWeights.uniform U).eventProbability (fun y => G y = r) ≤
      K / Fintype.card R)
    (he : ∀ c r, |finiteCellResidueMean (FiniteProbabilityWeights.uniform T) C F (fun x => e x.val) c r| ≤
      (finiteCellWeights (FiniteProbabilityWeights.uniform T) C).weight c * delta / Fintype.card R)
    (hd : ∀ c r, |finiteCellResidueMean (FiniteProbabilityWeights.uniform U) D G (fun y => d y.val) c r| ≤
      (finiteCellWeights (FiniteProbabilityWeights.uniform U) D).weight c * gamma / Fintype.card R)
    (hcell : ∀ c c' r, |cell c c' r| ≤ L)
    (hoff : ∀ x : T, ∀ y : U, F x ≠ G y →
      ((shiftedSmoothProductPMF a S hS hZ).map (smoothAffinePairRows t u)
        (affinePairRowsOfLocations (x.val, y.val))).toReal = 0)
    (hpoint : ∀ x : T, ∀ y : U, F x = G y →
      |V * ((shiftedSmoothProductPMF a S hS hZ).map (smoothAffinePairRows t u)
        (affinePairRowsOfLocations (x.val, y.val))).toReal -
          (Fintype.card R : ℝ) * k x y| ≤ Fintype.card R * epsilon)
    (hgrid : ∀ x y, F x = G y → |k x y - cell (C x) (D y) (F x)| ≤ zeta) :
    |(smoothSourceFiniteWeights a S hS hZ).mean
      (fun z => e (smoothAffineSample t z.val) * d (smoothAffineSample u z.val))| ≤
      ((T.card : ℝ) * U.card / V) *
        (L * delta * gamma + (epsilon + zeta) * (K / 2 *
          ((FiniteProbabilityWeights.uniform T).mean (fun x => e x.val ^ 2) +
           (FiniteProbabilityWeights.uniform U).mean (fun y => d y.val ^ 2)))) := by
  rw [smoothSource_pair_correlation a S hS hZ t u T U e d heoff hdoff]
  have h := uniform_joint_residual_bound C D F G (fun x => e x.val) (fun y => d y.val)
    (fun x y => ((shiftedSmoothProductPMF a S hS hZ).map (smoothAffinePairRows t u)
      (affinePairRowsOfLocations (x.val, y.val))).toReal) k cell
    hV hdelta hL hepsilon hzeta hp hq he hd hcell hoff hpoint hgrid
  have hsum (f : (I → ℤ) → (I → ℤ) → ℝ) :
      (∑ x : T, ∑ y : U, f x.val y.val) = ∑ x ∈ T, ∑ y ∈ U, f x y := by
    have hi (x : I → ℤ) : (∑ y : U, f x y.val) = ∑ y ∈ U, f x y :=
      Finset.sum_coe_sort U (f x)
    simp_rw [hi]
    exact Finset.sum_coe_sort T (fun x => ∑ y ∈ U, f x y)
  rw [hsum (fun x y => ((shiftedSmoothProductPMF a S hS hZ).map (smoothAffinePairRows t u)
    (affinePairRowsOfLocations (x, y))).toReal * e x * d y)] at h
  simpa only [Fintype.card_coe, mul_assoc] using h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem canonical_smooth_pair_correlation {J I A B : Type*}
    [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (t u : J → ℤ) (k : J) (hne : u k - t k ≠ 0)
    (H : I → ℝ) {L C κ δ : ℝ} (Q : ℕ) (hH : ∀ i, 0 < H i)
    (hL : 1 ≤ L) (hC : 1 ≤ C) (hκ : 0 < κ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (ht : ∀ j, |(t j : ℝ) / L| ≤ C) (hu : ∀ j, |(u j : ℝ) / L| ≤ C)
    (hgap : κ ≤ |((u k - t k : ℤ) : ℝ) / L|)
    (hQ : affinePairModulus t u ≤ Q)
    (hmesh : ∀ i, ((u k - t k).natAbs : ℝ) * L / H i ≤ δ)
    (hsmall : (4 : ℝ) ^ (2 + Fintype.card {j : J // j ≠ k}) * smoothPairRowLipschitz k * δ ≤ 1 / 2)
    (b : Option J × I → ℤ)
    (hZ : 0 < shiftedSmoothProductMass (fun z => (b z : ℝ))
      (fun z : Option J × I => smoothPairCoefficientScale (H z.2) L z.1))
    (T U : Finset (I → ℤ)) [Nonempty T] [Nonempty U]
    (e d : (I → ℤ) → ℝ) (heoff : ∀ x ∉ T, e x = 0) (hdoff : ∀ y ∉ U, d y = 0)
    (P : T → A) (R : U → B) (cell : A → B → (I → ZMod (affinePairModulus t u)) → ℝ)
    {alpha beta cap mass zeta : ℝ} (halpha : 0 ≤ alpha) (hcap : 0 ≤ cap) (hzeta : 0 ≤ zeta)
    (hp : ∀ r, (FiniteProbabilityWeights.uniform T).eventProbability
      (fun x => integerVectorResidue (affinePairModulus t u) x.val = r) ≤
      mass / (affinePairModulus t u : ℝ) ^ Fintype.card I)
    (hq : ∀ r, (FiniteProbabilityWeights.uniform U).eventProbability
      (fun y => integerVectorResidue (affinePairModulus t u) y.val = r) ≤
      mass / (affinePairModulus t u : ℝ) ^ Fintype.card I)
    (he : ∀ c r, |finiteCellResidueMean (FiniteProbabilityWeights.uniform T) P
      (fun x => integerVectorResidue (affinePairModulus t u) x.val) (fun x => e x.val) c r| ≤
      (finiteCellWeights (FiniteProbabilityWeights.uniform T) P).weight c * alpha /
        (affinePairModulus t u : ℝ) ^ Fintype.card I)
    (hd : ∀ c r, |finiteCellResidueMean (FiniteProbabilityWeights.uniform U) R
      (fun y => integerVectorResidue (affinePairModulus t u) y.val) (fun y => d y.val) c r| ≤
      (finiteCellWeights (FiniteProbabilityWeights.uniform U) R).weight c * beta /
        (affinePairModulus t u : ℝ) ^ Fintype.card I)
    (hcell : ∀ c c' r, |cell c c' r| ≤ cap)
    (hgrid : ∀ x : T, ∀ y : U,
      integerVectorResidue (affinePairModulus t u) x.val = integerVectorResidue (affinePairModulus t u) y.val →
      |shiftedPairLocationKernel t u k hne H L hH (zero_lt_one.trans_le hL) b x.val y.val -
        cell (P x) (R y) (integerVectorResidue (affinePairModulus t u) x.val)| ≤ zeta) :
    |(smoothSourceFiniteWeights (fun z => (b z : ℝ))
      (fun z : Option J × I => smoothPairCoefficientScale (H z.2) L z.1)
      (fun z => smoothPairCoefficientScale_pos (hH z.2) (zero_lt_one.trans_le hL) z.1) hZ).mean
      (fun z => e (smoothAffineSample t z.val) * d (smoothAffineSample u z.val))| ≤
      ((T.card : ℝ) * U.card / ∏ i, H i ^ 2) *
        (cap * alpha * beta + (fullSmoothPairError (Fintype.card I) k Q C κ δ + zeta) * (mass / 2 *
          ((FiniteProbabilityWeights.uniform T).mean (fun x => e x.val ^ 2) +
           (FiniteProbabilityWeights.uniform U).mean (fun y => d y.val ^ 2)))) := by
  let : NeZero (affinePairModulus t u) := ⟨(affinePairModulus_pos t u k hne).ne'⟩
  have hV : (0 : ℝ) < ∏ i, H i ^ 2 :=
    Finset.prod_pos (fun i _ => pow_pos (hH i) _)
  refine smoothSource_pair_kernel_reduction
    (fun z => (b z : ℝ)) (fun z : Option J × I => smoothPairCoefficientScale (H z.2) L z.1)
    (fun z => smoothPairCoefficientScale_pos (hH z.2) (zero_lt_one.trans_le hL) z.1) hZ
    t u T U e d heoff hdoff P R
    (fun x => integerVectorResidue (affinePairModulus t u) x.val)
    (fun y => integerVectorResidue (affinePairModulus t u) y.val)
    (fun x y => shiftedPairLocationKernel t u k hne H L hH (zero_lt_one.trans_le hL) b x.val y.val)
    cell hV halpha hcap (fullSmoothPairError_nonneg _ k Q C κ δ hδ) hzeta
    ?_ ?_ ?_ ?_ hcell ?_ ?_ hgrid
  · simpa only [integerVectorResidue_card, Nat.cast_pow] using hp
  · simpa only [integerVectorResidue_card, Nat.cast_pow] using hq
  · simpa only [integerVectorResidue_card, Nat.cast_pow] using he
  · simpa only [integerVectorResidue_card, Nat.cast_pow] using hd
  · intro x y hxy
    rw [affinePairPMF_zero_off_residue _ t u x.val y.val hxy, ENNReal.toReal_zero]
  · intro x y hxy
    simpa only [integerVectorResidue_card, Nat.cast_pow] using
      canonical_pair_point_error t u k hne H Q hH hL hC hκ hδ hδ1 ht hu hgap hQ hmesh hsmall
        b hZ x.val y.val hxy

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.BoxPairCorrelation
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem box_smooth_pair_correlation_s2_oai {J I A B : Type*}
    [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (t u : J → ℤ) (k : J) (hne : u k - t k ≠ 0)
    (H : I → ℝ) {L C κ δ : ℝ} (Q : ℕ) (hH : ∀ i, 0 < H i)
    (hL : 1 ≤ L) (hC : 1 ≤ C) (hκ : 0 < κ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (ht : ∀ j, |(t j : ℝ) / L| ≤ C) (hu : ∀ j, |(u j : ℝ) / L| ≤ C)
    (hgap : κ ≤ |((u k - t k : ℤ) : ℝ) / L|)
    (hQ : affinePairModulus t u ≤ Q)
    (hmesh : ∀ i, ((u k - t k).natAbs : ℝ) * L / H i ≤ δ)
    (hsmall : (4 : ℝ) ^ (2 + Fintype.card {j : J // j ≠ k}) * smoothPairRowLipschitz k * δ ≤ 1 / 2)
    (b : Option J × I → ℤ)
    (hZ : 0 < shiftedSmoothProductMass (fun z => (b z : ℝ))
      (fun z : Option J × I => smoothPairCoefficientScale (H z.2) L z.1))
    (loT hiT loU hiU : I → ℤ)
    (hlenT : ∀ i, loT i < hiT i) (hlenU : ∀ i, loU i < hiU i)
    (hwidthT : ∀ i, (affinePairModulus t u : ℝ) ≤ ((hiT i - loT i : ℤ) : ℝ))
    (hwidthU : ∀ i, (affinePairModulus t u : ℝ) ≤ ((hiU i - loU i : ℤ) : ℝ))
    (T U : Finset (I → ℤ)) [Nonempty T] [Nonempty U]
    (hT : T = Fintype.piFinset (fun i => Finset.Ico (loT i) (hiT i)))
    (hU : U = Fintype.piFinset (fun i => Finset.Ico (loU i) (hiU i)))
    (e d : (I → ℤ) → ℝ) (heoff : ∀ x ∉ T, e x = 0) (hdoff : ∀ y ∉ U, d y = 0)
    (P : T → A) (R : U → B) (cell : A → B → (I → ZMod (affinePairModulus t u)) → ℝ)
    {alpha beta cap zeta : ℝ} (halpha : 0 ≤ alpha) (hcap : 0 ≤ cap) (hzeta : 0 ≤ zeta)
    (he : ∀ c r, |finiteCellResidueMean (FiniteProbabilityWeights.uniform T) P
      (fun x => integerVectorResidue (affinePairModulus t u) x.val) (fun x => e x.val) c r| ≤
      (finiteCellWeights (FiniteProbabilityWeights.uniform T) P).weight c * alpha /
        (affinePairModulus t u : ℝ) ^ Fintype.card I)
    (hd : ∀ c r, |finiteCellResidueMean (FiniteProbabilityWeights.uniform U) R
      (fun y => integerVectorResidue (affinePairModulus t u) y.val) (fun y => d y.val) c r| ≤
      (finiteCellWeights (FiniteProbabilityWeights.uniform U) R).weight c * beta /
        (affinePairModulus t u : ℝ) ^ Fintype.card I)
    (hcell : ∀ c c' r, |cell c c' r| ≤ cap)
    (hgrid : ∀ x : T, ∀ y : U,
      integerVectorResidue (affinePairModulus t u) x.val = integerVectorResidue (affinePairModulus t u) y.val →
      |shiftedPairLocationKernel t u k hne H L hH (zero_lt_one.trans_le hL) b x.val y.val -
        cell (P x) (R y) (integerVectorResidue (affinePairModulus t u) x.val)| ≤ zeta) :
    |(smoothSourceFiniteWeights (fun z => (b z : ℝ))
      (fun z : Option J × I => smoothPairCoefficientScale (H z.2) L z.1)
      (fun z => smoothPairCoefficientScale_pos (hH z.2) (zero_lt_one.trans_le hL) z.1) hZ).mean
      (fun z => e (smoothAffineSample t z.val) * d (smoothAffineSample u z.val))| ≤
      ((T.card : ℝ) * U.card / ∏ i, H i ^ 2) *
        (cap * alpha * beta + (fullSmoothPairError (Fintype.card I) k Q C κ δ + zeta) * ((2 : ℝ) ^ Fintype.card I / 2 *
          ((FiniteProbabilityWeights.uniform T).mean (fun x => e x.val ^ 2) +
           (FiniteProbabilityWeights.uniform U).mean (fun y => d y.val ^ 2)))) := by
  subst T
  subst U
  refine canonical_smooth_pair_correlation t u k hne H Q hH hL hC hκ hδ hδ1
    ht hu hgap hQ hmesh hsmall b hZ _ _ e d heoff hdoff P R cell halpha hcap hzeta
    ?_ ?_ he hd hcell hgrid
  · exact uniform_interval_box_residue_bound loT hiT hlenT (affinePairModulus t u)
      (affinePairModulus_pos t u k hne) hwidthT
  · exact uniform_interval_box_residue_bound loU hiU hlenU (affinePairModulus t u)
      (affinePairModulus_pos t u k hne) hwidthU

end Erdos3

end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4} : type_of% @OAI.Erdos3.box_smooth_pair_correlation_s2_oai.{u_1, u_2, u_3, u_4} := @OAI.Erdos3.box_smooth_pair_correlation_s2_oai.{u_1, u_2, u_3, u_4}
