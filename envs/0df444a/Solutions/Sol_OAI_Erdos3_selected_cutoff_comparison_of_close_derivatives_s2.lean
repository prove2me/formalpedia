-- Prove2me | solution 1 for OAI.Erdos3.selected_cutoff_comparison_of_close_derivatives_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-17T10:33:16.013105+00:00
-- url     : https://prove2.me/submissions/e0f8a564-03db-4d97-b32f-5206ddd6a9fd

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B037
import Definitions.Def_OAIE3v2B083
import Theorems.Thm_OAI_Erdos3_box_image_comparison_s2
import Theorems.Thm_OAI_Erdos3_imageTranslationBound_of_inverse_budget_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteInversePerturbation
namespace OAI

section

namespace Erdos3

open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_le_twice_mul_of_inverse_perturbation
    (A B : E →L[ℝ] E) (hA : A.IsInvertible) (K : ℝ≥0)
    (hK : ‖A.inverse‖ ≤ K) (hsmall : (K : ℝ) * ‖B - A‖ ≤ 1 / 2) (v : E) :
    ‖v‖ ≤ 2 * (K : ℝ) * ‖B v‖ := by
  have hid : v = A.inverse (B v) - A.inverse ((B - A) v) := by
    rw [← map_sub]
    simp only [sub_apply, sub_sub_cancel, hA.inverse_apply_self]
  have hmain : ‖A.inverse (B v)‖ ≤ (K : ℝ) * ‖B v‖ :=
    (A.inverse.le_opNorm _).trans (mul_le_mul_of_nonneg_right hK (norm_nonneg _))
  have herr : ‖A.inverse ((B - A) v)‖ ≤ (1 / 2 : ℝ) * ‖v‖ := by
    calc
      _ ≤ ‖A.inverse‖ * ‖(B - A) v‖ := A.inverse.le_opNorm _
      _ ≤ (K : ℝ) * (‖B - A‖ * ‖v‖) :=
        mul_le_mul hK ((B - A).le_opNorm _) (norm_nonneg _) K.coe_nonneg
      _ = ((K : ℝ) * ‖B - A‖) * ‖v‖ := by ring
      _ ≤ (1 / 2 : ℝ) * ‖v‖ := mul_le_mul_of_nonneg_right hsmall (norm_nonneg _)
  have hnorm : ‖v‖ ≤ (K : ℝ) * ‖B v‖ + (1 / 2 : ℝ) * ‖v‖ := by
    calc
      ‖v‖ = ‖A.inverse (B v) - A.inverse ((B - A) v)‖ := congrArg norm hid
      _ ≤ ‖A.inverse (B v)‖ + ‖A.inverse ((B - A) v)‖ := norm_sub_le _ _
      _ ≤ _ := add_le_add hmain herr
  linarith

theorem inverse_perturbation_bound [FiniteDimensional ℝ E]
    (A B : E →L[ℝ] E) (hA : A.IsInvertible) (K : ℝ≥0)
    (hK : ‖A.inverse‖ ≤ K) (hsmall : (K : ℝ) * ‖B - A‖ ≤ 1 / 2) :
    B.IsInvertible ∧ ‖B.inverse‖ ≤ 2 * (K : ℝ) := by
  have hlower := norm_le_twice_mul_of_inverse_perturbation A B hA K hK hsmall
  have hinj : Function.Injective B := by
    intro x y hxy
    have h := hlower (x - y)
    rw [map_sub, hxy, sub_self, norm_zero, mul_zero] at h
    exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm h (norm_nonneg _)))
  have hbij : Function.Bijective B :=
    ⟨hinj, LinearMap.surjective_of_injective (f := B.toLinearMap) hinj⟩
  have hB : B.IsInvertible :=
    ⟨(LinearEquiv.ofBijective B.toLinearMap hbij).toContinuousLinearEquiv, rfl⟩
  refine ⟨hB, B.inverse.opNorm_le_bound (by positivity) ?_⟩
  intro v
  simpa only [hB.self_apply_inverse] using hlower (B.inverse v)

end Erdos3

end

end OAI
end

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

theorem ae_realDensityMeasure_of_forall_nonzero {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) (hf : Measurable f) (P : X → Prop)
    (hP : ∀ x, f x ≠ 0 → P x) : ∀ᵐ x ∂realDensityMeasure μ f, P x := by
  apply (ae_withDensity_iff hf.ennreal_ofReal).mpr
  filter_upwards [] with x hx
  apply hP x
  intro hzero
  simp only [hzero, ENNReal.ofReal_zero, ne_eq, not_true_eq_false] at hx

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

theorem cutoffMeasure_mass_le_one {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (w : Ω → ℝ) (hw : Measurable w)
    (hbound : ∀ a, w a ∈ Set.Icc (0 : ℝ) 1) : (realDensityMeasure μ w).real Set.univ ≤ 1 := by
  have hi := cutoff_integrable μ w hw hbound
  rw [realDensityMeasure_real_univ μ w hi (fun a => (hbound a).1)]
  have h := integral_mono hi (integrable_const (1 : ℝ)) (fun a => (hbound a).2)
  simpa using h

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CutoffBoxImageComparison
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]

theorem cutoff_box_image_comparison (μ : Measure Ω) [IsProbabilityMeasure μ]
    (w : Ω → ℝ) (hw : Measurable w) (hw01 : ∀ a, w a ∈ Set.Icc (0 : ℝ) 1)
    (U V : Ω → (ι → ℝ)) (hU : Measurable U) (hV : Measurable V)
    (H_U H_V : ℝ≥0) (hTU : ImageTranslationBound (realDensityMeasure μ w) U H_U)
    (hTV : ImageTranslationBound (realDensityMeasure μ w) V H_V)
    {ε η : ℝ} (hε : 0 ≤ ε) (hcut : (∫ a, 1 - w a ∂μ) ≤ η)
    (hclose : ∀ᵐ a ∂realDensityMeasure μ w, dist (U a) (V a) ≤ ε)
    (δ : ℝ) (hδ : 0 < δ) (φ : (ι → ℝ) → ℝ) (hφ : Measurable φ) (hbound : ∀ x, ‖φ x‖ ≤ 1) :
    |mappedTest μ U φ - mappedTest μ V φ| ≤
      2 * η + ((H_U : ℝ) + H_V) * δ + 2 * (Fintype.card ι : ℝ) * ε / δ := by
  let : IsFiniteMeasure (realDensityMeasure μ w) :=
    realDensityMeasure_finite μ w (cutoff_integrable μ w hw hw01) (fun a => (hw01 a).1)
  have hsmall := box_image_comparison_s2 (realDensityMeasure μ w) (cutoffMeasure_mass_le_one μ w hw hw01)
    U V hU hV H_U H_V hTU hTV hε hclose δ hδ φ hφ hbound
  have hu := (mappedTest_cutoff_error μ w hw hw01 U hU φ hφ hbound).trans hcut
  have hv := (mappedTest_cutoff_error μ w hw hw01 V hV φ hφ hbound).trans hcut
  have hv' : |mappedTest (realDensityMeasure μ w) V φ - mappedTest μ V φ| ≤ η := by
    rw [abs_sub_comm]
    exact hv
  calc
    |mappedTest μ U φ - mappedTest μ V φ| ≤
        |mappedTest μ U φ - mappedTest (realDensityMeasure μ w) U φ| +
          |mappedTest (realDensityMeasure μ w) U φ - mappedTest μ V φ| := abs_sub_le _ _ _
    _ ≤ |mappedTest μ U φ - mappedTest (realDensityMeasure μ w) U φ| +
        (|mappedTest (realDensityMeasure μ w) U φ - mappedTest (realDensityMeasure μ w) V φ| +
          |mappedTest (realDensityMeasure μ w) V φ - mappedTest μ V φ|) :=
      add_le_add le_rfl (abs_sub_le _ _ _)
    _ ≤ η + ((((H_U : ℝ) + H_V) * δ + 2 * (Fintype.card ι : ℝ) * ε / δ) + η) :=
      add_le_add hu (add_le_add hsmall hv')
    _ = 2 * η + ((H_U : ℝ) + H_V) * δ + 2 * (Fintype.card ι : ℝ) * ε / δ := by ring

theorem sqrt_smoothing_balance {b ε : ℝ} (hb : 0 < b) (hε : 0 < ε) :
    b * Real.sqrt (ε / b) + ε / Real.sqrt (ε / b) = 2 * Real.sqrt (b * ε) := by
  let d := Real.sqrt (ε / b)
  have hd : 0 < d := Real.sqrt_pos.mpr (div_pos hε hb)
  have hsq : d ^ 2 = ε / b := Real.sq_sqrt (div_nonneg hε.le hb.le)
  have hbd : b * d ^ 2 = ε := by
    rw [hsq]
    field_simp
  have hdiv : ε / d = b * d := (div_eq_iff hd.ne').mpr (by nlinarith [hbd])
  have hprod : (b * d) ^ 2 = b * ε := by
    calc
      (b * d) ^ 2 = b * (b * d ^ 2) := by ring
      _ = b * ε := by rw [hbd]
  have hroot : b * d = Real.sqrt (b * ε) := by
    nlinarith [Real.sq_sqrt (mul_pos hb hε).le, Real.sqrt_nonneg (b * ε), mul_pos hb hd]
  change b * d + ε / d = _
  rw [hdiv, hroot]
  ring

theorem cutoff_box_image_comparison_sqrt (μ : Measure Ω) [IsProbabilityMeasure μ]
    (w : Ω → ℝ) (hw : Measurable w) (hw01 : ∀ a, w a ∈ Set.Icc (0 : ℝ) 1)
    (U V : Ω → (ι → ℝ)) (hU : Measurable U) (hV : Measurable V)
    (B : ℝ≥0) (hB : 0 < (B : ℝ))
    (hTU : ImageTranslationBound (realDensityMeasure μ w) U ((Fintype.card ι : ℝ≥0) * B))
    (hTV : ImageTranslationBound (realDensityMeasure μ w) V ((Fintype.card ι : ℝ≥0) * B))
    {ε η : ℝ} (hε : 0 < ε) (hcut : (∫ a, 1 - w a ∂μ) ≤ η)
    (hclose : ∀ᵐ a ∂realDensityMeasure μ w, dist (U a) (V a) ≤ ε)
    (φ : (ι → ℝ) → ℝ) (hφ : Measurable φ) (hbound : ∀ x, ‖φ x‖ ≤ 1) :
    |mappedTest μ U φ - mappedTest μ V φ| ≤
      2 * η + 4 * (Fintype.card ι : ℝ) * Real.sqrt ((B : ℝ) * ε) := by
  have h := cutoff_box_image_comparison μ w hw hw01 U V hU hV _ _ hTU hTV hε.le hcut hclose
    (Real.sqrt (ε / (B : ℝ))) (Real.sqrt_pos.mpr (div_pos hε hB)) φ hφ hbound
  apply h.trans_eq
  have hbal := sqrt_smoothing_balance hB hε
  push_cast
  calc
    2 * η + ((Fintype.card ι : ℝ) * B + (Fintype.card ι : ℝ) * B) * Real.sqrt (ε / (B : ℝ)) +
        2 * (Fintype.card ι : ℝ) * ε / Real.sqrt (ε / (B : ℝ)) =
      2 * η + 2 * (Fintype.card ι : ℝ) *
        ((B : ℝ) * Real.sqrt (ε / (B : ℝ)) + ε / Real.sqrt (ε / (B : ℝ))) := by ring
    _ = 2 * η + 4 * (Fintype.card ι : ℝ) * Real.sqrt ((B : ℝ) * ε) := by rw [hbal]; ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BooleanSelectedDerivativeBound
namespace OAI

section

namespace Erdos3

open scoped NNReal

variable {κ ι : Type*} [Fintype κ] [Fintype ι]

theorem selectedDerivative_sub_norm_le
    (U V : (κ → ℝ) → (ι → ℝ)) (J : (ι → ℝ) →L[ℝ] (κ → ℝ)) (x : κ → ℝ) :
    ‖selectedDerivative V J x - selectedDerivative U J x‖ ≤
      ‖fderiv ℝ V x - fderiv ℝ U x‖ * ‖J‖ := by
  unfold selectedDerivative
  rw [← ContinuousLinearMap.sub_comp]
  exact (fderiv ℝ V x - fderiv ℝ U x).opNorm_comp_le J

theorem selected_inverse_perturbation
    (U V : (κ → ℝ) → (ι → ℝ)) (J : (ι → ℝ) →L[ℝ] (κ → ℝ)) (x : κ → ℝ)
    (hinv : (selectedDerivative U J x).IsInvertible) (K : ℝ≥0)
    (hK : ‖(selectedDerivative U J x).inverse‖ ≤ K)
    (hsmall : (K : ℝ) * (‖fderiv ℝ V x - fderiv ℝ U x‖ * ‖J‖) ≤ 1 / 2) :
    (selectedDerivative V J x).IsInvertible ∧
      ‖(selectedDerivative V J x).inverse‖ ≤ 2 * (K : ℝ) := by
  apply inverse_perturbation_bound (selectedDerivative U J x) (selectedDerivative V J x) hinv K hK
  exact (mul_le_mul_of_nonneg_left (selectedDerivative_sub_norm_le U V J x) K.coe_nonneg).trans hsmall

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.JointBooleanStability
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

theorem selected_cutoff_comparison_of_close_derivatives_s2_oai
    {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    (μ : Measure (κ → ℝ)) [IsProbabilityMeasure μ]
    (χ w : (κ → ℝ) → ℝ) (hχ : Measurable χ) (hχ01 : ∀ x, χ x ∈ Set.Icc (0 : ℝ) 1)
    (hw : ContDiff ℝ 1 w) (hs : HasCompactSupport w) (hw0 : ∀ x, 0 ≤ w x)
    (hlaw : realDensityMeasure volume w = realDensityMeasure μ χ)
    (U V : (κ → ℝ) → (ι → ℝ)) (hU : ContDiff ℝ 2 U) (hV : ContDiff ℝ 2 V)
    (J : (ι → ℝ) →L[ℝ] (κ → ℝ)) (hJ : ‖J‖ ≤ 1) (K H S : ℝ≥0)
    (hinv : ∀ x ∈ tsupport w, (selectedDerivative U J x).IsInvertible)
    (hK : ∀ x ∈ tsupport w, ‖(selectedDerivative U J x).inverse‖ ≤ K)
    (hsmall : ∀ x ∈ tsupport w, (K : ℝ) * ‖fderiv ℝ V x - fderiv ℝ U x‖ ≤ 1 / 2)
    (hHU : ∀ x ∈ tsupport w, ‖fderiv ℝ (selectedDerivative U J) x‖ ≤ H)
    (hHV : ∀ x ∈ tsupport w, ‖fderiv ℝ (selectedDerivative V J) x‖ ≤ H)
    (hS : (∑ j, ∫ x, |fderiv ℝ w x (Pi.single j 1)|) ≤ S)
    {ε η : ℝ} (hε : 0 < ε) (hmass : 1 - η ≤ ∫ x, w x)
    (hclose : ∀ x, w x ≠ 0 → dist (U x) (V x) ≤ ε)
    (φ : (ι → ℝ) → ℝ) (hφ : Measurable φ) (hbound : ∀ x, ‖φ x‖ ≤ 1) :
    let B := 1 + 2 * (K : ℝ) * S + (Fintype.card κ : ℝ) * ((2 * (K : ℝ)) ^ 2 * H)
    |mappedTest μ U φ - mappedTest μ V φ| ≤
      2 * η + 4 * (Fintype.card ι : ℝ) * Real.sqrt (B * ε) := by
  have hwi : Integrable w := hw.continuous.integrable_of_hasCompactSupport hs
  have hmass1 : (∫ x, |w x|) ≤ 1 := by
    have ht := cutoffMeasure_mass_le_one μ χ hχ hχ01
    rw [← hlaw, realDensityMeasure_real_univ volume w hwi hw0] at ht
    have he (x) : |w x| = w x := abs_of_nonneg (hw0 x)
    simpa only [he] using ht
  have hv (x) (hx : x ∈ tsupport w) :
      (selectedDerivative V J x).IsInvertible ∧ ‖(selectedDerivative V J x).inverse‖ ≤ 2 * K := by
    apply selected_inverse_perturbation U V J x (hinv x hx) K (hK x hx)
    apply le_trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hJ (norm_nonneg _)) K.coe_nonneg)
    simpa only [mul_one] using hsmall x hx
  let B : ℝ≥0 := 1 + (2 * K) * S + (Fintype.card κ : ℝ≥0) * ((2 * K) ^ 2 * H)
  have hB : 0 < (B : ℝ) := by dsimp only [B]; positivity
  have hbudget : ((2 * K : ℝ≥0) : ℝ) * S +
      (Fintype.card κ : ℝ) * (((2 * K : ℝ≥0) : ℝ) ^ 2 * H) ≤ B := by
    simp only [B, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_natCast,
      NNReal.coe_ofNat, NNReal.coe_one]
    linarith
  have hTU := imageTranslationBound_of_inverse_budget_s2 U hU J hJ w hw hs hw0 hmass1
    (2 * K) H S B hinv (fun x hx => (hK x hx).trans (by
      change (K : ℝ) ≤ 2 * K
      linarith [K.coe_nonneg])) hHU hS hbudget
  have hTV := imageTranslationBound_of_inverse_budget_s2 V hV J hJ w hw hs hw0 hmass1
    (2 * K) H S B (fun x hx => (hv x hx).1) (fun x hx => (hv x hx).2) hHV hS hbudget
  rw [hlaw] at hTU hTV
  have hc : ∀ᵐ x ∂realDensityMeasure μ χ, dist (U x) (V x) ≤ ε := by
    rw [← hlaw]
    exact ae_realDensityMeasure_of_forall_nonzero volume w hw.continuous.measurable _ hclose
  have ht := cutoff_box_image_comparison_sqrt μ χ hχ hχ01 U V hU.continuous.measurable
    hV.continuous.measurable B hB hTU hTV hε
    (cutoff_loss_of_density_mass μ volume χ w hχ hχ01 hwi hw0 hlaw hmass) hc φ hφ hbound
  simpa only [B, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_natCast,
    NNReal.coe_ofNat, NNReal.coe_one] using ht

end Erdos3

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Erdos3.selected_cutoff_comparison_of_close_derivatives_s2_oai.{u_1, u_2} := @OAI.Erdos3.selected_cutoff_comparison_of_close_derivatives_s2_oai.{u_1, u_2}
