-- Prove2me | solution 1 for OAI.Erdos3.twoBoxDifferenceDensity_mem_Icc_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-17T10:41:34.770412+00:00
-- url     : https://prove2.me/submissions/ec0d3c8d-84e4-4e4f-958b-209beabef625

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B035
import Definitions.Def_OAIE3v2B039
import Definitions.Def_OAIE3v2B061

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NormalizedIntervalWindow
namespace OAI

section

namespace Erdos3

open MeasureTheory _root_.Set

theorem intervalWindow_mem_Icc (a b t : ℝ) : intervalWindow a b t ∈ Icc (0 : ℝ) 1 := by
  by_cases ht : t ∈ Ioc a b <;> simp [intervalWindow, ht]

theorem intervalWindow_measurable (a b : ℝ) : Measurable (intervalWindow a b) :=
  measurable_const.indicator measurableSet_Ioc

theorem intervalWindow_integrable (a b : ℝ) : Integrable (intervalWindow a b) := by
  exact (integrableOn_const (s := Ioc a b) (μ := volume) (C := (1 : ℝ))
    (by simp only [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)).integrable_indicator
    measurableSet_Ioc

theorem integral_intervalWindow (a b : ℝ) :
    (∫ t, intervalWindow a b t) = max (b - a) 0 := by
  rw [intervalWindow, integral_indicator_const (1 : ℝ) measurableSet_Ioc, smul_eq_mul, mul_one,
    Real.volume_real_Ioc]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

theorem normalizedIntervalWindow_nonneg {ℓ : ℝ} (hℓ : 0 < ℓ) (x t : ℝ) :
    0 ≤ normalizedIntervalWindow ℓ x t := div_nonneg (intervalWindow_mem_Icc _ _ _).1 hℓ.le

theorem normalizedIntervalWindow_le {ℓ : ℝ} (hℓ : 0 < ℓ) (x t : ℝ) :
    normalizedIntervalWindow ℓ x t ≤ 1 / ℓ :=
  div_le_div_of_nonneg_right (intervalWindow_mem_Icc _ _ _).2 hℓ.le

theorem normalizedIntervalWindow_integrable (ℓ x : ℝ) :
    Integrable (normalizedIntervalWindow ℓ x) := (intervalWindow_integrable _ _).div_const ℓ

theorem normalizedIntervalWindow_measurable (ℓ x : ℝ) :
    Measurable (normalizedIntervalWindow ℓ x) := (intervalWindow_measurable _ _).div_const ℓ

theorem normalizedIntervalWindow_mass {ℓ : ℝ} (hℓ : 0 < ℓ) (x : ℝ) :
    (∫ t, normalizedIntervalWindow ℓ x t) = 1 := by
  unfold normalizedIntervalWindow
  rw [integral_div, integral_intervalWindow]
  simp only [add_sub_cancel_left, max_eq_left hℓ.le, div_self hℓ.ne']

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.KernelMixtureControl
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem kernelAverage_nonneg {X T : Type*} [MeasurableSpace T]
    (μ : Measure T) (K : X → T → ℝ) (g : T → ℝ)
    (hK : ∀ x t, 0 ≤ K x t) (hg : ∀ t, 0 ≤ g t) (x : X) :
    0 ≤ kernelAverage μ K g x := integral_nonneg (fun t => mul_nonneg (hK x t) (hg t))

theorem kernelAverage_cap {X T : Type*} [MeasurableSpace T]
    (μ : Measure T) (K : X → T → ℝ) (g : T → ℝ) {C : ℝ}
    (hK : ∀ x, Integrable (K x) μ) (hK0 : ∀ x t, 0 ≤ K x t)
    (hmass : ∀ x, (∫ t, K x t ∂μ) = 1) (hg : AEStronglyMeasurable g μ)
    (hgC : ∀ t, g t ∈ Set.Icc (0 : ℝ) C) (x : X) :
    kernelAverage μ K g x ≤ C := by
  have hnorm (t) : ‖g t‖ ≤ C := by simpa only [Real.norm_of_nonneg (hgC t).1] using (hgC t).2
  have hint : Integrable (fun t => K x t * g t) μ := (hK x).mul_bdd hg (Filter.Eventually.of_forall hnorm)
  have h := integral_mono hint ((hK x).mul_const C)
    (fun t => mul_le_mul_of_nonneg_left (hgC t).2 (hK0 x t))
  simpa only [kernelAverage, integral_mul_const, hmass, one_mul] using h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.BoxWindowAveraging
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

variable {ι : Type*} [Fintype ι]

theorem boxProbabilityWindow_nonneg (ℓ : ι → ℝ) (hℓ : ∀ i, 0 < ℓ i) (x t : ι → ℝ) :
    0 ≤ boxProbabilityWindow ℓ x t :=
  Finset.prod_nonneg (fun i _ => normalizedIntervalWindow_nonneg (hℓ i) _ _)

theorem boxProbabilityWindow_integrable (ℓ x : ι → ℝ) :
    Integrable (boxProbabilityWindow ℓ x) :=
  Integrable.fintype_prod (fun i => normalizedIntervalWindow_integrable (ℓ i) (x i))

theorem boxProbabilityWindow_measurable (ℓ x : ι → ℝ) : Measurable (boxProbabilityWindow ℓ x) := by
  apply Finset.measurable_prod
  intro i _
  exact (normalizedIntervalWindow_measurable _ _).comp (measurable_pi_apply i)

theorem boxProbabilityWindow_mass (ℓ : ι → ℝ) (hℓ : ∀ i, 0 < ℓ i) (x : ι → ℝ) :
    (∫ t, boxProbabilityWindow ℓ x t) = 1 := by
  unfold boxProbabilityWindow
  rw [integral_fintype_prod_volume_eq_prod]
  simp only [normalizedIntervalWindow_mass (hℓ _), Finset.prod_const_one]

theorem boxProbabilityWindow_cap (ℓ : ι → ℝ) (hℓ : ∀ i, 0 < ℓ i) (x t : ι → ℝ) :
    boxProbabilityWindow ℓ x t ≤ ∏ i, 1 / ℓ i :=
  Finset.prod_le_prod (fun i _ => normalizedIntervalWindow_nonneg (hℓ i) _ _)
    (fun i _ => normalizedIntervalWindow_le (hℓ i) _ _)

theorem boxAverage_mem_Icc (ℓ : ι → ℝ) (hℓ : ∀ i, 0 < ℓ i)
    (g : (ι → ℝ) → ℝ) {C : ℝ} (hg : AEStronglyMeasurable g volume)
    (hbound : ∀ t, g t ∈ Set.Icc (0 : ℝ) C) (x : ι → ℝ) :
    kernelAverage volume (boxProbabilityWindow ℓ) g x ∈ Set.Icc (0 : ℝ) C :=
  ⟨kernelAverage_nonneg volume _ g (boxProbabilityWindow_nonneg ℓ hℓ) (fun t => (hbound t).1) x,
    kernelAverage_cap volume _ g (boxProbabilityWindow_integrable ℓ) (boxProbabilityWindow_nonneg ℓ hℓ)
      (boxProbabilityWindow_mass ℓ hℓ) hg hbound x⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineBoxTest
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem normalizedIntervalWindow_translate (ℓ x t : ℝ) :
    normalizedIntervalWindow ℓ x t = normalizedIntervalWindow ℓ 0 (t - x) := by
  have hm : t ∈ Set.Ioc x (x + ℓ) ↔ t - x ∈ Set.Ioc 0 (0 + ℓ) := by
    simp only [Set.mem_Ioc]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  simp only [normalizedIntervalWindow, intervalWindow, Set.indicator, hm]

variable {ι : Type*} [Fintype ι]

theorem boxProbabilityWindow_translate (ℓ x t : ι → ℝ) :
    boxProbabilityWindow ℓ x t = boxProbabilityWindow ℓ 0 (t - x) := by
  apply Finset.prod_congr rfl
  intro i _
  exact normalizedIntervalWindow_translate _ _ _

theorem boxAverage_eq_translate (ℓ : ι → ℝ) (g : (ι → ℝ) → ℝ) (x : ι → ℝ) :
    kernelAverage volume (boxProbabilityWindow ℓ) g x =
      ∫ u, boxProbabilityWindow ℓ 0 u * g (u + x) := by
  change (∫ t, boxProbabilityWindow ℓ x t * g t) = _
  rw [← integral_add_right_eq_self (fun t => boxProbabilityWindow ℓ x t * g t) x]
  apply integral_congr_ae
  filter_upwards [] with u
  rw [boxProbabilityWindow_translate, add_sub_cancel_right]

theorem affineBoxAverage_eq (ℓ : ι → ℝ) (A : (ι → ℝ) ≃L[ℝ] (ι → ℝ))
    (g : (ι → ℝ) → ℝ) (x : ι → ℝ) :
    affineBoxAverage ℓ A.toContinuousLinearMap g x =
      kernelAverage volume (boxProbabilityWindow ℓ) (fun t => g (A t)) (A.symm x) := by
  rw [boxAverage_eq_translate]
  unfold affineBoxAverage
  apply integral_congr_ae
  filter_upwards [] with u
  simp only [map_add, A.apply_symm_apply, ContinuousLinearEquiv.coe_coe, add_comm]

theorem affineBoxAverage_mem_Icc (ℓ : ι → ℝ) (hℓ : ∀ i, 0 < ℓ i)
    (A : (ι → ℝ) ≃L[ℝ] (ι → ℝ)) (g : (ι → ℝ) → ℝ) {C : ℝ}
    (hg : Measurable g) (hbound : ∀ t, g t ∈ Set.Icc (0 : ℝ) C) (x : ι → ℝ) :
    affineBoxAverage ℓ A.toContinuousLinearMap g x ∈ Set.Icc (0 : ℝ) C := by
  rw [affineBoxAverage_eq]
  exact boxAverage_mem_Icc ℓ hℓ _ (hg.comp A.continuous.measurable).aestronglyMeasurable
    (fun t => hbound (A t)) _

end Erdos3

end

end OAI
end

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

omit [Fintype ι] in
theorem linearDensityPullback_nonneg (A : (ι → ℝ) ≃L[ℝ] (ι → ℝ))
    {f : (ι → ℝ) → ℝ} (hf : ∀ x, 0 ≤ f x) (x : ι → ℝ) :
    0 ≤ linearDensityPullback A f x := mul_nonneg (inverseJacobian_pos A).le (hf _)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

variable {ι : Type*} [Fintype ι]

theorem linearBoxDensity_measurable (ℓ : ι → ℝ) (A : (ι → ℝ) ≃L[ℝ] (ι → ℝ)) :
    Measurable (linearBoxDensity ℓ A) :=
  linearDensityPullback_measurable A (boxProbabilityWindow_measurable ℓ 0)

theorem linearBoxDensity_mem_Icc (ℓ : ι → ℝ) (hℓ : ∀ i, 0 < ℓ i)
    (A : (ι → ℝ) ≃L[ℝ] (ι → ℝ)) (x : ι → ℝ) :
    linearBoxDensity ℓ A x ∈ Set.Icc (0 : ℝ) (linearBoxDensityCap ℓ hℓ A) :=
  ⟨linearDensityPullback_nonneg A (boxProbabilityWindow_nonneg ℓ hℓ 0) x,
    mul_le_mul_of_nonneg_left (boxProbabilityWindow_cap ℓ hℓ 0 (A.symm x))
      (inverseJacobian_pos A).le⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.TwoBoxSmoothingComplex
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

variable {ι : Type*} [Fintype ι]

theorem twoBoxDifferenceDensity_mem_Icc_s2_oai (ℓ r : ι → ℝ)
    (hℓ : ∀ i, 0 < ℓ i) (hr : ∀ i, 0 < r i)
    (A B : (ι → ℝ) ≃L[ℝ] (ι → ℝ)) (x : ι → ℝ) :
    twoBoxDifferenceDensity ℓ r A B x ∈ Set.Icc (0 : ℝ) (linearBoxDensityCap r hr B) :=
  affineBoxAverage_mem_Icc ℓ hℓ A _ (linearBoxDensity_measurable r B)
    (linearBoxDensity_mem_Icc r hr B) x

end Erdos3

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Erdos3.twoBoxDifferenceDensity_mem_Icc_s2_oai.{u_1} := @OAI.Erdos3.twoBoxDifferenceDensity_mem_Icc_s2_oai.{u_1}
