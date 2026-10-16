-- Prove2me | solution 1 for OAI.Erdos3.jointSlicedProfileValue_unit_comparison
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-16T01:31:01.228789+00:00
-- url     : https://prove2.me/submissions/40570084-e6be-4c33-9204-9ca67ef8f723

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B174
import Theorems.Thm_OAI_Erdos3_selected_cutoff_comparison_of_close_derivatives

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BoundedProductDifference
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem bounded_nonnegative_prod_difference {ι : Type*} (s : Finset ι) (f g C : ι → ℝ)
    (hC : ∀ i, 1 ≤ C i) (hf : ∀ i, f i ∈ Set.Icc (0 : ℝ) (C i))
    (hg : ∀ i, g i ∈ Set.Icc (0 : ℝ) (C i)) :
    |(∏ i ∈ s, f i) - ∏ i ∈ s, g i| ≤ (∏ i ∈ s, C i) * ∑ i ∈ s, |f i - g i| := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.prod_insert hi, Finset.sum_insert hi]
    have hp0 : 0 ≤ ∏ j ∈ s, f j := Finset.prod_nonneg (fun j _ => (hf j).1)
    have hc0 : 0 ≤ ∏ j ∈ s, C j := Finset.prod_nonneg (fun j _ => zero_le_one.trans (hC j))
    have hpc : (∏ j ∈ s, f j) ≤ ∏ j ∈ s, C j :=
      Finset.prod_le_prod (fun index _ => (hf index).1) (fun index _ => (hf index).2)
    have hmul : |f i - g i| * (∏ j ∈ s, C j) ≤ C i * (|f i - g i| * ∏ j ∈ s, C j) :=
      le_mul_of_one_le_left (mul_nonneg (abs_nonneg _) hc0) (hC i)
    calc
      |f i * (∏ j ∈ s, f j) - g i * ∏ j ∈ s, g j| =
          |(f i - g i) * (∏ j ∈ s, f j) + g i * ((∏ j ∈ s, f j) - ∏ j ∈ s, g j)| := by
        congr 1
        ring
      _ ≤ |(f i - g i) * (∏ j ∈ s, f j)| + |g i * ((∏ j ∈ s, f j) - ∏ j ∈ s, g j)| := abs_add_le _ _
      _ = |f i - g i| * (∏ j ∈ s, f j) + g i * |(∏ j ∈ s, f j) - ∏ j ∈ s, g j| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hp0, abs_of_nonneg (hg i).1]
      _ ≤ |f i - g i| * (∏ j ∈ s, C j) + C i * ((∏ j ∈ s, C j) * ∑ j ∈ s, |f j - g j|) :=
        add_le_add (mul_le_mul_of_nonneg_left hpc (abs_nonneg _))
          (mul_le_mul (hg i).2 ih (abs_nonneg _) (zero_le_one.trans (hC i)))
      _ ≤ C i * (|f i - g i| * ∏ j ∈ s, C j) + C i * ((∏ j ∈ s, C j) * ∑ j ∈ s, |f j - g j|) :=
        add_le_add hmul le_rfl
      _ = (C i * ∏ j ∈ s, C j) * (|f i - g i| + ∑ j ∈ s, |f j - g j|) := by ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.UnitBoxAmplitude
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

theorem positiveUnitBox_measurable : MeasurableSet (positiveUnitBox ι) :=
  MeasurableSet.univ_pi (fun _ => measurableSet_Ioc)

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

theorem product_cutoff_loss_le {ι : Type*} [Fintype ι] (f : ι → ℝ)
    (hf : ∀ i, f i ∈ Set.Icc (0 : ℝ) 1) :
    1 - ∏ i, f i ≤ ∑ i, (1 - f i) := by
  have h := bounded_nonnegative_prod_difference Finset.univ (fun _ : ι => (1 : ℝ)) f
    (fun _ => (1 : ℝ)) (fun _ => le_rfl) (fun _ => ⟨zero_le_one, le_rfl⟩) hf
  have habs (i : ι) : |1 - f i| = 1 - f i := abs_of_nonneg (sub_nonneg.mpr (hf i).2)
  simpa only [Finset.prod_const_one, one_mul, habs,
    abs_of_nonneg (sub_nonneg.mpr (product_cutoff_range f hf).2)] using h

theorem product_cutoff_tsupport_subset {ι E : Type*} [Fintype ι] [TopologicalSpace E]
    (f : ι → E → ℝ) (i : ι) : tsupport (fun x => ∏ j, f j x) ⊆ tsupport (f i) := by
  classical
  apply closure_mono
  intro x hx
  change f i x ≠ 0
  intro hz
  exact hx (Finset.prod_eq_zero (Finset.mem_univ i) hz)

theorem product_cutoff_fderiv_norm_le {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ι → E → ℝ) (x : E) (hf : ∀ i, DifferentiableAt ℝ (f i) x)
    (hrange : ∀ i, f i x ∈ Set.Icc (0 : ℝ) 1) :
    ‖fderiv ℝ (fun y => ∏ i, f i y) x‖ ≤ ∑ i, ‖fderiv ℝ (f i) x‖ := by
  classical
  rw [fderiv_finsetProd (fun i _ => hf i)]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  have hp0 : 0 ≤ ∏ j ∈ Finset.univ.erase i, f j x :=
    Finset.prod_nonneg (fun j _ => (hrange j).1)
  have hp1 : (∏ j ∈ Finset.univ.erase i, f j x) ≤ 1 :=
    Finset.prod_le_one (fun j _ => (hrange j).1) (fun j _ => (hrange j).2)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hp0]
  exact mul_le_of_le_one_left (norm_nonneg _) hp1

theorem product_cutoff_integral_loss_le {ι E : Type*} [Fintype ι] [MeasurableSpace E]
    (μ : Measure E) [IsFiniteMeasure μ] (f : ι → E → ℝ)
    (hf : ∀ i, Measurable (f i)) (hrange : ∀ i x, f i x ∈ Set.Icc (0 : ℝ) 1) :
    (∫ x, 1 - ∏ i, f i x ∂μ) ≤ ∑ i, ∫ x, 1 - f i x ∂μ := by
  have hprod : Measurable (fun x => ∏ i, f i x) := Finset.measurable_prod _ (fun i _ => hf i)
  have hprodi := cutoff_integrable μ _ hprod (fun x => product_cutoff_range _ (fun i => hrange i x))
  have hfi (i : ι) : Integrable (fun x => 1 - f i x) μ :=
    (integrable_const (1 : ℝ)).sub (cutoff_integrable μ _ (hf i) (hrange i))
  calc
    _ ≤ ∫ x, ∑ i, (1 - f i x) ∂μ := integral_mono
      ((integrable_const (1 : ℝ)).sub hprodi) (integrable_finsetSum _ (fun i _ => hfi i))
      (fun x => product_cutoff_loss_le _ (fun i => hrange i x))
    _ = _ := integral_finsetSum _ (fun i _ => hfi i)

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

theorem halfspaceCutoff_eq_one {E : Type*} {r : ℝ} (hr : 0 < r)
    (d : E → ℝ) {x : E} (hx : 2 * r ≤ d x) : halfspaceCutoff r d x = 1 := by
  apply Real.smoothTransition.one_of_one_le
  have h := (le_div_iff₀ hr).mpr hx
  linarith

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

theorem halfspaceCutoff_fderiv_norm_le {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : ℝ≥0) (hLip : LipschitzWith A Real.smoothTransition)
    {r : ℝ} (hr : 0 < r) (d : E → ℝ) {x : E} (hd : DifferentiableAt ℝ d x) :
    ‖fderiv ℝ (halfspaceCutoff r d) x‖ ≤ (A : ℝ) / r * ‖fderiv ℝ d x‖ := by
  have ht : DifferentiableAt ℝ Real.smoothTransition (r⁻¹ • d x - 1) :=
    ((Real.smoothTransition.contDiff : ContDiff ℝ 1 _).differentiable one_ne_zero).differentiableAt
  have heq : halfspaceCutoff r d = Real.smoothTransition ∘ (fun y => r⁻¹ • d y - 1) := by
    funext y
    simp only [halfspaceCutoff, Function.comp_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
  rw [heq]
  change ‖fderiv ℝ (Real.smoothTransition ∘ (fun y => (r⁻¹ • d) y - 1)) x‖ ≤ _
  rw [fderiv_comp x ht ((hd.const_smul r⁻¹).sub_const 1),
    fderiv_sub_const, fderiv_const_smul hd]
  calc
    _ ≤ ‖fderiv ℝ Real.smoothTransition (r⁻¹ • d x - 1)‖ * ‖r⁻¹ • fderiv ℝ d x‖ :=
      (fderiv ℝ Real.smoothTransition _).opNorm_comp_le _
    _ ≤ (A : ℝ) * ‖r⁻¹ • fderiv ℝ d x‖ :=
      mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hLip) (norm_nonneg _)
    _ = _ := by rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr]; ring

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

theorem inequalityBoundaryCutoff_fderiv_norm_le {I E : Type*} [Fintype I]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : ℝ≥0) (hLip : LipschitzWith A Real.smoothTransition)
    (r : I → ℝ) (hr : ∀ i, 0 < r i) (d : I → E → ℝ) (hd : ∀ i, ContDiff ℝ ∞ (d i)) (x : E) :
    ‖fderiv ℝ (inequalityBoundaryCutoff r d) x‖ ≤
      ∑ i, ((A : ℝ) / r i) * ‖fderiv ℝ (d i) x‖ := by
  apply (product_cutoff_fderiv_norm_le (fun i => halfspaceCutoff (r i) (d i)) x
    (fun i => ((contDiff_halfspaceCutoff (r i) (d i) (hd i)).differentiable (by norm_num)).differentiableAt)
    (fun i => halfspaceCutoff_range (r i) (d i) x)).trans
  exact Finset.sum_le_sum (fun i _ => halfspaceCutoff_fderiv_norm_le A hLip (hr i) (d i)
    (((hd i).differentiable (by norm_num)).differentiableAt))

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem halfspaceCutoff_measurable {E : Type*} [MeasurableSpace E]
    (r : ℝ) (d : E → ℝ) (hd : Measurable d) : Measurable (halfspaceCutoff r d) :=
  Real.smoothTransition.continuous.measurable.comp ((hd.div_const r).sub_const 1)

theorem halfspaceCutoff_integral_loss_le {E : Type*} [MeasurableSpace E]
    (μ : Measure E) [IsFiniteMeasure μ] {r : ℝ} (hr : 0 < r)
    (d : E → ℝ) (hd : Measurable d) :
    (∫ x, 1 - halfspaceCutoff r d x ∂μ) ≤ μ.real {x | d x < 2 * r} := by
  let s := {x | d x < 2 * r}
  have hs : MeasurableSet s := measurableSet_lt hd measurable_const
  have hfi := cutoff_integrable μ _ (halfspaceCutoff_measurable r d hd) (halfspaceCutoff_range r d)
  calc
    _ ≤ ∫ x, s.indicator (fun _ => (1 : ℝ)) x ∂μ := by
      apply integral_mono ((integrable_const (1 : ℝ)).sub hfi)
        ((integrable_const (1 : ℝ)).indicator hs)
      intro x
      change 1 - halfspaceCutoff r d x ≤ s.indicator (fun _ => (1 : ℝ)) x
      by_cases hx : x ∈ s
      · rw [Set.indicator_of_mem hx]
        linarith [(halfspaceCutoff_range r d x).1]
      · rw [Set.indicator_of_notMem hx, halfspaceCutoff_eq_one hr d (le_of_not_gt hx)]
        norm_num
    _ = _ := integral_indicator_one hs

theorem inequalityBoundaryCutoff_integral_loss_le {I E : Type*} [Fintype I] [MeasurableSpace E]
    (μ : Measure E) [IsFiniteMeasure μ] (r : I → ℝ) (hr : ∀ i, 0 < r i)
    (d : I → E → ℝ) (hd : ∀ i, Measurable (d i)) :
    (∫ x, 1 - inequalityBoundaryCutoff r d x ∂μ) ≤ ∑ i, μ.real {x | d i x < 2 * r i} := by
  apply (product_cutoff_integral_loss_le μ (fun i => halfspaceCutoff (r i) (d i))
    (fun i => halfspaceCutoff_measurable (r i) (d i) (hd i))
    (fun i => halfspaceCutoff_range (r i) (d i))).trans
  exact Finset.sum_le_sum (fun i _ => halfspaceCutoff_integral_loss_le μ (hr i) (d i) (hd i))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators ContDiff

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

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

variable (ι : Type*) [Fintype ι]

theorem unitBoxMeasure_eq_pi :
    unitBoxMeasure ι = Measure.pi (fun _ : ι => unitScalarMeasure) := by
  change (Measure.pi (fun _ : ι => (volume : Measure ℝ))).restrict
    (Set.univ.pi (fun _ => Set.Ioc (0 : ℝ) 1)) = _
  exact Measure.restrict_pi_pi _ _

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

theorem operatorPrecompose_norm_le (J : E →L[ℝ] X) :
    ‖operatorPrecompose (Y := Y) J‖ ≤ ‖J‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg J)
  intro A
  exact (A.opNorm_comp_le J).trans_eq (mul_comm _ _)

end Erdos3

end

section

namespace Erdos3

variable {E X Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialParameterContinuity
namespace OAI

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

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

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped ContDiff

variable {I O : Type*} [Fintype I] [DecidableEq I] [Fintype O]

omit [DecidableEq I] in
theorem polynomialVectorMap_contDiff (p : O → MvPolynomial I ℝ) :
    ContDiff ℝ ∞ (polynomialVectorMap p) := contDiff_pi.mpr (fun o => mvPolynomial_contDiff_eval (p o))

theorem polynomialVectorMap_fderiv_entry (p : O → MvPolynomial I ℝ) (x : I → ℝ) (i : I) (o : O) :
    fderiv ℝ (polynomialVectorMap p) x (Pi.single i 1) o =
      MvPolynomial.eval x (MvPolynomial.pderiv i (p o)) := by
  have hd := (polynomialVectorMap_contDiff p).differentiable (by norm_num) x
  have he := mvPolynomial_fderiv_coordinate (p o) x i
  change fderiv ℝ (fun y => polynomialVectorMap p y o) x (Pi.single i 1) = _ at he
  rw [fderiv_apply hd o] at he
  exact he

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

end Erdos3

end

section

namespace Erdos3

open scoped ContDiff

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators ContDiff

theorem polynomialVectorMap_mass_c2_bounds {I O : Type*}
    [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
    (p : O → MvPolynomial I ℝ) {d : ℕ} (hd : ∀ o i, (p o).degreeOf i ≤ d)
    {C : ℝ} (hC : 0 ≤ C) (hmass : ∀ o, realPolynomialMass (p o) ≤ C)
    (x : I → ℝ) (hx : ∀ i, |x i| ≤ 1) :
    ‖polynomialVectorMap p x‖ ≤ C ∧
      ‖fderiv ℝ (polynomialVectorMap p) x‖ ≤ Fintype.card I * ((d : ℝ) * C) ∧
      ‖fderiv ℝ (fderiv ℝ (polynomialVectorMap p)) x‖ ≤
        Fintype.card I * (Fintype.card I * ((d : ℝ) * ((d : ℝ) * C))) := by
  have hfirst (o : O) (i : I) : realPolynomialMass (pderiv i (p o)) ≤ (d : ℝ) * C :=
    (realPolynomialMass_pderiv_degreeOf (p o) i (hd o i)).trans
      (mul_le_mul_of_nonneg_left (hmass o) (Nat.cast_nonneg _))
  have hsecond (o : O) (i j : I) :
      realPolynomialMass (pderiv j (pderiv i (p o))) ≤ (d : ℝ) * ((d : ℝ) * C) :=
    (realPolynomialMass_pderiv_degreeOf (pderiv i (p o)) j
      (mvPolynomial_pderiv_degreeOf_le (p o) i j (hd o j))).trans
      (mul_le_mul_of_nonneg_left (hfirst o i) (Nat.cast_nonneg _))
  refine ⟨?_, ?_, ?_⟩
  · apply (pi_norm_le_iff_of_nonneg hC).mpr
    intro o
    exact (mvPolynomial_eval_abs_le_sum_coeff (p o) x hx).trans (hmass o)
  · apply clm_norm_le_card_mul_of_entries _ (mul_nonneg (Nat.cast_nonneg _) hC)
    intro i o
    rw [polynomialVectorMap_fderiv_entry]
    exact (mvPolynomial_eval_abs_le_sum_coeff (pderiv i (p o)) x hx).trans (hfirst o i)
  · have hs : ContDiff ℝ 2 (polynomialVectorMap p) :=
      (polynomialVectorMap_contDiff p).of_le (by first | exact WithTop.coe_le_coe.2 le_top | exact ENat.LEInfty.out | (norm_cast; done) | exact_mod_cast le_top)
    have hs' : ContDiff ℝ 1 (fderiv ℝ (polynomialVectorMap p)) := hs.fderiv_right (by norm_num)
    exact polynomialOperator_fderiv_norm_le _ (fun o i => pderiv i (p o))
      (fun y o i => polynomialVectorMap_fderiv_entry p y i o) x (hs'.differentiable one_ne_zero x)
      (by positivity) (fun o i j =>
        (mvPolynomial_eval_abs_le_sum_coeff (pderiv j (pderiv i (p o))) x hx).trans (hsecond o i j))

theorem polynomialMassC2Budget_dominates (N d : ℕ) {C : ℝ} (hC : 0 ≤ C) :
    C ≤ polynomialMassC2Budget N d C ∧
      N * ((d : ℝ) * C) ≤ polynomialMassC2Budget N d C ∧
      N * (N * ((d : ℝ) * ((d : ℝ) * C))) ≤ polynomialMassC2Budget N d C := by
  have hx : 0 ≤ (N : ℝ) * d := by positivity
  have h0 : 1 ≤ (1 + (N : ℝ) * d)^2 := by nlinarith [sq_nonneg ((N : ℝ) * d)]
  have h1 : (N : ℝ) * d ≤ (1 + (N : ℝ) * d)^2 := by nlinarith [sq_nonneg ((N : ℝ) * d)]
  have h2 : ((N : ℝ) * d)^2 ≤ (1 + (N : ℝ) * d)^2 := by nlinarith
  unfold polynomialMassC2Budget
  refine ⟨?_, ?_, ?_⟩
  · simpa only [one_mul] using mul_le_mul_of_nonneg_right h0 hC
  · nlinarith [mul_le_mul_of_nonneg_right h1 hC]
  · nlinarith [mul_le_mul_of_nonneg_right h2 hC]

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.RestrictedComplexChartDensityComparison
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem realDensityMeasure_indicator {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) {S : Set X} (hS : MeasurableSet S) :
    realDensityMeasure μ (S.indicator f) = (realDensityMeasure μ f).restrict S := by
  have he : (fun x => ENNReal.ofReal (S.indicator f x)) =
      S.indicator (fun x => ENNReal.ofReal (f x)) := by
    funext x
    by_cases hx : x ∈ S
    · simp only [Set.indicator_of_mem hx]
    · simp only [Set.indicator_of_notMem hx, ENNReal.ofReal_zero]
  unfold realDensityMeasure
  rw [he, withDensity_indicator hS, restrict_withDensity hS]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory _root_.Set

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open MeasureTheory _root_.Set

end Erdos3

end

section

namespace Erdos3

open MeasureTheory _root_.Set

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {X Y : Type*}

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.UnitBoxInteriorCutoff
namespace OAI

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators ContDiff NNReal

variable {ι : Type*} [Fintype ι]

theorem unitBoxFace_contDiff (j : Bool × ι) : ContDiff ℝ ∞ (unitBoxFace j) := by
  rcases j with ⟨b, i⟩
  cases b
  · change ContDiff ℝ ∞ (fun x : ι → ℝ => x i)
    fun_prop
  · change ContDiff ℝ ∞ (fun x : ι → ℝ => 1 - x i)
    fun_prop

theorem unitBoxFace_lipschitz (j : Bool × ι) : LipschitzWith 1 (unitBoxFace j) := by
  rcases j with ⟨b, i⟩
  cases b
  · exact LipschitzWith.eval i
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [unitBoxFace, ↓reduceIte, NNReal.coe_one, one_mul, dist_sub_left] using
      dist_le_pi_dist x y i

theorem unitBoxInteriorCutoff_range (r : ℝ) (x : ι → ℝ) :
    unitBoxInteriorCutoff r x ∈ Set.Icc (0 : ℝ) 1 :=
  inequalityBoundaryCutoff_range _ _ _

theorem unitBoxInteriorCutoff_contDiff (r : ℝ) : ContDiff ℝ ∞ (unitBoxInteriorCutoff (ι := ι) r) :=
  inequalityBoundaryCutoff_smooth _ _ unitBoxFace_contDiff

theorem unitBoxInteriorCutoff_tsupport {r : ℝ} (hr : 0 < r)
    {x : ι → ℝ} (hx : x ∈ tsupport (unitBoxInteriorCutoff r)) :
    ∀ i, r ≤ x i ∧ x i ≤ 1 - r := by
  have h := inequalityBoundaryCutoff_tsupport_subset (fun _ : Bool × ι => r)
    (fun _ => hr) unitBoxFace (fun j => (unitBoxFace_contDiff j).continuous) hx
  intro i
  have h0 : r ≤ x i := h (false, i)
  have h1 : r ≤ 1 - x i := h (true, i)
  exact ⟨h0, by linarith⟩

theorem unitBoxInteriorCutoff_support_box {r : ℝ} (hr : 0 < r) :
    tsupport (unitBoxInteriorCutoff (ι := ι) r) ⊆ positiveUnitBox ι := by
  intro x hx i _
  have hi := unitBoxInteriorCutoff_tsupport hr hx i
  exact ⟨hr.trans_le hi.1, hi.2.trans (by linarith)⟩

theorem unitBoxInteriorCutoff_compact {r : ℝ} (hr : 0 < r) :
    HasCompactSupport (unitBoxInteriorCutoff (ι := ι) r) := by
  apply (isCompact_Icc : IsCompact (Set.Icc (fun _ : ι => r) (fun _ : ι => 1 - r))).of_isClosed_subset
    (isClosed_tsupport _)
  intro x hx
  exact ⟨fun i => (unitBoxInteriorCutoff_tsupport hr hx i).1,
    fun i => (unitBoxInteriorCutoff_tsupport hr hx i).2⟩

theorem unitBoxFace_strip {r : ℝ} (hr : 0 ≤ r) (j : Bool × ι) :
    (unitBoxMeasure ι).real {x | unitBoxFace j x < r} ≤ r := by
  rcases j with ⟨b, i⟩
  have he : (unitBoxMeasure ι).map (Function.eval i) = unitScalarMeasure := by
    rw [unitBoxMeasure_eq_pi]
    exact (measurePreserving_eval (fun _ : ι => unitScalarMeasure) i).map_eq
  cases b
  · change (unitBoxMeasure ι).real ((Function.eval i) ⁻¹' Set.Iio r) ≤ r
    rw [← map_measureReal_apply (measurable_pi_apply i) measurableSet_Iio, he,
      unitScalarMeasure, measureReal_restrict_apply measurableSet_Iio]
    calc
      _ ≤ volume.real (Set.Ioc (0 : ℝ) r) := measureReal_mono (by
        intro t ht
        exact ⟨ht.2.1, ht.1.le⟩) (by simp)
      _ = r := by rw [Real.volume_real_Ioc_of_le hr]; ring
  · let s := {t : ℝ | 1 - t < r}
    have hs : MeasurableSet s := measurableSet_lt (measurable_const.sub measurable_id) measurable_const
    change (unitBoxMeasure ι).real ((Function.eval i) ⁻¹' s) ≤ r
    rw [← map_measureReal_apply (measurable_pi_apply i) hs, he,
      unitScalarMeasure, measureReal_restrict_apply hs]
    calc
      _ ≤ volume.real (Set.Ioc (1 - r) 1) := measureReal_mono (by
        intro t ht
        have h : 1 - t < r := ht.1
        exact ⟨by linarith, ht.2.2⟩) (by simp)
      _ = r := by rw [Real.volume_real_Ioc_of_le (by linarith : 1 - r ≤ 1)]; ring

theorem unitBoxInteriorCutoff_loss {r : ℝ} (hr : 0 < r) :
    (∫ x, 1 - unitBoxInteriorCutoff r x ∂unitBoxMeasure ι) ≤ 4 * Fintype.card ι * r := by
  have h := inequalityBoundaryCutoff_integral_loss_le (unitBoxMeasure ι)
    (fun _ : Bool × ι => r) (fun _ => hr) unitBoxFace
    (fun j => (unitBoxFace_contDiff j).continuous.measurable)
  apply h.trans
  calc
    _ ≤ ∑ _j : Bool × ι, 2 * r := Finset.sum_le_sum (fun j _ => unitBoxFace_strip (by positivity) j)
    _ = _ := by simp [Fintype.card_prod]; ring

theorem unitBoxInteriorCutoff_integral {r : ℝ} (hr : 0 < r) :
    (∫ x : ι → ℝ, unitBoxInteriorCutoff r x) =
      ∫ x, unitBoxInteriorCutoff r x ∂unitBoxMeasure ι := by
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  exact image_eq_zero_of_notMem_tsupport (fun h => hx (unitBoxInteriorCutoff_support_box hr h))

theorem unitBoxInteriorCutoff_mass {r : ℝ} (hr : 0 < r) :
    1 - 4 * Fintype.card ι * r ≤ ∫ x : ι → ℝ, unitBoxInteriorCutoff r x := by
  have hi := cutoff_integrable (unitBoxMeasure ι) (unitBoxInteriorCutoff r)
    (unitBoxInteriorCutoff_contDiff r).continuous.measurable (unitBoxInteriorCutoff_range r)
  have h := unitBoxInteriorCutoff_loss (ι := ι) hr
  rw [integral_sub (integrable_const (1 : ℝ)) hi] at h
  simp only [integral_const, probReal_univ, one_smul] at h
  rw [unitBoxInteriorCutoff_integral hr]
  linarith

theorem unitBoxInteriorCutoff_density {r : ℝ} (hr : 0 < r) :
    realDensityMeasure volume (unitBoxInteriorCutoff (ι := ι) r) =
      realDensityMeasure (unitBoxMeasure ι) (unitBoxInteriorCutoff r) := by
  have hi : (positiveUnitBox ι).indicator (unitBoxInteriorCutoff r) = unitBoxInteriorCutoff r := by
    apply Set.indicator_eq_self.2
    intro x hx
    exact unitBoxInteriorCutoff_support_box hr (subset_tsupport _ hx)
  have h := realDensityMeasure_indicator volume (unitBoxInteriorCutoff r)
    (positiveUnitBox_measurable (ι := ι))
  rw [hi] at h
  exact h.trans (restrict_withDensity (positiveUnitBox_measurable (ι := ι)) _)

theorem unitBoxInteriorCutoff_fderiv_bound (A : ℝ≥0)
    (hA : LipschitzWith A Real.smoothTransition) {r : ℝ} (hr : 0 < r) (x : ι → ℝ) :
    ‖fderiv ℝ (unitBoxInteriorCutoff r) x‖ ≤ 2 * Fintype.card ι * A / r := by
  have h := inequalityBoundaryCutoff_fderiv_norm_le A hA
    (fun _ : Bool × ι => r) (fun _ => hr) unitBoxFace unitBoxFace_contDiff x
  apply h.trans
  calc
    _ ≤ ∑ _j : Bool × ι, (A : ℝ) / r := Finset.sum_le_sum (fun j _ =>
      mul_le_of_le_one_right (div_nonneg A.coe_nonneg hr.le)
        (norm_fderiv_le_of_lipschitz ℝ (unitBoxFace_lipschitz j)))
    _ = _ := by simp [Fintype.card_prod]; ring

theorem unitBoxInteriorCutoff_directional_integral (A : ℝ≥0)
    (hA : LipschitzWith A Real.smoothTransition) {r : ℝ} (hr : 0 < r) (v : ι → ℝ) :
    (∫ x, |fderiv ℝ (unitBoxInteriorCutoff r) x v|) ≤
      (2 * Fintype.card ι * A / r) * ‖v‖ := by
  let L : ℝ := 2 * Fintype.card ι * A / r
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hb (x : ι → ℝ) : |fderiv ℝ (unitBoxInteriorCutoff r) x v| ≤ L * ‖v‖ := by
    exact ((fderiv ℝ (unitBoxInteriorCutoff r) x).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (unitBoxInteriorCutoff_fderiv_bound A hA hr x) (norm_nonneg v))
  have hm : Measurable (fun x : ι → ℝ => |fderiv ℝ (unitBoxInteriorCutoff r) x v|) :=
    (((unitBoxInteriorCutoff_contDiff r).continuous_fderiv (by norm_num)).clm_apply
      continuous_const).abs.measurable
  have hi : Integrable (fun x : ι → ℝ => |fderiv ℝ (unitBoxInteriorCutoff r) x v|)
      (unitBoxMeasure ι) :=
    (integrable_const (L * ‖v‖)).mono' hm.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs, abs_abs] using hb x))
  have he : (∫ x, |fderiv ℝ (unitBoxInteriorCutoff r) x v|) =
      ∫ x, |fderiv ℝ (unitBoxInteriorCutoff r) x v| ∂unitBoxMeasure ι := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [fderiv_of_notMem_tsupport ℝ (fun h => hx (unitBoxInteriorCutoff_support_box hr h))]
    simp
  rw [he]
  have h := integral_mono hi (integrable_const (L * ‖v‖)) hb
  simpa only [integral_const, probReal_univ, one_smul] using h

theorem unitBoxInteriorCutoff_derivative_budget [DecidableEq ι] (A : ℝ≥0)
    (hA : LipschitzWith A Real.smoothTransition) {r : ℝ} (hr : 0 < r) :
    (∑ j : ι, ∫ x, |fderiv ℝ (unitBoxInteriorCutoff r) x (Pi.single j 1)|) ≤
      2 * (Fintype.card ι : ℝ) ^ 2 * A / r := by
  calc
    _ ≤ ∑ _j : ι, 2 * Fintype.card ι * A / r := Finset.sum_le_sum (fun j _ => by
      simpa only [Pi.norm_single, norm_one, mul_one] using
        unitBoxInteriorCutoff_directional_integral A hA hr (Pi.single j 1))
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FactoredC2Difference
namespace OAI

section

namespace Erdos3

variable {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem factoredDifference_fderiv (F G R : E → Y) (t : ℝ)
    (hF : Differentiable ℝ F) (hG : Differentiable ℝ G) (hR : Differentiable ℝ R)
    (he : ∀ x, F x - G x = t • R x) (x : E) :
    fderiv ℝ F x - fderiv ℝ G x = t • fderiv ℝ R x := by
  rw [← fderiv_sub (hF x) (hG x), show F - G = t • R from funext he,
    fderiv_const_smul (hR x)]

theorem factoredDifference_second_fderiv (F G R : E → Y) (t : ℝ)
    (hF : ContDiff ℝ 2 F) (hG : ContDiff ℝ 2 G) (hR : ContDiff ℝ 2 R)
    (he : ∀ x, F x - G x = t • R x) (x : E) :
    fderiv ℝ (fderiv ℝ F) x - fderiv ℝ (fderiv ℝ G) x = t • fderiv ℝ (fderiv ℝ R) x := by
  have hF' : ContDiff ℝ 1 (fderiv ℝ F) := hF.fderiv_right (by norm_num)
  have hG' : ContDiff ℝ 1 (fderiv ℝ G) := hG.fderiv_right (by norm_num)
  have hR' : ContDiff ℝ 1 (fderiv ℝ R) := hR.fderiv_right (by norm_num)
  exact factoredDifference_fderiv _ _ _ t (hF'.differentiable one_ne_zero)
    (hG'.differentiable one_ne_zero) (hR'.differentiable one_ne_zero)
    (factoredDifference_fderiv F G R t (hF.differentiable (by norm_num))
      (hG.differentiable (by norm_num)) (hR.differentiable (by norm_num)) he) x

theorem factoredDifference_c2_bounds (F G R : E → Y) (t : ℝ)
    (hF : ContDiff ℝ 2 F) (hG : ContDiff ℝ 2 G) (hR : ContDiff ℝ 2 R)
    (he : ∀ x, F x - G x = t • R x) (x : E) {B₀ B₁ B₂ : ℝ}
    (h₀ : ‖R x‖ ≤ B₀) (h₁ : ‖fderiv ℝ R x‖ ≤ B₁) (h₂ : ‖fderiv ℝ (fderiv ℝ R) x‖ ≤ B₂) :
    ‖F x - G x‖ ≤ |t| * B₀ ∧ ‖fderiv ℝ F x - fderiv ℝ G x‖ ≤ |t| * B₁ ∧
      ‖fderiv ℝ (fderiv ℝ F) x - fderiv ℝ (fderiv ℝ G) x‖ ≤ |t| * B₂ := by
  rw [he x, factoredDifference_fderiv F G R t (hF.differentiable (by norm_num))
    (hG.differentiable (by norm_num)) (hR.differentiable (by norm_num)) he x,
    factoredDifference_second_fderiv F G R t hF hG hR he x]
  refine ⟨?_, ?_, ?_⟩
  · exact (norm_smul_le t (R x)).trans (mul_le_mul_of_nonneg_left h₀ (abs_nonneg t))
  · exact (ContinuousLinearMap.opNorm_smul_le t (fderiv ℝ R x)).trans
      (mul_le_mul_of_nonneg_left h₁ (abs_nonneg t))
  · exact (ContinuousLinearMap.opNorm_smul_le t (fderiv ℝ (fderiv ℝ R) x)).trans
      (mul_le_mul_of_nonneg_left h₂ (abs_nonneg t))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RawCanonicalNormalizedPolynomial
namespace OAI

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem polynomial_coefficient_split {K : Type*} [DecidableEq K] (p : MvPolynomial K ℝ)
    (selected : Finset (K →₀ ℕ)) :
    p = (∑ n ∈ selected, MvPolynomial.monomial n (p.coeff n)) +
      ∑ n ∈ p.support \ selected, MvPolynomial.monomial n (p.coeff n) := by
  classical
  ext n
  by_cases hs : n ∈ selected
  · simp [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, hs]
  · by_cases hp : n ∈ p.support
    · simp [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, hs, hp]
    · have hc := MvPolynomial.notMem_support_iff.mp hp
      simp [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, hs, hp, hc]

theorem polynomial_coefficient_split_principal {K J : Type*} [Fintype J]
    (p : MvPolynomial K ℝ) (principal : J → K →₀ ℕ)
    (hinj : Function.Injective principal) (hzero : ∀ j, principal j ≠ 0) :
    p = MvPolynomial.C (p.coeff 0) +
      (∑ j, MvPolynomial.monomial (principal j) (p.coeff (principal j))) +
      ∑ n ∈ nonprincipalSupport p principal, MvPolynomial.monomial n (p.coeff n) := by
  classical
  have hnot : (0 : K →₀ ℕ) ∉ Finset.univ.image principal := by
    simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    exact hzero
  have he := polynomial_coefficient_split p (insert 0 (Finset.univ.image principal))
  rw [Finset.sum_insert hnot, Finset.sum_image (fun i _ j _ hij => hinj hij)] at he
  exact he

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.FixedSupportRawArray
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem monomialArrayPolynomial_support_subset {J K : Type*} [Fintype J]
    (e : J → K →₀ ℕ) (a : J → ℝ) :
    ∀ ⦃m⦄, m ∈ (monomialArrayPolynomial e a).support → m ∈ Set.range e := by
  intro m hm
  by_contra hn
  have hz := monomialArrayPolynomial_coeff_zero_of_not_mem e a m
    (fun j hj => hn ⟨j, hj⟩)
  exact (MvPolynomial.mem_support_iff.mp hm) hz

theorem polynomial_coefficient_split_principal_on {K J : Type*} [Fintype J]
    (p : MvPolynomial K ℝ) (S : Finset (K →₀ ℕ)) (hS : p.support ⊆ S)
    (principal : J → K →₀ ℕ) (hinj : Function.Injective principal) (hzero : ∀ j, principal j ≠ 0) :
    p = MvPolynomial.C (p.coeff 0) +
      (∑ j, MvPolynomial.monomial (principal j) (p.coeff (principal j))) +
      ∑ n ∈ fixedNonprincipalExponents S principal, MvPolynomial.monomial n (p.coeff n) := by
  classical
  unfold fixedNonprincipalExponents
  have hsub : nonprincipalSupport p principal ⊆ S \ insert 0 (Finset.univ.image principal) :=
    Finset.sdiff_subset_sdiff hS (Finset.Subset.refl _)
  have hsum : (∑ n ∈ nonprincipalSupport p principal, MvPolynomial.monomial n (p.coeff n)) =
      ∑ n ∈ S \ insert 0 (Finset.univ.image principal), MvPolynomial.monomial n (p.coeff n) := by
    apply Finset.sum_subset hsub
    intro n hn hnot
    have hns : n ∉ p.support := by
      intro hp
      exact hnot (Finset.mem_sdiff.mpr ⟨hp, (Finset.mem_sdiff.mp hn).2⟩)
    simp only [MvPolynomial.notMem_support_iff.mp hns, map_zero]
  rw [← hsum]
  exact polynomial_coefficient_split_principal p principal hinj hzero

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialPerturbationScaleBudget
namespace OAI

section

namespace Erdos3

theorem polynomialPerturbationScale_spec {K M Q τ : ℝ}
    (hK : 0 ≤ K) (hM : 0 ≤ M) (hQ : 0 ≤ Q) (hτ : 0 < τ) (m : ℕ) :
    let t := polynomialPerturbationScale K M Q τ m
    0 < t ∧ t ≤ 1 ∧ K * (t * M) ≤ 1 / 2 ∧ t * M ≤ 1 ∧
      4 * (m : ℝ) * Real.sqrt (Q * (t * (1 + M))) ≤ τ := by
  let t := polynomialPerturbationScale K M Q τ m
  have ht : 0 < t := by dsimp [t, polynomialPerturbationScale]; positivity
  have ht1 : t ≤ 1 := min_le_left _ _
  have htK : t ≤ 1 / (2 * (1 + K) * (1 + M)) :=
    (min_le_right _ _).trans (min_le_left _ _)
  have htQ : t ≤ τ ^ 2 / (16 * ((m : ℝ) + 1) ^ 2 * (1 + Q) * (1 + M)) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hden : t * (2 * (1 + K) * (1 + M)) ≤ 1 :=
    (le_div_iff₀ (by positivity)).mp htK
  have h2KM : 2 * K * M ≤ 2 * (1 + K) * (1 + M) := by nlinarith
  have hMden : M ≤ 2 * (1 + K) * (1 + M) := by nlinarith [mul_nonneg hK hM]
  have hsmall : K * (t * M) ≤ 1 / 2 := by
    have hh := (mul_le_mul_of_nonneg_left h2KM ht.le).trans hden
    nlinarith
  have hsecond : t * M ≤ 1 := (mul_le_mul_of_nonneg_left hMden ht.le).trans hden
  refine ⟨ht, ht1, hsmall, hsecond, ?_⟩
  have hdenQ : t * (16 * ((m : ℝ) + 1) ^ 2 * (1 + Q) * (1 + M)) ≤ τ ^ 2 :=
    (le_div_iff₀ (by positivity)).mp htQ
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hm2 : (m : ℝ) ^ 2 ≤ ((m : ℝ) + 1) ^ 2 := by nlinarith
  have hpoly : 16 * (m : ℝ) ^ 2 * Q * (1 + M) ≤
      16 * ((m : ℝ) + 1) ^ 2 * (1 + Q) * (1 + M) := by
    gcongr
    linarith
  have hb := (mul_le_mul_of_nonneg_left hpoly ht.le).trans hdenQ
  have hroot := Real.sq_sqrt (show 0 ≤ Q * (t * (1 + M)) by positivity)
  have hroot0 := Real.sqrt_nonneg (Q * (t * (1 + M)))
  have hsquare : (4 * (m : ℝ) * Real.sqrt (Q * (t * (1 + M)))) ^ 2 ≤ τ ^ 2 := by
    calc
      _ = t * (16 * (m : ℝ) ^ 2 * Q * (1 + M)) := by
        rw [mul_pow, mul_pow, hroot]
        ring
      _ ≤ _ := hb
  nlinarith [mul_nonneg (show 0 ≤ 4 * (m : ℝ) by positivity) hroot0]

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SlicedPrincipalInverse
namespace OAI

section

namespace Erdos3

open scoped BigOperators ContDiff NNReal

variable {B F : Type*} [Fintype B] [Fintype F] [DecidableEq B] [DecidableEq F]

omit [DecidableEq B] [DecidableEq F] in
theorem principalSliceValue_contDiff (c : B → ℝ) (lower width : B × F → ℝ) :
    ContDiff ℝ ∞ (principalSliceValue c lower width) := by
  unfold principalSliceValue
  fun_prop

theorem principalSliceValue_fderiv_single (c : B → ℝ) (lower width : B × F → ℝ)
    (x : B × F → ℝ) (b : B) (i : F) :
    fderiv ℝ (principalSliceValue c lower width) x (Pi.single (b, i) 1) =
      principalSliceSlope c lower width x b i := by
  let g := fun b j (y : B × F → ℝ) => lower (b, j) + width (b, j) * y (b, j)
  have hd (b : B) (j : F) : HasFDerivAt (g b j)
      (width (b, j) • (ContinuousLinearMap.proj (b, j) : (B × F → ℝ) →L[ℝ] ℝ)) x := by
    have he : HasFDerivAt (fun y : B × F → ℝ => y (b, j))
        (ContinuousLinearMap.proj (b, j) : (B × F → ℝ) →L[ℝ] ℝ) x :=
      hasFDerivAt_apply (b, j) x
    simpa only [g] using (he.const_mul (width (b, j))).const_add (lower (b, j))
  have hp (b : B) := HasFDerivAt.finsetProd (u := Finset.univ) (fun j _ => hd b j)
  have hs := HasFDerivAt.fun_sum (u := Finset.univ) (fun b _ => (hp b).const_mul (c b))
  change fderiv ℝ (fun y => ∑ b, c b * ∏ j, g b j y) x (Pi.single (b, i) 1) = _
  rw [hs.fderiv]
  simp only [sum_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  rw [Finset.sum_eq_single b]
  · rw [Finset.sum_eq_single i]
    · simp only [Pi.single_eq_same, mul_one, principalSliceSlope, g]
      ring
    · intro j _ hji
      simp [hji]
    · simp
  · intro b' _ hbb
    simp [hbb]
  · simp

omit [Fintype B] [DecidableEq B] in
theorem principalSliceSlope_lower (c : B → ℝ) (lower width : B × F → ℝ)
    (x : B × F → ℝ) (b : B) (i : F) {a δ r : ℝ}
    (ha : 0 ≤ a) (hδ : 0 ≤ δ) (hr : 0 ≤ r) (hc : a ≤ |c b|)
    (hw : ∀ j, δ ≤ width (b, j))
    (hlower : ∀ j ≠ i, 0 ≤ lower (b, j)) (hx : ∀ j ≠ i, r ≤ x (b, j)) :
    a * δ * (δ * r) ^ (Fintype.card F - 1) ≤ |principalSliceSlope c lower width x b i| := by
  have hfactor (j) (hj : j ∈ Finset.univ.erase i) :
      δ * r ≤ lower (b, j) + width (b, j) * x (b, j) := by
    have hji := Finset.ne_of_mem_erase hj
    exact (mul_le_mul (hw j) (hx j hji) hr (hδ.trans (hw j))).trans
      (le_add_of_nonneg_left (hlower j hji))
  have hprod : (δ * r) ^ (Fintype.card F - 1) ≤
      ∏ j ∈ Finset.univ.erase i, (lower (b, j) + width (b, j) * x (b, j)) := by
    have h := Finset.prod_le_prod (s := Finset.univ.erase i)
      (fun _ _ => mul_nonneg hδ hr) hfactor
    simpa only [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i),
      Finset.card_univ] using h
  have hp0 := (pow_nonneg (mul_nonneg hδ hr) (Fintype.card F - 1)).trans hprod
  rw [principalSliceSlope, abs_mul, abs_mul, abs_of_nonneg (hδ.trans (hw i)),
    abs_of_nonneg hp0]
  exact mul_le_mul (mul_le_mul hc (hw i) hδ (ha.trans hc)) hprod
    (pow_nonneg (mul_nonneg hδ hr) _) (mul_nonneg (abs_nonneg _) (hδ.trans (hw i)))

end Erdos3

end

section

namespace Erdos3

open scoped NNReal ContDiff BigOperators

theorem scalar_identity_inverse_abs_bound {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {a : ℝ} (ha : a ≠ 0) :
    (a • ContinuousLinearMap.id ℝ E).IsInvertible ∧
      ‖(a • ContinuousLinearMap.id ℝ E).inverse‖ ≤ |a|⁻¹ := by
  let A := a • ContinuousLinearMap.id ℝ E
  let B := a⁻¹ • ContinuousLinearMap.id ℝ E
  have hAB : A.comp B = ContinuousLinearMap.id ℝ E := by
    ext x
    simp [A, B, smul_smul, ha]
  have hBA : B.comp A = ContinuousLinearMap.id ℝ E := by
    ext x
    simp [A, B, smul_smul, ha]
  refine ⟨ContinuousLinearMap.IsInvertible.of_inverse hAB hBA, ?_⟩
  change ‖A.inverse‖ ≤ _
  rw [ContinuousLinearMap.inverse_eq hAB hBA]
  calc
    ‖B‖ = |a|⁻¹ * ‖ContinuousLinearMap.id ℝ E‖ := by
      simp only [B, norm_smul, Real.norm_eq_abs, abs_inv]
    _ ≤ |a|⁻¹ := mul_le_of_le_one_right (inv_nonneg.mpr (abs_nonneg _))
      ContinuousLinearMap.norm_id_le

variable {B F : Type*} [Fintype B] [Fintype F] [DecidableEq B] [DecidableEq F]

omit [DecidableEq B] [DecidableEq F] in
theorem principalSliceSingleton_contDiff (c : B → ℝ) (lower width : B × F → ℝ) :
    ContDiff ℝ ∞ (principalSliceSingleton c lower width) :=
  contDiff_pi.mpr (fun _ => principalSliceValue_contDiff c lower width)

theorem principalSliceSingleton_selectedDerivative (c : B → ℝ) (lower width : B × F → ℝ)
    (x : B × F → ℝ) (b : B) (i : F) :
    selectedDerivative (principalSliceSingleton c lower width)
      (coordinateInjection (fun _ : Unit => (b, i))) x =
      principalSliceSlope c lower width x b i • ContinuousLinearMap.id ℝ (Unit → ℝ) := by
  have hd := (principalSliceSingleton_contDiff c lower width).differentiable (by norm_num)
  have hh := principalSliceValue_fderiv_single c lower width x b i
  change fderiv ℝ (fun y => principalSliceSingleton c lower width y ()) x
    (Pi.single (b, i) 1) = _ at hh
  rw [fderiv_apply (hd x) ()] at hh
  change (fderiv ℝ (principalSliceSingleton c lower width) x (Pi.single (b, i) 1)) () =
    principalSliceSlope c lower width x b i at hh
  ext y u
  cases u
  have hJ : coordinateInjection (fun _ : Unit => (b, i)) y =
      y () • (Pi.single (b, i) 1 : B × F → ℝ) := by
    simp only [coordinateInjection_apply, Fintype.sum_unique, ← Pi.single_smul, smul_eq_mul, mul_one]
  simp only [selectedDerivative, ContinuousLinearMap.comp_apply, hJ, map_smul,
    smul_apply, Pi.smul_apply, smul_eq_mul, ContinuousLinearMap.id_apply, hh]
  ring

theorem principalSliceSingleton_inverse_bound (c : B → ℝ) (lower width : B × F → ℝ)
    (x : B × F → ℝ) (b : B) (i : F) {κ : ℝ} (hκ : 0 < κ)
    (hbound : κ ≤ |principalSliceSlope c lower width x b i|) :
    (selectedDerivative (principalSliceSingleton c lower width)
      (coordinateInjection (fun _ : Unit => (b, i))) x).IsInvertible ∧
      ‖(selectedDerivative (principalSliceSingleton c lower width)
        (coordinateInjection (fun _ : Unit => (b, i))) x).inverse‖ ≤ κ⁻¹ := by
  rw [principalSliceSingleton_selectedDerivative]
  have h := scalar_identity_inverse_abs_bound
    (E := Unit → ℝ) (abs_pos.mp (hκ.trans_le hbound))
  exact ⟨h.1, h.2.trans (inv_anti₀ hκ hbound)⟩

section Joint

variable {D : Type*} [Fintype D]
variable {B F : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (F d)]
variable [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (F d)]

theorem jointSlicedInjection_norm_le (b : ∀ d, B d) (i : ∀ d, F d) :
    ‖jointSlicedInjection b i‖ ≤ 1 :=
  sigmaAxisOperator_norm_le _ zero_le_one
    (fun _ => coordinateInjection_norm_le _ (Function.injective_of_subsingleton _))

omit [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (F d)] in
theorem jointSlicedPrincipal_contDiff (c : ∀ d, B d → ℝ)
    (lower width : ∀ d, B d × F d → ℝ) :
    ContDiff ℝ ∞ (jointSlicedPrincipal c lower width) :=
  sigmaAxisSampler_contDiff _ (fun d => principalSliceSingleton_contDiff (c d) (lower d) (width d))

theorem jointSlicedPrincipal_inverse_bound (c : ∀ d, B d → ℝ)
    (lower width : ∀ d, B d × F d → ℝ) (b : ∀ d, B d) (i : ∀ d, F d)
    (x : (Σ d, B d × F d) → ℝ) {κ : ℝ} (hκ : 0 < κ)
    (hbound : ∀ d, κ ≤ |principalSliceSlope (c d) (lower d) (width d)
      (sigmaAxisProjection (fun d => B d × F d) d x) (b d) (i d)|) :
    (selectedDerivative (jointSlicedPrincipal c lower width) (jointSlicedInjection b i) x).IsInvertible ∧
      ‖(selectedDerivative (jointSlicedPrincipal c lower width) (jointSlicedInjection b i) x).inverse‖ ≤ κ⁻¹ := by
  have hi (d) := principalSliceSingleton_inverse_bound (c d) (lower d) (width d)
    (sigmaAxisProjection (fun d => B d × F d) d x) (b d) (i d) hκ (hbound d)
  exact sigmaAxisSampler_inverse_bound _ _ x
    (fun d => (principalSliceSingleton_contDiff (c d) (lower d) (width d)).differentiable
      (by norm_num) _) (fun d => (hi d).1) (inv_nonneg.mpr hκ.le) (fun d => (hi d).2)

end Joint

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.SlicedPrincipalPolynomial
namespace OAI

section

namespace Erdos3

open scoped BigOperators ContDiff

variable {B F : Type*} [Fintype B] [Fintype F]

theorem principalSlicePolynomial_eval [DecidableEq B] [DecidableEq F]
    (c : B → ℝ) (lower width : B × F → ℝ) (x : B × F → ℝ) :
    MvPolynomial.eval x (principalSlicePolynomial c lower width) = principalSliceValue c lower width x := by
  simp [principalSlicePolynomial, principalSliceValue]

theorem principalSlicePolynomial_degree (c : B → ℝ) (lower width : B × F → ℝ) :
    (principalSlicePolynomial c lower width).totalDegree ≤ Fintype.card F := by
  classical
  apply MvPolynomial.totalDegree_finsetSum_le
  intro b _
  apply (MvPolynomial.totalDegree_mul _ _).trans
  simp only [MvPolynomial.totalDegree_C, zero_add]
  apply (MvPolynomial.totalDegree_finsetProd _ _).trans
  calc
    _ ≤ ∑ _i : F, 1 := Finset.sum_le_sum (fun i _ => by
      apply (MvPolynomial.totalDegree_add _ _).trans
      apply max_le (by simp)
      exact (MvPolynomial.totalDegree_mul _ _).trans (by simp))
    _ = _ := by simp

theorem principalSlicePolynomial_mass (c : B → ℝ) (lower width : B × F → ℝ)
    (hwidth : ∀ p, |lower p| + |width p| ≤ 1) :
    realPolynomialMass (principalSlicePolynomial c lower width) ≤ ∑ b, |c b| := by
  classical
  apply (realPolynomialMass_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro b _
  apply (realPolynomialMass_C_mul_le _ _).trans
  apply mul_le_of_le_one_right (abs_nonneg _)
  apply (realPolynomialMass_prod_le _ _).trans
  apply Finset.prod_le_one (fun _ _ => realPolynomialMass_nonneg _)
  intro i _
  apply (realPolynomialMass_add_le _ _).trans
  calc
    _ ≤ |lower (b, i)| + |width (b, i)| := by
      rw [realPolynomialMass_C]
      apply add_le_add le_rfl
      simpa only [realPolynomialMass_X, mul_one] using
        realPolynomialMass_C_mul_le (width (b, i)) (MvPolynomial.X (b, i))
    _ ≤ 1 := hwidth (b, i)

section Joint

variable {D : Type*} [Fintype D] {B F : D → Type*}
variable [∀ d, Fintype (B d)] [∀ d, Fintype (F d)]
variable [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (F d)]

omit [Fintype D] in
theorem jointSlicedPolynomial_map (c : ∀ d, B d → ℝ)
    (lower width : ∀ d, B d × F d → ℝ) :
    polynomialVectorMap (jointSlicedPolynomial c lower width) = jointSlicedPrincipal c lower width := by
  funext x o
  change MvPolynomial.eval x (MvPolynomial.rename _ _) = _
  rw [MvPolynomial.eval_rename, principalSlicePolynomial_eval]
  rfl

theorem jointSlicedPrincipal_c2_bounds (c : ∀ d, B d → ℝ)
    (lower width : ∀ d, B d × F d → ℝ) {m : ℕ}
    (hdegree : ∀ d, Fintype.card (F d) ≤ m)
    (hwidth : ∀ d p, |lower d p| + |width d p| ≤ 1)
    {C : ℝ} (hC : 0 ≤ C) (hc : ∀ d, (∑ b, |c d b|) ≤ C)
    (x : (Σ d, B d × F d) → ℝ) (hx : ∀ p, |x p| ≤ 1) :
    let N := Fintype.card (Σ d, B d × F d)
    ‖jointSlicedPrincipal c lower width x‖ ≤ C ∧
      ‖fderiv ℝ (jointSlicedPrincipal c lower width) x‖ ≤ N * ((m : ℝ) * C) ∧
      ‖fderiv ℝ (fderiv ℝ (jointSlicedPrincipal c lower width)) x‖ ≤
        N * (N * ((m : ℝ) * ((m : ℝ) * C))) := by
  classical
  have hd (o : Σ _d : D, Unit) (p : Σ d, B d × F d) :
      (jointSlicedPolynomial c lower width o).degreeOf p ≤ m :=
    (MvPolynomial.degreeOf_le_totalDegree _ _).trans
      ((MvPolynomial.totalDegree_rename_le _ _).trans
        ((principalSlicePolynomial_degree _ _ _).trans (hdegree o.1)))
  have hm (o : Σ _d : D, Unit) : realPolynomialMass (jointSlicedPolynomial c lower width o) ≤ C :=
    (realPolynomialMass_rename_le _ _).trans
      ((principalSlicePolynomial_mass _ _ _ (hwidth o.1)).trans (hc o.1))
  have h := polynomialVectorMap_mass_c2_bounds (jointSlicedPolynomial c lower width) hd hC hm x hx
  rwa [jointSlicedPolynomial_map] at h

end Joint

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.JointBooleanStability
namespace OAI

section

namespace Erdos3

variable {I O : Type*} [Fintype I] [Fintype O]

theorem selectedDerivative_fderiv_eq (U : (I → ℝ) → (O → ℝ))
    (J : (O → ℝ) →L[ℝ] (I → ℝ)) (x : I → ℝ)
    (hU : DifferentiableAt ℝ (fderiv ℝ U) x) :
    fderiv ℝ (selectedDerivative U J) x =
      (operatorPrecompose J).comp (fderiv ℝ (fderiv ℝ U) x) := by
  let L : ((I → ℝ) →L[ℝ] (O → ℝ)) →L[ℝ] ((O → ℝ) →L[ℝ] (O → ℝ)) := operatorPrecompose J
  change fderiv ℝ (L ∘ fderiv ℝ U) x = _
  rw [fderiv_comp x L.differentiableAt hU, L.fderiv]

theorem selectedDerivative_second_error (U V : (I → ℝ) → (O → ℝ))
    (hU : ContDiff ℝ 2 U) (hV : ContDiff ℝ 2 V)
    (J : (O → ℝ) →L[ℝ] (I → ℝ)) (hJ : ‖J‖ ≤ 1) (x : I → ℝ) :
    ‖fderiv ℝ (selectedDerivative V J) x - fderiv ℝ (selectedDerivative U J) x‖ ≤
      ‖fderiv ℝ (fderiv ℝ V) x - fderiv ℝ (fderiv ℝ U) x‖ := by
  have hU' : ContDiff ℝ 1 (fderiv ℝ U) := hU.fderiv_right (by norm_num)
  have hV' : ContDiff ℝ 1 (fderiv ℝ V) := hV.fderiv_right (by norm_num)
  rw [selectedDerivative_fderiv_eq V J x (hV'.differentiable one_ne_zero x),
    selectedDerivative_fderiv_eq U J x (hU'.differentiable one_ne_zero x),
    ← ContinuousLinearMap.comp_sub]
  have hL : ‖operatorPrecompose (Y := O → ℝ) J‖ ≤ 1 := (operatorPrecompose_norm_le J).trans hJ
  calc
    _ ≤ ‖operatorPrecompose J‖ * ‖fderiv ℝ (fderiv ℝ V) x - fderiv ℝ (fderiv ℝ U) x‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * ‖fderiv ℝ (fderiv ℝ V) x - fderiv ℝ (fderiv ℝ U) x‖ :=
      mul_le_mul_of_nonneg_right hL
        (norm_nonneg (fderiv ℝ (fderiv ℝ V) x - fderiv ℝ (fderiv ℝ U) x))
    _ = _ := one_mul _

theorem selectedDerivative_bound_of_second_error (U V : (I → ℝ) → (O → ℝ))
    (hU : ContDiff ℝ 2 U) (hV : ContDiff ℝ 2 V)
    (J : (O → ℝ) →L[ℝ] (I → ℝ)) (hJ : ‖J‖ ≤ 1) (x : I → ℝ)
    {H E : ℝ} (hH : ‖fderiv ℝ (selectedDerivative U J) x‖ ≤ H)
    (hE : ‖fderiv ℝ (fderiv ℝ V) x - fderiv ℝ (fderiv ℝ U) x‖ ≤ E) :
    ‖fderiv ℝ (selectedDerivative V J) x‖ ≤ H + E := by
  have ht := norm_add_le (fderiv ℝ (selectedDerivative V J) x - fderiv ℝ (selectedDerivative U J) x)
    (fderiv ℝ (selectedDerivative U J) x)
  have he : fderiv ℝ (selectedDerivative V J) x - fderiv ℝ (selectedDerivative U J) x +
      fderiv ℝ (selectedDerivative U J) x = fderiv ℝ (selectedDerivative V J) x := by
    ext y z i
    simp
  rw [he] at ht
  exact ht.trans ((add_le_add ((selectedDerivative_second_error U V hU hV J hJ x).trans hE) hH).trans_eq
    (add_comm E H))

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
open scoped BigOperators ContDiff NNReal

theorem slicedPrincipalComparisonBudget_nonneg (N m : ℕ) {C A r κ : ℝ}
    (hC : 0 ≤ C) (hA : 0 ≤ A) (hr : 0 < r) (hκ : 0 < κ) :
    0 ≤ slicedPrincipalComparisonBudget N m C A r κ := by
  unfold slicedPrincipalComparisonBudget
  positivity

theorem jointSlicedPrincipal_unitBox_comparison
    {D : Type*} [Fintype D] {B F : D → Type*}
    [∀ d, Fintype (B d)] [∀ d, Fintype (F d)]
    [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (F d)]
    (c : ∀ d, B d → ℝ) (lower width : ∀ d, B d × F d → ℝ)
    (b : ∀ d, B d) (i : ∀ d, F d) {m : ℕ}
    (hdegree : ∀ d, Fintype.card (F d) ≤ m)
    (hwidth : ∀ d p, |lower d p| + |width d p| ≤ 1)
    {C a δ r κ ε : ℝ} (hC : 0 ≤ C) (hc : ∀ d, (∑ b, |c d b|) ≤ C)
    (ha : 0 < a) (hδ : 0 < δ) (hr : 0 < r) (hκ : 0 < κ)
    (hprincipal : ∀ d, a ≤ |c d (b d)|)
    (hselectedWidth : ∀ d j, δ ≤ width d (b d, j))
    (hselectedLower : ∀ d j, j ≠ i d → 0 ≤ lower d (b d, j))
    (hminor : ∀ d, κ ≤ a * δ * (δ * r) ^ (Fintype.card (F d) - 1))
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition)
    (V : ((Σ d, B d × F d) → ℝ) → ((Σ _d : D, Unit) → ℝ))
    (hV : ContDiff ℝ 2 V) (hε : 0 < ε) (hεone : ε ≤ 1) (hsmall : κ⁻¹ * ε ≤ 1 / 2)
    (herr : ∀ x, (∀ p, |x p| ≤ 1) →
      ‖V x - jointSlicedPrincipal c lower width x‖ ≤ ε ∧
      ‖fderiv ℝ V x - fderiv ℝ (jointSlicedPrincipal c lower width) x‖ ≤ ε ∧
      ‖fderiv ℝ (fderiv ℝ V) x - fderiv ℝ (fderiv ℝ (jointSlicedPrincipal c lower width)) x‖ ≤ ε)
    (φ : ((Σ _d : D, Unit) → ℝ) → ℝ) (hφ : Measurable φ) (hφone : ∀ y, ‖φ y‖ ≤ 1) :
    let N := Fintype.card (Σ d, B d × F d)
    |mappedTest (unitBoxMeasure (Σ d, B d × F d)) (jointSlicedPrincipal c lower width) φ -
      mappedTest (unitBoxMeasure (Σ d, B d × F d)) V φ| ≤
      8 * N * r + 4 * (Fintype.card D : ℝ) *
        Real.sqrt (slicedPrincipalComparisonBudget N m C A r κ * ε) := by
  classical
  let N := Fintype.card (Σ d, B d × F d)
  let U := jointSlicedPrincipal c lower width
  let J := jointSlicedInjection b i
  let w := unitBoxInteriorCutoff (ι := Σ d, B d × F d) r
  let H₀ : ℝ := N * (N * ((m : ℝ) * ((m : ℝ) * C)))
  let K : ℝ≥0 := ⟨κ⁻¹, inv_nonneg.mpr hκ.le⟩
  let H : ℝ≥0 := ⟨H₀ + 1, by dsimp [H₀]; positivity⟩
  let S : ℝ≥0 := ⟨2 * (N : ℝ) ^ 2 * A / r, by positivity⟩
  have hU : ContDiff ℝ 2 U := (jointSlicedPrincipal_contDiff c lower width).of_le (WithTop.coe_le_coe.2 le_top)
  have hJ : ‖J‖ ≤ 1 := jointSlicedInjection_norm_le b i
  have hbox (x) (hx : x ∈ tsupport w) : ∀ p, |x p| ≤ 1 := by
    intro p
    have hp := unitBoxInteriorCutoff_tsupport hr hx p
    rw [abs_of_nonneg (hr.le.trans hp.1)]
    linarith
  have hinv (x) (hx : x ∈ tsupport w) :
      (selectedDerivative U J x).IsInvertible ∧ ‖(selectedDerivative U J x).inverse‖ ≤ K := by
    apply jointSlicedPrincipal_inverse_bound c lower width b i x hκ
    intro d
    apply (hminor d).trans
    apply principalSliceSlope_lower (c d) (lower d) (width d) _ (b d) (i d)
      ha.le hδ.le hr.le (hprincipal d) (hselectedWidth d) (hselectedLower d)
    intro j _
    exact (unitBoxInteriorCutoff_tsupport hr hx ⟨d, b d, j⟩).1
  have hHU₀ (x) (hx : x ∈ tsupport w) : ‖fderiv ℝ (selectedDerivative U J) x‖ ≤ H₀ := by
    have hsecond := (jointSlicedPrincipal_c2_bounds c lower width hdegree hwidth hC hc x (hbox x hx)).2.2
    have hUd : DifferentiableAt ℝ (fderiv ℝ U) x :=
      (hU.fderiv_right (by norm_num : 1 + 1 ≤ (2 : WithTop ℕ∞))).differentiable one_ne_zero x
    rw [selectedDerivative_fderiv_eq U J x hUd]
    have hnonneg : 0 ≤ ‖fderiv ℝ (fderiv ℝ U) x‖ := ContinuousLinearMap.opNorm_nonneg _
    calc
      _ ≤ ‖operatorPrecompose J‖ * ‖fderiv ℝ (fderiv ℝ U) x‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * ‖fderiv ℝ (fderiv ℝ U) x‖ :=
        mul_le_mul_of_nonneg_right ((operatorPrecompose_norm_le J).trans hJ) hnonneg
      _ ≤ H₀ := by simpa only [one_mul] using hsecond
  have hHU (x) (hx : x ∈ tsupport w) : ‖fderiv ℝ (selectedDerivative U J) x‖ ≤ H :=
    (hHU₀ x hx).trans (by change H₀ ≤ H₀ + 1; linarith)
  have hHV (x) (hx : x ∈ tsupport w) : ‖fderiv ℝ (selectedDerivative V J) x‖ ≤ H :=
    (selectedDerivative_bound_of_second_error U V hU hV J hJ x (hHU₀ x hx)
      (herr x (hbox x hx)).2.2).trans (add_le_add le_rfl hεone)
  have h := selected_cutoff_comparison_of_close_derivatives
    (unitBoxMeasure (Σ d, B d × F d)) w w
    (unitBoxInteriorCutoff_contDiff r).continuous.measurable (unitBoxInteriorCutoff_range r)
    ((unitBoxInteriorCutoff_contDiff r).of_le (by norm_num))
    (unitBoxInteriorCutoff_compact hr) (fun x => (unitBoxInteriorCutoff_range r x).1)
    (unitBoxInteriorCutoff_density hr) U V hU hV J hJ K H S
    (fun x hx => (hinv x hx).1) (fun x hx => (hinv x hx).2)
    (fun x hx => (mul_le_mul_of_nonneg_left (herr x (hbox x hx)).2.1 K.coe_nonneg).trans hsmall)
    hHU hHV (unitBoxInteriorCutoff_derivative_budget A hA hr) hε
    (unitBoxInteriorCutoff_mass hr)
    (fun x hx => by
      rw [dist_comm, dist_eq_norm]
      exact (herr x (hbox x (subset_tsupport w hx))).1) φ hφ hφone
  change |mappedTest (unitBoxMeasure (Σ d, B d × F d)) U φ -
      mappedTest (unitBoxMeasure (Σ d, B d × F d)) V φ| ≤
    2 * (4 * (N : ℝ) * r) + 4 * (Fintype.card (Σ _d : D, Unit) : ℝ) *
      Real.sqrt (slicedPrincipalComparisonBudget N m C A r κ * ε) at h
  have hcard : Fintype.card (Σ _d : D, Unit) = Fintype.card D := by simp
  rw [hcard] at h
  exact h.trans_eq (by ring)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators ContDiff NNReal

theorem slicedPrincipalBoundaryRadius_spec (N : ℕ) {η : ℝ} (hη : 0 < η) :
    let r := slicedPrincipalBoundaryRadius N η
    0 < r ∧ r ≤ 1 / 4 ∧ 8 * N * r ≤ η / 2 := by
  let r := slicedPrincipalBoundaryRadius N η
  have hr : 0 < r := by dsimp [r, slicedPrincipalBoundaryRadius]; positivity
  have hr1 : r ≤ 1 / 4 := min_le_left _ _
  have he : r ≤ η / (16 * ((N : ℝ) + 1)) := min_le_right _ _
  have hh := (le_div_iff₀ (by positivity : 0 < 16 * ((N : ℝ) + 1))).mp he
  refine ⟨hr, hr1, ?_⟩
  nlinarith [Nat.cast_nonneg (α := ℝ) N]

theorem slicedPrincipalC2Tolerance_spec
    {D : Type*} [Fintype D] {B F : D → Type*}
    [∀ d, Fintype (B d)] [∀ d, Fintype (F d)]
    [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (F d)]
    {m : ℕ} (hdegree : ∀ d, Fintype.card (F d) ≤ m)
    {C a δ η : ℝ} (hC : 0 ≤ C) (ha : 0 < a) (hδ : 0 < δ) (hδone : δ ≤ 1) (hη : 0 < η)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) :
    let t := slicedPrincipalC2Tolerance (Fintype.card (Σ d, B d × F d)) (Fintype.card D) m C a δ A η
    0 < t ∧ t ≤ 1 ∧
    ∀ (c : ∀ d, B d → ℝ) (lower width : ∀ d, B d × F d → ℝ)
      (b : ∀ d, B d) (i : ∀ d, F d),
      (∀ d p, |lower d p| + |width d p| ≤ 1) →
      (∀ d, (∑ b, |c d b|) ≤ C) → (∀ d, a ≤ |c d (b d)|) →
      (∀ d j, δ ≤ width d (b d, j)) →
      (∀ d j, j ≠ i d → 0 ≤ lower d (b d, j)) →
      ∀ V : ((Σ d, B d × F d) → ℝ) → ((Σ _d : D, Unit) → ℝ),
      ContDiff ℝ 2 V →
      (∀ x, (∀ p, |x p| ≤ 1) →
        ‖V x - jointSlicedPrincipal c lower width x‖ ≤ t ∧
        ‖fderiv ℝ V x - fderiv ℝ (jointSlicedPrincipal c lower width) x‖ ≤ t ∧
        ‖fderiv ℝ (fderiv ℝ V) x - fderiv ℝ (fderiv ℝ (jointSlicedPrincipal c lower width)) x‖ ≤ t) →
      ∀ φ : ((Σ _d : D, Unit) → ℝ) → ℝ, Measurable φ → (∀ y, ‖φ y‖ ≤ 1) →
        |mappedTest (unitBoxMeasure (Σ d, B d × F d)) (jointSlicedPrincipal c lower width) φ -
          mappedTest (unitBoxMeasure (Σ d, B d × F d)) V φ| ≤ η := by
  let N := Fintype.card (Σ d, B d × F d)
  let r := slicedPrincipalBoundaryRadius N η
  have hr := slicedPrincipalBoundaryRadius_spec N hη
  let κ := a * δ * (δ * r) ^ m
  have hκ : 0 < κ := mul_pos (mul_pos ha hδ) (pow_pos (mul_pos hδ hr.1) _)
  have hdr : δ * r ≤ 1 := by
    calc
      _ ≤ 1 * 1 := mul_le_mul hδone (hr.2.1.trans (by norm_num)) hr.1.le zero_le_one
      _ = 1 := one_mul _
  let Q := slicedPrincipalComparisonBudget N m C A r κ
  have hQ : 0 ≤ Q := slicedPrincipalComparisonBudget_nonneg N m hC A.coe_nonneg hr.1 hκ
  let t := slicedPrincipalC2Tolerance N (Fintype.card D) m C a δ A η
  have ht := polynomialPerturbationScale_spec (inv_nonneg.mpr hκ.le) zero_le_one hQ
    (half_pos hη) (Fintype.card D)
  change 0 < t ∧ t ≤ 1 ∧ κ⁻¹ * (t * 1) ≤ 1 / 2 ∧ t * 1 ≤ 1 ∧
    4 * (Fintype.card D : ℝ) * Real.sqrt (Q * (t * (1 + 1))) ≤ η / 2 at ht
  refine ⟨ht.1, ht.2.1, ?_⟩
  intro c lower width b i hwidth hc hprincipal hw hlower V hV herr φ hφ hφone
  have hminor (d) : κ ≤ a * δ * (δ * r) ^ (Fintype.card (F d) - 1) :=
    mul_le_mul_of_nonneg_left
      (pow_le_pow_of_le_one (mul_pos hδ hr.1).le hdr ((Nat.sub_le _ _).trans (hdegree d)))
      (mul_pos ha hδ).le
  have h := jointSlicedPrincipal_unitBox_comparison c lower width b i hdegree hwidth hC hc
    ha hδ hr.1 hκ hprincipal hw hlower hminor A hA V hV ht.1 ht.2.1
    (by simpa only [mul_one] using ht.2.2.1) herr φ hφ hφone
  have hsqrt : 4 * (Fintype.card D : ℝ) * Real.sqrt (Q * t) ≤ η / 2 := by
    apply le_trans _ ht.2.2.2.2
    apply mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (by positivity)
    exact mul_le_mul_of_nonneg_left (by nlinarith [ht.1] : t ≤ t * (1 + 1)) hQ
  exact h.trans (by change 8 * (N : ℝ) * r + 4 * (Fintype.card D : ℝ) * Real.sqrt (Q * t) ≤ η; linarith [hr.2.2])

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {B F : Type*} [Fintype B] [Fintype F]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff NNReal BigOperators

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff NNReal BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff NNReal BigOperators

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)] [∀ d, Nonempty (O d)]
  [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.SlicedPolynomialPerturbation
namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators ContDiff

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators ContDiff NNReal

theorem jointSlicedPrincipal_polynomial_tail_comparison
    {D : Type*} [Fintype D] {B F : D → Type*}
    [∀ j, Fintype (B j)] [∀ j, Fintype (F j)]
    [∀ j, DecidableEq (B j)] [∀ j, DecidableEq (F j)]
    (c : ∀ j, B j → ℝ) (lower width : ∀ j, B j × F j → ℝ)
    (b : ∀ j, B j) (i : ∀ j, F j)
    {m d : ℕ} (hdegree : ∀ j, Fintype.card (F j) ≤ m)
    {C M a δ η : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M)
    (ha : 0 < a) (hδ : 0 < δ) (hδone : δ ≤ 1) (hη : 0 < η)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition)
    (hwidth : ∀ j p, |lower j p| + |width j p| ≤ 1)
    (hc : ∀ j, (∑ b, |c j b|) ≤ C) (hprincipal : ∀ j, a ≤ |c j (b j)|)
    (hw : ∀ j l, δ ≤ width j (b j, l))
    (hlower : ∀ j l, l ≠ i j → 0 ≤ lower j (b j, l))
    (q : (Σ _j : D, Unit) → MvPolynomial (Σ j, B j × F j) ℝ)
    (hqdegree : ∀ o v, (q o).degreeOf v ≤ d) (hqmass : ∀ o, realPolynomialMass (q o) ≤ M)
    (t : ℝ)
    (ht : |t| * polynomialMassC2Budget (Fintype.card (Σ j, B j × F j)) d M ≤
      slicedPrincipalC2Tolerance (Fintype.card (Σ j, B j × F j)) (Fintype.card D) m C a δ A η)
    (shift : (Σ _j : D, Unit) → ℝ)
    (φ : ((Σ _j : D, Unit) → ℝ) → ℝ) (hφ : Measurable φ) (hφone : ∀ y, ‖φ y‖ ≤ 1) :
    |mappedTest (unitBoxMeasure (Σ j, B j × F j))
        (fun x => shift + jointSlicedPrincipal c lower width x) φ -
      mappedTest (unitBoxMeasure (Σ j, B j × F j))
        (fun x => shift + jointSlicedPrincipal c lower width x + t • polynomialVectorMap q x) φ| ≤ η := by
  classical
  let U := jointSlicedPrincipal c lower width
  let V := fun x => U x + t • polynomialVectorMap q x
  have hU : ContDiff ℝ 2 U := (jointSlicedPrincipal_contDiff c lower width).of_le (by first | exact WithTop.coe_le_coe.2 le_top | exact ENat.LEInfty.out | (norm_cast; done) | exact_mod_cast le_top)
  have hq : ContDiff ℝ 2 (polynomialVectorMap q) := (polynomialVectorMap_contDiff q).of_le (by first | exact WithTop.coe_le_coe.2 le_top | exact ENat.LEInfty.out | (norm_cast; done) | exact_mod_cast le_top)
  have hV : ContDiff ℝ 2 V := hU.add (hq.const_smul t)
  have hε := slicedPrincipalC2Tolerance_spec (B := B) (F := F) hdegree hC ha hδ hδone hη A hA
  have herr := hε.2.2 c lower width b i hwidth hc hprincipal hw hlower V hV
  have hclose : ∀ x, (∀ p, |x p| ≤ 1) →
      ‖V x - U x‖ ≤ slicedPrincipalC2Tolerance (Fintype.card (Σ j, B j × F j)) (Fintype.card D) m C a δ A η ∧
      ‖fderiv ℝ V x - fderiv ℝ U x‖ ≤ slicedPrincipalC2Tolerance (Fintype.card (Σ j, B j × F j)) (Fintype.card D) m C a δ A η ∧
      ‖fderiv ℝ (fderiv ℝ V) x - fderiv ℝ (fderiv ℝ U) x‖ ≤ slicedPrincipalC2Tolerance (Fintype.card (Σ j, B j × F j)) (Fintype.card D) m C a δ A η := by
    intro x hx
    have hb := polynomialVectorMap_mass_c2_bounds q hqdegree hM hqmass x hx
    have hdom := polynomialMassC2Budget_dominates (Fintype.card (Σ j, B j × F j)) d hM
    have he := factoredDifference_c2_bounds V U (polynomialVectorMap q) t hV hU hq
      (fun x => add_sub_cancel_left (U x) _) x (hb.1.trans hdom.1)
      (hb.2.1.trans hdom.2.1) (hb.2.2.trans hdom.2.2)
    exact ⟨he.1.trans ht, he.2.1.trans ht, he.2.2.trans ht⟩
  have he := herr hclose (fun y => φ (shift + y)) (hφ.comp (measurable_const.add measurable_id))
    (fun y => hφone (shift + y))
  simpa only [mappedTest, V, U, add_assoc] using he

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

theorem nonprincipalCoefficientSlots_image {C B K : Type*} [Fintype C] [Fintype B] [DecidableEq (K →₀ ℕ)]
    (e : C → K →₀ ℕ) (principal : B → K →₀ ℕ) :
    (nonprincipalCoefficientSlots e principal).image e =
      fixedNonprincipalExponents (monomialExponentSet e) principal := by
  classical
  ext m
  constructor
  · intro hm
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hm
    exact (mem_nonprincipalCoefficientSlots e principal j).mp hj
  · intro hm
    have hs : m ∈ monomialExponentSet e :=
      ((mem_fixedNonprincipalExponents _ principal m).mp hm).1
    obtain ⟨j, rfl⟩ := (mem_monomialExponentSet e m).mp hs
    have hj := (mem_nonprincipalCoefficientSlots e principal j).mpr hm
    exact Finset.mem_image.mpr ⟨j, hj, rfl⟩

theorem nonprincipalCoefficientSlots_sum {C B K R : Type*} [Fintype C] [Fintype B] [AddCommMonoid R]
    (e : C → K →₀ ℕ) (he : Function.Injective e) (principal : B → K →₀ ℕ) (f : (K →₀ ℕ) → R) :
    (∑ j ∈ nonprincipalCoefficientSlots e principal, f (e j)) =
      ∑ m ∈ fixedNonprincipalExponents (monomialExponentSet e) principal, f m := by
  classical
  rw [← nonprincipalCoefficientSlots_image e principal, Finset.sum_image (fun _ _ _ _ h => he h)]

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.SmallAffinePolynomial
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem monomialArrayPolynomial_indexed_split {C B K : Type*} [Fintype C] [Fintype B]
    (e : C → K →₀ ℕ) (he : Function.Injective e)
    (principal : B → K →₀ ℕ) (hp : Function.Injective principal) (hp0 : ∀ b, principal b ≠ 0)
    (index : B → C) (hindex : ∀ b, e (index b) = principal b) (a : C → ℝ) :
    monomialArrayPolynomial e a = MvPolynomial.C ((monomialArrayPolynomial e a).coeff 0) +
      (∑ b, MvPolynomial.monomial (principal b) (a (index b))) +
      ∑ j ∈ nonprincipalCoefficientSlots e principal, MvPolynomial.monomial (e j) (a j) := by
  classical
  have hS : (monomialArrayPolynomial e a).support ⊆ monomialExponentSet e := by
    intro m hm
    obtain ⟨j, rfl⟩ := monomialArrayPolynomial_support_subset e a hm
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
  have hs := polynomial_coefficient_split_principal_on (monomialArrayPolynomial e a)
    (monomialExponentSet e) hS principal hp hp0
  rw [← nonprincipalCoefficientSlots_sum e he principal] at hs
  have hc (b) : (monomialArrayPolynomial e a).coeff (principal b) = a (index b) := by
    rw [← hindex b]
    exact monomialArrayPolynomial_coeff e he a (index b)
  simpa only [hc, monomialArrayPolynomial_coeff e he] using hs

theorem nonprincipalDilation_constant_coeff {C B K : Type*} [Fintype C] [Fintype B]
    (e : C → K →₀ ℕ) (principal : B → K →₀ ℕ) (t : ℝ) (a : C → ℝ) :
    (monomialArrayPolynomial e (fun j => nonprincipalDilation e principal t j*a j)).coeff 0 =
      (monomialArrayPolynomial e a).coeff 0 := by
  classical
  simp only [monomialArrayPolynomial, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : e j = 0
  · simp only [hj, ite_true, nonprincipalDilation_zero e principal t j hj, one_mul]
  · simp only [hj, ite_false]

theorem monomialArrayPolynomial_dilated_split {C B K : Type*} [Fintype C] [Fintype B]
    (e : C → K →₀ ℕ) (he : Function.Injective e)
    (principal : B → K →₀ ℕ) (hp : Function.Injective principal) (hp0 : ∀ b, principal b ≠ 0)
    (index : B → C) (hindex : ∀ b, e (index b) = principal b) (t : ℝ) (a : C → ℝ) :
    monomialArrayPolynomial e (fun j => nonprincipalDilation e principal t j*a j) =
      MvPolynomial.C ((monomialArrayPolynomial e a).coeff 0) +
      (∑ b, MvPolynomial.monomial (principal b) (a (index b))) +
      ∑ j ∈ nonprincipalCoefficientSlots e principal, MvPolynomial.monomial (e j) (t*a j) := by
  have hs := monomialArrayPolynomial_indexed_split e he principal hp hp0 index hindex
    (fun j => nonprincipalDilation e principal t j*a j)
  rw [nonprincipalDilation_constant_coeff] at hs
  have hpv (b) : nonprincipalDilation e principal t (index b)*a (index b) = a (index b) := by
    rw [nonprincipalDilation_principal e principal t (index b) b (hindex b), one_mul]
  simp_rw [hpv] at hs
  rw [hs]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [nonprincipalDilation_mem e principal t j hj]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem monomialArrayPolynomial_affine_dilated_split {C B K : Type*} [Fintype C] [Fintype B]
    (e : C → K →₀ ℕ) (he : Function.Injective e)
    (principal : B → K →₀ ℕ) (hp : Function.Injective principal) (hp0 : ∀ b, principal b ≠ 0)
    (index : B → C) (hindex : ∀ b, e (index b) = principal b) (t : ℝ) (c w r : C → ℝ) :
    monomialArrayPolynomial e (fun j => nonprincipalDilation e principal t j*c j +
      (nonprincipalDilation e principal t j*w j)*r j) =
      MvPolynomial.C ((monomialArrayPolynomial e (fun j => c j+w j*r j)).coeff 0) +
      (∑ b, MvPolynomial.monomial (principal b) (c (index b)+w (index b)*r (index b))) +
      ∑ j ∈ nonprincipalCoefficientSlots e principal, MvPolynomial.monomial (e j) (t*(c j+w j*r j)) := by
  have ha : (fun j => nonprincipalDilation e principal t j*c j +
      (nonprincipalDilation e principal t j*w j)*r j) =
      (fun j => nonprincipalDilation e principal t j*(c j+w j*r j)) := by
    funext j
    ring
  rw [ha]
  exact monomialArrayPolynomial_dilated_split e he principal hp hp0 index hindex t _

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

theorem boundedProfileCenter_dilation (γ t : ℝ)
    (e : BoundedCoefficientExponent (SamplerTupleIndex G B h) (h d)) :
    coefficientProfileCenter (principalCoefficientSlots h d) γ e =
      nonprincipalDilation Subtype.val (canonicalPrincipalExponent h d) t e *
        coefficientProfileCenter (principalCoefficientSlots h d) γ e := by
  classical
  by_cases hp : e ∈ principalCoefficientSlots h d
  · obtain ⟨b, hb⟩ := (mem_principalCoefficientSlots h d e).mp hp
    rw [nonprincipalDilation_principal Subtype.val (canonicalPrincipalExponent h d)
      t e b (congrArg Subtype.val hb.symm), one_mul]
  · simp only [coefficientProfileCenter, hp, ite_false, mul_zero]

theorem boundedProfileWidth_dilation (ρ γ ε t : ℝ)
    (e : BoundedCoefficientExponent (SamplerTupleIndex G B h) (h d)) :
    coefficientProfileWidth (principalCoefficientSlots h d) (constantCoefficientSlot _ _)
        ρ γ (t * ε) e =
      nonprincipalDilation Subtype.val (canonicalPrincipalExponent h d) t e *
        coefficientProfileWidth (principalCoefficientSlots h d) (constantCoefficientSlot _ _)
          ρ γ ε e := by
  classical
  by_cases hz : e = constantCoefficientSlot _ _
  · rw [nonprincipalDilation_zero Subtype.val (canonicalPrincipalExponent h d)
      t e (congrArg Subtype.val hz)]
    simp only [coefficientProfileWidth, hz, ite_true, one_mul]
  · by_cases hp : e ∈ principalCoefficientSlots h d
    · obtain ⟨b, hb⟩ := (mem_principalCoefficientSlots h d e).mp hp
      rw [nonprincipalDilation_principal Subtype.val (canonicalPrincipalExponent h d)
        t e b (congrArg Subtype.val hb.symm), one_mul]
      simp only [coefficientProfileWidth, hz, hp, ite_false, ite_true]
    · rw [nonprincipalDilation_mem Subtype.val (canonicalPrincipalExponent h d) t e
        ((bounded_mem_nonprincipalCoefficientSlots h d e).mpr ⟨hz, hp⟩)]
      simp only [coefficientProfileWidth, hz, hp, ite_false]

theorem boundedProfile_polynomial_split (hd : 0 < h d) (ρ γ ε t : ℝ)
    (r : BoundedCoefficientExponent (SamplerTupleIndex G B h) (h d) → ℝ) :
    monomialArrayPolynomial Subtype.val (fun e =>
      coefficientProfileCenter (principalCoefficientSlots h d) γ e +
        coefficientProfileWidth (principalCoefficientSlots h d) (constantCoefficientSlot _ _)
          ρ γ (t * ε) e * r e) =
      MvPolynomial.C (ρ * r (constantCoefficientSlot _ _)) +
      (∑ b, MvPolynomial.monomial (canonicalPrincipalExponent h d b)
        (3 * γ / 2 + γ / 2 * r (principalCoefficientSlot h d b))) +
      ∑ e ∈ nonprincipalCoefficientSlots
          (Subtype.val : BoundedCoefficientExponent (SamplerTupleIndex G B h) (h d) → _)
          (canonicalPrincipalExponent h d),
        MvPolynomial.monomial e.val (t * (ε * r e)) := by
  classical
  let c := coefficientProfileCenter (principalCoefficientSlots (G := G) (B := B) h d) γ
  let w := coefficientProfileWidth (principalCoefficientSlots (G := G) (B := B) h d)
    (constantCoefficientSlot _ _) ρ γ ε
  have heq : (fun e => c e + coefficientProfileWidth (principalCoefficientSlots h d)
      (constantCoefficientSlot _ _) ρ γ (t * ε) e * r e) =
      (fun e => nonprincipalDilation Subtype.val (canonicalPrincipalExponent h d) t e * c e +
        (nonprincipalDilation Subtype.val (canonicalPrincipalExponent h d) t e * w e) * r e) := by
    funext e
    rw [boundedProfileWidth_dilation]
    congr 1
    exact boundedProfileCenter_dilation h d γ t e
  rw [heq, monomialArrayPolynomial_affine_dilated_split Subtype.val Subtype.val_injective
    (canonicalPrincipalExponent h d) (canonicalPrincipalExponent_injective h d hd)
    (canonicalPrincipalExponent_ne_zero h d hd) (principalCoefficientSlot h d) (fun _ => rfl)]
  have hc : (monomialArrayPolynomial Subtype.val (fun e => c e + w e * r e)).coeff 0 =
      ρ * r (constantCoefficientSlot _ _) := by
    rw [show (0 : SamplerTupleIndex G B h →₀ ℕ) =
      (constantCoefficientSlot (SamplerTupleIndex G B h) (h d)).val from rfl,
      monomialArrayPolynomial_coeff Subtype.val Subtype.val_injective]
    simp only [c, w, coefficientProfileCenter, coefficientProfileWidth,
      constantCoefficientSlot_not_principal h d hd, ite_false, ite_true, zero_add]
  rw [hc]
  congr 1
  · congr 1
    apply Finset.sum_congr rfl
    intro b _
    have hp : principalCoefficientSlot h d b ∈ principalCoefficientSlots (G := G) h d :=
      (mem_principalCoefficientSlots h d _).mpr ⟨b, rfl⟩
    have hz : principalCoefficientSlot (G := G) h d b ≠ constantCoefficientSlot _ _ := by
      intro hz
      exact constantCoefficientSlot_not_principal h d hd (hz ▸ hp)
    simp only [c, w, coefficientProfileCenter, coefficientProfileWidth, hp, hz, ite_true, ite_false]
  · apply Finset.sum_congr rfl
    intro e he
    obtain ⟨hz, hp⟩ := (bounded_mem_nonprincipalCoefficientSlots h d e).mp he
    simp only [c, w, coefficientProfileCenter, coefficientProfileWidth, hz, hp, ite_false, zero_add]

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

theorem unitProfileTailSize_pos (d : D) : 0 < unitProfileTailSize (G := G) (B := B) h d :=
  tailProfileSize_pos zero_lt_one zero_lt_one _

omit [DecidablePred P] in
theorem partitionedProfileTail_unit_sum (d : {d // ¬P d}) :
    (∑ _e ∈ partitionedProfileTerms (G := G) (B := B) h P d,
      |unitProfileTailSize (G := G) (B := B) h d.val|) ≤ 1 := by
  have he := unitProfileTailSize_pos (G := G) (B := B) h d.val
  have hb := allocatedProfile_budget (R := 1) (σ := 1) zero_le_one le_rfl 0
    (Fintype.card (SamplerCoefficientSlot G B h d.val))
  simp only [Nat.cast_zero, mul_zero, add_zero] at hb
  rw [abs_of_pos he, Finset.sum_const, nsmul_eq_mul]
  calc
    _ ≤ (Fintype.card (SamplerCoefficientSlot G B h d.val) : ℝ) *
        unitProfileTailSize (G := G) (B := B) h d.val :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_univ _) he.le
    _ ≤ 1 := by unfold unitProfileTailSize; nlinarith

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

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.SlicedProfilePolynomial
namespace OAI

section

namespace Erdos3

open VectorPolynomial
open scoped BigOperators

variable {D G : Type*} [Fintype D] [Fintype G]
variable {B : D → Type*} [∀ d, Fintype (B d)] (h : D → ℕ) (d : D)
variable {I : Type*}

theorem slicedProfileTailPolynomial_degree
    (ε : ℝ) (r : SamplerCoefficientSlot G B h d → ℝ)
    (ξ : SamplerTupleIndex G B h → MvPolynomial I ℝ)
    (hξ : ∀ k, (ξ k).totalDegree ≤ 1) :
    (slicedProfileTailPolynomial h d ε r ξ).totalDegree ≤ h d := by
  classical
  apply (polynomial_substitution_totalDegree_le _ ξ hξ ?_).trans (Nat.mul_one _).le
  apply MvPolynomial.totalDegree_finsetSum_le
  intro e _
  exact (MvPolynomial.totalDegree_monomial_le _ _).trans e.property

theorem slicedProfileTailPolynomial_mass
    (ε : ℝ) (r : SamplerCoefficientSlot G B h d → ℝ) (hr : ∀ e, |r e| ≤ 1)
    (ξ : SamplerTupleIndex G B h → MvPolynomial I ℝ)
    (hξ : ∀ k, realPolynomialMass (ξ k) ≤ 1) :
    realPolynomialMass (slicedProfileTailPolynomial h d ε r ξ) ≤
      (nonprincipalCoefficientSlots
        (Subtype.val : SamplerCoefficientSlot G B h d → _)
        (canonicalPrincipalExponent h d)).card * |ε| := by
  classical
  apply (realPolynomialMass_substitution_le _ ξ (M := 1) le_rfl hξ le_rfl).trans
  simp only [one_pow, mul_one]
  apply (realPolynomialMass_sum_le _ _).trans
  calc
    _ ≤ ∑ _e ∈ nonprincipalCoefficientSlots
        (Subtype.val : SamplerCoefficientSlot G B h d → _) (canonicalPrincipalExponent h d),
        |ε| := by
      apply Finset.sum_le_sum
      intro e _
      rw [realPolynomialMass_monomial, abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (hr e)
    _ = _ := by simp

theorem slicedProfileTailPolynomial_unit_mass
    (r : SamplerCoefficientSlot G B h d → ℝ) (hr : ∀ e, |r e| ≤ 1)
    (ξ : SamplerTupleIndex G B h → MvPolynomial I ℝ)
    (hξ : ∀ k, realPolynomialMass (ξ k) ≤ 1) :
    realPolynomialMass (slicedProfileTailPolynomial h d
      (unitProfileTailSize (G := G) (B := B) h d) r ξ) ≤ 1 := by
  apply (slicedProfileTailPolynomial_mass h d _ r hr ξ hξ).trans
  have he := partitionedProfileTail_unit_sum (G := G) (B := B) h (fun _ => False) ⟨d, by simp⟩
  simpa only [partitionedProfileTerms, Finset.sum_const, nsmul_eq_mul] using he

theorem slicedProfile_eval_split
    (hd : 0 < h d) (ρ γ ε t : ℝ) (r : SamplerCoefficientSlot G B h d → ℝ)
    (ξ : SamplerTupleIndex G B h → MvPolynomial I ℝ) (x : I → ℝ) :
    MvPolynomial.eval (fun k => MvPolynomial.eval x (ξ k))
      (monomialArrayPolynomial Subtype.val (fun e : SamplerCoefficientSlot G B h d =>
        coefficientProfileCenter (principalCoefficientSlots h d) γ e +
          coefficientProfileWidth (principalCoefficientSlots h d) (constantCoefficientSlot _ _)
            ρ γ (t * ε) e * r e)) =
      ρ * r (constantCoefficientSlot _ _) +
        (∑ b, (3 * γ / 2 + γ / 2 * r (principalCoefficientSlot h d b)) *
          ∏ v, MvPolynomial.eval x (ξ (.inr ⟨d, b, v⟩))) +
        t * MvPolynomial.eval x (slicedProfileTailPolynomial h d ε r ξ) := by
  classical
  rw [boundedProfile_polynomial_split h d hd]
  simp only [map_add, map_sum, MvPolynomial.eval_C]
  congr 1
  · congr 1
    apply Finset.sum_congr rfl
    intro b _
    simp only [canonicalPrincipalExponent, productBlockExponent_monomial,
      map_mul, MvPolynomial.eval_C, map_prod, MvPolynomial.eval_X]
    ring
  · simp only [slicedProfileTailPolynomial, map_sum, MvPolynomial.eval₂Hom_monomial,
      map_mul, MvPolynomial.eval_C, map_prod, map_pow, MvPolynomial.eval_monomial,
      Finsupp.prod, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedSlicedEndpointIdentity
namespace OAI

section

namespace Erdos3

open MeasureTheory VectorPolynomial
open scoped BigOperators NNReal

variable {D G E : Type*} [Fintype D] [Fintype G] [Fintype E]
variable {B : D → Type*} [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)]
variable (h : D → ℕ) (axis : E → D)

local notation "Input" => (Σ e, B (axis e) × Fin (h (axis e)))
local notation "Output" => (Σ _e : E, Unit)

omit [Fintype E] [∀ index, DecidableEq (B index)] in
theorem jointSlicedProfileValue_split
    (hh : ∀ e, 0 < h (axis e)) (ρ γ ε : D → ℝ)
    (r : ∀ e, SamplerCoefficientSlot G B h (axis e) → ℝ)
    (ξ : E → SamplerTupleIndex G B h → MvPolynomial Input ℝ)
    (lower width : ∀ e, B (axis e) × Fin (h (axis e)) → ℝ)
    (hξ : ∀ e b i, ξ e (.inr ⟨axis e, b, i⟩) =
      MvPolynomial.C (lower e (b, i)) + MvPolynomial.C (width e (b, i)) * MvPolynomial.X ⟨e, b, i⟩)
    (t : ℝ) :
    jointSlicedProfileValue h axis ρ γ ε r ξ t = fun x =>
      jointSlicedProfileShift h axis ρ r +
        jointSlicedPrincipal (jointSlicedProfilePrincipal h axis γ r) lower width x +
        t • polynomialVectorMap (jointSlicedProfileTail h axis ε r ξ) x := by
  funext x o
  rw [jointSlicedProfileValue, slicedProfile_eval_split h (axis o.1) (hh o.1)]
  simp only [hξ, map_add, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
  rfl

omit [Fintype D] [Fintype G] [Fintype E] [∀ index, DecidableEq (B index)] in
theorem jointSlicedProfilePrincipal_unit_bounds
    (r : ∀ e, SamplerCoefficientSlot G B h (axis e) → ℝ) (hr : ∀ e j, |r e j| ≤ 1)
    (e : E) (b : B (axis e)) :
    unitProfilePrincipalSize (B := B) (axis e) ≤
      |jointSlicedProfilePrincipal h axis (unitProfilePrincipalSize (B := B)) r e b| ∧
    |jointSlicedProfilePrincipal h axis (unitProfilePrincipalSize (B := B)) r e b| ≤
      2 * unitProfilePrincipalSize (B := B) (axis e) := by
  have hγ := unitProfilePrincipalSize_pos (B := B) (axis e)
  obtain ⟨hl, hu⟩ := abs_le.mp (hr e (principalCoefficientSlot h (axis e) b))
  have hlo : unitProfilePrincipalSize (B := B) (axis e) ≤
      jointSlicedProfilePrincipal h axis (unitProfilePrincipalSize (B := B)) r e b := by
    unfold jointSlicedProfilePrincipal
    nlinarith
  rw [abs_of_nonneg (hγ.le.trans hlo)]
  refine ⟨hlo, ?_⟩
  unfold jointSlicedProfilePrincipal
  nlinarith

omit [Fintype D] [Fintype G] [Fintype E] [∀ index, DecidableEq (B index)] in
theorem jointSlicedProfilePrincipal_unit_mass
    (r : ∀ e, SamplerCoefficientSlot G B h (axis e) → ℝ) (hr : ∀ e j, |r e j| ≤ 1)
    (e : E) :
    (∑ b, |jointSlicedProfilePrincipal h axis (unitProfilePrincipalSize (B := B)) r e b|) ≤ 1 := by
  have hb := allocatedProfile_budget (R := 1) (σ := 1) zero_le_one le_rfl
    (Fintype.card (B (axis e))) 0
  simp only [Nat.cast_zero, mul_zero, add_zero] at hb
  calc
    _ ≤ ∑ _b : B (axis e), 2 * unitProfilePrincipalSize (B := B) (axis e) :=
      Finset.sum_le_sum (fun b _ => (jointSlicedProfilePrincipal_unit_bounds h axis r hr e b).2)
    _ = 2 * principalProfileSize 1 (Fintype.card (B (axis e))) * Fintype.card (B (axis e)) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, unitProfilePrincipalSize]
      ring
    _ ≤ 1 := by linarith

theorem jointSlicedProfileValue_unit_comparison_oai
    {m : ℕ} (hh : ∀ e, 0 < h (axis e)) (hm : ∀ e, h (axis e) ≤ m)
    (ρ : D → ℝ) (r : ∀ e, SamplerCoefficientSlot G B h (axis e) → ℝ)
    (hr : ∀ e j, |r e j| ≤ 1)
    (ξ : E → SamplerTupleIndex G B h → MvPolynomial Input ℝ)
    (hξdegree : ∀ e k, (ξ e k).totalDegree ≤ 1)
    (hξmass : ∀ e k, realPolynomialMass (ξ e k) ≤ 1)
    (lower width : ∀ e, B (axis e) × Fin (h (axis e)) → ℝ)
    (hξ : ∀ e b i, ξ e (.inr ⟨axis e, b, i⟩) =
      MvPolynomial.C (lower e (b, i)) + MvPolynomial.C (width e (b, i)) * MvPolynomial.X ⟨e, b, i⟩)
    (hwidth : ∀ e p, |lower e p| + |width e p| ≤ 1)
    (b : ∀ e, B (axis e)) (i : ∀ e, Fin (h (axis e)))
    {a δ η : ℝ} (ha : 0 < a) (hδ : 0 < δ) (hδone : δ ≤ 1) (hη : 0 < η)
    (hprincipal : ∀ e, a ≤ unitProfilePrincipalSize (B := B) (axis e))
    (hw : ∀ e j, δ ≤ width e (b e, j))
    (hlower : ∀ e j, j ≠ i e → 0 ≤ lower e (b e, j))
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition)
    (t : ℝ)
    (ht : |t| * polynomialMassC2Budget (Fintype.card Input) m 1 ≤
      slicedPrincipalC2Tolerance (Fintype.card Input) (Fintype.card E) m 1 a δ A η)
    (φ : (Output → ℝ) → ℝ) (hφ : Measurable φ) (hφone : ∀ y, ‖φ y‖ ≤ 1) :
    |mappedTest (unitBoxMeasure Input)
        (fun x => jointSlicedProfileShift h axis ρ r +
          jointSlicedPrincipal (jointSlicedProfilePrincipal h axis (unitProfilePrincipalSize (B := B)) r)
            lower width x) φ -
      mappedTest (unitBoxMeasure Input)
        (jointSlicedProfileValue h axis ρ (unitProfilePrincipalSize (B := B))
          (unitProfileTailSize (G := G) (B := B) h) r ξ t) φ| ≤ η := by
  classical
  rw [jointSlicedProfileValue_split h axis hh ρ _ _ r ξ lower width hξ t]
  apply jointSlicedPrincipal_polynomial_tail_comparison _ lower width b i
    (by simpa only [Fintype.card_fin] using hm) zero_le_one zero_le_one ha hδ hδone hη A hA hwidth
    (jointSlicedProfilePrincipal_unit_mass h axis r hr)
    (fun e => (hprincipal e).trans (jointSlicedProfilePrincipal_unit_bounds h axis r hr e (b e)).1)
    hw hlower _ _ _ t ht _ φ hφ hφone
  · intro o v
    exact (MvPolynomial.degreeOf_le_totalDegree _ _).trans
      ((slicedProfileTailPolynomial_degree h (axis o.1) _ (r o.1) (ξ o.1) (hξdegree o.1)).trans (hm o.1))
  · intro o
    exact slicedProfileTailPolynomial_unit_mass h (axis o.1) (r o.1) (hr o.1) (ξ o.1) (hξmass o.1)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {D G : Type*} {B : D → Type*} (h : D → ℕ)
variable (P : D → Prop) [DecidablePred P]

variable (lower width : ∀ d : {d // ¬P d}, B d.val × Fin (h d.val) → ℝ)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {D G Z : Type*} [Fintype D] [Fintype G]
variable {B : D → Type*} [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)]
variable (h : D → ℕ) (P : D → Prop) [DecidablePred P]
variable (extra : G → Option (Fin 1) → Z)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

variable (A : Type*) [Fintype A]

end Erdos3

end

section

namespace Erdos3
open scoped NNReal

variable {D : Type*} [Fintype D] (P : D → Prop) [DecidablePred P]

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

variable (A : Type*) [Fintype A]

end Erdos3

end

section

namespace Erdos3
open scoped NNReal

variable {D : Type*} [Fintype D] (P : D → Prop) [DecidablePred P] (R : D → ℝ)

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable (x : G → IntegerScalarCubeBox (Fin 1) S.value)
variable (u : PrincipalAxisTuples (α := Fin 1) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n

end Erdos3.VectorPolynomial

end

end OAI

end

theorem solution.{u_1, u_2, u_3, u_4} : type_of% @OAI.Erdos3.jointSlicedProfileValue_unit_comparison_oai.{u_1, u_2, u_3, u_4} := @OAI.Erdos3.jointSlicedProfileValue_unit_comparison_oai.{u_1, u_2, u_3, u_4}
