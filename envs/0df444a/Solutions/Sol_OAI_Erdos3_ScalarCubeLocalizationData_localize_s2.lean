-- Prove2me | solution 1 for OAI.Erdos3.ScalarCubeLocalizationData.localize_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-17T11:25:14.739147+00:00
-- url     : https://prove2.me/submissions/291adfe7-0152-4f1a-8491-7aa72da6ff84

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B113
import Definitions.Def_OAIE3v2B125
import Definitions.Def_OAIE3v2B137
import Theorems.Thm_OAI_Erdos3_scalarCubeResidueWeights_riemann_s2

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteFiberVolumeBound
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem product_measureReal_le_of_fiber_bound {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) [SFinite μ] [SFinite ν]
    (s : Set (A × B)) (hs : MeasurableSet s) (hsfin : (μ.prod ν) s ≠ ⊤)
    (T : Set A) (hT : MeasurableSet T) (hTfin : μ T ≠ ⊤)
    (hbase : ∀ z ∈ s, z.1 ∈ T) {b : ℝ}
    (hbound : ∀ x, ν.real {y | (x, y) ∈ s} ≤ b) :
    (μ.prod ν).real s ≤ μ.real T * b := by
  have hi : Integrable (s.indicator (fun _ => (1 : ℝ))) (μ.prod ν) :=
    (integrableOn_const hsfin).integrable_indicator hs
  have hmajor : Integrable (T.indicator (fun _ => b)) μ :=
    (integrableOn_const hTfin).integrable_indicator hT
  rw [← integral_indicator_one hs]
  change (∫ z, s.indicator (fun _ => (1 : ℝ)) z ∂μ.prod ν) ≤ _
  rw [integral_prod _ hi]
  calc
    _ ≤ ∫ x, T.indicator (fun _ => b) x ∂μ := by
      apply integral_mono hi.integral_prod_left hmajor
      intro x
      change (∫ y, s.indicator (fun _ => (1 : ℝ)) (x, y) ∂ν) ≤ T.indicator (fun _ => b) x
      rw [integral_indicator_fiber ν s hs]
      by_cases hx : x ∈ T
      · rw [Set.indicator_of_mem hx]
        exact hbound x
      · have hempty : {y | (x, y) ∈ s} = ∅ := by
          apply Set.eq_empty_iff_forall_notMem.mpr
          intro y hy
          exact hx (hbase (x, y) hy)
        rw [hempty, measureReal_empty, Set.indicator_of_notMem hx]
    _ = _ := by rw [integral_indicator_const _ hT, smul_eq_mul]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BooleanMinorDimension
namespace OAI

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

theorem inequalityBoundaryCutoff_tsupport_domain {I E : Type*} [Fintype I]
    [TopologicalSpace E] (r : I → ℝ) (hr : ∀ i, 0 < r i)
    (d : I → E → ℝ) (hd : ∀ i, Continuous (d i)) :
    tsupport (inequalityBoundaryCutoff r d) ⊆ positiveInequalityDomain d := by
  intro x hx i
  exact (hr i).trans_le (inequalityBoundaryCutoff_tsupport_subset r hr d hd hx i)

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

theorem scalarCubeFace_card (α : Type*) [Fintype α] :
    Fintype.card (Bool × Finset α) = 2 * 2 ^ Fintype.card α := by simp

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

theorem scalarCubeLinearMap_apply {α : Type*} [Fintype α] [DecidableEq α]
    (t : Finset α) (a : Option α → ℝ) : scalarCubeLinearMap t a = scalarCubeValue a t := by
  simp only [scalarCubeLinearMap, sum_apply, smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, scalarCubeValue]

theorem scalarCubeLinearMap_single {α : Type*} [Fintype α] [DecidableEq α]
    (t : Finset α) (r : Option α) :
    scalarCubeLinearMap t (Pi.single r 1) = (booleanFeature r t : ℝ) := by
  rw [scalarCubeLinearMap_apply]
  simp [scalarCubeValue, Pi.single_apply, mul_ite]

theorem scalarCubeLinearMap_norm_le {α : Type*} [Fintype α] [DecidableEq α] (t : Finset α) :
    ‖scalarCubeLinearMap t‖ ≤ (Fintype.card α : ℝ) + 1 := by
  have h := clm_norm_le_card_mul_of_basis (scalarCubeLinearMap t) zero_le_one (fun r => by
    rw [scalarCubeLinearMap_single, Real.norm_eq_abs]
    exact booleanFeature_abs_le_one r t)
  simpa only [Fintype.card_option, Nat.cast_add, Nat.cast_one, mul_one] using h

theorem scalarCubeValue_fderiv_norm_le {α : Type*} [Fintype α] [DecidableEq α]
    (t : Finset α) (a : Option α → ℝ) :
    ‖fderiv ℝ (fun x => scalarCubeValue x t) a‖ ≤ (Fintype.card α : ℝ) + 1 := by
  have heq : (fun x => scalarCubeValue x t) = scalarCubeLinearMap t :=
    funext (fun x => (scalarCubeLinearMap_apply t x).symm)
  rw [heq, ContinuousLinearMap.fderiv]
  exact scalarCubeLinearMap_norm_le t

theorem scalarCubeFace_fderiv_norm_le {α : Type*} [Fintype α] [DecidableEq α]
    (i : Bool × Finset α) (a : Option α → ℝ) :
    ‖fderiv ℝ (scalarCubeFace i) a‖ ≤ (Fintype.card α : ℝ) + 1 := by
  rcases i with ⟨b, t⟩
  cases b with
  | false => exact scalarCubeValue_fderiv_norm_le t a
  | true =>
    change ‖fderiv ℝ (fun x => 1 - scalarCubeValue x t) a‖ ≤ _
    rw [fderiv_const_sub, norm_neg]
    exact scalarCubeValue_fderiv_norm_le t a

theorem scalarCubeBoundaryCutoff_fderiv_norm_le {α : Type*} [Fintype α] [DecidableEq α]
    (A : ℝ≥0) (hLip : LipschitzWith A Real.smoothTransition) {r : ℝ} (hr : 0 < r)
    (a : Option α → ℝ) :
    ‖fderiv ℝ (inequalityBoundaryCutoff (fun _ : Bool × Finset α => r) scalarCubeFace) a‖ ≤
      ((2 * 2 ^ Fintype.card α : ℕ) : ℝ) * ((A : ℝ) / r * ((Fintype.card α : ℝ) + 1)) := by
  apply (inequalityBoundaryCutoff_fderiv_norm_le A hLip _ (fun _ => hr)
    scalarCubeFace scalarCubeFace_contDiff a).trans
  calc
    _ ≤ ∑ _i : Bool × Finset α, (A : ℝ) / r * ((Fintype.card α : ℝ) + 1) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (scalarCubeFace_fderiv_norm_le i a)
        (div_nonneg A.coe_nonneg hr.le))
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, scalarCubeFace_card, nsmul_eq_mul]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ScalarCubeCoordinates
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem scalarCubeJoin_none {α : Type*} (z : (α → ℝ) × ℝ) : scalarCubeJoin z none = z.2 := rfl

theorem scalarCubeJoin_some {α : Type*} (z : (α → ℝ) × ℝ) (i : α) :
    scalarCubeJoin z (some i) = z.1 i := rfl

theorem scalarCubeJoin_measurable (α : Type*) : Measurable (@scalarCubeJoin α) :=
  (MeasurableEquiv.piOptionEquivProd (fun _ : Option α => ℝ)).symm.measurable

theorem scalarCubeJoin_measurePreserving (α : Type*) [Fintype α] :
    MeasurePreserving (@scalarCubeJoin α) volume volume := by
  refine ⟨scalarCubeJoin_measurable α, ?_⟩
  exact Measure.pi_map_piOptionEquivProd (fun _ : Option α => (volume : Measure ℝ))

theorem scalarCubeJoin_value {α : Type*} [Fintype α] [DecidableEq α]
    (z : (α → ℝ) × ℝ) (t : Finset α) :
    scalarCubeValue (scalarCubeJoin z) t = z.2 + ∑ i ∈ t, z.1 i := by
  simp [scalarCubeValue, Fintype.sum_option, booleanFeature, scalarCubeJoin_none,
    scalarCubeJoin_some, ite_mul]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ScalarCubeBoundaryVolume
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem scalarCubeFaceStrip_measurable {α : Type*} [Fintype α] [DecidableEq α]
    (i : Bool × Finset α) (u : ℝ) : MeasurableSet (scalarCubeFaceStrip i u) :=
  (scalarCubeDomain_isOpen α).measurableSet.inter
    (measurableSet_lt (scalarCubeFace_contDiff i).continuous.measurable measurable_const)

theorem scalarCubeFaceStrip_volume_lt_top {α : Type*} [Fintype α] [DecidableEq α]
    (i : Bool × Finset α) (u : ℝ) : volume (scalarCubeFaceStrip i u) < ⊤ :=
  (measure_mono Set.inter_subset_left).trans_lt (scalarCubeDomain_volume_lt_top α)

theorem scalarCubeFaceStrip_fiber_interval {α : Type*} [Fintype α] [DecidableEq α]
    (i : Bool × Finset α) (u : ℝ) (b : α → ℝ) :
    ∃ lo : ℝ, {y | scalarCubeJoin (b, y) ∈ scalarCubeFaceStrip i u} ⊆ Set.Ioo lo (lo + u) := by
  rcases i with ⟨side, t⟩
  cases side with
  | false =>
    refine ⟨-(∑ k ∈ t, b k), ?_⟩
    intro y hy
    have hpos := (hy.1 t).1
    have hupper := hy.2
    change scalarCubeValue (scalarCubeJoin (b, y)) t < u at hupper
    rw [scalarCubeJoin_value] at hpos hupper
    exact ⟨by linarith, by linarith⟩
  | true =>
    refine ⟨1 - (∑ k ∈ t, b k) - u, ?_⟩
    intro y hy
    have hpos := (hy.1 t).2
    have hlower := hy.2
    change 1 - scalarCubeValue (scalarCubeJoin (b, y)) t < u at hlower
    rw [scalarCubeJoin_value] at hpos hlower
    exact ⟨by linarith, by linarith⟩

theorem scalarCubeFaceStrip_fiber_volume_le {α : Type*} [Fintype α] [DecidableEq α]
    (i : Bool × Finset α) {u : ℝ} (hu : 0 ≤ u) (b : α → ℝ) :
    volume.real {y | scalarCubeJoin (b, y) ∈ scalarCubeFaceStrip i u} ≤ u := by
  obtain ⟨lo, hsub⟩ := scalarCubeFaceStrip_fiber_interval i u b
  have hlen : volume.real (Set.Ioo lo (lo + u)) = u := by
    rw [Real.volume_real_Ioo]
    simpa only [add_sub_cancel_left] using max_eq_left hu
  exact (measureReal_mono (μ := volume) hsub (by simp [Real.volume_Ioo])).trans_eq hlen

theorem scalarCubeFaceStrip_base_bound {α : Type*} [Fintype α] [DecidableEq α]
    (i : Bool × Finset α) (u : ℝ) {z : (α → ℝ) × ℝ}
    (hz : scalarCubeJoin z ∈ scalarCubeFaceStrip i u) : z.1 ∈ Metric.closedBall (0 : α → ℝ) 1 := by
  rw [Metric.mem_closedBall, dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro k
  have h := (scalarCubeDomain_coordinate_abs_lt_one hz.1 (some k)).le
  simpa only [scalarCubeJoin_some, Real.norm_eq_abs] using h

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

theorem scalarCubeFaceStrip_volume_le {α : Type*} [Fintype α] [DecidableEq α]
    (i : Bool × Finset α) {u : ℝ} (hu : 0 ≤ u) :
    volume.real (scalarCubeFaceStrip i u) ≤ (2 : ℝ) ^ Fintype.card α * u := by
  let s : Set ((α → ℝ) × ℝ) := scalarCubeJoin ⁻¹' scalarCubeFaceStrip i u
  have hs : MeasurableSet s := (scalarCubeFaceStrip_measurable i u).preimage (scalarCubeJoin_measurable α)
  have hpres := scalarCubeJoin_measurePreserving α
  have hmass : volume s = volume (scalarCubeFaceStrip i u) :=
    hpres.measure_preimage (scalarCubeFaceStrip_measurable i u).nullMeasurableSet
  have hreal : volume.real s = volume.real (scalarCubeFaceStrip i u) :=
    hpres.measureReal_preimage (scalarCubeFaceStrip_measurable i u).nullMeasurableSet
  have hsfin : (volume : Measure ((α → ℝ) × ℝ)) s ≠ ⊤ := by
    rw [hmass]
    exact (scalarCubeFaceStrip_volume_lt_top i u).ne
  have h := product_measureReal_le_of_fiber_bound
    (volume : Measure (α → ℝ)) (volume : Measure ℝ) s hs hsfin
    (Metric.closedBall (0 : α → ℝ) 1) measurableSet_closedBall
    (isCompact_closedBall _ _).measure_ne_top
    (fun z hz => scalarCubeFaceStrip_base_bound i u hz)
    (scalarCubeFaceStrip_fiber_volume_le i hu)
  change volume.real s ≤ _ at h
  rw [hreal] at h
  have hbase : volume.real (Metric.closedBall (0 : α → ℝ) 1) = (2 : ℝ) ^ Fintype.card α := by
    rw [measureReal_def, Real.volume_pi_closedBall _ (by norm_num)]
    simp
  rw [hbase] at h
  exact h

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

theorem scalarCubeMeasure_real_apply {α : Type*} [Fintype α] [DecidableEq α]
    (s : Set (Option α → ℝ)) (hs : MeasurableSet s) :
    (scalarCubeMeasure α).real s = scalarCubeDomainDensity α * volume.real (scalarCubeDomain α ∩ s) := by
  rw [scalarCubeMeasure, measureReal_ennreal_smul_apply, measureReal_restrict_apply hs,
    ENNReal.toReal_inv, Set.inter_comm]
  rfl

theorem scalarCubeMeasure_face_bound {α : Type*} [Fintype α] [DecidableEq α]
    (i : Bool × Finset α) {u : ℝ} (hu : 0 ≤ u) :
    (scalarCubeMeasure α).real {a | scalarCubeFace i a < u} ≤
      scalarCubeDomainDensity α * (2 : ℝ) ^ Fintype.card α * u := by
  rw [scalarCubeMeasure_real_apply _ (measurableSet_lt
    (scalarCubeFace_contDiff i).continuous.measurable measurable_const)]
  have h := mul_le_mul_of_nonneg_left (scalarCubeFaceStrip_volume_le i hu) (scalarCubeDomainDensity_pos α).le
  exact h.trans_eq (by ring)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem scalarCubeBoundaryCutoff_mass_loss (α : Type*) [Fintype α] [DecidableEq α]
    {r : ℝ} (hr : 0 < r) :
    (∫ a, 1 - inequalityBoundaryCutoff (fun _ : Bool × Finset α => r) scalarCubeFace a
      ∂scalarCubeMeasure α) ≤ scalarCubeBoundaryConstant α * r := by
  apply (inequalityBoundaryCutoff_integral_loss_le (scalarCubeMeasure α) _ (fun _ => hr)
    scalarCubeFace (fun i => (scalarCubeFace_contDiff i).continuous.measurable)).trans
  calc
    _ ≤ ∑ _i : Bool × Finset α,
        scalarCubeDomainDensity α * (2 : ℝ) ^ Fintype.card α * (2 * r) :=
      Finset.sum_le_sum (fun i _ => scalarCubeMeasure_face_bound i (by positivity))
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, scalarCubeFace_card, nsmul_eq_mul]
      simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow, scalarCubeBoundaryConstant]
      ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ScalarCubeFaceSlab
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped Classical

theorem scalarCubeDomain_subset_halfOpen (I : Type*) [Fintype I] [DecidableEq I] :
    scalarCubeDomain I ⊆ halfOpenScalarCubeDomain I :=
  fun _ hx t => ⟨(hx t).1.le, (hx t).2⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProductCutoffLipschitz
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem finiteRectangleRefinement_val {I : Type*} (K N : I → ℕ)
    (k : ∀ i, Fin (K i)) (t : ∀ i, Fin (N i)) (i : I) :
    (finiteRectangleRefinement K N (k, t) i).val = N i * (k i).val + (t i).val := by
  exact Nat.add_comm _ _

theorem expect_finiteRectangleRefinement {I V : Type*} [Fintype I] [DecidableEq I]
    [AddCommMonoid V] [Module ℚ≥0 V] (K N : I → ℕ)
    (F : (∀ i, Fin (K i * N i)) → V) :
    (𝔼 x, F x) = 𝔼 k, 𝔼 t, F (finiteRectangleRefinement K N (k, t)) := by
  calc
    _ = 𝔼 p, F (finiteRectangleRefinement K N p) :=
      (Fintype.expect_equiv (finiteRectangleRefinement K N) _ _ (fun _ => rfl)).symm
    _ = _ := expect_prod_split _

end Erdos3

end

section

namespace Erdos3

theorem finiteRectangleRefinement_affine {I : Type*} (K N : I → ℕ) (u v : I → ℝ)
    (k : ∀ i, Fin (K i)) (t : ∀ i, Fin (N i)) :
    (fun i => u i + v i * (finiteRectangleRefinement K N (k, t) i).val) =
      fun i => progressionCellCorner N u v k i + v i * (t i).val := by
  funext i
  rw [finiteRectangleRefinement_val]
  simp only [Nat.cast_add, progressionCellCorner]
  ring

theorem progressionCell_dist_corner {I : Type*} [Fintype I]
    (K N : I → ℕ) (u v : I → ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hmesh : ∀ i, |v i| * N i ≤ δ)
    (k : ∀ i, Fin (K i)) (t : ∀ i, Fin (N i)) :
    dist (fun i => u i + v i * (finiteRectangleRefinement K N (k, t) i).val)
      (progressionCellCorner N u v k) ≤ δ := by
  rw [finiteRectangleRefinement_affine, dist_eq_norm]
  apply (pi_norm_le_iff_of_nonneg hδ).mpr
  intro i
  simp only [Pi.sub_apply, add_sub_cancel_left, norm_mul, Real.norm_eq_abs,
    abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (t i).val)]
  exact (mul_le_mul_of_nonneg_left
    (by exact_mod_cast (t i).isLt.le : ((t i).val : ℝ) ≤ N i) (abs_nonneg _)).trans (hmesh i)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

theorem norm_weighted_cell_replacement {C T : Type*} [Fintype C] [Fintype T]
    [Nonempty C] [Nonempty T] (w : C → T → ℝ) (c : C → ℝ) (F : C → T → ℂ)
    {ε : ℝ} (hw : ∀ k t, |w k t - c k| ≤ ε) (hF : ∀ k t, ‖F k t‖ ≤ 1) :
    ‖(𝔼 k, 𝔼 t, (w k t : ℂ) * F k t) -
      (𝔼 k, (c k : ℂ) * (𝔼 t, F k t))‖ ≤ ε := by
  have heq : (𝔼 k, 𝔼 t, (w k t : ℂ) * F k t) -
      (𝔼 k, (c k : ℂ) * (𝔼 t, F k t)) =
      𝔼 k, 𝔼 t, ((w k t - c k : ℝ) : ℂ) * F k t := by
    simp only [Complex.ofReal_sub, sub_mul, Finset.expect_sub_distrib, Finset.mul_expect]
  rw [heq]
  apply (RCLike.norm_expect_le (K := ℂ)).trans
  apply (Finset.expect_le_expect (fun k _ => RCLike.norm_expect_le (K := ℂ))).trans
  calc
    _ ≤ 𝔼 _k : C, 𝔼 _t : T, ε := by
      apply Finset.expect_le_expect
      intro k _
      apply Finset.expect_le_expect
      intro t _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact (mul_le_of_le_one_right (abs_nonneg _) (hF k t)).trans (hw k t)
    _ = ε := by simp

theorem exists_cell_of_weighted_bias {C T : Type*} [Fintype C] [Fintype T]
    [Nonempty C] [Nonempty T] (w : C → T → ℝ) (c : C → ℝ) (F : C → T → ℂ)
    {ζ ε B : ℝ} (hB : 0 < B) (hε : ε < ζ)
    (hc : ∀ k, 0 ≤ c k) (hmass : (𝔼 k, c k) ≤ B)
    (hw : ∀ k t, |w k t - c k| ≤ ε) (hF : ∀ k t, ‖F k t‖ ≤ 1)
    (hbias : ζ ≤ ‖𝔼 k, 𝔼 t, (w k t : ℂ) * F k t‖) :
    ∃ k, 0 < c k ∧ (ζ - ε) / B ≤ ‖𝔼 t, F k t‖ := by
  classical
  have he := norm_weighted_cell_replacement w c F hw hF
  have ht := norm_le_norm_sub_add (𝔼 j, 𝔼 t, (w j t : ℂ) * F j t)
    (𝔼 j, (c j : ℂ) * (𝔼 t, F j t))
  have hpos : (Finset.univ.filter (fun k => 0 < c k)).Nonempty := by
    by_contra h
    have hz (k) : c k = 0 := by
      have hn : ¬ 0 < c k := by
        intro hk
        exact h ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ k, hk⟩⟩
      exact le_antisymm (le_of_not_gt hn) (hc k)
    simp only [hz, Complex.ofReal_zero, zero_mul, Fintype.expect_const, sub_zero] at he
    linarith
  obtain ⟨k, hkpos, hk⟩ := Finset.exists_max_image _ (fun k => ‖𝔼 t, F k t‖) hpos
  have hupper : ‖𝔼 j, (c j : ℂ) * (𝔼 t, F j t)‖ ≤ B * ‖𝔼 t, F k t‖ := by
    apply (RCLike.norm_expect_le (K := ℂ)).trans
    calc
      _ ≤ 𝔼 j, c j * ‖𝔼 t, F k t‖ := by
        apply Finset.expect_le_expect
        intro j _
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hc j)]
        by_cases hj : 0 < c j
        · exact mul_le_mul_of_nonneg_left
            (hk j (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩)) (hc j)
        · rw [le_antisymm (le_of_not_gt hj) (hc j), zero_mul, zero_mul]
      _ = (𝔼 j, c j) * ‖𝔼 t, F k t‖ := (Finset.expect_mul _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hmass (norm_nonneg _)
  refine ⟨k, (Finset.mem_filter.mp hkpos).2, (div_le_iff₀ hB).mpr ?_⟩
  nlinarith

theorem exists_cell_of_lipschitz_weight {C T E : Type*} [Fintype C] [Fintype T]
    [Nonempty C] [Nonempty T] [PseudoMetricSpace E]
    (x : C → T → E) (a : C → E) (w : E → ℝ) (F : C → T → ℂ)
    {K : ℝ≥0} (hLip : LipschitzWith K w) {δ ζ B : ℝ}
    (hB : 0 < B) (hδ : (K : ℝ) * δ < ζ)
    (hw : ∀ k, 0 ≤ w (a k)) (hmass : (𝔼 k, w (a k)) ≤ B)
    (hcell : ∀ k t, dist (x k t) (a k) ≤ δ) (hF : ∀ k t, ‖F k t‖ ≤ 1)
    (hbias : ζ ≤ ‖𝔼 k, 𝔼 t, (w (x k t) : ℂ) * F k t‖) :
    ∃ k, 0 < w (a k) ∧ (ζ - K * δ) / B ≤ ‖𝔼 t, F k t‖ := by
  apply exists_cell_of_weighted_bias (fun k t => w (x k t)) (fun k => w (a k))
    F hB hδ hw hmass _ hF hbias
  intro k t
  have h := hLip.dist_le_mul (x k t) (a k)
  rw [Real.dist_eq] at h
  exact h.trans (mul_le_mul_of_nonneg_left (hcell k t) K.coe_nonneg)

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem scalarCubeBoundaryCutoff_lipschitz (I : Type*) [Fintype I] [DecidableEq I]
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition)
    {r : ℝ≥0} (hr : 0 < r) :
    LipschitzWith (scalarCubeCutoffLipschitzConstant I A r)
      (inequalityBoundaryCutoff (fun _ : Bool × Finset I => (r : ℝ)) scalarCubeFace) := by
  apply lipschitzWith_of_nnnorm_fderiv_le
    ((inequalityBoundaryCutoff_smooth _ _ scalarCubeFace_contDiff).differentiable (by norm_num))
  intro x
  apply NNReal.coe_le_coe.mp
  simpa only [scalarCubeCutoffLipschitzConstant, NNReal.coe_mul, NNReal.coe_div,
    NNReal.coe_natCast, NNReal.coe_add, NNReal.coe_one, coe_nnnorm] using
    scalarCubeBoundaryCutoff_fderiv_norm_le A hA (show (0 : ℝ) < r from hr) x

theorem scalarCubeFace_lipschitz {I : Type*} [Fintype I] [DecidableEq I]
    (i : Bool × Finset I) : LipschitzWith (Fintype.card I + 1 : ℝ≥0) (scalarCubeFace i) := by
  apply lipschitzWith_of_nnnorm_fderiv_le
    ((scalarCubeFace_contDiff i).differentiable (by norm_num))
  intro x
  apply NNReal.coe_le_coe.mp
  simpa only [NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one, coe_nnnorm] using
    scalarCubeFace_fderiv_norm_le i x

theorem scalarCubeBoundaryCutoff_near_support {I : Type*} [Fintype I] [DecidableEq I]
    {r δ : ℝ} (hr : 0 < r) {x y : Option I → ℝ}
    (hx : x ∈ tsupport
      (inequalityBoundaryCutoff (fun _ : Bool × Finset I => r) scalarCubeFace))
    (hxy : dist x y ≤ δ) (hδ : ((Fintype.card I : ℝ) + 1) * δ < r) :
    y ∈ scalarCubeDomain I := by
  rw [← positiveInequalityDomain_scalarCubeFace I]
  intro i
  have hface := inequalityBoundaryCutoff_tsupport_subset _ (fun _ => hr) _
    (fun i => (scalarCubeFace_contDiff i).continuous) hx i
  have hd := (scalarCubeFace_lipschitz i).dist_le_mul x y
  rw [Real.dist_eq] at hd
  simp only [NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one] at hd
  have hmul := mul_le_mul_of_nonneg_left hxy (by positivity : 0 ≤ (Fintype.card I : ℝ) + 1)
  have hu := (le_abs_self (scalarCubeFace i x - scalarCubeFace i y)).trans hd
  linarith

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

theorem exists_interior_progression_cell {I : Type*} [Fintype I] [DecidableEq I]
    (K N : I → ℕ) (hK : ∀ i, 0 < K i) (hN : ∀ i, 0 < N i) (u v : I → ℝ)
    (w : (I → ℝ) → ℝ) (D : Set (I → ℝ)) {Q : ℝ≥0} (hLip : LipschitzWith Q w)
    {δ ζ B : ℝ} (hδ : 0 ≤ δ) (hB : 0 < B) (herror : (Q : ℝ) * δ < ζ)
    (hmesh : ∀ i, |v i| * N i ≤ δ) (hw : ∀ x, 0 ≤ w x ∧ w x ≤ B)
    (hsafe : ∀ x, 0 < w x → ∀ y, dist y x ≤ δ → y ∈ D)
    (F : (∀ i, Fin (K i * N i)) → ℂ) (hF : ∀ x, ‖F x‖ ≤ 1)
    (hbias : ζ ≤ ‖𝔼 x, (w (fun i => u i + v i * (x i).val) : ℂ) * F x‖) :
    ∃ k : ∀ i, Fin (K i),
      (∀ t : ∀ i, Fin (N i),
        (fun i => progressionCellCorner N u v k i + v i * (t i).val) ∈ D) ∧
      (ζ - Q * δ) / B ≤ ‖𝔼 t, F (finiteRectangleRefinement K N (k, t))‖ := by
  let : ∀ i, Nonempty (Fin (K i)) := fun i => ⟨⟨0, hK i⟩⟩
  let : ∀ i, Nonempty (Fin (N i)) := fun i => ⟨⟨0, hN i⟩⟩
  have hb : ζ ≤ ‖𝔼 k, 𝔼 t,
      (w (fun i => u i + v i * (finiteRectangleRefinement K N (k, t) i).val) : ℂ) *
        F (finiteRectangleRefinement K N (k, t))‖ := by
    rwa [expect_finiteRectangleRefinement K N] at hbias
  obtain ⟨k, hk, hphase⟩ := exists_cell_of_lipschitz_weight
    (fun k t i => u i + v i * (finiteRectangleRefinement K N (k, t) i).val)
    (progressionCellCorner N u v) w (fun k t => F (finiteRectangleRefinement K N (k, t)))
    hLip hB herror (fun k => (hw _).1)
    ((Finset.expect_le_expect (fun k _ => (hw (progressionCellCorner N u v k)).2)).trans_eq
      (Fintype.expect_const B))
    (progressionCell_dist_corner K N u v hδ hmesh) (fun _ _ => hF _) hb
  refine ⟨k, fun t => ?_, hphase⟩
  have hd := hsafe _ hk _ (progressionCell_dist_corner K N u v hδ hmesh k t)
  rwa [finiteRectangleRefinement_affine] at hd

theorem scalarCube_cutoff_safe {I : Type*} [Fintype I] [DecidableEq I]
    {r δ : ℝ} (hr : 0 < r) (hδ : ((Fintype.card I : ℝ) + 1) * δ < r)
    (w : (Option I → ℝ) → ℝ)
    (hs : tsupport w ⊆ tsupport
      (inequalityBoundaryCutoff (fun _ : Bool × Finset I => r) scalarCubeFace)) :
    ∀ x, 0 < w x → ∀ y, dist y x ≤ δ → y ∈ scalarCubeDomain I := by
  intro x hx y hy
  exact scalarCubeBoundaryCutoff_near_support hr
    (hs (subset_closure (show x ∈ Function.support w from ne_of_gt hx)))
    (by rwa [dist_comm]) hδ

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

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LowWeightFibers
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

theorem reweight_complexMean {X : Type*} [Fintype X] (p : FiniteProbabilityWeights X)
    (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (htotal : p.mean w = 1) (F : X → ℂ) :
    (p.reweight w hw htotal).complexMean F = p.complexMean (fun x => (w x : ℂ) * F x) := by
  simp only [complexMean, reweight, Complex.ofReal_mul, mul_assoc]

end Erdos3.FiniteProbabilityWeights

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RepresentativeWindowPatch
namespace OAI

section

namespace Erdos3

open scoped NNReal

namespace FiniteProbabilityWeights

theorem norm_complexMean_weighted_cutoff_error {X : Type*} [Fintype X]
    (p : FiniteProbabilityWeights X) (b w : X → ℝ) (F : X → ℂ) {B : ℝ}
    (hb : ∀ x, b x ∈ Set.Icc (0 : ℝ) 1) (hw : ∀ x, |w x| ≤ B)
    (hF : ∀ x, ‖F x‖ ≤ 1) :
    ‖p.complexMean (fun x => (w x : ℂ) * F x) -
      p.complexMean (fun x => ((w x * b x : ℝ) : ℂ) * F x)‖ ≤
      B * p.mean (fun x => 1 - b x) := by
  rw [← p.mean_const_mul]
  apply p.norm_complexMean_sub_le
  intro x _
  have heq : (w x : ℂ) * F x - ((w x * b x : ℝ) : ℂ) * F x =
      ((1 - b x : ℝ) : ℂ) * ((w x : ℂ) * F x) := by push_cast; ring
  rw [heq, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real]
  simp only [Real.norm_eq_abs]
  rw [abs_of_nonneg (sub_nonneg.mpr (hb x).2)]
  have hweight := (mul_le_of_le_one_right (abs_nonneg (w x)) (hF x)).trans (hw x)
  exact (mul_le_mul_of_nonneg_left hweight (sub_nonneg.mpr (hb x).2)).trans_eq (mul_comm _ _)

theorem weighted_cutoff_bias_lower {X : Type*} [Fintype X]
    (p : FiniteProbabilityWeights X) (b w : X → ℝ) (F : X → ℂ) {B ζ ε : ℝ}
    (hB : 0 ≤ B) (hb : ∀ x, b x ∈ Set.Icc (0 : ℝ) 1) (hw : ∀ x, |w x| ≤ B)
    (hF : ∀ x, ‖F x‖ ≤ 1)
    (hbias : ζ ≤ ‖p.complexMean (fun x => (w x : ℂ) * F x)‖)
    (hloss : p.mean (fun x => 1 - b x) ≤ ε) :
    ζ - B * ε ≤ ‖p.complexMean (fun x => ((w x * b x : ℝ) : ℂ) * F x)‖ := by
  have he := (p.norm_complexMean_weighted_cutoff_error b w F hb hw hF).trans
    (mul_le_mul_of_nonneg_left hloss hB)
  have ht := norm_le_norm_sub_add (p.complexMean (fun x => (w x : ℂ) * F x))
    (p.complexMean (fun x => ((w x * b x : ℝ) : ℂ) * F x))
  linarith

end FiniteProbabilityWeights

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ScalarResidueInteriorCell
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem paddedIntegerPoint_injective {I : Type*} (L P : ℕ) :
    Function.Injective (paddedIntegerPoint (I := I) L P) := by
  intro x y h
  funext i
  apply Fin.ext
  have hi := congrFun h i
  dsimp only [paddedIntegerPoint] at hi
  omega

theorem paddedIntegerPoint_covers {I : Type*} {L P : ℕ} (hP : 2 * L ≤ P)
    (k : I → ℤ) (hk : ∀ i, -(L : ℤ) ≤ k i ∧ k i < L) :
    ∃ x : I → Fin P, paddedIntegerPoint L P x = k := by
  let x : I → Fin P := fun i => ⟨(k i + L).toNat, by
    have := hk i
    omega⟩
  refine ⟨x, ?_⟩
  funext i
  have := hk i
  dsimp only [paddedIntegerPoint, x]
  omega

theorem sum_eq_sum_of_cover_and_support {X Y V : Type*} [Fintype X]
    [DecidableEq Y] [AddCommMonoid V] (S : Finset Y) (e : X → Y)
    (he : Function.Injective e) (hcover : ∀ y ∈ S, ∃ x, e x = y)
    (F : Y → V) (hsupport : ∀ y, y ∉ S → F y = 0) :
    (∑ y ∈ S, F y) = ∑ x, F (e x) := by
  classical
  have hsub : S ⊆ Finset.univ.image e := by
    intro y hy
    obtain ⟨x, hx⟩ := hcover y hy
    exact Finset.mem_image.mpr ⟨x, Finset.mem_univ x, hx⟩
  calc
    _ = ∑ y ∈ Finset.univ.image e, F y :=
      Finset.sum_subset hsub (fun y _ hy => hsupport y hy)
    _ = _ := Finset.sum_image (fun _ _ _ _ h => he h)

theorem expect_eq_card_ratio_mul_expect {X Y : Type*} [Fintype X] [Nonempty X]
    [DecidableEq Y] (S : Finset Y) (e : X → Y) (he : Function.Injective e)
    (hcover : ∀ y ∈ S, ∃ x, e x = y) (F : Y → ℂ)
    (hsupport : ∀ y, y ∉ S → F y = 0) :
    (𝔼 y ∈ S, F y) = ((Fintype.card X : ℂ) / S.card) * 𝔼 x, F (e x) := by
  have hc : (Fintype.card X : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [Finset.expect_eq_sum_div_card, Fintype.expect_eq_sum_div_card,
    sum_eq_sum_of_cover_and_support S e he hcover F hsupport]
  field_simp

end Erdos3

end

section

namespace Erdos3

theorem residueCellCount_pos (L N : ℕ) : 0 < residueCellCount L N := by
  exact Nat.succ_pos _

theorem residueCellCount_padding {L N : ℕ} (hN : 0 < N) (hNL : N ≤ L) :
    2 * L ≤ residueCellCount L N * N ∧ residueCellCount L N * N ≤ 3 * L := by
  have hdiv := Nat.div_add_mod (2 * L) N
  have hmod := Nat.mod_lt (2 * L) hN
  unfold residueCellCount
  constructor
  · calc
      2 * L = N * (2 * L / N) + 2 * L % N := hdiv.symm
      _ ≤ N * (2 * L / N) + N := Nat.add_le_add_left hmod.le _
      _ = (2 * L / N + 1) * N := by ring
  · have hprod : N * (2 * L / N) ≤ 2 * L := by omega
    calc
      (2 * L / N + 1) * N = N * (2 * L / N) + N := by ring
      _ ≤ 2 * L + N := Nat.add_le_add_right hprod _
      _ ≤ 3 * L := by omega

theorem residueCellLength_bounds {δ : ℝ} {L M : ℕ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hL : 0 < L) (hM : 0 < M)
    (hlarge : 2 * (M : ℝ) ≤ δ * L) :
    0 < residueCellLength δ L M ∧ residueCellLength δ L M ≤ L ∧
      δ * L / (2 * M) ≤ (residueCellLength δ L M : ℝ) ∧
      (M : ℝ) / L * residueCellLength δ L M ≤ δ := by
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hx0 : 0 ≤ δ * L / M := by positivity
  have hx2 : 2 ≤ δ * L / M := (le_div_iff₀ hM').mpr hlarge
  have hfloor := Nat.floor_le hx0
  have hceil := Nat.lt_floor_add_one (δ * L / M)
  have hpos : 0 < residueCellLength δ L M := by
    unfold residueCellLength
    apply Nat.floor_pos.mpr
    linarith
  have hxL : δ * L / M ≤ L := by
    apply (div_le_iff₀ hM').mpr
    nlinarith
  have hNL : residueCellLength δ L M ≤ L := by
    exact_mod_cast hfloor.trans hxL
  refine ⟨hpos, hNL, ?_, ?_⟩
  · change δ * L / (2 * M) ≤ (⌊δ * L / M⌋₊ : ℝ)
    have he : δ * L / (2 * M) = (δ * L / M) / 2 := by ring
    rw [he]
    have hp : (1 : ℝ) ≤ ⌊δ * L / M⌋₊ := by exact_mod_cast hpos
    linarith
  · have hmul := (le_div_iff₀ hM').mp hfloor
    change (M : ℝ) / L * (⌊δ * L / M⌋₊ : ℝ) ≤ δ
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hL').mpr
    nlinarith

theorem residueCellLength_stride_mesh {δ : ℝ} {L M : ℕ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hL : 0 < L) (hM : 0 < M)
    (hlarge : 2 * (M : ℝ) ≤ δ * L) {m : ℕ} (hm : m ≤ M) :
    |(m : ℝ) / L| * residueCellLength δ L M ≤ δ := by
  rw [abs_of_nonneg (by positivity : 0 ≤ (m : ℝ) / L)]
  apply le_trans _ (residueCellLength_bounds hδ hδ1 hL hM hlarge).2.2.2
  exact mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right (by exact_mod_cast hm) (by positivity)) (by positivity)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem scalarCubeResidueWeights_grid_mean (I : Type*) [Fintype I] [DecidableEq I]
    (L M : ℕ) (hL : 0 < L) (m : Option I → ℕ) (r : ∀ i, ZMod (m i))
    (hm : ∀ i, 0 < m i) (hmM : ∀ i, m i ≤ M) (hsize : (Fintype.card I + 1)*M ≤ L)
    (φ : (Option I → ℝ) → ℝ) :
    (scalarCubeResidueWeights I L M hL m r hm hmM hsize).mean
      (fun z => φ (fun i => (z i : ℝ) / L)) =
      𝔼 k ∈ scalarCubeGridSet I (scalarResidueGridOffset m r) (scalarResidueGridScale L m),
        φ (rectangularLatticePoint (scalarResidueGridOffset m r) (scalarResidueGridScale L m) k) := by
  rw [scalarCubeResidueWeights_mean]
  let e := scalarCubeResidueGridEquiv I L hL m r hm
  have he (k : ↥(scalarCubeGridSet I (scalarResidueGridOffset m r) (scalarResidueGridScale L m))) :
      rectangularLatticePoint (scalarResidueGridOffset m r) (scalarResidueGridScale L m) k.val =
        fun i => ((e k).val i : ℝ) / L := by
    rw [scalarResidueGrid_normalized hL m r hm]
    funext i
    rfl
  calc
    _ = 𝔼 k : ↥(scalarCubeGridSet I (scalarResidueGridOffset m r) (scalarResidueGridScale L m)),
        φ (rectangularLatticePoint (scalarResidueGridOffset m r) (scalarResidueGridScale L m) k.val) := by
      symm
      exact Fintype.expect_equiv e _ _ (fun k => congrArg φ (he k))
    _ = _ := by
      rw [Fintype.expect_eq_sum_div_card, Finset.expect_eq_sum_div_card, Fintype.card_coe]
      congr 1
      exact Finset.sum_coe_sort _ (fun k =>
        φ (rectangularLatticePoint (scalarResidueGridOffset m r) (scalarResidueGridScale L m) k))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem FiniteProbabilityWeights.complexMean_im {X : Type*} [Fintype X]
    (p : FiniteProbabilityWeights X) (F : X → ℂ) :
    (p.complexMean F).im = p.mean (fun x => (F x).im) := by
  simp [complexMean, mean, Complex.mul_im]

theorem scalarCubeResidueWeights_grid_complexMean (I : Type*) [Fintype I] [DecidableEq I]
    (L M : ℕ) (hL : 0 < L) (m : Option I → ℕ) (r : ∀ i, ZMod (m i))
    (hm : ∀ i, 0 < m i) (hmM : ∀ i, m i ≤ M) (hsize : (Fintype.card I + 1)*M ≤ L)
    (F : (Option I → ℝ) → ℂ) :
    (scalarCubeResidueWeights I L M hL m r hm hmM hsize).complexMean
      (fun z => F (fun i => (z i : ℝ) / L)) =
      𝔼 k ∈ scalarCubeGridSet I (scalarResidueGridOffset m r) (scalarResidueGridScale L m),
        F (rectangularLatticePoint (scalarResidueGridOffset m r) (scalarResidueGridScale L m) k) := by
  apply Complex.ext
  · rw [FiniteProbabilityWeights.complexMean_re, Complex.re_expect]
    exact scalarCubeResidueWeights_grid_mean I L M hL m r hm hmM hsize (fun x => (F x).re)
  · rw [FiniteProbabilityWeights.complexMean_im, Complex.im_expect]
    exact scalarCubeResidueWeights_grid_mean I L M hL m r hm hmM hsize (fun x => (F x).im)

end Erdos3

end

section

namespace Erdos3

theorem residue_index_bounds {L m : ℕ} (hm : 0 < m) (r : ZMod m) (k : ℤ)
    (hk : -(L : ℤ) < (r.val : ℤ) + m * k ∧ (r.val : ℤ) + m * k < L) :
    -(L : ℤ) ≤ k ∧ k < L := by
  let : NeZero m := ⟨hm.ne'⟩
  have hm' : (1 : ℤ) ≤ m := by exact_mod_cast hm
  have hr : (r.val : ℤ) < m := by exact_mod_cast ZMod.val_lt r
  have hr0 : (0 : ℤ) ≤ r.val := by positivity
  constructor
  · by_contra! h
    have hmul := mul_le_mul_of_nonneg_left (show k ≤ -(L : ℤ) - 1 by omega) (by positivity : (0 : ℤ) ≤ m)
    have hsize := mul_le_mul_of_nonneg_right hm' (by positivity : (0 : ℤ) ≤ L)
    nlinarith [hk.1]
  · by_contra! h
    have hmul := mul_le_mul_of_nonneg_left h (by positivity : (0 : ℤ) ≤ m)
    have hsize := mul_le_mul_of_nonneg_right hm' (by positivity : (0 : ℤ) ≤ L)
    nlinarith [hk.2]

theorem scalarCubeResidueGrid_index_bounds {I : Type*} [Fintype I] [DecidableEq I]
    {L : ℕ} (hL : 0 < L) (m : Option I → ℕ) (r : ∀ i, ZMod (m i))
    (hm : ∀ i, 0 < m i) (k : Option I → ℤ)
    (hk : k ∈ scalarCubeGridSet I (scalarResidueGridOffset m r) (scalarResidueGridScale L m)) :
    ∀ i, -(L : ℤ) ≤ k i ∧ k i < L := by
  have hx := (mem_scalarCubeGridSet _ _ (scalarResidueGridScale_pos hL m hm) k).mp hk
  rw [scalarResidueGrid_normalized hL m r hm] at hx
  have hc := (integerScalarCube_iff_normalized hL _).mpr hx
  intro i
  exact residue_index_bounds (hm i) (r i) (k i) (integerScalarCube_coordinates hc i)

theorem scalarCubeResidueGrid_padded_cover {I : Type*} [Fintype I] [DecidableEq I]
    {L P : ℕ} (hL : 0 < L) (hP : 2 * L ≤ P)
    (m : Option I → ℕ) (r : ∀ i, ZMod (m i)) (hm : ∀ i, 0 < m i)
    (k : Option I → ℤ)
    (hk : k ∈ scalarCubeGridSet I (scalarResidueGridOffset m r) (scalarResidueGridScale L m)) :
    ∃ x : Option I → Fin P, paddedIntegerPoint L P x = k :=
  paddedIntegerPoint_covers hP k (scalarCubeResidueGrid_index_bounds hL m r hm k hk)

end Erdos3

end

section

namespace Erdos3

theorem paddedResidueCoordinates_eq {I : Type*} [Fintype I] {L P : ℕ} (hL : 0 < L)
    (m : Option I → ℕ) (r : ∀ i, ZMod (m i)) (hm : ∀ i, 0 < m i)
    (x : Option I → Fin P) :
    rectangularLatticePoint (scalarResidueGridOffset m r) (scalarResidueGridScale L m)
      (paddedIntegerPoint L P x) =
      fun i => paddedResidueOffset L m r i + paddedResidueStep L m i * (x i).val := by
  rw [scalarResidueGrid_normalized hL m r hm]
  funext i
  simp only [scalarResidueGridPoint, paddedIntegerPoint, paddedResidueOffset,
    paddedResidueStep, Int.cast_add, Int.cast_mul, Int.cast_sub, Int.cast_natCast]
  ring

theorem scalarCubeResidueGrid_card (I : Type*) [Fintype I] [DecidableEq I]
    {L : ℕ} (hL : 0 < L) (m : Option I → ℕ) (r : ∀ i, ZMod (m i))
    (hm : ∀ i, 0 < m i) :
    (scalarCubeGridSet I (scalarResidueGridOffset m r) (scalarResidueGridScale L m)).card =
      ((integerScalarCubeSet I L) ∩ scalarCubeResidueSet I L m r).card := by
  simpa only [Fintype.card_coe] using Fintype.card_congr (scalarCubeResidueGridEquiv I L hL m r hm)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

theorem scalarCubeResidueCutoff_loss (I : Type*) [Fintype I] [DecidableEq I]
    (L M : ℕ) (hL : 0 < L) (m : Option I → ℕ) (res : ∀ i, ZMod (m i))
    (hm : ∀ i, 0 < m i) (hmM : ∀ i, m i ≤ M)
    (hsize : (Fintype.card I + 1) * M ≤ L)
    (hsmall : scalarCubeGridBoundaryConstant I * ((M : ℝ) / L) <
      volume.real (scalarCubeDomain I))
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition)
    {r : ℝ≥0} (hr : 0 < r) :
    (scalarCubeResidueWeights I L M hL m res hm hmM hsize).mean
      (fun z => 1 - inequalityBoundaryCutoff (fun _ : Bool × Finset I => (r : ℝ))
        scalarCubeFace (fun i => (z i : ℝ) / L)) ≤
      scalarCubeResidueCutoffBudget I A r L M := by
  let b := inequalityBoundaryCutoff (fun _ : Bool × Finset I => (r : ℝ)) scalarCubeFace
  have hLip : LipschitzWith (scalarCubeCutoffLipschitzConstant I A r)
      (fun x => 1 - b x) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq, show (1 - b x) - (1 - b y) = b y - b x by ring, abs_sub_comm]
    exact (scalarCubeBoundaryCutoff_lipschitz I A hA hr).dist_le_mul x y
  have hbound (x : Option I → ℝ) : ‖1 - b x‖ ≤ 1 := by
    have h := inequalityBoundaryCutoff_range (fun _ : Bool × Finset I => (r : ℝ)) scalarCubeFace x
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr h.2)]
    linarith [h.1]
  have hquad := scalarCubeResidueWeights_riemann_s2 I L M hL m res hm hmM hsize hsmall
    (fun x => 1 - b x) hLip zero_le_one hbound
  have hcont := scalarCubeBoundaryCutoff_mass_loss I (show (0 : ℝ) < r from hr)
  have hu := (le_abs_self _).trans hquad
  dsimp only [scalarCubeResidueCutoffBudget]
  dsimp only [b] at hu
  linarith

end Erdos3

end

section

namespace Erdos3

theorem scalarCubeResidue_card_pos (I : Type*) [Fintype I] [DecidableEq I]
    (L M : ℕ) (hL : 0 < L) (m : Option I → ℕ) (r : ∀ i, ZMod (m i))
    (hm : ∀ i, 0 < m i) (hmM : ∀ i, m i ≤ M)
    (hsize : (Fintype.card I + 1) * M ≤ L) :
    0 < ((integerScalarCubeSet I L) ∩ scalarCubeResidueSet I L m r).card := by
  have hcap := scalarCubeResidueDensityCap_pos I M ((hm none).trans_le (hmM none))
  have h := scalarCubeResidueReference_mass_lower I L M hL m r hm hmM hsize
  let : Nonempty (IntegerScalarCubeBox I L) := ⟨integerScalarCubeBoxZero I L hL⟩
  rw [integerScalarCubeReference, FiniteProbabilityWeights.uniform_mass] at h
  by_contra! hz
  have hzero : ((integerScalarCubeSet I L) ∩ scalarCubeResidueSet I L m r).card = 0 := by omega
  rw [hzero, Nat.cast_zero, zero_div] at h
  exact (not_le_of_gt (inv_pos.mpr hcap)) h

theorem paddedResidueDensityFactor_pos (I : Type*) [Fintype I] [DecidableEq I]
    (L M P : ℕ) (hL : 0 < L) (hP : 0 < P)
    (m : Option I → ℕ) (r : ∀ i, ZMod (m i)) (hm : ∀ i, 0 < m i)
    (hmM : ∀ i, m i ≤ M) (hsize : (Fintype.card I + 1) * M ≤ L) :
    0 < paddedResidueDensityFactor I L P m r := by
  apply div_pos (pow_pos (by exact_mod_cast hP) _)
  exact_mod_cast scalarCubeResidue_card_pos I L M hL m r hm hmM hsize

theorem paddedResidueDensityFactor_le (I : Type*) [Fintype I] [DecidableEq I]
    (L M P : ℕ) (hL : 0 < L) (hP : P ≤ 4 * L)
    (m : Option I → ℕ) (r : ∀ i, ZMod (m i)) (hm : ∀ i, 0 < m i)
    (hmM : ∀ i, m i ≤ M) (hsize : (Fintype.card I + 1) * M ≤ L) :
    paddedResidueDensityFactor I L P m r ≤ paddedResidueDensityCap I M := by
  let S := (integerScalarCubeSet I L) ∩ scalarCubeResidueSet I L m r
  have hS : (0 : ℝ) < S.card := by
    exact_mod_cast scalarCubeResidue_card_pos I L M hL m r hm hmM hsize
  have hcap := scalarCubeResidueDensityCap_pos I M ((hm none).trans_le (hmM none))
  have hbase : (0 : ℝ) < (2 * (L : ℝ)) ^ (Fintype.card I + 1) := by positivity
  have h := scalarCubeResidueReference_mass_lower I L M hL m r hm hmM hsize
  let : Nonempty (IntegerScalarCubeBox I L) := ⟨integerScalarCubeBoxZero I L hL⟩
  rw [integerScalarCubeReference, FiniteProbabilityWeights.uniform_mass,
    integerScalarCubeBox_card] at h
  push_cast at h
  have hmass : (2 * (L : ℝ)) ^ (Fintype.card I + 1) ≤
      S.card * scalarCubeResidueDensityCap I M := by
    have hh : 1 / scalarCubeResidueDensityCap I M ≤
        (S.card : ℝ) / (2 * (L : ℝ)) ^ (Fintype.card I + 1) := by
      simpa only [one_div, S] using h
    simpa only [one_mul] using (div_le_div_iff₀ hcap hbase).mp hh
  apply (div_le_iff₀ hS).mpr
  calc
    (P : ℝ) ^ (Fintype.card I + 1) ≤ (2 * (2 * (L : ℝ))) ^ (Fintype.card I + 1) :=
      pow_le_pow_left₀ (Nat.cast_nonneg P)
        (by exact_mod_cast (show P ≤ 2 * (2 * L) by omega)) _
    _ = 2 ^ (Fintype.card I + 1) * (2 * (L : ℝ)) ^ (Fintype.card I + 1) := mul_pow _ _ _
    _ ≤ 2 ^ (Fintype.card I + 1) * (S.card * scalarCubeResidueDensityCap I M) :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = paddedResidueDensityCap I M * S.card := by unfold paddedResidueDensityCap; ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem scalarCubeResidueWeights_padded_mean (I : Type*) [Fintype I] [DecidableEq I]
    (L M P : ℕ) (hL : 0 < L) (hP : 2 * L ≤ P)
    (m : Option I → ℕ) (r : ∀ i, ZMod (m i)) (hm : ∀ i, 0 < m i)
    (hmM : ∀ i, m i ≤ M) (hsize : (Fintype.card I + 1) * M ≤ L)
    (w : (Option I → ℝ) → ℝ) (hw : Function.support w ⊆ halfOpenScalarCubeDomain I)
    (F : (Option I → ℝ) → ℂ) :
    (scalarCubeResidueWeights I L M hL m r hm hmM hsize).complexMean
      (fun z => (w (fun i => (z i : ℝ) / L) : ℂ) * F (fun i => (z i : ℝ) / L)) =
      𝔼 x : Option I → Fin P,
        ((paddedResidueDensityFactor I L P m r *
          w (fun i => paddedResidueOffset L m r i + paddedResidueStep L m i * (x i).val) : ℝ) : ℂ) *
        F (fun i => paddedResidueOffset L m r i + paddedResidueStep L m i * (x i).val) := by
  have hPpos : 0 < P := by omega
  let : Nonempty (Fin P) := ⟨⟨0, hPpos⟩⟩
  let S := scalarCubeGridSet I (scalarResidueGridOffset m r) (scalarResidueGridScale L m)
  let f := fun k => (w (rectangularLatticePoint (scalarResidueGridOffset m r)
    (scalarResidueGridScale L m) k) : ℂ) *
    F (rectangularLatticePoint (scalarResidueGridOffset m r) (scalarResidueGridScale L m) k)
  have hsupport (k) (hk : k ∉ S) : f k = 0 := by
    have hz : w (rectangularLatticePoint (scalarResidueGridOffset m r)
        (scalarResidueGridScale L m) k) = 0 := by
      by_contra h
      exact hk ((mem_scalarCubeGridSet _ _ (scalarResidueGridScale_pos hL m hm) k).mpr (hw h))
    simp only [f, hz, Complex.ofReal_zero, zero_mul]
  rw [scalarCubeResidueWeights_grid_complexMean I L M hL m r hm hmM hsize
    (fun y => (w y : ℂ) * F y)]
  change (𝔼 k ∈ S, f k) = _
  rw [expect_eq_card_ratio_mul_expect S (paddedIntegerPoint L P)
    (paddedIntegerPoint_injective L P)
    (scalarCubeResidueGrid_padded_cover hL hP m r hm) f hsupport]
  have hfactor : (Fintype.card (Option I → Fin P) : ℂ) / S.card =
      (paddedResidueDensityFactor I L P m r : ℂ) := by
    simp only [Fintype.card_fun, Fintype.card_option, Fintype.card_fin, S,
      scalarCubeResidueGrid_card I hL m r hm, paddedResidueDensityFactor,
      Nat.cast_pow, Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_natCast]
  rw [hfactor, Finset.mul_expect]
  apply Finset.expect_congr rfl
  intro x _
  dsimp only [f]
  rw [paddedResidueCoordinates_eq hL m r hm x, Complex.ofReal_mul, mul_assoc]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem scalarCubeResidueWeights_padded_bias (I : Type*) [Fintype I] [DecidableEq I]
    (L M P : ℕ) (hL : 0 < L) (hP : 2 * L ≤ P) (hPupper : P ≤ 4 * L)
    (m : Option I → ℕ) (r : ∀ i, ZMod (m i)) (hm : ∀ i, 0 < m i)
    (hmM : ∀ i, m i ≤ M) (hsize : (Fintype.card I + 1) * M ≤ L)
    (w : (Option I → ℝ) → ℝ) (hw : Function.support w ⊆ halfOpenScalarCubeDomain I)
    (F : (Option I → ℝ) → ℂ) {ζ : ℝ}
    (hbias : ζ ≤ ‖(scalarCubeResidueWeights I L M hL m r hm hmM hsize).complexMean
      (fun z => (w (fun i => (z i : ℝ) / L) : ℂ) * F (fun i => (z i : ℝ) / L))‖) :
    ζ / paddedResidueDensityCap I M ≤
      ‖𝔼 x : Option I → Fin P,
        (w (fun i => paddedResidueOffset L m r i + paddedResidueStep L m i * (x i).val) : ℂ) *
        F (fun i => paddedResidueOffset L m r i + paddedResidueStep L m i * (x i).val)‖ := by
  have hcap : 0 < paddedResidueDensityCap I M := by
    unfold paddedResidueDensityCap
    exact mul_pos (by positivity)
      (scalarCubeResidueDensityCap_pos I M ((hm none).trans_le (hmM none)))
  have hfactor := paddedResidueDensityFactor_pos I L M P hL (by omega) m r hm hmM hsize
  have hle := paddedResidueDensityFactor_le I L M P hL hPupper m r hm hmM hsize
  have hlaw := scalarCubeResidueWeights_padded_mean I L M P hL hP m r hm hmM hsize w hw F
  simp only [Complex.ofReal_mul, mul_assoc, ← Finset.mul_expect] at hlaw
  rw [hlaw, norm_mul, Complex.norm_real, Real.norm_of_nonneg hfactor.le] at hbias
  apply (div_le_iff₀ hcap).mpr
  exact hbias.trans ((mul_le_mul_of_nonneg_right hle (norm_nonneg _)).trans_eq (mul_comm _ _))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.WeightedScalarResidueCell
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

theorem scalarCubeResidue_supported_weight_cell (I : Type*) [Fintype I] [DecidableEq I]
    (L M N K : ℕ) (hL : 0 < L) (hN : 0 < N) (hK : 0 < K)
    (hcover : 2 * L ≤ K * N) (hupper : K * N ≤ 4 * L)
    (m : Option I → ℕ) (res : ∀ i, ZMod (m i))
    (hm : ∀ i, 0 < m i) (hmM : ∀ i, m i ≤ M)
    (hsize : (Fintype.card I + 1) * M ≤ L)
    (w : (Option I → ℝ) → ℝ) {Q : ℝ≥0} (hLip : LipschitzWith Q w)
    {δ η ζ B : ℝ} (hδ : 0 ≤ δ) (hη : 0 < η) (hB : 0 < B)
    (hmesh : ∀ i, |paddedResidueStep L m i| * N ≤ δ)
    (hw : ∀ x, 0 ≤ w x ∧ w x ≤ B)
    (hsupport : Function.support w ⊆ halfOpenScalarCubeDomain I)
    (hsafe : ∀ x, 0 < w x → ∀ y, dist y x ≤ δ → y ∈ scalarCubeDomain I)
    (herror : paddedResidueDensityCap I M * (Q * δ + B * η) ≤ ζ)
    (F : (Option I → ℝ) → ℂ) (hF : ∀ x, ‖F x‖ ≤ 1)
    (hbias : ζ ≤ ‖(scalarCubeResidueWeights I L M hL m res hm hmM hsize).complexMean
      (fun z => (w (fun i => (z i : ℝ) / L) : ℂ) * F (fun i => (z i : ℝ) / L))‖) :
    ∃ k : Option I → Fin K,
      (∀ t : Option I → Fin N, residueCellPosition L N K m res k t ∈ scalarCubeDomain I) ∧
      η ≤ ‖𝔼 t : Option I → Fin N, F (residueCellPosition L N K m res k t)‖ := by
  have hcap : 0 < paddedResidueDensityCap I M := by
    exact mul_pos (by positivity)
      (scalarCubeResidueDensityCap_pos I M ((hm none).trans_le (hmM none)))
  have hpad := scalarCubeResidueWeights_padded_bias I L M (K * N) hL hcover hupper
    m res hm hmM hsize w hsupport F hbias
  have hthreshold : Q * δ + B * η ≤ ζ / paddedResidueDensityCap I M := by
    apply (le_div_iff₀ hcap).mpr
    nlinarith
  have hpad' := hthreshold.trans hpad
  obtain ⟨k, hinside, hphase⟩ := exists_interior_progression_cell
    (fun _ : Option I => K) (fun _ => N) (fun _ => hK) (fun _ => hN)
    (paddedResidueOffset L m res) (paddedResidueStep L m) w (scalarCubeDomain I)
    hLip hδ hB (show (Q : ℝ) * δ < Q * δ + B * η by nlinarith)
    hmesh hw hsafe
    (fun x => F (fun i => paddedResidueOffset L m res i + paddedResidueStep L m i * (x i).val))
    (fun x => hF _) hpad'
  refine ⟨k, hinside, ?_⟩
  have he (t : Option I → Fin N) := finiteRectangleRefinement_affine
    (fun _ : Option I => K) (fun _ => N) (paddedResidueOffset L m res) (paddedResidueStep L m) k t
  have hmean :
      (𝔼 t : Option I → Fin N, F (fun i => paddedResidueOffset L m res i +
        paddedResidueStep L m i *
          (finiteRectangleRefinement (fun _ : Option I => K) (fun _ => N) (k, t) i).val)) =
      𝔼 t : Option I → Fin N, F (residueCellPosition L N K m res k t) := by
    apply Finset.expect_congr rfl
    intro t _
    exact congrArg F (he t)
  rw [hmean] at hphase
  simpa only [add_sub_cancel_left, mul_div_cancel_left₀ _ hB.ne'] using hphase

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

theorem scalarCubeResidue_weighted_interior_cell (I : Type*) [Fintype I] [DecidableEq I]
    (L M : ℕ) (hL : 0 < L) (m : Option I → ℕ) (res : ∀ i, ZMod (m i))
    (hm : ∀ i, 0 < m i) (hmM : ∀ i, m i ≤ M)
    (hsize : (Fintype.card I + 1) * M ≤ L)
    (hsmall : scalarCubeGridBoundaryConstant I * ((M : ℝ) / L) <
      volume.real (scalarCubeDomain I))
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) {r : ℝ≥0} (hr : 0 < r)
    (w : (Option I → ℝ) → ℝ) {B T : ℝ≥0} (hB : 0 < B)
    (hw : ∀ x, 0 ≤ w x ∧ w x ≤ B) (hLip : LipschitzWith T w)
    {δ η ζ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hη : 0 < η)
    (hlarge : 2 * (M : ℝ) ≤ δ * L)
    (hmargin : ((Fintype.card I : ℝ) + 1) * δ < r)
    (herror : B * scalarCubeResidueCutoffBudget I A r L M +
      paddedResidueDensityCap I M *
        (((T : ℝ) + B * scalarCubeCutoffLipschitzConstant I A r) * δ + B * η) ≤ ζ)
    (F : (Option I → ℝ) → ℂ) (hF : ∀ x, ‖F x‖ ≤ 1)
    (hbias : ζ ≤ ‖(scalarCubeResidueWeights I L M hL m res hm hmM hsize).complexMean
      (fun z => (w (fun i => (z i : ℝ) / L) : ℂ) * F (fun i => (z i : ℝ) / L))‖) :
    let N := residueCellLength δ L M
    let K := residueCellCount L N
    ∃ k : Option I → Fin K,
      (∀ t : Option I → Fin N, residueCellPosition L N K m res k t ∈ scalarCubeDomain I) ∧
      η ≤ ‖𝔼 t : Option I → Fin N, F (residueCellPosition L N K m res k t)‖ := by
  let N := residueCellLength δ L M
  let K := residueCellCount L N
  have hM : 0 < M := (hm none).trans_le (hmM none)
  have hN := residueCellLength_bounds hδ hδ1 hL hM hlarge
  have hP : 2 * L ≤ K * N ∧ K * N ≤ 3 * L := residueCellCount_padding hN.1 hN.2.1
  let b := inequalityBoundaryCutoff (fun _ : Bool × Finset I => (r : ℝ)) scalarCubeFace
  let g := fun x => w x * b x
  have hb (x) : b x ∈ Set.Icc (0 : ℝ) 1 := inequalityBoundaryCutoff_range _ _ x
  have hwabs (x) : |w x| ≤ B := by rw [abs_of_nonneg (hw x).1]; exact (hw x).2
  have hbabs (x) : |b x| ≤ 1 := by rw [abs_of_nonneg (hb x).1]; exact (hb x).2
  have hglip : LipschitzWith (T + B * scalarCubeCutoffLipschitzConstant I A r) g :=
    bounded_weight_cutoff_lipschitz w b hwabs hbabs hLip (scalarCubeBoundaryCutoff_lipschitz I A hA hr)
  have hg (x) : 0 ≤ g x ∧ g x ≤ B :=
    ⟨mul_nonneg (hw x).1 (hb x).1,
      (mul_le_of_le_one_right (hw x).1 (hb x).2).trans (hw x).2⟩
  have hsupport : Function.support g ⊆ halfOpenScalarCubeDomain I := by
    intro x hx
    exact scalarCubeDomain_subset_halfOpen I
      (scalarCubeBoundaryCutoff_tsupport_domain I (show (0 : ℝ) < r from hr)
        (tsupport_mul_subset_right (subset_closure hx)))
  have hsafe := scalarCube_cutoff_safe (show (0 : ℝ) < r from hr) hmargin g tsupport_mul_subset_right
  have hcut := FiniteProbabilityWeights.weighted_cutoff_bias_lower
    (scalarCubeResidueWeights I L M hL m res hm hmM hsize)
    (fun z => b (fun i => (z i : ℝ) / L)) (fun z => w (fun i => (z i : ℝ) / L))
    (fun z => F (fun i => (z i : ℝ) / L)) B.coe_nonneg
    (fun z => hb _) (fun z => hwabs _) (fun z => hF _) hbias
    (scalarCubeResidueCutoff_loss I L M hL m res hm hmM hsize hsmall A hA hr)
  apply scalarCubeResidue_supported_weight_cell I L M N K hL hN.1
    (residueCellCount_pos L N) hP.1 (by omega) m res hm hmM hsize g hglip
    hδ.le hη (show (0 : ℝ) < B from hB)
    (fun i => residueCellLength_stride_mesh hδ hδ1 hL hM hlarge (hmM i))
    hg hsupport hsafe _ F hF hcut
  simp only [NNReal.coe_add, NNReal.coe_mul]
  linarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoefficientSliceEmbedding
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

namespace ScalarCubeLocalizationData

variable {I : Type*} [Fintype I] [DecidableEq I] (d : ScalarCubeLocalizationData I)

theorem source_complexMean (F : (Option I → ℝ) → ℂ) :
    d.source.complexMean (fun z => F (d.point z)) =
      d.baseLaw.complexMean (fun z => (d.weight (d.point z) : ℂ) * F (d.point z)) :=
  d.baseLaw.reweight_complexMean _ _ _ _

theorem localize_s2_oai {ζ η : ℝ} (hη : 0 < η) (herror : d.error η ≤ ζ)
    (F : (Option I → ℝ) → ℂ) (hF : ∀ x, ‖F x‖ ≤ 1)
    (hbias : ζ ≤ ‖d.source.complexMean (fun z => F (d.point z))‖) :
    ∃ k : Option I → Fin d.cellCount,
      (∀ t : Option I → Fin d.cellLength, d.cell k t ∈ scalarCubeDomain I) ∧
      η ≤ ‖𝔼 t : Option I → Fin d.cellLength, F (d.cell k t)‖ := by
  rw [d.source_complexMean] at hbias
  exact scalarCubeResidue_weighted_interior_cell I d.length d.modulusBound d.length_pos
    d.modulus d.residue d.modulus_pos d.modulus_le d.size d.gridSmall
    d.transitionBound d.transition_lipschitz d.radius_pos d.weight d.weightBound_pos
    d.weight_range d.weight_lipschitz d.mesh_pos d.mesh_le_one hη d.meshLarge d.margin
    herror F hF hbias

end ScalarCubeLocalizationData

end Erdos3

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Erdos3.ScalarCubeLocalizationData.localize_s2_oai.{u_1} := @OAI.Erdos3.ScalarCubeLocalizationData.localize_s2_oai.{u_1}
