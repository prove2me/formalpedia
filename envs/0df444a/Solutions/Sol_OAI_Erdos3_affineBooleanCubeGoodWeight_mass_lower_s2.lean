-- Prove2me | solution 1 for OAI.Erdos3.affineBooleanCubeGoodWeight_mass_lower_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-17T10:49:12.484279+00:00
-- url     : https://prove2.me/submissions/5ec62406-c6ee-4569-9068-789c3cb695c6

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B112
import Definitions.Def_OAIE3v2B113

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

open scoped ContDiff

theorem booleanMinorDeterminant_contDiff {B O F α : Type*}
    [Fintype B] [Fintype O] [Fintype F] [Fintype α]
    [DecidableEq B] [DecidableEq O] [DecidableEq F] [DecidableEq α]
    (c : B → ℝ) (sets : O → Finset α) (block : O → B) (v : F) (r : O → Option α) :
    ContDiff ℝ ∞ (booleanMinorDeterminant c sets block v r) := by
  change ContDiff ℝ ∞ (fun a => ((booleanSelectedMinor c sets block v r).map (MvPolynomial.eval a)).det)
  rw [polynomial_det_eval_function]
  exact mvPolynomial_contDiff_eval _

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SmoothSublevelCutoff
namespace OAI

section

namespace Erdos3

open scoped NNReal ContDiff

theorem sublevelCutoff_range {E : Type*} (ψ : ℝ → ℝ)
    (hψ : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1) (r : ℝ) (d : E → ℝ) (x : E) :
    sublevelCutoff ψ r d x ∈ Set.Icc (0 : ℝ) 1 := hψ _

theorem sublevelCutoff_eq_one {E : Type*} (ψ : ℝ → ℝ)
    (hψ : ∀ t, 2 ≤ |t| → ψ t = 1) {r : ℝ} (hr : 0 < r)
    (d : E → ℝ) {x : E} (hx : 2 * r ≤ |d x|) : sublevelCutoff ψ r d x = 1 := by
  apply hψ
  rw [abs_div, abs_of_pos hr]
  exact (le_div_iff₀ hr).mpr hx

theorem contDiff_sublevelCutoff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (r : ℝ) (d : E → ℝ)
    (hd : ContDiff ℝ ∞ d) : ContDiff ℝ ∞ (sublevelCutoff ψ r d) :=
  hψ.comp (hd.div_const r)

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
open scoped NNReal ContDiff

theorem sublevelCutoff_integral_loss_le {E : Type*} [MeasurableSpace E]
    (μ : Measure E) [IsFiniteMeasure μ] (ψ : ℝ → ℝ) (hψ : Measurable ψ)
    (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hone : ∀ t, 2 ≤ |t| → ψ t = 1) {r : ℝ} (hr : 0 < r)
    (d : E → ℝ) (hd : Measurable d) :
    (∫ x, 1 - sublevelCutoff ψ r d x ∂μ) ≤ μ.real {x | |d x| < 2 * r} := by
  let s := {x | |d x| < 2 * r}
  have hs : MeasurableSet s := measurableSet_lt hd.abs measurable_const
  have hf : Measurable (sublevelCutoff ψ r d) := hψ.comp (hd.div_const r)
  have hfi := cutoff_integrable μ _ hf (sublevelCutoff_range ψ hrange r d)
  calc
    _ ≤ ∫ x, s.indicator (fun _ => (1 : ℝ)) x ∂μ := by
      apply integral_mono ((integrable_const (1 : ℝ)).sub hfi)
        ((integrable_const (1 : ℝ)).indicator hs)
      intro x
      change 1 - sublevelCutoff ψ r d x ≤ s.indicator (fun _ => (1 : ℝ)) x
      by_cases hx : x ∈ s
      · rw [Set.indicator_of_mem hx]
        change 1 - ψ (d x / r) ≤ 1
        linarith [(hrange (d x / r)).1]
      · rw [Set.indicator_of_notMem hx]
        have hx' : 2 * r ≤ |d x| := le_of_not_gt hx
        rw [sublevelCutoff_eq_one ψ hone hr d hx']
        norm_num
    _ = _ := integral_indicator_one hs

end Erdos3

end

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

theorem goodDomainCutoff_integral_loss_le {ι E : Type*} [Fintype ι] [MeasurableSpace E]
    (μ : Measure E) [IsFiniteMeasure μ]
    (ψ : ℝ → ℝ) (hψ : Measurable ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hone : ∀ t, 2 ≤ |t| → ψ t = 1) (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (d : ι → E → ℝ) (hd : ∀ i, Measurable (d i))
    (b : E → ℝ) (hb : Measurable b) (hbrange : ∀ x, b x ∈ Set.Icc (0 : ℝ) 1) :
    (∫ x, 1 - goodDomainCutoff ψ r d b x ∂μ) ≤
      (∫ x, 1 - b x ∂μ) + ∑ i, μ.real {x | |d i x| < 2 * r i} := by
  let f : Option ι → E → ℝ := fun o => match o with
    | none => b
    | some i => sublevelCutoff ψ (r i) (d i)
  have hfm : ∀ o, Measurable (f o) := by
    intro o
    cases o with
    | none => exact hb
    | some i => exact hψ.comp ((hd i).div_const (r i))
  have hfr : ∀ o y, f o y ∈ Set.Icc (0 : ℝ) 1 := by
    intro o y
    cases o with
    | none => exact hbrange y
    | some i => exact sublevelCutoff_range ψ hrange (r i) (d i) y
  have h := product_cutoff_integral_loss_le μ f hfm hfr
  simp only [Fintype.prod_option, Fintype.sum_option, f] at h
  change (∫ x, 1 - goodDomainCutoff ψ r d b x ∂μ) ≤ _ at h
  apply h.trans
  apply add_le_add le_rfl
  exact Finset.sum_le_sum (fun i _ => sublevelCutoff_integral_loss_le μ ψ hψ hrange hone
    (hr i) (d i) (hd i))

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

theorem tensorCutoffWeight_mass_loss {ι : Type*} {E : ι → Type*} [Fintype ι] [∀ i, MeasureSpace (E i)]
    [∀ i, SigmaFinite (volume : Measure (E i))] (w : ∀ i, E i → ℝ)
    (hw : ∀ i x, 0 ≤ w i x) (hm : ∀ i, (∫ y, w i y) ≤ 1)
    (e : ι → ℝ) (he : ∀ i, 1 - e i ≤ ∫ y, w i y) :
    1 - ∑ i, e i ≤ ∫ x, tensorCutoffWeight w x := by
  rw [tensorCutoffWeight_integral]
  have h := product_cutoff_loss_le (fun i => ∫ y, w i y)
    (fun i => ⟨integral_nonneg (hw i), hm i⟩)
  have hs : (∑ i, (1 - ∫ y, w i y)) ≤ ∑ i, e i :=
    Finset.sum_le_sum (fun i _ => by linarith [he i])
  linarith

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

theorem scalarCubeMeasure_integral {α : Type*} [Fintype α] [DecidableEq α]
    (f : (Option α → ℝ) → ℝ) :
    (∫ a, f a ∂scalarCubeMeasure α) = scalarCubeDomainDensity α * ∫ a in scalarCubeDomain α, f a := by
  rw [scalarCubeMeasure, integral_smul_measure, ENNReal.toReal_inv, smul_eq_mul]
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

theorem scalarCubeBoundaryWeight_mass_lower (α : Type*) [Fintype α] [DecidableEq α]
    {r : ℝ} (hr : 0 < r) :
    1 - scalarCubeBoundaryConstant α * r ≤ ∫ a, scalarCubeBoundaryWeight α r a := by
  let b := inequalityBoundaryCutoff (fun _ : Bool × Finset α => r) scalarCubeFace
  have hbs : tsupport b ⊆ scalarCubeDomain α := scalarCubeBoundaryCutoff_tsupport_domain α hr
  have hbi : Integrable b (scalarCubeMeasure α) := cutoff_integrable _ b
    (inequalityBoundaryCutoff_smooth _ _ scalarCubeFace_contDiff).continuous.measurable
    (inequalityBoundaryCutoff_range _ _)
  have hloss := scalarCubeBoundaryCutoff_mass_loss α hr
  change (∫ a, 1 - b a ∂scalarCubeMeasure α) ≤ _ at hloss
  rw [integral_sub (integrable_const (1 : ℝ)) hbi] at hloss
  simp only [integral_const, probReal_univ, one_smul] at hloss
  change _ ≤ ∫ a, scalarCubeCutoffWeight b a
  rw [scalarCubeCutoffWeight_integral b hbs]
  linarith

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

theorem scalarCubeProductWeight_mass_lower {ι α : Type*} [Fintype ι] [Fintype α]
    [DecidableEq α] (r : ι → ℝ) (hr : ∀ i, 0 < r i) :
    1 - scalarCubeBoundaryConstant α * ∑ i, r i ≤ ∫ x, scalarCubeProductWeight α r x := by
  have h := fun i => scalarCubeBoundaryWeight_spec α (hr i)
  have hm (i : ι) : (∫ y, scalarCubeBoundaryWeight α (r i) y) ≤ 1 := by
    have habs (y) : |scalarCubeBoundaryWeight α (r i) y| =
        scalarCubeBoundaryWeight α (r i) y := abs_of_nonneg ((h i).2.2.2.1 y)
    simpa only [habs] using (h i).2.2.2.2
  have hb := tensorCutoffWeight_mass_loss (fun i => scalarCubeBoundaryWeight α (r i))
    (fun i => (h i).2.2.2.1) hm (fun i => scalarCubeBoundaryConstant α * r i)
    (fun i => scalarCubeBoundaryWeight_mass_lower α (hr i))
  simp only [← Finset.mul_sum] at hb
  exact hb

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

theorem scalarCubeProductCutoff_mass_loss {ι α : Type*} [Fintype ι] [Fintype α]
    [DecidableEq α] (r : ι → ℝ) (hr : ∀ i, 0 < r i) :
    (∫ x, 1 - scalarCubeProductCutoff α r x ∂scalarCubeProductMeasure ι α) ≤
      scalarCubeBoundaryConstant α * ∑ i, r i := by
  have hi := cutoff_integrable (scalarCubeProductMeasure ι α) (scalarCubeProductCutoff α r)
    (scalarCubeProductCutoff_smooth r).continuous.measurable (scalarCubeProductCutoff_range r)
  rw [integral_sub (integrable_const (1 : ℝ)) hi]
  simp only [integral_const, probReal_univ, one_smul]
  have he := scalarCubeProductWeight_integral_test (α := α) r hr (fun _ => 1)
  simp only [mul_one] at he
  rw [← he]
  linarith [scalarCubeProductWeight_mass_lower (α := α) r hr]

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.JointBooleanGoodWeight
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem blockCubeWeight_integral {B F α : Type*} [Fintype B] [Fintype F] [Fintype α]
    (w : ((B × F) → Option α → ℝ) → ℝ) :
    (∫ a, blockCubeWeight w a) = ∫ x, w x :=
  (blockCubeFlatten_symm_measurePreserving B F α).integral_comp
    (blockCubeFlatten B F α).symm.toHomeomorph.toMeasurableEquiv.measurableEmbedding w

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

theorem blockCubeMeasure_real_apply {B F α : Type*} [Fintype B] [Fintype F] [Fintype α]
    [DecidableEq α] (s : Set (BlockParameter B F α → ℝ)) (hs : MeasurableSet s) :
    (blockCubeMeasure B F α).real s =
      (scalarCubeProductMeasure (B × F) α).real (blockCubeFlatten B F α ⁻¹' s) := by
  rw [measureReal_def, blockCubeMeasure,
    Measure.map_apply (blockCubeFlatten B F α).continuous.measurable hs]
  rfl

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff BigOperators

theorem scalarCubeGoodWeight_integral_test {I J α : Type*} [Fintype I] [Fintype J]
    [Fintype α] [DecidableEq α] (ψ : ℝ → ℝ) (r : I → ℝ) (hr : ∀ i, 0 < r i)
    (κ : J → ℝ) (d : J → (I → Option α → ℝ) → ℝ) (f : (I → Option α → ℝ) → ℝ) :
    (∫ x, scalarCubeGoodWeight α ψ r κ d x * f x) =
      ∫ x, goodDomainCutoff ψ κ d (scalarCubeProductCutoff α r) x * f x
        ∂scalarCubeProductMeasure I α := by
  have h := scalarCubeProductWeight_integral_test r hr
    (fun x => sublevelCutoffProduct ψ κ d x * f x)
  simpa only [scalarCubeGoodWeight, sublevelCutoffProduct, goodDomainCutoff, mul_assoc] using h

theorem scalarCubeGoodWeight_mass_lower {I J α : Type*} [Fintype I] [Fintype J]
    [Fintype α] [DecidableEq α] (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (r : I → ℝ) (hr : ∀ i, 0 < r i) (κ : J → ℝ) (hκ : ∀ i, 0 < κ i)
    (d : J → (I → Option α → ℝ) → ℝ) (hd : ∀ i, ContDiff ℝ ∞ (d i)) :
    1 - scalarCubeBoundaryConstant α * ∑ i, r i -
        ∑ i, (scalarCubeProductMeasure I α).real {x | |d i x| < 2 * κ i} ≤
      ∫ x, scalarCubeGoodWeight α ψ r κ d x := by
  let b := scalarCubeProductCutoff α r
  have hb : ContDiff ℝ ∞ b := scalarCubeProductCutoff_smooth r
  have hbr : ∀ x, b x ∈ Set.Icc (0 : ℝ) 1 := scalarCubeProductCutoff_range r
  have hχ := goodDomainCutoff_smooth ψ hψ κ d hd b hb
  have hχi := cutoff_integrable (scalarCubeProductMeasure I α) _ hχ.continuous.measurable
    (goodDomainCutoff_range ψ hrange κ d b hbr)
  have hl := goodDomainCutoff_integral_loss_le (scalarCubeProductMeasure I α) ψ
    hψ.continuous.measurable hrange hone κ hκ d (fun i => (hd i).continuous.measurable)
    b hb.continuous.measurable hbr
  rw [integral_sub (integrable_const (1 : ℝ)) hχi] at hl
  simp only [integral_const, probReal_univ, one_smul] at hl
  have he := scalarCubeGoodWeight_integral_test ψ r hr κ d (fun _ => 1)
  simp only [mul_one] at he
  rw [← he] at hl
  have hboundary := scalarCubeProductCutoff_mass_loss (α := α) r hr
  change (∫ x, 1 - b x ∂scalarCubeProductMeasure I α) ≤ _ at hboundary
  linarith

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

theorem affineBooleanCubeGoodWeight_mass_lower_s2_oai
    (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hone : ∀ t, 2 ≤ |t| → ψ t = 1) (hr : ∀ i, 0 < r i) (hκ : ∀ j, 0 < κ j) :
    1 - scalarCubeBoundaryConstant α * ∑ i, r i -
        ∑ j, (blockCubeMeasure B (Fin h) α).real
          {a | |booleanMinorDeterminant (c j) sets (block j) v (sel j) (b + L a)| < 2 * κ j} ≤
      ∫ a, affineBooleanCubeGoodWeight c sets block v sel L b ψ r κ a := by
  unfold affineBooleanCubeGoodWeight
  rw [blockCubeWeight_integral]
  have hs := scalarCubeGoodWeight_mass_lower ψ hψ hrange hone r hr κ hκ
    (fun j => affineBooleanCubeDeterminant (c j) sets (block j) v (sel j) L b)
    (fun j => affineBooleanCubeDeterminant_contDiff (c j) sets (block j) v (sel j) L b)
  have he (j : J) :
      (scalarCubeProductMeasure (B × Fin h) α).real
        {x | |affineBooleanCubeDeterminant (c j) sets (block j) v (sel j) L b x| < 2 * κ j} =
      (blockCubeMeasure B (Fin h) α).real
        {a | |booleanMinorDeterminant (c j) sets (block j) v (sel j) (b + L a)| < 2 * κ j} := by
    symm
    exact blockCubeMeasure_real_apply _ (measurableSet_lt
      (((booleanMinorDeterminant_contDiff (c j) sets (block j) v (sel j)).comp
        (contDiff_const.add L.contDiff)).continuous.measurable.abs) measurable_const)
  simp_rw [he] at hs
  exact hs

end Erdos3

end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4} : type_of% @OAI.Erdos3.affineBooleanCubeGoodWeight_mass_lower_s2_oai.{u_1, u_2, u_3, u_4} := @OAI.Erdos3.affineBooleanCubeGoodWeight_mass_lower_s2_oai.{u_1, u_2, u_3, u_4}
