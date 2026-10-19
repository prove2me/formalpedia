-- Prove2me | solution 1 for OAI.Erdos3.unitBoxInteriorCutoff_mass_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-17T10:41:35.773673+00:00
-- url     : https://prove2.me/submissions/80f81363-6c16-4bab-a2c0-68e53ab366cd

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B060
import Definitions.Def_OAIE3v2B061
import Definitions.Def_OAIE3v2B067
import Definitions.Def_OAIE3v2B070

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

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ScaledCubeProductMeasure
namespace OAI

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

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.UnitBoxInteriorCutoff
namespace OAI

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

theorem unitBoxInteriorCutoff_mass_s2_oai {r : ℝ} (hr : 0 < r) :
    1 - 4 * Fintype.card ι * r ≤ ∫ x : ι → ℝ, unitBoxInteriorCutoff r x := by
  have hi := cutoff_integrable (unitBoxMeasure ι) (unitBoxInteriorCutoff r)
    (unitBoxInteriorCutoff_contDiff r).continuous.measurable (unitBoxInteriorCutoff_range r)
  have h := unitBoxInteriorCutoff_loss (ι := ι) hr
  rw [integral_sub (integrable_const (1 : ℝ)) hi] at h
  simp only [integral_const, probReal_univ, one_smul] at h
  rw [unitBoxInteriorCutoff_integral hr]
  linarith

end Erdos3

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Erdos3.unitBoxInteriorCutoff_mass_s2_oai.{u_1} := @OAI.Erdos3.unitBoxInteriorCutoff_mass_s2_oai.{u_1}
