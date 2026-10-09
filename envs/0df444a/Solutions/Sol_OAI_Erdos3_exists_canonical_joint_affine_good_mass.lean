-- Prove2me | solution 1 for OAI.Erdos3.exists_canonical_joint_affine_good_mass
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T04:31:32.841885+00:00
-- url     : https://prove2.me/submissions/4ea70f3d-e8b2-42ad-b75c-28fadb2d5edc

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B109
import Definitions.Def_OAIErdos3B120

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.DiagonalDensityTransport
namespace OAI

section

namespace Erdos3

open MeasureTheory

variable {ι : Type*}

variable [Fintype ι]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

variable {ι : Type*} [Fintype ι]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {ι : Type*} [Fintype ι] (a : ι → ℝ) (ha : ∀ i, a i ≠ 0)

theorem diagonalDensityTransport_det :
    LinearMap.det (coordinateScaleEquiv a ha).toLinearMap = ∏ i, a i := by
  classical
  have hm : LinearMap.toMatrix' (coordinateScaleEquiv a ha).toLinearMap = Matrix.diagonal a := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [LinearMap.toMatrix'_apply, coordinateScaleEquiv_apply]
    · simp [LinearMap.toMatrix'_apply, coordinateScaleEquiv_apply, hij]
  rw [← LinearMap.det_toMatrix', hm, Matrix.det_diagonal]

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SmoothSublevelCutoff
namespace OAI

section

namespace Erdos3

open scoped ContDiff NNReal

end Erdos3

end

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

theorem sublevelCutoff_eq_one {E : Type*} (ψ : ℝ → ℝ)
    (hψ : ∀ t, 2 ≤ |t| → ψ t = 1) {r : ℝ} (hr : 0 < r)
    (d : E → ℝ) {x : E} (hx : 2 * r ≤ |d x|) : sublevelCutoff ψ r d x = 1 := by
  apply hψ
  rw [abs_div, abs_of_pos hr]
  exact (le_div_iff₀ hr).mpr hx

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

theorem sigmaAxisWeight_integral (w : ∀ d, (I d → ℝ) → ℝ) :
    (∫ x, sigmaAxisWeight w x) = ∏ d, ∫ y, w d y := by
  calc
    _ = ∫ x, tensorCutoffWeight w x :=
      (sigmaAxisCoordinates_measurePreserving I).integral_comp
        (sigmaAxisCoordinates I).toHomeomorph.toMeasurableEquiv.measurableEmbedding _
    _ = _ := tensorCutoffWeight_integral w

theorem sigmaAxisWeight_mass_loss (w : ∀ d, (I d → ℝ) → ℝ)
    (hw : ∀ d y, 0 ≤ w d y) (hm : ∀ d, (∫ y, w d y) ≤ 1)
    (e : D → ℝ) (he : ∀ d, 1 - e d ≤ ∫ y, w d y) :
    1 - ∑ d, e d ≤ ∫ x, sigmaAxisWeight w x := by
  rw [sigmaAxisWeight_integral, ← tensorCutoffWeight_integral w]
  exact tensorCutoffWeight_mass_loss w hw hm e he

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PaddedBooleanFeatures
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_padded_boolean_labels {α : Type*} [DecidableEq α]
    (s : Finset α) (h : ℕ) (hs : s.card ≤ h) :
    ∃ label : Fin h → Option α, ∀ a, (∃ i, label i = some a) ↔ a ∈ s := by
  classical
  let e : s ≃ Fin s.card := Fintype.equivFinOfCardEq (Fintype.card_coe s)
  let label : Fin h → Option α := fun i =>
    if hi : i.val < s.card then some (e.symm ⟨i.val, hi⟩).val else none
  refine ⟨label, ?_⟩
  intro a
  constructor
  · rintro ⟨i, hi⟩
    dsimp [label] at hi
    split_ifs at hi with hc
    · have ha := Option.some.inj hi
      exact ha ▸ (e.symm ⟨i.val, hc⟩).property
  · intro ha
    let j := e ⟨a, ha⟩
    let i : Fin h := ⟨j.val, lt_of_lt_of_le j.isLt hs⟩
    refine ⟨i, ?_⟩
    dsimp [label, i]
    rw [if_pos j.isLt]
    change some (e.symm (e ⟨a, ha⟩)).val = some a
    simp

theorem booleanFeature_product {α ι R : Type*} [DecidableEq α] [Fintype ι] [CommMonoidWithZero R]
    (label : ι → Option α) (s : Finset α)
    (hlabel : ∀ a, (∃ i, label i = some a) ↔ a ∈ s) (t : Finset α) :
    (∏ i, (booleanFeature (label i) t : R)) = if s ⊆ t then 1 else 0 := by
  classical
  by_cases hst : s ⊆ t
  · rw [if_pos hst]
    apply Finset.prod_eq_one
    intro i _
    cases hi : label i with
    | none => rfl
    | some a =>
      have ha := hst ((hlabel a).mp ⟨i, hi⟩)
      simp only [booleanFeature, ha, ite_true]
  · rw [if_neg hst]
    obtain ⟨a, has, hat⟩ := Finset.not_subset.mp hst
    obtain ⟨i, hi⟩ := (hlabel a).mpr has
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp only [hi, booleanFeature, hat, ite_false]

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

theorem blockSpecialization_abs_le_one {B F α : Type*} [DecidableEq α]
    (label : B → F → Option α) (z : BlockParameter B F α) : |blockSpecialization label z| ≤ 1 := by
  unfold blockSpecialization
  split_ifs <;> norm_num

theorem booleanAffinePolynomial_specialization {B F α : Type*} [Fintype α] [DecidableEq α]
    (label : B → F → Option α) (b : B) (v : F) (t : Finset α) :
    MvPolynomial.eval (blockSpecialization label) (booleanAffinePolynomial b v t) =
      (booleanFeature (label b v) t : ℝ) := by
  classical
  simp only [booleanAffinePolynomial, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
    blockSpecialization, mul_ite, mul_one, mul_zero]
  simp

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

theorem booleanAffinePolynomial_degreeOf_le {B F α : Type*} [Fintype α] [DecidableEq α]
    (b : B) (v : F) (t : Finset α) (j : BlockParameter B F α) :
    (booleanAffinePolynomial b v t).degreeOf j ≤ 1 := by
  classical
  unfold booleanAffinePolynomial
  apply (MvPolynomial.degreeOf_sum_le j Finset.univ _).trans
  apply Finset.sup_le
  intro r _
  apply (MvPolynomial.degreeOf_C_mul_le _ j _).trans
  simp only [MvPolynomial.degreeOf_X]
  split_ifs <;> omega

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

omit [Fintype B] [DecidableEq B] in
theorem booleanSelectedColumn_specialization (c : B → ℝ) (label : B → F → Option α)
    (b : B) (v : F) (S s : Finset α)
    (hlabel : ∀ a, (∃ k, label b k = some a) ↔ a ∈ S) :
    MvPolynomial.eval (blockSpecialization label) (booleanSelectedColumn c b v (label b v) s) =
      c b * if s = S then 1 else 0 := by
  rw [booleanSelectedColumn, map_mul, MvPolynomial.eval_C, booleanCoefficient_map]
  have hinner (t : Finset α) :
      MvPolynomial.eval (blockSpecialization label)
        (MvPolynomial.C (booleanFeature (label b v) t : ℝ) *
          ∏ k ∈ Finset.univ.erase v, booleanAffinePolynomial b k t) =
      if S ⊆ t then (1 : ℝ) else 0 := by
    simp only [map_mul, MvPolynomial.eval_C, map_prod, booleanAffinePolynomial_specialization]
    rw [Finset.mul_prod_erase Finset.univ (fun k => (booleanFeature (label b k) t : ℝ)) (Finset.mem_univ v)]
    exact booleanFeature_product (label b) S hlabel t
  simp_rw [hinner]
  rw [booleanCoefficient_monomial]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.BooleanBlockCoefficientPhase
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem booleanCoefficient_degreeOf_le {α ι : Type*} [DecidableEq α]
    (f : Finset α → MvPolynomial ι ℝ) (s : Finset α) (j : ι) (d : ℕ)
    (hf : ∀ t ∈ s.powerset, (f t).degreeOf j ≤ d) :
    (booleanCoefficient f s).degreeOf j ≤ d := by
  classical
  unfold booleanCoefficient
  apply (MvPolynomial.degreeOf_sum_le j s.powerset _).trans
  apply Finset.sup_le
  intro t ht
  have hc : (-1 : MvPolynomial ι ℝ) ^ (s \ t).card =
      MvPolynomial.C ((-1 : ℝ) ^ (s \ t).card) := by simp
  rw [hc]
  exact (MvPolynomial.degreeOf_C_mul_le _ j _).trans (hf t ht)

theorem booleanSelectedColumn_degreeOf_le {B F α : Type*} [Fintype F] [Fintype α]
    [DecidableEq F] [DecidableEq α]
    (c : B → ℝ) (b : B) (v : F) (r : Option α) (s : Finset α) (j : BlockParameter B F α) :
    (booleanSelectedColumn c b v r s).degreeOf j ≤ Fintype.card F - 1 := by
  unfold booleanSelectedColumn
  apply (MvPolynomial.degreeOf_C_mul_le _ j _).trans
  apply booleanCoefficient_degreeOf_le
  intro t _
  apply (MvPolynomial.degreeOf_C_mul_le _ j _).trans
  apply (MvPolynomial.degreeOf_prod_le j (Finset.univ.erase v) _).trans
  calc
    _ ≤ ∑ _k ∈ Finset.univ.erase v, (1 : ℕ) :=
      Finset.sum_le_sum (fun k _ => booleanAffinePolynomial_degreeOf_le b k t j)
    _ = _ := by simp

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

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialDeterminantDegree
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem polynomial_det_value_abs_lower {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (MvPolynomial κ ℝ)) (x : κ → ℝ) (a : ι → ℝ)
    (hdiag : M.map (MvPolynomial.eval x) = Matrix.diagonal a)
    {c : ℝ} (hc : 0 ≤ c) (ha : ∀ i, c ≤ |a i|) :
    c ^ Fintype.card ι ≤ |MvPolynomial.eval x M.det| := by
  rw [(MvPolynomial.eval x).map_det]
  change c ^ Fintype.card ι ≤ |(M.map (MvPolynomial.eval x)).det|
  rw [hdiag, Matrix.det_diagonal, Finset.abs_prod]
  calc
    c ^ Fintype.card ι = ∏ _i : ι, c := by simp
    _ ≤ ∏ i : ι, |a i| := Finset.prod_le_prod (fun _ _ => hc) (fun index _ => ha index)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.EmbeddedMatrixDeterminantPolynomial
namespace OAI

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

open MeasureTheory
open scoped Pointwise

theorem polynomial_sublevel_bounded_set_bound {N d : ℕ} (hN : 0 < N) (hd : 0 < d)
    (p : MvPolynomial (Fin N) ℝ) (hp : ∀ j, p.degreeOf j ≤ d)
    (Ω : Set (Fin N → ℝ)) {R u c : ℝ} (hR : 1 ≤ R)
    (hΩ : ∀ x ∈ Ω, ∀ i, |x i| ≤ R) (hu : 0 < u) (hc : 0 < c) (m : Fin N →₀ ℕ)
    (hm : c ≤ |p.coeff m|) :
    volume.real (Ω ∩ {x | |MvPolynomial.eval x p| ≤ u}) ≤
      R ^ N * multivariateSublevelConstant N d * (u / c) ^ (((N * d : ℕ) : ℝ)⁻¹) := by
  have hs : Ω ∩ {x | |MvPolynomial.eval x p| ≤ u} ⊆ boxMvPolynomialSublevel p R u :=
    fun x hx => ⟨hΩ x hx.1, hx.2⟩
  exact (measureReal_mono hs (boxMvPolynomialSublevel_volume_ne_top p (zero_lt_one.trans_le hR) u)).trans
    (polynomial_sublevel_box_bound hN hd p hp hR hu hc m hm)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

theorem polynomial_sublevel_bound_of_value {N d : ℕ} (hN : 0 < N) (hd : 0 < d)
    (p : MvPolynomial (Fin N) ℝ) (hp : ∀ j, p.degreeOf j ≤ d)
    (Ω : Set (Fin N → ℝ)) {R u v : ℝ} (hR : 1 ≤ R)
    (hΩ : ∀ x ∈ Ω, ∀ i, |x i| ≤ R) (hu : 0 < u) (hv : 0 < v)
    (x₀ : Fin N → ℝ) (hx₀ : ∀ i, |x₀ i| ≤ 1) (hval : v ≤ |MvPolynomial.eval x₀ p|) :
    volume.real (Ω ∩ {x | |MvPolynomial.eval x p| ≤ u}) ≤
      R ^ N * multivariateSublevelConstant N d *
        (u * (d + 1 : ℝ) ^ N / v) ^ (((N * d : ℕ) : ℝ)⁻¹) := by
  obtain ⟨m, hm⟩ := exists_coefficient_of_unit_box_value p hp x₀ hx₀ hv hval
  have h := polynomial_sublevel_bounded_set_bound hN hd p hp Ω hR hΩ hu
    (div_pos hv (by positivity : 0 < (d + 1 : ℝ) ^ N)) m hm
  simpa only [div_div_eq_mul_div] using h

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

theorem polynomial_det_sublevel_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    {N e d : ℕ} (hN : 0 < N) (hd : 0 < d) (hdeg : Fintype.card ι * e ≤ d)
    (M : Matrix ι ι (MvPolynomial (Fin N) ℝ)) (hM : ∀ a b j, (M a b).degreeOf j ≤ e)
    (x₀ : Fin N → ℝ) (hx₀ : ∀ j, |x₀ j| ≤ 1) (a : ι → ℝ)
    (hdiag : M.map (MvPolynomial.eval x₀) = Matrix.diagonal a)
    {c : ℝ} (hc : 0 < c) (ha : ∀ i, c ≤ |a i|)
    (Ω : Set (Fin N → ℝ)) {R u : ℝ} (hR : 1 ≤ R)
    (hΩ : ∀ x ∈ Ω, ∀ j, |x j| ≤ R) (hu : 0 < u) :
    volume.real (Ω ∩ {x | |(M.map (MvPolynomial.eval x)).det| ≤ u}) ≤
      R ^ N * multivariateSublevelConstant N d *
        (u * (d + 1 : ℝ) ^ N / c ^ Fintype.card ι) ^ (((N * d : ℕ) : ℝ)⁻¹) := by
  have h := polynomial_sublevel_bound_of_value hN hd M.det
    (fun j => (polynomial_det_degreeOf_le M j e (fun a b => hM a b j)).trans hdeg)
    Ω hR hΩ hu (pow_pos hc _) x₀ hx₀ (polynomial_det_value_abs_lower M x₀ a hdiag hc.le ha)
  simp only [RingHom.map_det, RingHom.mapMatrix_apply] at h
  exact h

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
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

theorem reindexPolynomialMatrix_degreeOf {I J O : Type*} (e : I ≃ J)
    (M : Matrix O O (MvPolynomial I ℝ)) (a b : O) (j : J) :
    (reindexPolynomialMatrix e M a b).degreeOf j = (M a b).degreeOf (e.symm j) := by
  have h := MvPolynomial.degreeOf_rename_of_injective (p := M a b) e.injective (e.symm j)
  simp only [e.apply_symm_apply] at h
  exact h

theorem reindexPolynomialMatrix_eval {I J O : Type*} (e : I ≃ J)
    (M : Matrix O O (MvPolynomial I ℝ)) (x : J → ℝ) :
    (reindexPolynomialMatrix e M).map (MvPolynomial.eval x) =
      M.map (MvPolynomial.eval (x ∘ e)) := by
  ext a b
  exact MvPolynomial.eval_rename e x (M a b)

theorem reindexed_polynomial_det_sublevel_bound {I O : Type*}
    [Fintype O] [DecidableEq O] {N t d : ℕ} (e : I ≃ Fin N)
    (hN : 0 < N) (hd : 0 < d) (hdeg : Fintype.card O * t ≤ d)
    (M : Matrix O O (MvPolynomial I ℝ)) (hM : ∀ a b j, (M a b).degreeOf j ≤ t)
    (x₀ : I → ℝ) (hx₀ : ∀ j, |x₀ j| ≤ 1) (a : O → ℝ)
    (hdiag : M.map (MvPolynomial.eval x₀) = Matrix.diagonal a)
    {c : ℝ} (hc : 0 < c) (ha : ∀ i, c ≤ |a i|)
    (Ω : Set (Fin N → ℝ)) {R u : ℝ} (hR : 1 ≤ R)
    (hΩ : ∀ x ∈ Ω, ∀ j, |x j| ≤ R) (hu : 0 < u) :
    volume.real (Ω ∩ {x | |(M.map (MvPolynomial.eval (x ∘ e))).det| ≤ u}) ≤
      R ^ N * multivariateSublevelConstant N d *
        (u * (d + 1 : ℝ) ^ N / c ^ Fintype.card O) ^ (((N * d : ℕ) : ℝ)⁻¹) := by
  have hM' : ∀ a b j, (reindexPolynomialMatrix e M a b).degreeOf j ≤ t := by
    intro a b j
    rw [reindexPolynomialMatrix_degreeOf]
    exact hM a b (e.symm j)
  have hdiag' : (reindexPolynomialMatrix e M).map (MvPolynomial.eval (x₀ ∘ e.symm)) =
      Matrix.diagonal a := by
    rw [reindexPolynomialMatrix_eval]
    simpa only [Function.comp_def, e.symm_apply_apply] using hdiag
  have h := polynomial_det_sublevel_bound hN hd hdeg (reindexPolynomialMatrix e M) hM'
    (x₀ ∘ e.symm) (fun j => hx₀ (e.symm j)) a hdiag' hc ha Ω hR hΩ hu
  simp only [reindexPolynomialMatrix_eval] at h
  exact h

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
open scoped BigOperators Classical

variable {n N : ℕ}

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

theorem booleanSelectedMinor_degreeOf_le (c : B → ℝ) (sets : O → Finset α)
    (block : O → B) (v : F) (r : O → Option α) (row col : O) (j : BlockParameter B F α) :
    (booleanSelectedMinor c sets block v r row col).degreeOf j ≤ Fintype.card F - 1 := by
  unfold booleanSelectedMinor
  rw [booleanSamplerPolynomial_pderiv]
  exact booleanSelectedColumn_degreeOf_le c (block col) v (r col) (sets row) j

theorem booleanSelectedMinor_specialization [DecidableEq O]
    (c : B → ℝ) (sets : O → Finset α) (hsets : Function.Injective sets) (block : O → B) (v : F)
    (label : B → F → Option α)
    (hlabel : ∀ o a, (∃ k, label (block o) k = some a) ↔ a ∈ sets o) :
    (booleanSelectedMinor c sets block v (fun o => label (block o) v)).map
      (MvPolynomial.eval (blockSpecialization label)) = Matrix.diagonal (fun o => c (block o)) := by
  ext row col
  change MvPolynomial.eval (blockSpecialization label)
    (MvPolynomial.pderiv (block col, v, label (block col) v) (booleanSamplerPolynomial c (sets row))) = _
  rw [booleanSamplerPolynomial_pderiv, booleanSelectedColumn_specialization c label
    (block col) v (sets col) (sets row) (hlabel col)]
  by_cases h : row = col
  · subst row
    simp
  · have hs : sets row ≠ sets col := fun he => h (hsets he)
    simp [h, hs]

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

theorem booleanSelectedColumn_restrict_eval {B O F α : Type*}
    [Fintype F] [Fintype α] [DecidableEq F] [DecidableEq α]
    (c : B → ℝ) (block : O → B) (a : BlockParameter B F α → ℝ)
    (o : O) (v : F) (r : Option α) (s : Finset α) :
    MvPolynomial.eval a (booleanSelectedColumn c (block o) v r s) =
      MvPolynomial.eval (restrictBlockParameters block a)
        (booleanSelectedColumn (c ∘ block) o v r s) := by
  simp only [booleanSelectedColumn, map_mul, MvPolynomial.eval_C, booleanCoefficient_map,
    map_prod, booleanAffinePolynomial_eval, Function.comp_apply, restrictBlockParameters]

theorem booleanSelectedMinor_restrict_eval {B O F α : Type*}
    [Fintype B] [Fintype O] [Fintype F] [Fintype α]
    [DecidableEq B] [DecidableEq O] [DecidableEq F] [DecidableEq α]
    (c : B → ℝ) (sets : O → Finset α) (block : O → B) (v : F) (r : O → Option α)
    (a : BlockParameter B F α → ℝ) :
    (booleanSelectedMinor c sets block v r).map (MvPolynomial.eval a) =
      (booleanSelectedMinor (c ∘ block) sets id v r).map
        (MvPolynomial.eval (restrictBlockParameters block a)) := by
  ext row col
  change MvPolynomial.eval a (MvPolynomial.pderiv (block col, v, r col) _) =
    MvPolynomial.eval (restrictBlockParameters block a) (MvPolynomial.pderiv (col, v, r col) _)
  rw [booleanSamplerPolynomial_pderiv, booleanSamplerPolynomial_pderiv]
  exact booleanSelectedColumn_restrict_eval c block a col v (r col) (sets row)

end Erdos3

end

section

namespace Erdos3

theorem exists_allocated_boolean_labels {B O α : Type*} [DecidableEq α]
    (sets : O → Finset α) (h : ℕ) (hcard : ∀ o, (sets o).card ≤ h)
    (block : O → B) (hblock : Function.Injective block) :
    ∃ label : B → Fin h → Option α,
      ∀ o a, (∃ k, label (block o) k = some a) ↔ a ∈ sets o := by
  classical
  choose label hlabel using fun o => exists_padded_boolean_labels (sets o) h (hcard o)
  refine ⟨Function.extend block label (fun _ _ => none), ?_⟩
  intro o a
  simpa only [hblock.extend_apply] using hlabel o a

theorem exists_boolean_minor_specialization {B O α : Type*}
    [Fintype B] [Fintype α] [DecidableEq B] [DecidableEq O] [DecidableEq α]
    (c : B → ℝ) (sets : O → Finset α) (hsets : Function.Injective sets)
    (h : ℕ) (hh : 0 < h) (hcard : ∀ o, (sets o).card ≤ h)
    (block : O → B) (hblock : Function.Injective block) :
    ∃ (r : O → Option α) (a₀ : BlockParameter B (Fin h) α → ℝ),
      (∀ j, |a₀ j| ≤ 1) ∧
      (booleanSelectedMinor c sets block (⟨0, hh⟩ : Fin h) r).map (MvPolynomial.eval a₀) =
        Matrix.diagonal (fun o => c (block o)) := by
  obtain ⟨label, hlabel⟩ := exists_allocated_boolean_labels sets h hcard block hblock
  let v : Fin h := ⟨0, hh⟩
  have habs : ∀ j : BlockParameter B (Fin h) α, |blockSpecialization label j| ≤ 1 :=
    blockSpecialization_abs_le_one label
  have hdiag := booleanSelectedMinor_specialization c sets hsets block v label hlabel
  refine ⟨(fun o => label (block o) v), blockSpecialization label, ?_, ?_⟩
  · exact habs
  · exact hdiag

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

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

theorem exists_boolean_minor_sublevel_bound {O α : Type*}
    [Fintype O] [Fintype α] [DecidableEq O] [DecidableEq α]
    (c : O → ℝ) (sets : O → Finset α) (hsets : Function.Injective sets)
    (h : ℕ) (hh : 0 < h) (hcard : ∀ o, (sets o).card ≤ h)
    {N : ℕ} (e : BlockParameter O (Fin h) α ≃ Fin N) (hN : 0 < N)
    {c₀ : ℝ} (hc₀ : 0 < c₀) (hc : ∀ o, c₀ ≤ |c o|) :
    ∃ r : O → Option α, ∀ (d : ℕ), 0 < d → Fintype.card O * (h - 1) ≤ d →
      ∀ (Ω : Set (Fin N → ℝ)) (R u : ℝ), 1 ≤ R →
      (∀ x ∈ Ω, ∀ j, |x j| ≤ R) → 0 < u →
      volume.real (Ω ∩ {x | |((booleanSelectedMinor c sets id (⟨0, hh⟩ : Fin h) r).map
        (MvPolynomial.eval (x ∘ e))).det| ≤ u}) ≤
        R ^ N * multivariateSublevelConstant N d *
          (u * (d + 1 : ℝ) ^ N / c₀ ^ Fintype.card O) ^ (((N * d : ℕ) : ℝ)⁻¹) := by
  obtain ⟨r, a₀, ha₀, hdiag⟩ :=
    exists_boolean_minor_specialization c sets hsets h hh hcard id Function.injective_id
  refine ⟨r, ?_⟩
  intro d hd hdeg Ω R u hR hΩ hu
  have hM : ∀ a b j, (booleanSelectedMinor c sets id (⟨0, hh⟩ : Fin h) r a b).degreeOf j ≤
      h - 1 := by
    intro a b j
    simpa only [Fintype.card_fin] using
      booleanSelectedMinor_degreeOf_le c sets id (⟨0, hh⟩ : Fin h) r a b j
  exact reindexed_polynomial_det_sublevel_bound e hN hd hdeg
    (booleanSelectedMinor c sets id (⟨0, hh⟩ : Fin h) r) hM a₀ ha₀ c hdiag hc₀ hc Ω hR hΩ hu

end Erdos3

end

section

namespace Erdos3

theorem boolean_minor_parameter_count_pos (O α : Type*) [Fintype O] [Nonempty O]
    [Fintype α] {h : ℕ} (hh : 0 < h) :
    0 < Fintype.card O * (h * (Fintype.card α + 1)) :=
  Nat.mul_pos Fintype.card_pos (Nat.mul_pos hh (Nat.succ_pos _))

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ScalarCubeDomainDensity
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem scalarCubeDomainDensity_pos (α : Type*) [Fintype α] [DecidableEq α] :
    0 < scalarCubeDomainDensity α := inv_pos.mpr (scalarCubeDomain_volumeReal_pos α)

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

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem scalarCubeBoundaryConstant_pos (α : Type*) [Fintype α] [DecidableEq α] :
    0 < scalarCubeBoundaryConstant α := by
  have h := scalarCubeDomainDensity_pos α
  unfold scalarCubeBoundaryConstant
  positivity

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProductCutoffLipschitz
namespace OAI

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

open scoped BigOperators NNReal

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

end Erdos3

end

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

open scoped BigOperators NNReal

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

section

namespace Erdos3

open scoped BigOperators NNReal

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ScalarCubeBoundaryLogBudget
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

theorem scalarCubeProductBoundaryRadius_pos (ι α : Type*) [Fintype ι] [Fintype α]
    [DecidableEq α] {η : ℝ} (hη : 0 < η) : 0 < scalarCubeProductBoundaryRadius ι α η :=
  div_pos hη (mul_pos (scalarCubeBoundaryConstant_pos α) (by positivity))

theorem scalarCubeProductBoundaryRadius_loss (ι α : Type*) [Fintype ι] [Fintype α]
    [DecidableEq α] {η : ℝ} (hη : 0 < η) :
    scalarCubeBoundaryConstant α * ∑ _i : ι, scalarCubeProductBoundaryRadius ι α η ≤ η := by
  have hC := scalarCubeBoundaryConstant_pos α
  have hm : 0 < (Fintype.card ι : ℝ) + 1 := by positivity
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have he : scalarCubeBoundaryConstant α *
      ((Fintype.card ι : ℝ) * scalarCubeProductBoundaryRadius ι α η) =
      η * (Fintype.card ι : ℝ) / ((Fintype.card ι : ℝ) + 1) := by
    unfold scalarCubeProductBoundaryRadius
    field_simp
  rw [he]
  apply (div_le_iff₀ hm).mpr
  nlinarith

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

section

namespace Erdos3

open MeasureTheory
open scoped Topology

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
open scoped NNReal

variable {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal ContDiff BigOperators

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

theorem blockCubeMeasure_real_apply {B F α : Type*} [Fintype B] [Fintype F] [Fintype α]
    [DecidableEq α] (s : Set (BlockParameter B F α → ℝ)) (hs : MeasurableSet s) :
    (blockCubeMeasure B F α).real s =
      (scalarCubeProductMeasure (B × F) α).real (blockCubeFlatten B F α ⁻¹' s) := by
  rw [measureReal_def, blockCubeMeasure,
    Measure.map_apply (blockCubeFlatten B F α).continuous.measurable hs]
  rfl

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

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff

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

section

namespace Erdos3

open MeasureTheory

theorem restrictBlockParameters_measurable {B O F α : Type*} (block : O → B) :
    Measurable (restrictBlockParameters (F := F) (α := α) block) := by
  unfold restrictBlockParameters
  fun_prop

theorem restrictBlockParameters_cube_measurePreserving {B O F α : Type*}
    [Fintype B] [Fintype O] [Fintype F] [Fintype α] [DecidableEq α]
    (block : O → B) (hblock : Function.Injective block) :
    MeasurePreserving (restrictBlockParameters (F := F) (α := α) block)
      (blockCubeMeasure B F α) (blockCubeMeasure O F α) := by
  let e : O × F → B × F := fun z => (block z.1, z.2)
  have he : Function.Injective e := by
    intro x y hxy
    exact Prod.ext (hblock (congrArg (fun z : B × F => z.1) hxy))
      (congrArg (fun z : B × F => z.2) hxy)
  have hsel := finiteProductMarginal_measurePreserving
    (fun _ : B × F => scalarCubeMeasure α) e he
  change MeasurePreserving _ (scalarCubeProductMeasure (B × F) α)
    (scalarCubeProductMeasure (O × F) α) at hsel
  refine ⟨restrictBlockParameters_measurable block, ?_⟩
  change Measure.map (restrictBlockParameters block)
      (Measure.map (blockCubeFlatten B F α) (scalarCubeProductMeasure (B × F) α)) =
    Measure.map (blockCubeFlatten O F α) (scalarCubeProductMeasure (O × F) α)
  rw [Measure.map_map (restrictBlockParameters_measurable block)
    (blockCubeFlatten B F α).continuous.measurable]
  have hcomp : restrictBlockParameters block ∘ blockCubeFlatten B F α =
      blockCubeFlatten O F α ∘ (fun x : (B × F) → Option α → ℝ => fun z => x (e z)) := rfl
  rw [hcomp, ← Measure.map_map (blockCubeFlatten O F α).continuous.measurable hsel.measurable]
  exact congrArg (Measure.map (blockCubeFlatten O F α)) hsel.map_eq

theorem booleanMinorDeterminant_restrict {B O F α : Type*}
    [Fintype B] [Fintype O] [Fintype F] [Fintype α]
    [DecidableEq B] [DecidableEq O] [DecidableEq F] [DecidableEq α]
    (c : B → ℝ) (sets : O → Finset α) (block : O → B) (v : F) (r : O → Option α)
    (a : BlockParameter B F α → ℝ) :
    booleanMinorDeterminant c sets block v r a =
      booleanMinorDeterminant (c ∘ block) sets id v r (restrictBlockParameters block a) :=
  congrArg Matrix.det (booleanSelectedMinor_restrict_eval c sets block v r a)

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
open scoped ContDiff BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff BigOperators

variable {D α : Type*} [Fintype D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.BlockCubeDensity
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem blockCubeDomain_measurable (B F α : Type*) [Fintype B] [Fintype F] [Fintype α]
    [DecidableEq α] : MeasurableSet (blockCubeDomain B F α) :=
  (MeasurableSet.univ_pi (fun _ => (scalarCubeDomain_isOpen α).measurableSet)).preimage
    (blockCubeFlatten B F α).symm.continuous.measurable

theorem blockCubeDomain_box {B F α : Type*} [Fintype B] [Fintype F] [Fintype α]
    [DecidableEq α] {a : BlockParameter B F α → ℝ} (ha : a ∈ blockCubeDomain B F α)
    (z : BlockParameter B F α) : |a z| ≤ 1 := by
  have h := blockCubeFlatten_box ha z
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using h

theorem scalarCubeProductMeasure_real_apply {I α : Type*} [Fintype I] [Fintype α]
    [DecidableEq α] (s : Set (I → Option α → ℝ)) (hs : MeasurableSet s) :
    (scalarCubeProductMeasure I α).real s = scalarCubeDomainDensity α ^ Fintype.card I *
      volume.real (scalarCubeProductDomain I α ∩ s) := by
  rw [scalarCubeProductMeasure_eq_smul_restrict, measureReal_ennreal_smul_apply,
    measureReal_restrict_apply hs, ENNReal.toReal_pow, ENNReal.toReal_inv, Set.inter_comm]
  rfl

theorem blockCubeMeasure_real_apply_domain {B F α : Type*} [Fintype B] [Fintype F]
    [Fintype α] [DecidableEq α]
    (s : Set (BlockParameter B F α → ℝ)) (hs : MeasurableSet s) :
    (blockCubeMeasure B F α).real s =
      scalarCubeDomainDensity α ^ Fintype.card (B × F) * volume.real (blockCubeDomain B F α ∩ s) := by
  rw [blockCubeMeasure_real_apply s hs, scalarCubeProductMeasure_real_apply _
    (hs.preimage (blockCubeFlatten B F α).continuous.measurable)]
  have he : scalarCubeProductDomain (B × F) α ∩ blockCubeFlatten B F α ⁻¹' s =
      blockCubeFlatten B F α ⁻¹' (blockCubeDomain B F α ∩ s) := by
    ext x
    simp only [blockCubeDomain, Set.mem_inter_iff, Set.mem_preimage,
      ContinuousLinearEquiv.symm_apply_apply]
  rw [he, (blockCubeFlatten_measurePreserving B F α).measureReal_preimage
    ((blockCubeDomain_measurable B F α).inter hs).nullMeasurableSet]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ReindexedCubeDomain
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem coordinateReindex_measurePreserving {I J : Type*} [Fintype I] [Fintype J]
    (e : I ≃ J) : MeasurePreserving (fun x : J → ℝ => x ∘ e) volume volume := by
  have h := volume_measurePreserving_piCongrLeft (fun _ : I => ℝ) e.symm
  convert h using 1
  funext x i
  simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]

theorem reindexedBlockCubeDomain_box {B F α : Type*} [Fintype B] [Fintype F]
    [Fintype α] [DecidableEq α] {N : ℕ} (e : BlockParameter B F α ≃ Fin N)
    {x : Fin N → ℝ} (hx : x ∈ reindexedBlockCubeDomain e) (j : Fin N) : |x j| ≤ 1 := by
  have h := blockCubeDomain_box hx (e.symm j)
  simpa only [Function.comp_apply, e.apply_symm_apply] using h

theorem blockCubeMeasure_real_reindex {B F α : Type*} [Fintype B] [Fintype F]
    [Fintype α] [DecidableEq α] {N : ℕ} (e : BlockParameter B F α ≃ Fin N)
    (s : Set (BlockParameter B F α → ℝ)) (hs : MeasurableSet s) :
    (blockCubeMeasure B F α).real s = scalarCubeDomainDensity α ^ Fintype.card (B × F) *
      volume.real (reindexedBlockCubeDomain e ∩ {x | x ∘ e ∈ s}) := by
  rw [blockCubeMeasure_real_apply_domain s hs]
  have hm := (coordinateReindex_measurePreserving e).measureReal_preimage
    ((blockCubeDomain_measurable B F α).inter hs).nullMeasurableSet
  rw [← hm]
  rfl

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CanonicalCubeMinorThreshold
namespace OAI

section

namespace Erdos3

theorem cubeMinorProbabilityConstant_pos (O α : Type*) [Fintype O] [Fintype α]
    [DecidableEq α] (h : ℕ) {N : ℕ} (hN : 0 < N) (d : ℕ) :
    0 < cubeMinorProbabilityConstant O α h N d :=
  mul_pos (pow_pos (scalarCubeDomainDensity_pos α) _) (multivariateSublevelConstant_pos hN d)

theorem cubeMinorProbabilityScale_pos (O : Type*) [Fintype O] (N d : ℕ)
    {c₀ : ℝ} (hc₀ : 0 < c₀) : 0 < cubeMinorProbabilityScale O N d c₀ := by
  unfold cubeMinorProbabilityScale
  positivity

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
open scoped BigOperators

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

variable {I : Type*} [Fintype I]

theorem affine_preimage_volume_real (L : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (b : I → ℝ) (s : Set (I → ℝ)) :
    volume.real ((fun x => b + L x) ⁻¹' s) = inverseJacobian L * volume.real s := by
  change (volume (L ⁻¹' ((fun x => b + x) ⁻¹' s))).toReal = _
  rw [Measure.addHaar_preimage_continuousLinearEquiv volume L, measure_preimage_add,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _)]
  rfl

theorem affine_sublevel_volume_real (L : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (b : I → ℝ) (Ω : Set (I → ℝ)) (g : (I → ℝ) → ℝ) (u : ℝ) :
    volume.real (Ω ∩ {x | |g (b + L x)| ≤ u}) = inverseJacobian L *
      volume.real (((fun x => b + L x) '' Ω) ∩ {x | |g x| ≤ u}) := by
  have he : Ω ∩ {x | |g (b + L x)| ≤ u} =
      (fun x => b + L x) ⁻¹' (((fun x => b + L x) '' Ω) ∩ {x | |g x| ≤ u}) := by
    ext x
    constructor
    · rintro ⟨hx, hg⟩
      exact ⟨⟨x, hx, rfl⟩, hg⟩
    · rintro ⟨⟨y, hy, he⟩, hg⟩
      have hyx : y = x := L.injective (add_left_cancel he)
      exact ⟨hyx ▸ hy, hg⟩
  rw [he, affine_preimage_volume_real]

theorem exists_affine_boolean_minor_sublevel_bound {O α : Type*}
    [Fintype O] [Fintype α] [DecidableEq O] [DecidableEq α]
    (c : O → ℝ) (sets : O → Finset α) (hsets : Function.Injective sets)
    (h : ℕ) (hh : 0 < h) (hcard : ∀ o, (sets o).card ≤ h)
    {N : ℕ} (e : BlockParameter O (Fin h) α ≃ Fin N) (hN : 0 < N)
    {c₀ : ℝ} (hc₀ : 0 < c₀) (hc : ∀ o, c₀ ≤ |c o|) :
    ∃ r : O → Option α, ∀ (d : ℕ), 0 < d → Fintype.card O * (h - 1) ≤ d →
      ∀ (L : (Fin N → ℝ) ≃L[ℝ] (Fin N → ℝ)) (b : Fin N → ℝ)
        (Ω : Set (Fin N → ℝ)) (R u : ℝ), 1 ≤ R →
      (∀ x ∈ Ω, ∀ j, |(b + L x) j| ≤ R) → 0 < u →
      volume.real (Ω ∩ {x | |((booleanSelectedMinor c sets id (⟨0, hh⟩ : Fin h) r).map
        (MvPolynomial.eval ((b + L x) ∘ e))).det| ≤ u}) ≤
        inverseJacobian L * (R ^ N * multivariateSublevelConstant N d *
          (u * (d + 1 : ℝ) ^ N / c₀ ^ Fintype.card O) ^ (((N * d : ℕ) : ℝ)⁻¹)) := by
  obtain ⟨r, hr⟩ := exists_boolean_minor_sublevel_bound c sets hsets h hh hcard e hN hc₀ hc
  refine ⟨r, ?_⟩
  intro d hd hdeg L b Ω R u hR hΩ hu
  rw [affine_sublevel_volume_real L b Ω
    (fun x => ((booleanSelectedMinor c sets id (⟨0, hh⟩ : Fin h) r).map
      (MvPolynomial.eval (x ∘ e))).det) u]
  apply mul_le_mul_of_nonneg_left _ (inverseJacobian_pos L).le
  apply hr d hd hdeg _ R u hR _ hu
  rintro y ⟨x, hx, rfl⟩ j
  exact hΩ x hx j

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

theorem reindexedAffineSource_continuous {I : Type*} [Fintype I] {N : ℕ}
    (e : I ≃ Fin N) (L : (Fin N → ℝ) ≃L[ℝ] (Fin N → ℝ)) (b : Fin N → ℝ) :
    Continuous (reindexedAffineSource e L b) := by
  unfold reindexedAffineSource
  fun_prop

theorem reindexedAffineSource_apply {I : Type*} {N : ℕ} (e : I ≃ Fin N)
    (L : (Fin N → ℝ) ≃L[ℝ] (Fin N → ℝ)) (b x : Fin N → ℝ) :
    reindexedAffineSource e L b (x ∘ e) = (b + L x) ∘ e := by
  have he : (x ∘ e) ∘ e.symm = x := by funext j; simp
  simp only [reindexedAffineSource, he]

theorem exists_affine_cube_minor_probability_bound {O α : Type*}
    [Fintype O] [Fintype α] [DecidableEq O] [DecidableEq α]
    (c : O → ℝ) (sets : O → Finset α) (hsets : Function.Injective sets)
    (h : ℕ) (hh : 0 < h) (hcard : ∀ o, (sets o).card ≤ h)
    {N : ℕ} (e : BlockParameter O (Fin h) α ≃ Fin N) (hN : 0 < N)
    {c₀ : ℝ} (hc₀ : 0 < c₀) (hc : ∀ o, c₀ ≤ |c o|) :
    ∃ r : O → Option α, ∀ d : ℕ, 0 < d → Fintype.card O * (h - 1) ≤ d →
      ∀ (L : (Fin N → ℝ) ≃L[ℝ] (Fin N → ℝ)) (b : Fin N → ℝ) (R u : ℝ),
      1 ≤ R → (∀ x ∈ reindexedBlockCubeDomain e, ∀ j, |(b + L x) j| ≤ R) → 0 < u →
      (blockCubeMeasure O (Fin h) α).real
        {a | |booleanMinorDeterminant c sets id (⟨0, hh⟩ : Fin h) r
          (reindexedAffineSource e L b a)| ≤ u} ≤
        scalarCubeDomainDensity α ^ Fintype.card (O × Fin h) * inverseJacobian L *
          (R ^ N * multivariateSublevelConstant N d *
            (u * (d + 1 : ℝ) ^ N / c₀ ^ Fintype.card O) ^ (((N * d : ℕ) : ℝ)⁻¹)) := by
  obtain ⟨r, hr⟩ := exists_affine_boolean_minor_sublevel_bound c sets hsets h hh hcard e hN hc₀ hc
  refine ⟨r, ?_⟩
  intro d hd hdeg L b R u hR hbox hu
  have hsm : MeasurableSet {a | |booleanMinorDeterminant c sets id (⟨0, hh⟩ : Fin h) r
      (reindexedAffineSource e L b a)| ≤ u} :=
    measurableSet_le (((booleanMinorDeterminant_contDiff c sets id (⟨0, hh⟩ : Fin h) r).continuous.comp
      (reindexedAffineSource_continuous e L b)).measurable.abs) measurable_const
  rw [blockCubeMeasure_real_reindex e _ hsm]
  simp only [Set.mem_ofPred_eq, reindexedAffineSource_apply]
  have hvol := hr d hd hdeg L b (reindexedBlockCubeDomain e) R u hR hbox hu
  exact (mul_le_mul_of_nonneg_left hvol
    (pow_nonneg (scalarCubeDomainDensity_pos α).le (Fintype.card (O × Fin h)))).trans_eq
      (mul_assoc _ _ _).symm

theorem booleanMinorDeterminant_affine_sublevel_marginal {B O F α : Type*}
    [Fintype B] [Fintype O] [Fintype F] [Fintype α]
    [DecidableEq B] [DecidableEq O] [DecidableEq F] [DecidableEq α]
    (c : B → ℝ) (sets : O → Finset α) (block : O → B) (hblock : Function.Injective block)
    (v : F) (r : O → Option α)
    (T : (BlockParameter B F α → ℝ) → (BlockParameter B F α → ℝ))
    (T₀ : (BlockParameter O F α → ℝ) → (BlockParameter O F α → ℝ))
    (hT₀ : Measurable T₀)
    (hrestrict : ∀ a, restrictBlockParameters block (T a) = T₀ (restrictBlockParameters block a)) (u : ℝ) :
    (blockCubeMeasure B F α).real {a | |booleanMinorDeterminant c sets block v r (T a)| ≤ u} =
      (blockCubeMeasure O F α).real {a | |booleanMinorDeterminant (c ∘ block) sets id v r (T₀ a)| ≤ u} := by
  have hs : MeasurableSet {a | |booleanMinorDeterminant (c ∘ block) sets id v r (T₀ a)| ≤ u} :=
    measurableSet_le (((booleanMinorDeterminant_contDiff (c ∘ block) sets id v r).continuous.measurable.comp
      hT₀).abs) measurable_const
  have hm := (restrictBlockParameters_cube_measurePreserving (F := F) (α := α) block hblock).measureReal_preimage
    hs.nullMeasurableSet
  have he : {a | |booleanMinorDeterminant c sets block v r (T a)| ≤ u} =
      restrictBlockParameters block ⁻¹'
        {a | |booleanMinorDeterminant (c ∘ block) sets id v r (T₀ a)| ≤ u} := by
    ext a
    change |booleanMinorDeterminant c sets block v r (T a)| ≤ u ↔ _
    rw [booleanMinorDeterminant_restrict c sets block v r (T a), hrestrict]
    rfl
  rw [he]
  exact hm

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem inverseJacobian_coordinateScale_le {I : Type*} [Fintype I]
    (a : I → ℝ) (ha : ∀ i, a i ≠ 0) {δ : ℝ} (hδ : 0 < δ)
    (hwidth : ∀ i, δ ≤ |a i|) :
    inverseJacobian (coordinateScaleEquiv a ha).toContinuousLinearEquiv ≤ δ⁻¹ ^ Fintype.card I := by
  rw [inverseJacobian_eq]
  change |LinearMap.det (coordinateScaleEquiv a ha).toLinearMap|⁻¹ ≤ _
  rw [diagonalDensityTransport_det, Finset.abs_prod, ← Finset.prod_inv_distrib]
  calc
    _ ≤ ∏ _i : I, δ⁻¹ := by
      apply Finset.prod_le_prod
      · intro i _
        exact inv_nonneg.mpr (abs_nonneg _)
      · intro i _
        simpa only [one_div] using one_div_le_one_div_of_le hδ (hwidth i)
    _ = _ := by simp

theorem exists_allocated_affine_cube_minor_probability_bound {B O α : Type*}
    [Fintype B] [Fintype O] [Fintype α]
    [DecidableEq B] [DecidableEq O] [DecidableEq α]
    (c : B → ℝ) (sets : O → Finset α) (hsets : Function.Injective sets)
    (h : ℕ) (hh : 0 < h) (hcard : ∀ o, (sets o).card ≤ h)
    (block : O → B) (hblock : Function.Injective block)
    {N : ℕ} (e : BlockParameter O (Fin h) α ≃ Fin N) (hN : 0 < N)
    {c₀ : ℝ} (hc₀ : 0 < c₀) (hc : ∀ o, c₀ ≤ |c (block o)|) :
    ∃ r : O → Option α, ∀ d : ℕ, 0 < d → Fintype.card O * (h - 1) ≤ d →
      ∀ (center width : BlockParameter B (Fin h) α → ℝ) (δ u : ℝ), 0 < δ →
      (∀ z : BlockParameter O (Fin h) α, δ ≤ |restrictBlockParameters block width z|) →
      (∀ z : BlockParameter O (Fin h) α,
        |restrictBlockParameters block center z| + |restrictBlockParameters block width z| ≤ 1) →
      0 < u →
      (blockCubeMeasure B (Fin h) α).real
        {a | |booleanMinorDeterminant c sets block (⟨0, hh⟩ : Fin h) r
          (fun z => center z + width z * a z)| ≤ u} ≤
        scalarCubeDomainDensity α ^ Fintype.card (O × Fin h) * δ⁻¹ ^ N *
          (multivariateSublevelConstant N d *
            (u * (d + 1 : ℝ) ^ N / c₀ ^ Fintype.card O) ^ (((N * d : ℕ) : ℝ)⁻¹)) := by
  obtain ⟨r, hr⟩ := exists_affine_cube_minor_probability_bound
    (c ∘ block) sets hsets h hh hcard e hN hc₀ hc
  refine ⟨r, ?_⟩
  intro d hd hdeg center width δ u hδ hwidth hbox hu
  let w : Fin N → ℝ := restrictBlockParameters block width ∘ e.symm
  let b : Fin N → ℝ := restrictBlockParameters block center ∘ e.symm
  have hw (i) : δ ≤ |w i| := hwidth (e.symm i)
  have hwne (i) : w i ≠ 0 := abs_pos.mp (hδ.trans_le (hw i))
  let L := (coordinateScaleEquiv w hwne).toContinuousLinearEquiv
  let T := fun a : BlockParameter B (Fin h) α → ℝ => fun z => center z + width z * a z
  let T₀ := reindexedAffineSource e L b
  have hrestrict (a) : restrictBlockParameters block (T a) = T₀ (restrictBlockParameters block a) := by
    funext z
    change center (block z.1, z.2) + width (block z.1, z.2) * a (block z.1, z.2) =
      b (e z) + w (e z) * restrictBlockParameters block a (e.symm (e z))
    simp only [w, b, Function.comp_apply, e.symm_apply_apply, restrictBlockParameters]
  rw [booleanMinorDeterminant_affine_sublevel_marginal c sets block hblock (⟨0, hh⟩ : Fin h) r
    T T₀ (reindexedAffineSource_continuous e L b).measurable hrestrict u]
  have hbox' (x) (hx : x ∈ reindexedBlockCubeDomain e) (i) : |(b + L x) i| ≤ (1 : ℝ) := by
    change |b i + w i * x i| ≤ 1
    calc
      _ ≤ |b i| + |w i * x i| := abs_add_le _ _
      _ = |b i| + |w i| * |x i| := by rw [abs_mul]
      _ ≤ |b i| + |w i| := add_le_add le_rfl
        (mul_le_of_le_one_right (abs_nonneg _) (reindexedBlockCubeDomain_box e hx i))
      _ ≤ 1 := hbox (e.symm i)
  have hp := hr d hd hdeg L b 1 u le_rfl hbox' hu
  simp only [one_pow, one_mul] at hp
  apply hp.trans
  have hJ : inverseJacobian L ≤ δ⁻¹ ^ N := by
    simpa only [Fintype.card_fin] using inverseJacobian_coordinateScale_le w hwne hδ hw
  have hconst : 0 ≤ multivariateSublevelConstant N d := (multivariateSublevelConstant_pos hN d).le
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hJ (pow_nonneg (scalarCubeDomainDensity_pos α).le _))
    (mul_nonneg hconst (Real.rpow_nonneg (by positivity) _))

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem affineCubeMinorThreshold_pos (J O α : Type*) [Fintype J] [Fintype O] [Fintype α]
    [DecidableEq α] (h : ℕ) {N : ℕ} (hN : 0 < N) (d : ℕ)
    {c₀ δ η : ℝ} (hc₀ : 0 < c₀) (hδ : 0 < δ) (hη : 0 < η) :
    0 < affineCubeMinorThreshold J O α h N d c₀ δ η :=
  polynomialSublevelThreshold_pos _ _
    (mul_nonneg (cubeMinorProbabilityConstant_pos O α h hN d).le (pow_nonneg (inv_nonneg.mpr hδ.le) _))
    (cubeMinorProbabilityScale_pos O N d hc₀).le hη

theorem exists_affine_cube_minor_thresholds {B O J α : Type*}
    [Fintype B] [Fintype O] [Fintype J] [Fintype α]
    [DecidableEq B] [DecidableEq O] [DecidableEq α]
    (c : J → B → ℝ) (sets : O → Finset α) (hsets : Function.Injective sets)
    (h : ℕ) (hh : 0 < h) (hcard : ∀ o, (sets o).card ≤ h)
    (block : J → O → B) (hblock : ∀ j, Function.Injective (block j))
    {N : ℕ} (e : BlockParameter O (Fin h) α ≃ Fin N) (hN : 0 < N)
    (d : ℕ) (hd : 0 < d) (hdeg : Fintype.card O * (h - 1) ≤ d)
    {c₀ : ℝ} (hc₀ : 0 < c₀) (hc : ∀ j o, c₀ ≤ |c j (block j o)|) :
    ∃ sel : J → O → Option α, ∀ δ η : ℝ, 0 < δ → 0 < η →
      ∀ center width : BlockParameter B (Fin h) α → ℝ,
      (∀ j z, δ ≤ |restrictBlockParameters (block j) width z|) →
      (∀ j z, |restrictBlockParameters (block j) center z| +
        |restrictBlockParameters (block j) width z| ≤ 1) →
      (∑ j, (blockCubeMeasure B (Fin h) α).real
        {a | |booleanMinorDeterminant (c j) sets (block j) (⟨0, hh⟩ : Fin h) (sel j) (fun z => center z + width z * a z)| <
          2 * affineCubeMinorThreshold J O α h N d c₀ δ η}) ≤ η / 2 := by
  choose sel hsel using (fun j => exists_allocated_affine_cube_minor_probability_bound
    (c j) sets hsets h hh hcard (block j) (hblock j) e hN hc₀ (hc j))
  refine ⟨sel, ?_⟩
  intro δ η hδ hη center width hwidth hbox
  let K := cubeMinorProbabilityConstant O α h N d * δ⁻¹ ^ N
  let scale := cubeMinorProbabilityScale O N d c₀
  let κ := affineCubeMinorThreshold J O α h N d c₀ δ η
  have hK : 0 < K := mul_pos (cubeMinorProbabilityConstant_pos O α h hN d) (pow_pos (inv_pos.mpr hδ) _)
  have hscale : 0 < scale := cubeMinorProbabilityScale_pos O N d hc₀
  have hκ : 0 < κ := affineCubeMinorThreshold_pos J O α h hN d hc₀ hδ hη
  have hp (j : J) : (blockCubeMeasure B (Fin h) α).real
      {a | |booleanMinorDeterminant (c j) sets (block j) (⟨0, hh⟩ : Fin h) (sel j) (fun z => center z + width z * a z)| < 2 * κ} ≤
        K * (2 * κ * scale) ^ (((N * d : ℕ) : ℝ)⁻¹) := by
    have hm : (blockCubeMeasure B (Fin h) α).real
        {a | |booleanMinorDeterminant (c j) sets (block j) (⟨0, hh⟩ : Fin h) (sel j) (fun z => center z + width z * a z)| < 2 * κ} ≤
      (blockCubeMeasure B (Fin h) α).real
        {a | |booleanMinorDeterminant (c j) sets (block j) (⟨0, hh⟩ : Fin h) (sel j) (fun z => center z + width z * a z)| ≤ 2 * κ} := by
      apply measureReal_mono
      · intro a ha
        change |booleanMinorDeterminant (c j) sets (block j) (⟨0, hh⟩ : Fin h) (sel j) (fun z => center z + width z * a z)| ≤ 2 * κ
        exact le_of_lt ha
      · exact measure_ne_top _ _
    apply hm.trans
    have hb := hsel j d hd hdeg center width δ (2 * κ) hδ (hwidth j) (hbox j) (by positivity)
    simpa only [K, scale, cubeMinorProbabilityConstant, cubeMinorProbabilityScale,
      div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hb
  calc
    _ ≤ ∑ _j : J, K * (2 * κ * scale) ^ (((N * d : ℕ) : ℝ)⁻¹) :=
      Finset.sum_le_sum (fun j _ => hp j)
    _ = (Fintype.card J : ℝ) * K * (2 * κ * scale) ^ (((N * d : ℕ) : ℝ)⁻¹) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring
    _ ≤ η / 2 := polynomialSublevelThreshold_total_bound (Nat.mul_pos hN hd) hK.le hscale.le hη

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

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

theorem affineBooleanCubeGoodWeight_mass_lower
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

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff BigOperators NNReal

variable {B O J α : Type*} [Fintype B] [Fintype O] [Fintype J] [Fintype α]
  [DecidableEq B] [DecidableEq O] [DecidableEq α] {h : ℕ}

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators ContDiff

theorem exists_affine_cube_good_mass {B O J α : Type*}
    [Fintype B] [Fintype O] [Fintype J] [Fintype α]
    [DecidableEq B] [DecidableEq O] [DecidableEq α]
    (c : J → B → ℝ) (sets : O → Finset α) (hsets : Function.Injective sets)
    (h : ℕ) (hh : 0 < h) (hcard : ∀ o, (sets o).card ≤ h)
    (block : J → O → B) (hblock : ∀ j, Function.Injective (block j))
    {N : ℕ} (e : BlockParameter O (Fin h) α ≃ Fin N) (hN : 0 < N)
    (d : ℕ) (hd : 0 < d) (hdeg : Fintype.card O * (h - 1) ≤ d)
    {c₀ : ℝ} (hc₀ : 0 < c₀) (hc : ∀ j o, c₀ ≤ |c j (block j o)|)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hone : ∀ t, 2 ≤ |t| → ψ t = 1) :
    ∃ sel : J → O → Option α, ∀ δ η : ℝ, 0 < δ → 0 < η →
      ∀ (center width : BlockParameter B (Fin h) α → ℝ) (hw : ∀ z, width z ≠ 0),
      (∀ j z, δ ≤ |restrictBlockParameters (block j) width z|) →
      (∀ j z, |restrictBlockParameters (block j) center z| +
        |restrictBlockParameters (block j) width z| ≤ 1) →
      1 - η ≤ ∫ a, affineBooleanCubeGoodWeight c sets block (⟨0, hh⟩ : Fin h) sel
        (coordinateScaleEquiv width hw).toContinuousLinearEquiv.toContinuousLinearMap center ψ
        (fun _ => scalarCubeProductBoundaryRadius (B × Fin h) α (η / 2))
        (fun _ => affineCubeMinorThreshold J O α h N d c₀ δ η) a := by
  obtain ⟨sel, hs⟩ := exists_affine_cube_minor_thresholds c sets hsets h hh hcard
    block hblock e hN d hd hdeg hc₀ hc
  refine ⟨sel, ?_⟩
  intro δ η hδ hη center width hw hwidth hbox
  let κ := affineCubeMinorThreshold J O α h N d c₀ δ η
  have hκ : 0 < κ := affineCubeMinorThreshold_pos J O α h hN d hc₀ hδ hη
  have hr := scalarCubeProductBoundaryRadius_pos (B × Fin h) α (half_pos hη)
  have hm := affineBooleanCubeGoodWeight_mass_lower c sets block (⟨0, hh⟩ : Fin h) sel
    (coordinateScaleEquiv width hw).toContinuousLinearEquiv.toContinuousLinearMap center ψ
    (fun _ => scalarCubeProductBoundaryRadius (B × Fin h) α (η / 2)) (fun _ => κ)
    hψ hrange hone (fun _ => hr) (fun _ => hκ)
  have hp := hs δ η hδ hη center width hwidth hbox
  have he (a : BlockParameter B (Fin h) α → ℝ) :
      center + (coordinateScaleEquiv width hw).toContinuousLinearEquiv.toContinuousLinearMap a =
        fun z => center z + width z * a z := rfl
  simp only [he] at hm
  have hb := scalarCubeProductBoundaryRadius_loss (B × Fin h) α (half_pos hη)
  linarith only [hm, hp, hb]

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

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators ContDiff

variable {D α : Type*} [Fintype D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)]

theorem exists_joint_affine_boolean_good_mass
    (h : D → ℕ) (hh : ∀ d, 0 < h d)
    (c : ∀ d, B d → ℝ) (sets : ∀ d, O d → Finset α) (hsets : ∀ d, Function.Injective (sets d))
    (hcard : ∀ d o, (sets d o).card ≤ h d)
    (block : ∀ d, O d → B d) (hblock : ∀ d, Function.Injective (block d))
    (N : D → ℕ) (e : ∀ d, BlockParameter (O d) (Fin (h d)) α ≃ Fin (N d))
    (hN : ∀ d, 0 < N d) (degree : D → ℕ) (hdegree : ∀ d, 0 < degree d)
    (hdeg : ∀ d, Fintype.card (O d) * (h d - 1) ≤ degree d)
    (c₀ : D → ℝ) (hc₀ : ∀ d, 0 < c₀ d) (hc : ∀ d o, c₀ d ≤ |c d (block d o)|)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1) :
    ∃ sel : ∀ d, O d → Option α, ∀ (δ : ℝ) (η : D → ℝ), 0 < δ → (∀ d, 0 < η d) →
      ∀ (center width : ∀ d, BlockParameter (B d) (Fin (h d)) α → ℝ)
        (hw : ∀ d z, width d z ≠ 0),
      (∀ d z, δ ≤ |restrictBlockParameters (block d) (width d) z|) →
      (∀ d z, |restrictBlockParameters (block d) (center d) z| +
        |restrictBlockParameters (block d) (width d) z| ≤ 1) →
      1 - ∑ d, η d ≤ ∫ x, jointAffineBooleanGoodWeight c sets block
        (fun d => (⟨0, hh d⟩ : Fin (h d))) sel
        (fun d => (coordinateScaleEquiv (width d) (hw d)).toContinuousLinearEquiv.toContinuousLinearMap)
        center ψ (fun d _ => scalarCubeProductBoundaryRadius (B d × Fin (h d)) α (η d / 2))
        (fun d => affineCubeMinorThreshold Unit (O d) α (h d) (N d) (degree d) (c₀ d) δ (η d)) x := by
  choose sel hs using fun d => exists_affine_cube_good_mass (fun _ : Unit => c d) (sets d) (hsets d)
    (h d) (hh d) (hcard d) (fun _ => block d) (fun _ => hblock d) (e d) (hN d)
    (degree d) (hdegree d) (hdeg d) (hc₀ d) (fun _ => hc d) ψ hψ hrange hone
  refine ⟨fun d => sel d (), ?_⟩
  intro δ η hδ hη center width hw hwidth hbox
  let κ := fun d => affineCubeMinorThreshold Unit (O d) α (h d) (N d) (degree d) (c₀ d) δ (η d)
  let r := fun d (_ : B d × Fin (h d)) => scalarCubeProductBoundaryRadius (B d × Fin (h d)) α (η d / 2)
  let w := fun d => affineBooleanCubeGoodWeight (fun _ : Unit => c d) (sets d) (fun _ => block d)
    (⟨0, hh d⟩ : Fin (h d)) (fun _ => sel d ())
    (coordinateScaleEquiv (width d) (hw d)).toContinuousLinearEquiv.toContinuousLinearMap
    (center d) ψ (r d) (fun _ => κ d)
  have hspec (d) := affineBooleanCubeGoodWeight_spec (fun _ : Unit => c d) (sets d) (fun _ => block d)
    (⟨0, hh d⟩ : Fin (h d)) (fun _ => sel d ())
    (coordinateScaleEquiv (width d) (hw d)).toContinuousLinearEquiv.toContinuousLinearMap
    (center d) ψ (r d) (fun _ => κ d) hψ hrange hzero
    (fun _ => scalarCubeProductBoundaryRadius_pos _ _ (half_pos (hη d)))
    (fun _ => affineCubeMinorThreshold_pos Unit (O d) α (h d) (hN d) (degree d) (hc₀ d) hδ (hη d))
  have hu (d) : (∫ y, w d y) ≤ 1 := by
    have he : (fun y => |w d y|) = w d := funext (fun y => abs_of_nonneg ((hspec d).2.2.1 y))
    have hu := (hspec d).2.2.2.1
    change (∫ y, |w d y|) ≤ 1 at hu
    rw [he] at hu
    exact hu
  apply sigmaAxisWeight_mass_loss w (fun d => (hspec d).2.2.1) hu η
  intro d
  have he : (fun _ : Unit => sel d ()) = sel d := funext (fun j => by cases j; rfl)
  change 1 - η d ≤ ∫ a, affineBooleanCubeGoodWeight _ _ _ _ (fun _ : Unit => sel d ()) _ _ _ _ _ a
  rw [he]
  exact hs d δ (η d) hδ (hη d) (center d) (width d) (hw d) (fun _ => hwidth d) (fun _ => hbox d)

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

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)] {h : D → ℕ}

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped ContDiff NNReal BigOperators

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)] {h : D → ℕ}

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators ContDiff NNReal

variable {D α : Type*} [Fintype D] [Fintype α] [decidableEqAlpha : DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]

theorem exists_canonical_joint_affine_good_mass
    [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)] [∀ d, Nonempty (O d)]
    (h : D → ℕ) (hh : ∀ d, 0 < h d)
    (c : ∀ d, B d → ℝ) (sets : ∀ d, O d → Finset α) (hsets : ∀ d, Function.Injective (sets d))
    (hcard : ∀ d o, (sets d o).card ≤ h d)
    (block : ∀ d, O d → B d) (hblock : ∀ d, Function.Injective (block d))
    (c₀ : D → ℝ) (hc₀ : ∀ d, 0 < c₀ d) (hc : ∀ d o, c₀ d ≤ |c d (block d o)|)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1) :
    ∃ sel : ∀ d, O d → Option α, ∀ (δ : ℝ) (η : D → ℝ), 0 < δ → (∀ d, 0 < η d) →
      ∀ (center width : ∀ d, BlockParameter (B d) (Fin (h d)) α → ℝ)
        (hw : ∀ d z, width d z ≠ 0),
      (∀ d z, δ ≤ |width d z|) → (∀ d z, |center d z| + |width d z| ≤ 1) →
      1 - ∑ d, η d ≤ ∫ x, jointAffineBooleanGoodWeight c sets block
        (fun d => (⟨0, hh d⟩ : Fin (h d))) sel
        (fun d => (coordinateScaleEquiv (width d) (hw d)).toContinuousLinearEquiv.toContinuousLinearMap)
        center ψ (fun d _ => scalarCubeProductBoundaryRadius (B d × Fin (h d)) α (η d / 2))
        (fun d => canonicalAffineCubeMinorThreshold (O d) α (h d) (c₀ d) δ (η d)) x := by
  obtain ⟨sel, hs⟩ := exists_joint_affine_boolean_good_mass h hh c sets hsets hcard block hblock
    (fun d => cubeMinorVariableCount (O d) α (h d)) (fun d => booleanBlockParameterEquiv (O d) α (h d))
    (fun d => boolean_minor_parameter_count_pos (O d) α (hh d))
    (fun d => cubeMinorDegree (O d) (h d)) (fun _ => lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _))
    (fun _ => le_max_right _ _) c₀ hc₀ hc ψ hψ hrange hzero hone
  refine ⟨sel, ?_⟩
  intro δ η hδ hη center width hw hwidth hbox
  exact hs δ η hδ hη center width hw
    (fun d z => hwidth d ((block d z.1, z.2.1, z.2.2)))
    (fun d z => hbox d ((block d z.1, z.2.1, z.2.2)))

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped ContDiff NNReal BigOperators

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)] {h : D → ℕ}

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators ContDiff NNReal

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)] [∀ d, Nonempty (O d)]

end Erdos3

end

end OAI

end

theorem solution.{u_1, u_2, u_3, u_4} : type_of% @OAI.Erdos3.exists_canonical_joint_affine_good_mass.{u_1, u_2, u_3, u_4} := @OAI.Erdos3.exists_canonical_joint_affine_good_mass.{u_1, u_2, u_3, u_4}
