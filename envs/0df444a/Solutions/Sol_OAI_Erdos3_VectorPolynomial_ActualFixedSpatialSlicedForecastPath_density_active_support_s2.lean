-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.density_active_support_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T06:34:26.228754+00:00
-- url     : https://prove2.me/submissions/00a64e16-d4c1-480c-8d10-f01067c3b48a

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B125
import Definitions.Def_OAIE3v2B126
import Definitions.Def_OAIE3v2B301
import Theorems.Thm_OAI_Erdos3_canonicalSlicedPrincipalDensity_law_bounds_s2

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.SampledWeightCellLaw
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

variable {ι : Type*} [Fintype ι]

theorem independentCoordinateDensity_cap (f : ι → ℝ → ℝ) (C : ι → ℝ)
    (hf : ∀ i x, f i x ∈ Set.Icc (0 : ℝ) (C i)) (x : ι → ℝ) :
    independentCoordinateDensity f x ∈ Set.Icc (0 : ℝ) (∏ i, C i) :=
  ⟨Finset.prod_nonneg (fun i _ => (hf i (x i)).1),
    Finset.prod_le_prod (fun i _ => (hf i (x i)).1) (fun i _ => (hf i (x i)).2)⟩

theorem independentCoordinateDensity_lipschitz (f : ι → ℝ → ℝ) (C L : ι → ℝ≥0)
    (hf : ∀ i x, f i x ∈ Set.Icc (0 : ℝ) (C i)) (hL : ∀ i, LipschitzWith (L i) (f i)) :
    LipschitzWith ((∏ i, (C i + 1)) * ∑ i, L i) (independentCoordinateDensity f) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq]
  have h := bounded_nonnegative_prod_difference Finset.univ (fun i => f i (x i))
    (fun i => f i (y i)) (fun i => (C i : ℝ) + 1)
    (fun i => by linarith [(C i).coe_nonneg])
    (fun i => ⟨(hf i _).1, (hf i _).2.trans (by linarith)⟩)
    (fun i => ⟨(hf i _).1, (hf i _).2.trans (by linarith)⟩)
  have hsum : (∑ i, |f i (x i) - f i (y i)|) ≤ (∑ i, (L i : ℝ)) * dist x y := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i _
    have hi := (hL i).dist_le_mul (x i) (y i)
    rw [Real.dist_eq] at hi
    exact hi.trans (mul_le_mul_of_nonneg_left (dist_le_pi_dist x y i) (L i).coe_nonneg)
  apply h.trans
  have hprod : 0 ≤ ∏ i, ((C i : ℝ) + 1) :=
    Finset.prod_nonneg (fun i _ => add_nonneg (C i).coe_nonneg zero_le_one)
  have hb := mul_le_mul_of_nonneg_left hsum hprod
  simpa only [NNReal.coe_mul, NNReal.coe_prod, NNReal.coe_sum, NNReal.coe_add,
    NNReal.coe_one, mul_assoc] using hb

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

theorem unitBoxMeasure_ae : ∀ᵐ x ∂unitBoxMeasure ι, ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1 := by
  filter_upwards [ae_restrict_mem (μ := volume) (positiveUnitBox_measurable (ι := ι))] with x hx
  exact fun i => hx i (Set.mem_univ i)

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

variable {D : Type*} [Fintype D] {I : D → Type*} [∀ d, Fintype (I d)]

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

theorem realDensityMeasure_eq_indicator_of_ae {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) {S : Set X} (hS : MeasurableSet S)
    (hf : ∀ᵐ x ∂realDensityMeasure μ f, x ∈ S) :
    realDensityMeasure μ f = realDensityMeasure μ (S.indicator f) := by
  rw [realDensityMeasure_indicator μ f hS, Measure.restrict_eq_self_of_ae_mem hf]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

theorem continuousDensity_zero_off_closed {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [SigmaFinite μ] [μ.IsOpenPosMeasure]
    (f : X → ℝ) (hf : Continuous f) (hf0 : ∀ x, 0 ≤ f x)
    {S : Set X} (hS : IsClosed S) (hs : ∀ᵐ x ∂realDensityMeasure μ f, x ∈ S) :
    ∀ x ∉ S, f x = 0 := by
  have hm := realDensityMeasure_eq_indicator_of_ae μ f hS.measurableSet hs
  have hi : Measurable (S.indicator f) := hf.measurable.indicator hS.measurableSet
  have h := (withDensity_eq_iff_of_sigmaFinite
    hf.measurable.ennreal_ofReal.aemeasurable hi.ennreal_ofReal.aemeasurable).mp hm
  have he : f =ᵐ[μ.restrict Sᶜ] (fun _ => 0) := by
    filter_upwards [ae_restrict_of_ae h, ae_restrict_mem hS.measurableSet.compl] with x hx hxS
    rw [Set.indicator_of_notMem hxS, ENNReal.ofReal_zero] at hx
    exact le_antisymm (ENNReal.ofReal_eq_zero.mp hx) (hf0 x)
  have hall := Measure.eqOn_open_of_ae_eq he hS.isOpen_compl hf.continuousOn continuousOn_const
  exact fun x hx => hall hx

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.SlicedRemainderDensityFamily
namespace OAI

section

namespace Erdos3

open MeasureTheory

variable {D : Type*} [Fintype D] {I O : D → Type*}
  [∀ d, Fintype (I d)] [∀ d, Fintype (O d)]

omit [∀ d, Fintype (O d)] in
theorem sigmaAxisSampler_measurable (U : ∀ d, (I d → ℝ) → (O d → ℝ))
    (hU : ∀ d, Measurable (U d)) : Measurable (sigmaAxisSampler U) :=
  measurable_pi_iff.mpr (fun s => (measurable_pi_apply s.2).comp
    ((hU s.1).comp (sigmaAxisProjection I s.1).continuous.measurable))

theorem sigmaAxisSampler_image_law (μ : ∀ d, Measure (I d → ℝ))
    [∀ d, IsProbabilityMeasure (μ d)]
    (U : ∀ d, (I d → ℝ) → (O d → ℝ)) (hU : ∀ d, Measurable (U d)) :
    Measure.map (sigmaAxisSampler U) (sigmaAxisMeasure μ) =
      sigmaAxisMeasure (fun d => Measure.map (U d) (μ d)) := by
  let : ∀ d, IsProbabilityMeasure (Measure.map (U d) (μ d)) :=
    fun d => Measure.isProbabilityMeasure_map (hU d).aemeasurable
  rw [sigmaAxisMeasure, Measure.map_map (sigmaAxisSampler_measurable U hU)
    (sigmaAxisCoordinates I).symm.continuous.measurable]
  have he : sigmaAxisSampler U ∘ (sigmaAxisCoordinates I).symm =
      (sigmaAxisCoordinates O).symm ∘ (fun x d => U d (x d)) := rfl
  have hPi : Measurable (fun x : ∀ d, I d → ℝ => fun d => U d (x d)) :=
    measurable_pi_iff.mpr (fun d => (hU d).comp (measurable_pi_apply d))
  rw [he, ← Measure.map_map (sigmaAxisCoordinates O).symm.continuous.measurable
    hPi]
  rw [Measure.pi_map_pi (fun d => (hU d).aemeasurable)]
  rfl

end Erdos3

end

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

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem sigmaAxisMeasure_unitBox {D : Type*} [Fintype D] (I : D → Type*) [∀ d, Fintype (I d)] :
    sigmaAxisMeasure (fun d => unitBoxMeasure (I d)) = unitBoxMeasure (Σ d, I d) := by
  unfold sigmaAxisMeasure
  simp_rw [unitBoxMeasure_eq_pi]
  exact sigmaProductMeasure_flatten (fun _ : Σ d, I d => unitScalarMeasure)

theorem realDensityMeasure_unit_lift (f : ℝ → ℝ) :
    (realDensityMeasure volume f).map (fun x (_ : Unit) => x) =
      realDensityMeasure volume (fun v : Unit → ℝ => f (v ())) := by
  have hvol := (volume_preserving_funUnique Unit ℝ).symm (MeasurableEquiv.funUnique Unit ℝ)
  have he := realDensityMeasure_map_equiv (MeasurableEquiv.funUnique Unit ℝ).symm volume f
  rw [hvol.map_eq] at he
  exact he

theorem unit_lift_integral (f : ℝ → ℝ) :
    (∫ v : Unit → ℝ, f (v ())) = ∫ x, f x :=
  (volume_preserving_funUnique Unit ℝ).integral_comp (MeasurableEquiv.funUnique Unit ℝ).measurableEmbedding f

theorem scalarJoint_image_density
    {D : Type*} [Fintype D] {I : D → Type*} [∀ d, Fintype (I d)]
    (F : ∀ d, (I d → ℝ) → ℝ) (hF : ∀ d, Measurable (F d)) (f : D → ℝ → ℝ)
    (_hf : ∀ d, Integrable (f d)) (hf0 : ∀ d x, 0 ≤ f d x) (hfm : ∀ d, (∫ x, f d x) = 1)
    (hlaw : ∀ d, (unitBoxMeasure (I d)).map (F d) = realDensityMeasure volume (f d))
    (shift : D → ℝ) :
    (unitBoxMeasure (Σ d, I d)).map
        (fun x (o : Σ _d : D, Unit) => shift o.1 + F o.1 (fun i => x ⟨o.1, i⟩)) =
      realDensityMeasure volume
        (sigmaAxisWeight (fun d (v : Unit → ℝ) => f d (v () - shift d))) := by
  let U := fun d (x : I d → ℝ) (_ : Unit) => shift d + F d x
  have hU (d) : Measurable (U d) := measurable_pi_iff.mpr (fun _ => measurable_const.add (hF d))
  have hsingle (d) : (unitBoxMeasure (I d)).map (U d) =
      realDensityMeasure volume (fun v : Unit → ℝ => f d (v () - shift d)) := by
    have ha : Measurable (fun x : ℝ => x + shift d) := measurable_id.add measurable_const
    have hc : Measurable (fun x : ℝ => fun _ : Unit => x) := measurable_pi_iff.mpr (fun _ => measurable_id)
    rw [← realDensityMeasure_unit_lift (fun y => f d (y - shift d)), ← realDensityMeasure_map_add_right,
      ← hlaw d, Measure.map_map ha (hF d), Measure.map_map hc (ha.comp (hF d))]
    congr 1
    funext x u
    exact add_comm _ _
  have hi (d) : Integrable (fun v : Unit → ℝ => f d (v () - shift d)) := by
    apply Integrable.of_integral_ne_zero
    rw [unit_lift_integral (fun y => f d (y - shift d)), integral_sub_right_eq_self, hfm d]
    exact one_ne_zero
  rw [← sigmaAxisMeasure_unitBox I]
  change (sigmaAxisMeasure (fun d => unitBoxMeasure (I d))).map (sigmaAxisSampler U) = _
  rw [sigmaAxisSampler_image_law _ U hU]
  simp_rw [hsingle]
  exact sigmaAxisMeasure_density _ hi (fun d v => hf0 d _)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {B F : Type*} [Fintype B] [Fintype F] [DecidableEq B] [DecidableEq F]

omit [DecidableEq B] [DecidableEq F] in
theorem principalSliceValue_measurable [DecidableEq B] [DecidableEq F]
    (c : B → ℝ) (lower width : B × F → ℝ) :
    Measurable (principalSliceValue c lower width) := by
  unfold principalSliceValue
  fun_prop

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.IntegerPolynomialActiveProfileSupport
namespace OAI

section

namespace Erdos3

variable {J V : Type*}
variable (P : Finset J) (j₀ : J) (h K L s : ℕ)
variable (hh : 0 < h) (hK : 0 < K) (hL : 0 < L)
variable (T : V → ℝ) (hT : ∀ v, 0 < T v) (hTL : ∀ v, T v ≤ L)
variable (e : J → V →₀ ℕ) (he : ∀ j, (e j).sum (fun _ n => n) ≤ s)
variable (ρ γ ε : ℝ) (hρ : 0 < ρ) (hγ : 0 < γ) (hε : 0 < ε)
variable (hgap : L ^ h < K → (principalSamplingGapRatio γ * L) ^ h ≤ K)
variable (hεL : 8 * (probabilityProfileLipschitz : ℝ) ≤ ε * L)

theorem integerPolynomialCoordinatePMF_active_profile_bound
    (hj₀ : j₀ ∉ P) (he₀ : e j₀ = 0)
    (hprincipal : ∀ j ∈ P,
      monomialScale T (e j) = (integerAxisSideLength h K L γ : ℝ) ^ h)
    (hactive : L ^ h < K) (j : J) {k : ℤ}
    (hk : k ∈ (integerPolynomialCoordinatePMF P j₀ h K L s hh hK hL T hT hTL e he
      ρ γ ε hρ hγ hε hgap hεL j).support) :
    |(k : ℝ) / K * monomialScale T (e j) - coefficientProfileCenter P γ j| ≤
      coefficientProfileWidth P j₀ ρ γ ε j := by
  classical
  by_cases hj : j = j₀
  · subst j
    simp only [integerPolynomialCoordinatePMF, ↓reduceIte] at hk
    have hb := constantIntegerPMF_support K ρ (by exact_mod_cast hK) hρ hk
    simp only [coefficientProfileCenter, coefficientProfileWidth, hj₀, ↓reduceIte,
      he₀, monomialScale_zero, mul_one, sub_zero]
    linarith
  · by_cases hp : j ∈ P
    · simp only [integerPolynomialCoordinatePMF, hj, hp, ↓reduceIte] at hk
      have hb := integerAxisPrincipalPMF_active hh hK hL hγ hgap hactive hk
      have hscale : monomialScale T (e j) = (L : ℝ) ^ h := by
        rw [hprincipal j hp]
        simp only [integerAxisSideLength, hactive, ↓reduceIte]
      simp only [coefficientProfileCenter, coefficientProfileWidth, hj, hp, ↓reduceIte, hscale]
      have heq : (k : ℝ) / K * (L : ℝ) ^ h = (L : ℝ) ^ h * (k : ℝ) / K := by ring
      rw [heq, abs_le]
      constructor <;> linarith [hb.1, hb.2]
    · simp only [integerPolynomialCoordinatePMF, hj, hp, ↓reduceIte] at hk
      have hb := integerAxisTailPMF_support T hT hK hL hTL hε hεL (e j) (he j) hk
      simp only [coefficientProfileCenter, coefficientProfileWidth, hj, hp, ↓reduceIte,
        sub_zero, abs_mul, abs_of_pos (monomialScale_pos T hT (e j))]
      linarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.LayerSamplerWitnessScale
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule

variable {m : ℕ}

variable {G : Type*} {I : Fin m → Type*} {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

theorem layerContinuousPrincipalSlots_card (j : Fin m) (i : I j) :
    (layerContinuousPrincipalSlots (G := G) B j i).card = Fintype.card (B ⟨j, Sum.inl i⟩) :=
  principalCoefficientSlots_card _ _ (Nat.zero_lt_succ _)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.JointBooleanStability
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {B F : Type*} [Fintype B] [Fintype F]

theorem principalSliceValue_abs_le (c : B → ℝ) (lower width : B × F → ℝ)
    (hwidth : ∀ p, |lower p| + |width p| ≤ 1)
    (x : B × F → ℝ) (hx : ∀ p, |x p| ≤ 1) :
    |principalSliceValue c lower width x| ≤ ∑ b, |c b| := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro b _
  rw [abs_mul, Finset.abs_prod]
  have hp : (∏ i : F, |lower (b,i) + width (b,i) * x (b,i)|) ≤ 1 := by
    apply Finset.prod_le_one (fun _ _ => abs_nonneg _)
    intro i _
    apply (abs_add_le _ _).trans
    rw [abs_mul]
    exact (add_le_add le_rfl (mul_le_of_le_one_right (abs_nonneg _) (hx _))).trans (hwidth _)
  exact mul_le_of_le_one_right (abs_nonneg _) hp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ActiveProfileNoise
namespace OAI

section

namespace Erdos3

theorem principalProfileSize_mul (R S : ℝ) (b : ℕ) :
    principalProfileSize (R * S) b = R * principalProfileSize S b := by
  unfold principalProfileSize
  ring

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

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {D : Type*} [Fintype D] (B : D → Type*) [∀ d, Fintype (B d)]

theorem unitProfilePrincipalLowerBound_le (d : D) :
    unitProfilePrincipalLowerBound B ≤ unitProfilePrincipalSize (B := B) d := by
  classical
  have hcard : Fintype.card (B d) ≤ ∑ a, Fintype.card (B a) :=
    Finset.single_le_sum (f := fun a : D => Fintype.card (B a))
      (fun a _ => Nat.zero_le _) (Finset.mem_univ d)
  unfold unitProfilePrincipalLowerBound unitProfilePrincipalSize principalProfileSize
  apply one_div_le_one_div_of_le (by positivity)
  have hcardR : (Fintype.card (B d) : ℝ) ≤ ((∑ a, Fintype.card (B a) : ℕ) : ℝ) := by
    exact_mod_cast hcard
  linarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedKernelScaleWithCutoff
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Matrix Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

theorem allocatedContinuousProfileScales_pos (j : Fin m) (d) :
    0 < allocatedContinuousProfileScales B U basis S j d :=
  one_div_pos.mpr (monomialScale_pos _
    (fun v => lt_of_lt_of_le zero_lt_one (layerSamplerBox_one_le B U basis S v)) d.val)

include hR hσ in
theorem allocatedContinuousProfileWidths_pos (j : Fin m) (i : I j) (d) :
    0 < allocatedContinuousProfileWidths (G := G) B R σ j i d :=
  coefficientProfileWidth_pos _ _ (div_pos (hR j) (by norm_num))
    (principalProfileSize_pos (hR j) _) (tailProfileSize_pos (hR j) (hσ j) _) d

theorem allocatedLayerCenters_scale (j : Fin m) (i : I j) (d) :
    allocatedLayerCenters B U basis S j i d =
      allocatedContinuousProfileScales B U basis S j d * allocatedContinuousProfileCenters B R j i d := by
  unfold allocatedLayerCenters allocatedArrayCenters allocatedContinuousProfileScales
    allocatedContinuousProfileCenters
  ring

theorem allocatedLayerWidths_scale (j : Fin m) (i : I j) (d) :
    allocatedLayerWidths B U basis S j i d =
      allocatedContinuousProfileScales B U basis S j d * allocatedContinuousProfileWidths B R σ j i d := by
  unfold allocatedLayerWidths allocatedArrayWidths allocatedContinuousProfileScales
    allocatedContinuousProfileWidths
  ring

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedPartitionedProfileJet
namespace OAI

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

theorem allocatedAxisProfilePolynomial_eq (R σ : Fin m → ℝ) (a : LayerSamplerAxis I n)
    (r : SamplerCoefficientSlot G B (layerSamplerDegree I n) a → ℝ) :
    allocatedAxisProfilePolynomial B R σ a r =
      monomialArrayPolynomial Subtype.val (fun e =>
        coefficientProfileCenter (principalCoefficientSlots (layerSamplerDegree I n) a)
          (principalProfileSize (R a.1) (Fintype.card (B a))) e +
        coefficientProfileWidth (principalCoefficientSlots (layerSamplerDegree I n) a)
          (constantCoefficientSlot _ _) (R a.1 / 4)
          (principalProfileSize (R a.1) (Fintype.card (B a)))
          (tailProfileSize (R a.1) (σ a.1)
            (Fintype.card (SamplerCoefficientSlot G B (layerSamplerDegree I n) a))) e * r e) := by
  rcases a with ⟨j, i⟩
  cases i with
  | inl i =>
    simp only [allocatedAxisProfilePolynomial, allocatedContinuousProfileCenters,
      allocatedContinuousProfileWidths, layerContinuousPrincipalSlots_card]
    rfl
  | inr i =>
    simp only [allocatedAxisProfilePolynomial, allocatedIntegerProfileCenters,
      allocatedIntegerProfileWidths, layerIntegerPrincipalSlots_card]
    rfl

end Erdos3.VectorPolynomial

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

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedSlicedIdealDensity
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

variable {D : Type*} [Fintype D] {B F : D → Type*}
variable [∀ d, Fintype (B d)] [∀ d, Fintype (F d)]
variable [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (F d)]
variable (hB : ∀ d, 4 ≤ Fintype.card (B d)) (i : ∀ d, F d)

theorem jointSlicedPrincipalDensity_image_probability
    (c : ∀ d, B d → ℝ) (lower width : ∀ d, B d × F d → ℝ) (shift : D → ℝ)
    {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ)
    (hc : ∀ d b, a ≤ |c d b|) (hw : ∀ d p, δ ≤ width d p) (hl : ∀ d p, 0 ≤ lower d p) :
    (unitBoxMeasure (Σ d, B d × F d)).map
      (fun x => (fun o : Σ _d : D, Unit => shift o.1) + jointSlicedPrincipal c lower width x) =
        realDensityMeasure volume (jointSlicedPrincipalDensity hB i c lower width shift) ∧
      (∀ y, 0 ≤ jointSlicedPrincipalDensity hB i c lower width shift y) ∧
      Integrable (jointSlicedPrincipalDensity hB i c lower width shift) ∧
      (∫ y, jointSlicedPrincipalDensity hB i c lower width shift y) = 1 := by
  have hs (d) := canonicalSlicedPrincipalDensity_law_bounds_s2 (hB d) (i d) (c d) (lower d) (width d)
    ha hδ (hc d) (hw d) (hl d)
  have hmass : (∫ y, jointSlicedPrincipalDensity hB i c lower width shift y) = 1 := by
    rw [jointSlicedPrincipalDensity, sigmaAxisWeight_integral]
    apply Finset.prod_eq_one
    intro d _
    rw [unit_lift_integral (fun y => canonicalSlicedPrincipalDensity (hB d) (i d)
      (c d) (lower d) (width d) (y - shift d)), integral_sub_right_eq_self]
    exact (hs d).2.2.2.2
  refine ⟨?_, sigmaAxisWeight_nonneg _ (fun d y => ((hs d).2.1 _).1),
    Integrable.of_integral_ne_zero (hmass.trans_ne one_ne_zero), hmass⟩
  exact scalarJoint_image_density (fun d => principalSliceValue (c d) (lower d) (width d))
    (fun d => principalSliceValue_measurable _ _ _)
    (fun d => canonicalSlicedPrincipalDensity (hB d) (i d) (c d) (lower d) (width d))
    (fun d => (hs d).2.2.2.1) (fun d y => ((hs d).2.1 y).1) (fun d => (hs d).2.2.2.2)
    (fun d => (hs d).1) shift

theorem jointSlicedPrincipalDensity_coordinate_product
    (c : ∀ d, B d → ℝ) (lower width : ∀ d, B d × F d → ℝ) (shift : D → ℝ) :
    jointSlicedPrincipalDensity hB i c lower width shift =
      independentCoordinateDensity (fun o : Σ _d : D, Unit =>
        fun y => canonicalSlicedPrincipalDensity (hB o.1) (i o.1) (c o.1) (lower o.1) (width o.1)
          (y - shift o.1)) := by
  let _ : ∀ index, DecidableEq (B index) := inferInstance
  funext y
  simp [jointSlicedPrincipalDensity, sigmaAxisWeight, tensorCutoffWeight,
    independentCoordinateDensity, Fintype.prod_sigma, sigmaAxisCoordinates]

theorem jointSlicedPrincipalDensity_cap_lipschitz
    (c : ∀ d, B d → ℝ) (lower width : ∀ d, B d × F d → ℝ) (shift : D → ℝ)
    {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ)
    (hc : ∀ d b, a ≤ |c d b|) (hw : ∀ d p, δ ≤ width d p) (hl : ∀ d p, 0 ≤ lower d p) :
    let K := fun d => SlicedProductBlock.uniformCap {j : F d // j ≠ i d}
      (a * δ ^ (Fintype.card {j : F d // j ≠ i d} + 1)) (mul_pos ha (pow_pos hδ _))
    (∀ y, jointSlicedPrincipalDensity hB i c lower width shift y ∈ Set.Icc (0 : ℝ) (∏ d, K d)) ∧
      LipschitzWith ((∏ d, (K d + 1)) * ∑ d, K d * (2 * K d))
        (jointSlicedPrincipalDensity hB i c lower width shift) := by
  intro K
  have hd (d) := canonicalSlicedPrincipalDensity_law_bounds_s2 (hB d) (i d) (c d) (lower d) (width d)
    ha hδ (hc d) (hw d) (hl d)
  let f := fun (o : Σ _d : D, Unit) (y : ℝ) =>
    canonicalSlicedPrincipalDensity (hB o.1) (i o.1) (c o.1) (lower o.1) (width o.1) (y - shift o.1)
  have hcap (o : Σ _d : D, Unit) (y : ℝ) : f o y ∈ Set.Icc (0 : ℝ) (K o.1) := (hd o.1).2.1 _
  have hLip (o : Σ _d : D, Unit) : LipschitzWith (K o.1 * (2 * K o.1)) (f o) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have he := ((hd o.1).2.2.1).dist_le_mul (x - shift o.1) (y - shift o.1)
    simpa only [dist_sub_right] using he
  rw [jointSlicedPrincipalDensity_coordinate_product]
  have hcap' := independentCoordinateDensity_cap f (fun o => (K o.1 : ℝ)) hcap
  have hLip' := independentCoordinateDensity_lipschitz f (fun o => K o.1) (fun o => K o.1 * (2 * K o.1)) hcap hLip
  constructor
  · simpa only [Fintype.prod_sigma, Fintype.prod_unique, NNReal.coe_prod] using hcap'
  · simpa only [Fintype.prod_sigma, Fintype.prod_unique, Fintype.sum_sigma, Fintype.sum_unique] using hLip'

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

theorem allocatedAxisProfilePolynomial_principal_coeff
    (R σ : Fin m → ℝ) (a : LayerSamplerAxis I n)
    (r : SamplerCoefficientSlot G B (layerSamplerDegree I n) a → ℝ) (b : B a) :
    (allocatedAxisProfilePolynomial B R σ a r).coeff
        (canonicalPrincipalExponent (layerSamplerDegree I n) a b) =
      3 * principalProfileSize (R a.1) (Fintype.card (B a)) / 2 +
        principalProfileSize (R a.1) (Fintype.card (B a)) / 2 *
          r (principalCoefficientSlot (layerSamplerDegree I n) a b) := by
  rw [allocatedAxisProfilePolynomial_eq]
  change (monomialArrayPolynomial Subtype.val _).coeff
    (principalCoefficientSlot (layerSamplerDegree I n) a b).val = _
  rw [monomialArrayPolynomial_coeff Subtype.val Subtype.val_injective]
  have hp : principalCoefficientSlot (layerSamplerDegree I n) a b ∈
      principalCoefficientSlots (G := G) (layerSamplerDegree I n) a :=
    (mem_principalCoefficientSlots _ _ _).mpr ⟨b, rfl⟩
  have hz : principalCoefficientSlot (G := G) (layerSamplerDegree I n) a b ≠
      constantCoefficientSlot _ _ := by
    intro hz
    exact constantCoefficientSlot_not_principal (layerSamplerDegree I n) a
      (Nat.zero_lt_succ _) (hz ▸ hp)
  simp only [coefficientProfileCenter, coefficientProfileWidth, hp, hz, ite_true, ite_false]

theorem allocatedAxisProfilePolynomial_constant_coeff
    (R σ : Fin m → ℝ) (a : LayerSamplerAxis I n)
    (r : SamplerCoefficientSlot G B (layerSamplerDegree I n) a → ℝ) :
    (allocatedAxisProfilePolynomial B R σ a r).coeff 0 =
      R a.1 / 4 * r (constantCoefficientSlot _ _) := by
  rw [allocatedAxisProfilePolynomial_eq]
  change (monomialArrayPolynomial Subtype.val _).coeff
    (constantCoefficientSlot (LayerSamplerVariables G I n B) (layerSamplerDegree I n a)).val = _
  rw [monomialArrayPolynomial_coeff Subtype.val Subtype.val_injective]
  simp only [coefficientProfileCenter, coefficientProfileWidth,
    constantCoefficientSlot_not_principal (layerSamplerDegree I n) a (Nat.zero_lt_succ _),
    ite_false, ite_true, zero_add]

variable [∀ a, DecidableEq (B a)]
variable (P : LayerSamplerAxis I n → Prop) [DecidablePred P]
variable (R σ : Fin m → ℝ)

local notation "degree" => layerSamplerDegree I n
local notation "Active" => {a // ¬P a}
local notation "Coeff" => ActiveProfileCoefficientIndex G B degree P
local notation "Input" => (Σ a : {a : LayerSamplerAxis I n // ¬P a},
  B (Subtype.val a) × Fin (layerSamplerDegree I n (Subtype.val a)))

omit [∀ a, DecidableEq (B a)] [DecidablePred P] in
theorem allocatedFixedPathPrincipal_eq (hR : ∀ j, R j ≠ 0) (r : Coeff → ℝ) :
    allocatedFixedPathPrincipal B P R σ r =
      jointSlicedProfilePrincipal degree Subtype.val (unitProfilePrincipalSize (B := B))
        (fun a e => r ⟨a, e⟩) := by
  funext a b
  rw [allocatedFixedPathPrincipal, allocatedAxisProfilePolynomial_principal_coeff]
  have hs : principalProfileSize (R a.val.1) (Fintype.card (B a.val)) =
      R a.val.1 * unitProfilePrincipalSize (B := B) a.val := by
    simpa only [unitProfilePrincipalSize, mul_one] using
      principalProfileSize_mul (R a.val.1) 1 (Fintype.card (B a.val))
  rw [hs]
  unfold jointSlicedProfilePrincipal
  field_simp [hR]

omit [∀ a, DecidableEq (B a)] [DecidablePred P] in
theorem allocatedFixedPathShift_eq (hR : ∀ j, R j ≠ 0) (r : Coeff → ℝ) :
    allocatedFixedPathShift B P R σ r =
      fun a => (1 / 4 : ℝ) * r ⟨a, constantCoefficientSlot _ _⟩ := by
  funext a
  rw [allocatedFixedPathShift, allocatedAxisProfilePolynomial_constant_coeff]
  field_simp [hR]

theorem allocatedFixedPathPrincipal_bounds (hR : ∀ j, R j ≠ 0)
    (r : Coeff → ℝ) (hr : ∀ e, |r e| ≤ 1) (a : Active) (b : B a.val) :
    unitProfilePrincipalSize (B := B) a.val ≤ |allocatedFixedPathPrincipal B P R σ r a b| ∧
      |allocatedFixedPathPrincipal B P R σ r a b| ≤ 2 * unitProfilePrincipalSize (B := B) a.val := by
  let _ : ∀ axisIndex, DecidableEq (B axisIndex) := inferInstance
  let _ : DecidablePred P := inferInstance
  rw [allocatedFixedPathPrincipal_eq B P R σ hR]
  exact jointSlicedProfilePrincipal_unit_bounds degree Subtype.val
    (fun a e => r ⟨a, e⟩) (fun _ _ => hr _) a b

theorem allocatedFixedPathLiftDensity_law_probability
    (hR : ∀ j, R j ≠ 0) (hB : ∀ a : Active, 4 ≤ Fintype.card (B a.val))
    (lower width : ∀ a : Active, B a.val × Fin (degree a.val) → ℝ)
    {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ)
    (hprincipal : ∀ j : Active, a ≤ unitProfilePrincipalSize (B := B) j.val)
    (hw : ∀ j p, δ ≤ width j p) (hl : ∀ j p, 0 ≤ lower j p)
    (r : Coeff → ℝ) (hr : ∀ e, |r e| ≤ 1) :
    (unitBoxMeasure Input).map (allocatedFixedPathLiftMap B P R σ lower width r) =
        realDensityMeasure volume (allocatedFixedPathLiftDensity B P R σ hB lower width r) ∧
      (∀ y, 0 ≤ allocatedFixedPathLiftDensity B P R σ hB lower width r y) ∧
      Integrable (allocatedFixedPathLiftDensity B P R σ hB lower width r) ∧
      (∫ y, allocatedFixedPathLiftDensity B P R σ hB lower width r y) = 1 := by
  exact jointSlicedPrincipalDensity_image_probability
    (D := Active) (B := fun j => B j.val) (F := fun j => Fin (degree j.val))
    hB (fun _ => ⟨0, Nat.zero_lt_succ _⟩)
    (allocatedFixedPathPrincipal B P R σ r) lower width
    (allocatedFixedPathShift B P R σ r) ha hδ
    (fun j b => (hprincipal j).trans
      (allocatedFixedPathPrincipal_bounds B P R σ hR r hr j b).1) hw hl

theorem allocatedFixedPathLiftDensity_cap_lipschitz
    (hR : ∀ j, R j ≠ 0) (hB : ∀ a : Active, 4 ≤ Fintype.card (B a.val))
    (lower width : ∀ a : Active, B a.val × Fin (degree a.val) → ℝ)
    {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ)
    (hprincipal : ∀ j : Active, a ≤ unitProfilePrincipalSize (B := B) j.val)
    (hw : ∀ j p, δ ≤ width j p) (hl : ∀ j p, 0 ≤ lower j p)
    (r : Coeff → ℝ) (hr : ∀ e, |r e| ≤ 1) :
    let K := allocatedFixedPathLiftRowCap P ha hδ
    (∀ y, allocatedFixedPathLiftDensity B P R σ hB lower width r y ∈
      Set.Icc (0 : ℝ) (∏ j, K j)) ∧
      LipschitzWith ((∏ j, (K j + 1)) * ∑ j, K j * (2 * K j))
        (allocatedFixedPathLiftDensity B P R σ hB lower width r) := by
  exact jointSlicedPrincipalDensity_cap_lipschitz
    (D := Active) (B := fun j => B j.val) (F := fun j => Fin (degree j.val))
    hB (fun _ => ⟨0, Nat.zero_lt_succ _⟩)
    (allocatedFixedPathPrincipal B P R σ r) lower width
    (allocatedFixedPathShift B P R σ r) ha hδ
    (fun j b => (hprincipal j).trans
      (allocatedFixedPathPrincipal_bounds B P R σ hR r hr j b).1) hw hl

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedRelativeChildSliceGeometry
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "vars" => LayerSamplerVariables G I n B
local notation "Sample" => CoefficientSamplerArrays (K := vars) I n

include hR hσ in
theorem allocatedSampleProfileNoise_continuous_bound (sample : Sample) (j : Fin m) (i : I j)
    (hs : affineProductProfile (allocatedLayerCenters B U basis S j i)
      (allocatedLayerWidths B U basis S j i) ((sample j).1 i) ≠ 0)
    (e : BoundedCoefficientExponent vars (j.val + 1)) :
    |allocatedSampleProfileNoise B U basis S sample ⟨j, .inl i⟩ e| ≤ 1 := by
  have he := (Finset.prod_ne_zero_iff.mp hs) e (Finset.mem_univ e)
  rw [allocatedLayerCenters_scale, allocatedLayerWidths_scale] at he
  have hscale := allocatedContinuousProfileScales_pos B U basis S j e
  have hwidth := allocatedContinuousProfileWidths_pos B hR hσ j i e
  have hb := affineProbabilityProfile_support _ (mul_pos hscale hwidth) he
  have hn : |(sample j).1 i e / allocatedContinuousProfileScales B U basis S j e -
      allocatedContinuousProfileCenters B R j i e| ≤
      allocatedContinuousProfileWidths B R σ j i e := by
    have heq : (sample j).1 i e / allocatedContinuousProfileScales B U basis S j e -
        allocatedContinuousProfileCenters B R j i e =
        ((sample j).1 i e - allocatedContinuousProfileScales B U basis S j e *
          allocatedContinuousProfileCenters B R j i e) / allocatedContinuousProfileScales B U basis S j e := by
      field_simp
    rw [heq, abs_div, abs_of_pos hscale]
    apply (div_le_iff₀ hscale).mpr
    nlinarith
  dsimp only [allocatedSampleProfileNoise, allocatedSampleNormalizedCoefficients]
  rw [abs_div, abs_of_pos hwidth]
  exact (div_le_one hwidth).mpr hn

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "vars" => LayerSamplerVariables G I n B
local notation "Sample" => CoefficientSamplerArrays (K := vars) I n

include hR hσ in
theorem allocatedSampleProfileNoise_active_integer_coordinate_bound
    (sample : Sample) (j : Fin m) (i : Fin (n j))
    (hactive : S.value ^ (j.val + 1) < basisAxisScale (basis j) i)
    (e : BoundedCoefficientExponent vars (j.val + 1))
    (he : (sample j).2 i e ∈ (allocatedLayerIntegerPMFs B U basis hR hσ S j i e).support) :
    |allocatedSampleProfileNoise B U basis S sample ⟨j, .inr i⟩ e| ≤ 1 := by
  have hb := integerPolynomialCoordinatePMF_active_profile_bound
    (P := layerIntegerPrincipalSlots B j i) (j₀ := constantCoefficientSlot _ _)
    (h := j.val + 1) (K := basisAxisScale (basis j) i) (L := S.value) (s := layerTailDegree m)
    (hh := Nat.zero_lt_succ _) (hK := basisAxisScale_pos (basis j) i) (hL := S.positive)
    (T := layerSamplerBox B U basis S)
    (hT := fun v => lt_of_lt_of_le zero_lt_one (layerSamplerBox_one_le B U basis S v))
    (hTL := layerSamplerBox_le B U basis S) (e := Subtype.val)
    (he := fun d => d.property.trans (layerDegree_le_tailDegree j))
    (ρ := R j / 4)
    (γ := principalProfileSize (R j) (layerIntegerPrincipalSlots (G := G) B j i).card)
    (ε := tailProfileSize (R j) (σ j)
      (Fintype.card (BoundedCoefficientExponent vars (j.val + 1))))
    (hρ := div_pos (hR j) (by norm_num)) (hγ := principalProfileSize_pos (hR j) _)
    (hε := tailProfileSize_pos (hR j) (hσ j) _)
    (hgap := S.gap j i) (hεL := S.width j)
    (hj₀ := layerIntegerPrincipalSlots_not_constant B j i) (he₀ := rfl)
    (hprincipal := layerSamplerSides_integer_principal B U basis R S.value j i)
    hactive e he
  have hb' : |allocatedSampleNormalizedCoefficients B U basis S sample ⟨j, .inr i⟩ e -
      allocatedIntegerProfileCenters B R j i e| ≤ allocatedIntegerProfileWidths B R σ j i e := by
    simpa only [allocatedSampleNormalizedCoefficients, allocatedIntegerProfileScales,
      allocatedIntegerProfileCenters, allocatedIntegerProfileWidths,
      div_div_eq_mul_div, div_mul_eq_mul_div] using hb
  have hw := allocatedIntegerProfileWidths_pos B hR hσ j i e
  change |(allocatedSampleNormalizedCoefficients B U basis S sample ⟨j, .inr i⟩ e -
    allocatedIntegerProfileCenters B R j i e) / allocatedIntegerProfileWidths B R σ j i e| ≤ 1
  rw [abs_div, abs_of_pos hw]
  exact (div_le_one hw).mpr hb'

include hR hσ in
theorem allocatedSampleProfileNoise_active_integer_bound
    (sample : Sample) (j : Fin m) (i : Fin (n j))
    (hactive : S.value ^ (j.val + 1) < basisAxisScale (basis j) i)
    (hs : ∀ e, (sample j).2 i e ∈ (allocatedLayerIntegerPMFs B U basis hR hσ S j i e).support)
    (e : BoundedCoefficientExponent vars (j.val + 1)) :
    |allocatedSampleProfileNoise B U basis S sample ⟨j, .inr i⟩ e| ≤ 1 :=
  allocatedSampleProfileNoise_active_integer_coordinate_bound B U basis hR hσ S sample j i hactive e (hs e)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedOriginalSampleQuadratureUniformBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "vars" => LayerSamplerVariables G I n B
local notation "degree" => layerSamplerDegree I n
local notation "grid" => allocatedShortAxis (I := I) U basis S.value
local notation "Sample" => CoefficientSamplerArrays (K := vars) I n

include hR hσ in
theorem allocatedSampleRestrictedProfileNoise_short_abs_le (sample : Sample)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j) (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    (e : ActiveProfileCoefficientIndex G B degree grid) :
    |allocatedSampleRestrictedProfileNoise B U basis S grid sample e| ≤ 1 := by
  rcases e with ⟨⟨⟨j, i⟩, ha⟩, e⟩
  have hrows := (mixedArraySupported_iff_rows _ _ _ (sample j)).mp (hs j)
  cases i with
  | inl i =>
    exact allocatedSampleProfileNoise_continuous_bound B U basis hR hσ S sample j i (hrows.1 i) e
  | inr i =>
    exact allocatedSampleProfileNoise_active_integer_bound B U basis hR hσ S sample j i
      (Nat.lt_of_not_ge ha) (hrows.2 i) e

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedFixedPathLiftSupport
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable [∀ a, DecidableEq (B a)]
variable (P : LayerSamplerAxis I n → Prop) [DecidablePred P]
variable (R σ : Fin m → ℝ)

local notation "degree" => layerSamplerDegree I n
local notation "Active" => {a // ¬P a}
local notation "Coeff" => ActiveProfileCoefficientIndex G B degree P
local notation "Input" => (Σ a : {a : LayerSamplerAxis I n // ¬P a},
  B (Subtype.val a) × Fin (layerSamplerDegree I n (Subtype.val a)))
local notation "Output" => (Σ _a : Active, Unit)

omit [∀ a, DecidableEq (B a)] in
theorem allocatedFixedPathLiftMap_measurable
    (lower width : ∀ a : Active, B a.val × Fin (degree a.val) → ℝ) (r : Coeff → ℝ) :
    Measurable (allocatedFixedPathLiftMap B P R σ lower width r) := by
  unfold allocatedFixedPathLiftMap jointSlicedPrincipal sigmaAxisSampler
    principalSliceSingleton principalSliceValue
  fun_prop

omit [∀ a, DecidableEq (B a)] in
theorem allocatedFixedPathLiftMap_norm_le (hR : ∀ j, R j ≠ 0)
    (lower width : ∀ a : Active, B a.val × Fin (degree a.val) → ℝ)
    (hwidth : ∀ a p, |lower a p| + |width a p| ≤ 1)
    (r : Coeff → ℝ) (hr : ∀ e, |r e| ≤ 1)
    (x : Input → ℝ) (hx : ∀ p, |x p| ≤ 1) :
    ‖allocatedFixedPathLiftMap B P R σ lower width r x‖ ≤ 2 := by
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)).mpr
  intro o
  have hp := principalSliceValue_abs_le
    (jointSlicedProfilePrincipal degree Subtype.val (unitProfilePrincipalSize (B := B))
      (fun a e => r ⟨a,e⟩) o.1)
    (lower o.1) (width o.1) (hwidth o.1) (fun p => x ⟨o.1,p⟩) (fun p => hx _)
  have hm := jointSlicedProfilePrincipal_unit_mass degree Subtype.val
    (fun a e => r ⟨a,e⟩) (fun _ _ => hr _) o.1
  have hc : |(1 / 4 : ℝ) * r ⟨o.1, constantCoefficientSlot _ _⟩| ≤ 1 / 4 := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
    exact mul_le_of_le_one_right (by norm_num) (hr _)
  simp only [allocatedFixedPathLiftMap, allocatedFixedPathPrincipal_eq B P R σ hR,
    allocatedFixedPathShift_eq B P R σ hR, Pi.add_apply]
  change |(1 / 4 : ℝ) * r ⟨o.1, constantCoefficientSlot _ _⟩ +
    principalSliceValue _ _ _ _| ≤ 2
  exact (abs_add_le _ _).trans ((add_le_add hc (hp.trans hm)).trans (by norm_num))

theorem allocatedFixedPathLiftDensity_zero_off_ball
    (hR : ∀ j, R j ≠ 0) (hB : ∀ a : Active, 4 ≤ Fintype.card (B a.val))
    (lower width : ∀ a : Active, B a.val × Fin (degree a.val) → ℝ)
    (hwidth : ∀ a p, |lower a p| + |width a p| ≤ 1)
    {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ)
    (hprincipal : ∀ j : Active, a ≤ unitProfilePrincipalSize (B := B) j.val)
    (hw : ∀ j p, δ ≤ width j p) (hl : ∀ j p, 0 ≤ lower j p)
    (r : Coeff → ℝ) (hr : ∀ e, |r e| ≤ 1)
    (z : Output → ℝ) (hz : 2 < ‖z‖) :
    allocatedFixedPathLiftDensity B P R σ hB lower width r z = 0 := by
  have hd := allocatedFixedPathLiftDensity_law_probability B P R σ hR hB lower width
    ha hδ hprincipal hw hl r hr
  have hb := allocatedFixedPathLiftDensity_cap_lipschitz B P R σ hR hB lower width
    ha hδ hprincipal hw hl r hr
  have hm := allocatedFixedPathLiftMap_measurable B P R σ lower width r
  apply continuousDensity_zero_off_closed volume _ hb.2.continuous hd.2.1
    (S := Metric.closedBall 0 2) Metric.isClosed_closedBall ?_ z
    (by simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hz)
  rw [← hd.1]
  apply (ae_map_iff hm.aemeasurable Metric.isClosed_closedBall.measurableSet).mpr
  filter_upwards [unitBoxMeasure_ae] with x hx
  simpa only [dist_zero_right] using
    allocatedFixedPathLiftMap_norm_le B P R σ hR lower width hwidth r hr x
    (fun p => by rw [abs_of_nonneg (hx p).1.le]; exact (hx p).2)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.FixedSpatialKernelProgressionForecastIntegral
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G X T : Type*} [Fintype G] [Fintype X] [DecidableEq X] [Fintype T]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "Output" => (Σ _a : Active, Unit)
local notation "Domain" => (((Σ _ : X, Unit ⊕ Empty) → ℝ) × (Output → ℝ))
local notation "noise" => allocatedSampleRestrictedProfileNoise B U basis S short
local notation "hamin" => unitProfilePrincipalLowerBound_pos B

variable (e : G ≃ X ⊕ (X ⊕ T)) (W L : ℝ) (z : Option G × X → ℝ)
variable (h0 : (fixedSpatialKernelBlock e W L z false).det ≠ 0)
  (h1 : (fixedSpatialKernelBlock e W L z true).det ≠ 0)
variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a},
    4 ≤ Fintype.card (B a.val))
  (lower width : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a},
    B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)

local notation "density" => fixedSpatialKernelOriginalForecastDensity B U basis S e W L z h0 h1 hB lower width

variable {δ : ℝ} (hδ : 0 < δ)
  (hw : ∀ a p, δ ≤ width a p) (hl : ∀ a p, 0 ≤ lower a p)
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
  (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
    (allocatedLayerWidths B U basis S j)
    (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))

include hR hσ hδ hw hl hs in
theorem fixedSpatialKernelOriginalForecastDensity_zero_of_active_norm_gt_two
    (hwidth : ∀ a p, |lower a p| + |width a p| ≤ 1)
    (y : Domain) (hy : 2 < ‖y.2‖) : density sample y = 0 := by
  classical
  have hr := allocatedSampleRestrictedProfileNoise_short_abs_le B U basis hR hσ S sample hs
  have hg := allocatedFixedPathLiftDensity_zero_off_ball B short R σ
    (fun j => (hR j).ne') hB lower width hwidth hamin hδ
    (fun a => unitProfilePrincipalLowerBound_le B a.val) hw hl (noise sample) hr y.2 hy
  change _ * allocatedFixedPathLiftDensity B short R σ hB lower width (noise sample) y.2 = 0
  rw [hg, mul_zero]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G X T : Type*} [Fintype G] [Fintype X] [Fintype T]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "Output" => (Σ _a : Active, Unit)
local notation "Domain" => (((Σ _ : X, Unit ⊕ Empty) → ℝ) × (Output → ℝ))

variable (e : G ≃ X ⊕ (X ⊕ T)) (W L : ℝ) (z : Option G × X → ℝ)
variable (lowerG widthG : G → ℝ)
variable (h0 : (fixedSpatialKernelBlock e W L z false).det ≠ 0)
  (h1 : (fixedSpatialKernelBlock e W L z true).det ≠ 0)
variable (hwG : ∀ g, widthG g ≠ 0)
variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a},
    4 ≤ Fintype.card (B a.val))
  (lowerP widthP : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a},
    B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)

local notation "frame" => fixedSpatialKernelSliceFrame W L z lowerG widthG
local notation "h0slice" => fixedSpatialKernelBlock_slice_det_ne_zero e W L z lowerG widthG false h0 hwG
local notation "h1slice" => fixedSpatialKernelBlock_slice_det_ne_zero e W L z lowerG widthG true h1 hwG

local notation "density" => fixedSpatialKernelSliceOriginalForecastDensity B U basis S e W L z
  lowerG widthG h0 h1 hwG hB lowerP widthP

variable {δP : ℝ} (hδP : 0 < δP)
  (hwP : ∀ a p, δP ≤ widthP a p) (hlP : ∀ a p, 0 ≤ lowerP a p)
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
  (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
    (allocatedLayerWidths B U basis S j)
    (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))

include hR hσ hδP hwP hlP hs in
theorem fixedSpatialKernelSliceOriginalForecastDensity_zero_of_active_norm_gt_two
    (hwidthP : ∀ a p, |lowerP a p| + |widthP a p| ≤ 1)
    (y : Domain) (hy : 2 < ‖y.2‖) : density sample y = 0 :=
  fixedSpatialKernelOriginalForecastDensity_zero_of_active_norm_gt_two B U basis hR hσ S
    e W L frame h0slice h1slice hB lowerP widthP hδP hwP hlP sample hs hwidthP y hy

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ActualFixedSpatialSlicedDensityBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped BigOperators NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {X : Type} [Fintype X] [decX : DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable (Dmod : ℕ) {Lrank : ℕ}
variable (spatial : Fin Lrank ↪ G)
variable (kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩)
variable {Tsp : Type} [Fintype Tsp]
variable (spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)) (Wsp Lsp : ℝ)
variable (physicalN : X → ℕ) (τ δslice P Pbad Ppres : ℝ)

namespace ActualFixedSpatialSlicedForecastPath
variable {B U b S hR hσ Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres}
variable (slice : ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)

theorem density_active_support_s2_oai
    (hBactive : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
      4 ≤ Fintype.card (B a.val)) (hδslice : 0 < δslice)
    (y : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
      ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a}, Unit) → ℝ)))
    (hy : slice.density hBactive y ≠ 0)
    (a : Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a}, Unit) :
    |y.2 a| ≤ 3 := by
  cases Subsingleton.elim decX (Classical.decEq X)
  let := Classical.decEq X
  have hnorm : ‖y.2‖ ≤ 2 := by
    by_contra! h
    exact hy (fixedSpatialKernelSliceOriginalForecastDensity_zero_of_active_norm_gt_two
      B U b hR hσ S spatialEquiv Wsp Lsp slice.path.normalizedNoise slice.kernelLower slice.kernelWidth
      slice.path.detFalse slice.path.detTrue slice.kernelWidth_ne_zero hBactive
      slice.path.lower slice.path.width hδslice slice.path.hwidth slice.path.hlower
      slice.path.sample slice.path.hs slice.path.hcontained y h)
  have hcoord : |y.2 a| ≤ ‖y.2‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm y.2 a
  linarith

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution : type_of% @OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.density_active_support_s2_oai := @OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.density_active_support_s2_oai
