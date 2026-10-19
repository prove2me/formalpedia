-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.allocatedFixedPath_sliced_density_residue_comparison_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T05:27:09.854507+00:00
-- url     : https://prove2.me/submissions/e2bbd5ea-6796-4d89-a5c0-7964632b1513

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B299
import Definitions.Def_OAIE3v2B197
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedFixedPath_sliced_joint_residue_comparison_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_fixedSpatialKernelEmptyDensity_image_law_s2
import Theorems.Thm_OAI_Erdos3_canonicalSlicedPrincipalDensity_law_bounds_s2
import Theorems.Thm_OAI_Erdos3_fixedSpatialKernelDensity_bounds_s2

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
theorem allocatedSampleProfileNoise_polynomial (sample : Sample) (a : LayerSamplerAxis I n) :
    allocatedAxisProfilePolynomial B R σ a (allocatedSampleProfileNoise B U basis S sample a) =
      monomialArrayPolynomial Subtype.val (allocatedSampleNormalizedCoefficients B U basis S sample a) := by
  rcases a with ⟨j, i⟩
  cases i with
  | inl i =>
    unfold allocatedAxisProfilePolynomial
    apply congrArg (monomialArrayPolynomial Subtype.val)
    funext e
    dsimp only [allocatedSampleProfileNoise]
    field_simp [(allocatedContinuousProfileWidths_pos B hR hσ j i e).ne']
    ring
  | inr i =>
    unfold allocatedAxisProfilePolynomial
    apply congrArg (monomialArrayPolynomial Subtype.val)
    funext e
    dsimp only [allocatedSampleProfileNoise]
    field_simp [(allocatedIntegerProfileWidths_pos B hR hσ j i e).ne']
    ring

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
local notation "Sample" => CoefficientSamplerArrays (K := vars) I n

variable (P : LayerSamplerAxis I n → Prop)

include hR hσ in
theorem allocatedFixedPathPrincipal_of_restricted_sample (sample : Sample)
    (a : {a // ¬P a}) (b : B a.val) :
    allocatedFixedPathPrincipal B P R σ (allocatedSampleRestrictedProfileNoise B U basis S P sample) a b =
      allocatedSampleNormalizedCoefficients B U basis S sample a.val
        (principalCoefficientSlot degree a.val b) / R a.val.1 := by
  unfold allocatedFixedPathPrincipal
  change (allocatedAxisProfilePolynomial B R σ a.val
    (allocatedSampleProfileNoise B U basis S sample a.val)).coeff _ / _ = _
  rw [allocatedSampleProfileNoise_polynomial B U basis hR hσ S]
  change (monomialArrayPolynomial Subtype.val _).coeff
    (principalCoefficientSlot degree a.val b).val / _ = _
  rw [monomialArrayPolynomial_coeff Subtype.val Subtype.val_injective]

include hR hσ in
theorem allocatedFixedPathShift_of_restricted_sample (sample : Sample) (a : {a // ¬P a}) :
    allocatedFixedPathShift B P R σ (allocatedSampleRestrictedProfileNoise B U basis S P sample) a =
      allocatedSampleNormalizedCoefficients B U basis S sample a.val
        (constantCoefficientSlot vars (degree a.val)) / R a.val.1 := by
  unfold allocatedFixedPathShift
  change (allocatedAxisProfilePolynomial B R σ a.val
    (allocatedSampleProfileNoise B U basis S sample a.val)).coeff _ / _ = _
  rw [allocatedSampleProfileNoise_polynomial B U basis hR hσ S]
  change (monomialArrayPolynomial Subtype.val _).coeff
    (constantCoefficientSlot vars (degree a.val)).val / _ = _
  rw [monomialArrayPolynomial_coeff Subtype.val Subtype.val_injective]

end Erdos3.VectorPolynomial

end

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
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "vars" => LayerSamplerVariables G I n B
local notation "degree" => layerSamplerDegree I n
local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "Input" => (Σ a : Active, B (Subtype.val a) × Fin (degree (Subtype.val a)))
local notation "Output" => (Σ _a : Active, Unit)
local notation "Sample" => CoefficientSamplerArrays (K := vars) I n

variable (lower width : ∀ a : {a : LayerSamplerAxis I n //
  ¬allocatedShortAxis U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)

theorem allocatedOriginalSampleLiftMap_apply (sample : Sample) (x : Input → ℝ) (o : Output) :
    allocatedOriginalSampleLiftMap B U basis S lower width sample x o =
      allocatedSampleNormalizedCoefficients B U basis S sample o.1.val
        (constantCoefficientSlot vars (degree o.1.val)) / R o.1.val.1 +
      ∑ b, (allocatedSampleNormalizedCoefficients B U basis S sample o.1.val
        (principalCoefficientSlot degree o.1.val b) / R o.1.val.1) *
        ∏ v, (lower o.1 (b, v) + width o.1 (b, v) * x ⟨o.1, b, v⟩) := rfl

variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)

include hR hσ in
theorem allocatedOriginalSamplePrincipal_eq_fixedPath (sample : Sample) :
    allocatedOriginalSamplePrincipal B U basis S sample =
      allocatedFixedPathPrincipal B short R σ
        (allocatedSampleRestrictedProfileNoise B U basis S short sample) := by
  funext a b
  exact (allocatedFixedPathPrincipal_of_restricted_sample B U basis hR hσ S short sample a b).symm

include hR hσ in
theorem allocatedOriginalSampleShift_eq_fixedPath (sample : Sample) :
    allocatedOriginalSampleShift B U basis S sample =
      allocatedFixedPathShift B short R σ
        (allocatedSampleRestrictedProfileNoise B U basis S short sample) := by
  funext a
  exact (allocatedFixedPathShift_of_restricted_sample B U basis hR hσ S short sample a).symm

include hR hσ in
theorem allocatedOriginalSampleLiftMap_eq_fixedPath (sample : Sample) :
    allocatedOriginalSampleLiftMap B U basis S lower width sample =
      allocatedFixedPathLiftMap B short R σ lower width
        (allocatedSampleRestrictedProfileNoise B U basis S short sample) := by
  funext x
  unfold allocatedOriginalSampleLiftMap allocatedFixedPathLiftMap
  rw [allocatedOriginalSamplePrincipal_eq_fixedPath B U basis S hR hσ sample,
    allocatedOriginalSampleShift_eq_fixedPath B U basis S hR hσ sample]

theorem allocatedOriginalSampleLiftMap_measurable :
    Measurable (fun p : Sample × (Input → ℝ) =>
      allocatedOriginalSampleLiftMap B U basis S lower width p.1 p.2) := by
  apply measurable_pi_iff.mpr
  rintro ⟨⟨⟨j, i⟩, ha⟩, u⟩
  cases i with
  | inl i =>
    simp only [allocatedOriginalSampleLiftMap_apply, allocatedSampleNormalizedCoefficients]
    fun_prop
  | inr i =>
    simp only [allocatedOriginalSampleLiftMap_apply, allocatedSampleNormalizedCoefficients]
    fun_prop

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.FixedSpatialEmptyCoordinates
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

variable {X : Type*}

variable [Fintype X]

theorem fixedSpatialEmptyDensity_bounds (f : (X → ℝ) → ℝ) {C : ℝ} {L : ℝ≥0}
    (hC : ∀ x, f x ∈ Set.Icc (0 : ℝ) C) (hL : LipschitzWith L f) :
    (∀ v, fixedSpatialEmptyDensity f v ∈ Set.Icc (0 : ℝ) C) ∧
      LipschitzWith L (fixedSpatialEmptyDensity f) := by
  refine ⟨fun v => hC _, ?_⟩
  have hi : LipschitzWith 1 (fun v : (Σ _ : X, Unit ⊕ Empty) → ℝ =>
      (fixedSpatialEmptyCoordinates (X := X)).symm v) := by
    apply LipschitzWith.of_dist_le_mul
    intro v w
    simp only [NNReal.coe_one, one_mul]
    exact le_of_eq ((fixedSpatialEmptyCoordinates (X := X)).symm.isometry.dist_eq v w)
  apply LipschitzWith.of_dist_le_mul
  intro v w
  exact (hL.dist_le_mul _ _).trans (mul_le_mul_of_nonneg_left
    (by simpa only [NNReal.coe_one, one_mul] using hi.dist_le_mul v w) (NNReal.coe_nonneg L))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedOriginalSampleForecastMeanRiemann
namespace OAI

section

namespace Erdos3

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical

namespace VectorPolynomial

variable {m : ℕ} {G X Zsp : Type*} [Fintype G] [Fintype X]
  [Fintype Zsp] [DecidableEq Zsp]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "Sample" => CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n

variable (lower width : ∀ a : {a : LayerSamplerAxis I n //
  ¬allocatedShortAxis (I := I) U basis S.value a},
  B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)

theorem allocatedOriginalSampleLiftMap_fixed_measurable (sample : Sample) :
    Measurable (allocatedOriginalSampleLiftMap B U basis S lower width sample) :=
  (allocatedOriginalSampleLiftMap_measurable B U basis S lower width).comp
    (measurable_const.prodMk measurable_id)

end VectorPolynomial
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ContainedKernelPhysicalDisplacement
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {G X : Type*} [Fintype G]

theorem fixedSpatialKernelMap_slice (W L : ℝ)
    (z : Option G × X → ℝ) (lower width t : G → ℝ) :
    fixedSpatialKernelMap W L (fixedSpatialKernelSliceFrame W L z lower width) t =
      fixedSpatialKernelMap W L z (fun g => lower g + width g * t g) := by
  funext a
  simp only [fixedSpatialKernelMap, fixedSpatialKernelSliceFrame_none,
    fixedSpatialKernelSliceFrame_some, mul_add, Finset.sum_add_distrib,
    mul_assoc, mul_left_comm]
  ring

end Erdos3

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
local notation "Input" => (Σ a : Active, B (Subtype.val a) × Fin (layerSamplerDegree I n (Subtype.val a)))
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

local notation "spatial" => fixedSpatialEmptyDensity (fixedSpatialKernelDensity e W L z h0 h1)
local notation "liftDensity" => (fun sample => allocatedFixedPathLiftDensity B short R σ hB lower width (noise sample))
local notation "density" => fixedSpatialKernelOriginalForecastDensity B U basis S e W L z h0 h1 hB lower width
local notation "source" => fixedSpatialKernelOriginalForecastSource B U basis S W L z lower width

variable {δ : ℝ} (hδ : 0 < δ)
  (hw : ∀ a p, δ ≤ width a p) (hl : ∀ a p, 0 ≤ lower a p)
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
  (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
    (allocatedLayerWidths B U basis S j)
    (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))

omit hR hσ [Fintype X] [DecidableEq X] in
theorem fixedSpatialKernelMap_measurable : Measurable (fixedSpatialKernelMap W L z) := by
  unfold fixedSpatialKernelMap
  fun_prop

include hR hσ hδ hw hl hs in
theorem fixedSpatialKernelOriginalForecastSource_density :
    source sample = realDensityMeasure volume (density sample) := by
  have hr := allocatedSampleRestrictedProfileNoise_short_abs_le B U basis hR hσ S sample hs
  have hg := allocatedFixedPathLiftDensity_law_probability B short R σ
    (fun j => (hR j).ne') hB lower width hamin hδ
    (fun a => unitProfilePrincipalLowerBound_le B a.val) hw hl (noise sample) hr
  have hglip := allocatedFixedPathLiftDensity_cap_lipschitz B short R σ
    (fun j => (hR j).ne') hB lower width hamin hδ
    (fun a => unitProfilePrincipalLowerBound_le B a.val) hw hl (noise sample) hr
  have hf := fixedSpatialKernelDensity_bounds_s2 e W L z h0 h1
  have hf' := fixedSpatialEmptyDensity_bounds _ hf.1 hf.2
  unfold fixedSpatialKernelOriginalForecastSource
  change Measure.map (Prod.map (fixedSpatialKernelMap W L z)
    (allocatedOriginalSampleLiftMap B U basis S lower width sample))
    ((unitBoxMeasure G).prod (unitBoxMeasure Input)) = _
  rw [← Measure.map_prod_map _ _ (fixedSpatialKernelMap_measurable W L z)
    (allocatedOriginalSampleLiftMap_fixed_measurable B U basis S lower width sample)]
  rw [fixedSpatialKernelEmptyDensity_image_law_s2 e W L z h0 h1,
    allocatedOriginalSampleLiftMap_eq_fixedPath B U basis S lower width hR hσ sample, hg.1]
  exact binaryDensity_measure volume volume spatial (liftDensity sample)
    hf'.2.continuous.measurable hglip.2.continuous.measurable (fun y => (hf'.1 y).1)

include hR hσ hδ hw hl hs in
theorem fixedSpatialKernelOriginalForecastDensity_test_integral
    (φ : Domain → ℂ) (hφ : Measurable φ) :
    (∫ y, φ y ∂realDensityMeasure volume (density sample)) =
      ∫ p, φ (fixedSpatialKernelMap W L z p.1,
        allocatedOriginalSampleLiftMap B U basis S lower width sample p.2)
        ∂(unitBoxMeasure G).prod (unitBoxMeasure Input) := by
  rw [← fixedSpatialKernelOriginalForecastSource_density B U basis hR hσ S e W L z h0 h1
    hB lower width hδ hw hl sample hs]
  apply integral_map _ hφ.aestronglyMeasurable
  exact (((fixedSpatialKernelMap_measurable W L z).comp measurable_fst).prodMk
    ((allocatedOriginalSampleLiftMap_fixed_measurable B U basis S lower width sample).comp
      measurable_snd)).aemeasurable

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
local notation "Input" => (Σ a : Active, B (Subtype.val a) × Fin (layerSamplerDegree I n (Subtype.val a)))
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
theorem fixedSpatialKernelSliceOriginalForecastDensity_test_integral
    (φ : Domain → ℂ) (hφ : Measurable φ) :
    (∫ y, φ y ∂realDensityMeasure volume (density sample)) =
      ∫ p, φ (fixedSpatialKernelMap W L z (fun g => lowerG g + widthG g * p.1 g),
        allocatedOriginalSampleLiftMap B U basis S lowerP widthP sample p.2)
        ∂(unitBoxMeasure G).prod (unitBoxMeasure Input) := by
  simpa only [fixedSpatialKernelMap_slice, fixedSpatialKernelSliceOriginalForecastDensity] using
    (fixedSpatialKernelOriginalForecastDensity_test_integral B U basis hR hσ S
      e W L frame h0slice h1slice hB lowerP widthP hδP hwP hlP sample hs φ hφ)

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
local notation "Input" => (Σ a : Active, B (Subtype.val a) × Fin (layerSamplerDegree I n (Subtype.val a)))
local notation "Output" => (Σ _a : Active, Unit)
local notation "Domain" => (((Σ _ : X, Unit ⊕ Empty) → ℝ) × (Output → ℝ))

variable (e : G ≃ X ⊕ (X ⊕ T)) (W L : ℝ) (z : Option G × X → ℝ)
variable (start : G → ℤ) (step : ℤ) (H : G → ℕ)
variable (hstep : 0 < step) (hH : ∀ g, 2 ≤ H g)
local notation "lowerG" => (fun g => (start g : ℝ) / S.value)
local notation "widthG" => (fun g => (step : ℝ) * ((H g - 1 : ℕ) : ℝ) / S.value)
variable (h0 : (fixedSpatialKernelBlock e W L z false).det ≠ 0)
  (h1 : (fixedSpatialKernelBlock e W L z true).det ≠ 0)
local notation "hwG" => (fun g => ne_of_gt (fixedSpatialKernelProgression_width_pos S.positive hstep (hH g)))
variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a},
    4 ≤ Fintype.card (B a.val))
  (lowerP widthP : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a},
    B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)

local notation "density" => fixedSpatialKernelSliceOriginalForecastDensity B U basis S e W L z
  lowerG widthG h0 h1 hwG hB lowerP widthP

variable {δP : ℝ} (hδP : 0 < δP)
  (hwP : ∀ a p, δP ≤ widthP a p) (hlP : ∀ a p, 0 ≤ lowerP a p)
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
  (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
    (allocatedLayerWidths B U basis S j)
    (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))

include hR hσ hδP hwP hlP hs in
theorem fixedSpatialKernelProgressionForecastDensity_iterated_test_integral
    (φ : Domain → ℂ) (hφ : Measurable φ) (hbound : ∀ y, ‖φ y‖ ≤ 1) :
    (∫ y, φ y ∂realDensityMeasure volume (density sample)) =
      ∫ k, ∫ v, φ (fixedSpatialKernelMap W L z
        (fun g => ((start g : ℝ) + (step : ℝ) * ((H g - 1 : ℕ) : ℝ) * k g) / S.value),
        allocatedOriginalSampleLiftMap B U basis S lowerP widthP sample v)
        ∂unitBoxMeasure Input ∂unitBoxMeasure G := by
  rw [fixedSpatialKernelSliceOriginalForecastDensity_test_integral B U basis hR hσ S
    e W L z lowerG widthG h0 h1 hwG hB lowerP widthP hδP hwP hlP sample hs φ hφ]
  have hparam (k : G → ℝ) :
      (fun g => lowerG g + widthG g * k g) =
      (fun g => ((start g : ℝ) + (step : ℝ) * ((H g - 1 : ℕ) : ℝ) * k g) / S.value) := by
    funext g
    dsimp only
    ring
  simp_rw [hparam]
  apply integral_prod
  refine ⟨?_, HasFiniteIntegral.of_bounded (Filter.Eventually.of_forall (fun p => hbound _))⟩
  apply Measurable.aestronglyMeasurable
  apply hφ.comp
  apply Measurable.prodMk
  · unfold fixedSpatialKernelMap
    fun_prop
  · exact (allocatedOriginalSampleLiftMap_fixed_measurable B U basis S lowerP widthP sample).comp
      measurable_snd

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedFixedPathSlicedRationalDensityComparison
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G X T : Type*} [Fintype T] [Fintype G] [DecidableEq G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "degree" => layerSamplerDegree I n
local notation "Input" => (Σ a : Active, B (Subtype.val a) × Fin (degree (Subtype.val a)))
local notation "Output" => (Σ _a : Active, Unit)
local notation "Sample" => CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n

variable (u : PrincipalAxisTuples (α := Empty)
  (allocatedShortAxis (I := I) U basis S.value) (allocatedPrincipalSides B U basis S))

local notation "Spatial" => ((Σ _ : X, Unit ⊕ Empty) → ℝ)
local notation "Domain" => Spatial × (Output → ℝ)
local notation "budget" => allocatedPhysicalRootBudget B U basis S (fun _ => 0)

include hR hσ in
theorem allocatedFixedPath_sliced_density_residue_comparison_s2_oai
    (z : Option G × X → ℝ) (hz : ∀ g x, |z (some g, x)| ≤ 1)
    (HG : G → ℕ) (hHG : ∀ g, 2 ≤ HG g) (cG : G → ℤ)
    (stepG : ℕ) (hstepG : 0 < stepG)
    (hcontainedG : ∀ g, integerProgressionSupport (cG g) (stepG : ℤ) (HG g) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ))
    (e : G ≃ X ⊕ (X ⊕ T))
    (h0 : (fixedSpatialKernelBlock e budget (S.value : ℝ) z false).det ≠ 0)
    (h1 : (fixedSpatialKernelBlock e budget (S.value : ℝ) z true).det ≠ 0)
    (hB : ∀ a : Active, 4 ≤ Fintype.card (B a.val))
    (sample : Sample)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    {t : ℝ} (ht : 0 < t) (hσbound : ∀ j, |σ j| ≤ t)
    (step H : Input → ℕ) (c : Input → ℤ)
    (hstep : ∀ j, 0 < step j) (hH : ∀ j, 2 ≤ H j)
    {δ : ℝ} (hδ : 0 < δ)
    (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ))
    (hdense : ∀ j, δ * S.value ≤
      ((integerProgressionSupport (c j) (step j : ℤ) (H j)).card : ℝ))
    (q : ℕ) [NeZero q]
    (hsizeG : ∀ g, q ≤ HG g)
    (hsmallG : ∀ g, scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / HG g) < 1) (hsize : ∀ j, q ≤ H j)
    (hsmall : ∀ j, scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / H j) < 1)
    {ε : ℝ} (hε : 0 ≤ ε) (hmesh : ∀ j, (step j : ℝ) / S.value ≤ ε)
    (hδone : δ ≤ 1) (b : ∀ a : Active, B a.val)
    {η : ℝ} (hη : 0 < η)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition)
    (htail : |t| * polynomialMassC2Budget (Fintype.card Input) m 1 ≤
      slicedPrincipalC2Tolerance (Fintype.card Input) (Fintype.card Active) m 1
        (unitProfilePrincipalLowerBound B) (δ / 2) A η)
    (φ : (G → ZMod q) → (Input → ZMod q) → Domain → ℂ) {Kφ : ℝ≥0}
    (hφ : ∀ rG r, LipschitzWith Kφ (φ rG r)) (hφone : ∀ rG r y, ‖φ rG r y‖ ≤ 1) :
    let lower := fun (a : Active) (p : B a.val × Fin (degree a.val)) => (c ⟨a, p⟩ : ℝ) / S.value
    let width := fun (a : Active) (p : B a.val × Fin (degree a.val)) =>
      (step ⟨a, p⟩ : ℝ) * ((H ⟨a, p⟩ : ℝ) - 1) / S.value
    let K := Kφ * allocatedOriginalSampleFullSliceLip B U basis S t
    let kernel := FiniteProbabilityWeights.pi (fun g => integerScalarCubeWeights Empty (HG g) (by have := hHG g; omega))
    let active := FiniteProbabilityWeights.pi (fun j : Input => integerScalarCubeWeights Empty (H j)
      (by have := hH j; omega))
    let embed := fun (x : ∀ g, IntegerScalarCubeBox Empty (HG g)) g =>
      containedProgressionCubeMap Empty S.value (HG g) stepG (cG g) S.positive (hcontainedG g) (x g)
    let density := fixedSpatialKernelSliceOriginalForecastDensity B U basis S e budget
      (S.value : ℝ) z (fun g => (cG g : ℝ) / S.value)
      (fun g => (stepG : ℝ) * ((HG g - 1 : ℕ) : ℝ) / S.value) h0 h1
      (fun g => ne_of_gt (fixedSpatialKernelProgression_width_pos S.positive
        (show (0 : ℤ) < stepG by exact_mod_cast hstepG) (hHG g))) hB lower width sample
    ‖kernel.complexMean (fun x => active.complexMean (fun v =>
        φ (fun g => ((cG g + (stepG : ℤ) * (x g none : ℤ) : ℤ) : ZMod q))
          (fun j => ((c j + (step j : ℤ) * (v j none : ℤ) : ℤ) : ZMod q))
          (fixedSpatialKernelMap budget (S.value : ℝ) z
            (fun g => ((cG g : ℝ) + (stepG : ℝ) * (x g none : ℝ)) / S.value),
            allocatedOriginalSampleFullSliceMap B U basis S (embed x) u (fun _ _ => 0) (fun _ _ => 1)
              sample (fun j => ((c j : ℝ) + (step j : ℝ) * (v j none : ℝ)) / S.value)))) -
      (FiniteProbabilityWeights.uniform (Input → ZMod q)).complexMean (fun rA =>
        (FiniteProbabilityWeights.uniform (G → ZMod q)).complexMean (fun rG =>
          ∫ y, φ (fun g => (cG g : ZMod q) + (stepG : ZMod q) * rG g)
            (fun j => (c j : ZMod q) + (step j : ZMod q) * rA j) y
            ∂realDensityMeasure volume density))‖ ≤
      ((∑ j, (q : ℝ) / H j) +
        (2 * ((2 * scalarCubeGridBoundaryConstant Empty + K * 2) *
          ∑ j, (q : ℝ) / H j + K * ε) + 2 * η)) +
      (1 + 2 * (2 * scalarCubeGridBoundaryConstant Empty + Kφ) + Kφ) * ∑ g, (q : ℝ) / HG g := by
  classical
  intro lower width K kernel active embed density
  have hg (a : Active) (p : B a.val × Fin (degree a.val)) :=
    progression_slice_endpoint_geometry (c ⟨a,p⟩) S.positive (hstep _) (hH _)
      hδ (hsubset _) (hdense _)
  have hid (rG : G → ZMod q) (rA : Input → ZMod q) :
      (∫ y, φ rG rA y ∂realDensityMeasure volume density) =
        ∫ k, ∫ v, φ rG rA
          (fixedSpatialKernelMap budget (S.value : ℝ) z
            (fun g => ((cG g : ℝ) + (stepG : ℝ) * ((HG g - 1 : ℕ) : ℝ) * k g) / S.value),
            allocatedOriginalSampleLiftMap B U basis S lower width sample v)
          ∂unitBoxMeasure Input ∂unitBoxMeasure G := by
    exact fixedSpatialKernelProgressionForecastDensity_iterated_test_integral B U basis hR hσ S
      e budget (S.value : ℝ) z cG (stepG : ℤ) HG
      (by exact_mod_cast hstepG) hHG h0 h1 hB lower width (half_pos hδ)
      (fun a p => (hg a p).2.1) (fun a p => (hg a p).1) sample hs
      (φ rG rA) (hφ rG rA).continuous.measurable (hφone rG rA)
  simp_rw [hid]
  exact allocatedFixedPath_sliced_joint_residue_comparison_s2 B U basis hR hσ S u z hz HG
    (fun g => by have := hHG g; omega) cG stepG hstepG hcontainedG sample hs ht hσbound
    step H c hstep hH hδ hsubset hdense q hsizeG hsmallG hsize hsmall hε hmesh
    hδone b hη A hA htail φ hφ hφone

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4, u_5, u_6} : type_of% @OAI.Erdos3.VectorPolynomial.allocatedFixedPath_sliced_density_residue_comparison_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6} := @OAI.Erdos3.VectorPolynomial.allocatedFixedPath_sliced_density_residue_comparison_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6}
