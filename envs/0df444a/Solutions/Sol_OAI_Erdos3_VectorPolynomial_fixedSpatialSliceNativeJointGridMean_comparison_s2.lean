-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.fixedSpatialSliceNativeJointGridMean_comparison_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T06:33:04.177015+00:00
-- url     : https://prove2.me/submissions/241b16a7-a5cb-499f-9b03-bedcd19bbd8d

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B218
import Definitions.Def_OAIE3v2B232
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_fixedSpatialKernelSliceOriginalForecastDensity_bounds_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_fixedSpatialKernelSliceOriginalForecastDensity_zero_of_norm_gt_two_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_forecastJointOriginalGridMean_comparison_s2
import Theorems.Thm_OAI_Erdos3_canonicalSlicedPrincipalDensity_law_bounds_s2
import Theorems.Thm_OAI_Erdos3_fixedSpatialKernelDensity_probability_density_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.BinaryDensity
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem binaryDensity_integrable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [SFinite ν] {f : X → ℝ} {g : Y → ℝ}
    (hf : Integrable f μ) (hg : Integrable g ν) :
    Integrable (binaryDensity f g) (μ.prod ν) := hf.mul_prod hg

theorem binaryDensity_mass {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν] (f : X → ℝ) (g : Y → ℝ) :
    (∫ p, binaryDensity f g p ∂μ.prod ν) = (∫ x, f x ∂μ) * ∫ y, g y ∂ν := integral_prod_mul f g

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.FixedSpatialEmptyCoordinates
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

variable {X : Type*}

variable [Fintype X]

theorem fixedSpatialEmptyCoordinates_measurePreserving :
    MeasurePreserving (fixedSpatialEmptyCoordinates (X := X)) volume volume := by
  have hp := volume_measurePreserving_piCongrLeft (fun _ : Σ _ : X, Unit ⊕ Empty => ℝ)
    (fixedSpatialEmptyIndex (X := X)).symm
  convert hp using 1
  funext u a
  rcases a with ⟨x, v | e⟩
  · cases v
    rfl
  · exact isEmptyElim e

theorem fixedSpatialEmptyCoordinates_symm_measurePreserving :
    MeasurePreserving (fixedSpatialEmptyCoordinates (X := X)).symm volume volume :=
  fixedSpatialEmptyCoordinates_measurePreserving.symm
    (fixedSpatialEmptyCoordinates (X := X)).toHomeomorph.toMeasurableEquiv

theorem fixedSpatialEmptyDensity_probability_data (f : (X → ℝ) → ℝ)
    (hf0 : ∀ x, 0 ≤ f x) (hfi : Integrable f) (hfm : (∫ x, f x) = 1) :
    (∀ v, 0 ≤ fixedSpatialEmptyDensity f v) ∧
      Integrable (fixedSpatialEmptyDensity f) ∧
      (∫ v, fixedSpatialEmptyDensity f v) = 1 := by
  refine ⟨fun v => hf0 _,
    fixedSpatialEmptyCoordinates_symm_measurePreserving.integrable_comp_of_integrable hfi, ?_⟩
  exact (fixedSpatialEmptyCoordinates_symm_measurePreserving.integral_comp
    (fixedSpatialEmptyCoordinates (X := X)).symm.toHomeomorph.toMeasurableEquiv.measurableEmbedding f).trans hfm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastNativePullbackBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module
open scoped Classical NNReal BigOperators

variable {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (R : Fin m → ℝ)

theorem forecastNativeAmbientLinear_lipschitz :
    LipschitzWith (forecastNativeAmbientLip U b o R) (forecastNativeAmbientLinear U b o R) :=
  (forecastNativeAmbientLinear U b o R).toContinuousLinearMap.lipschitz

variable (P : LayerSamplerAxis I n → Prop) [DecidablePred P]
local notation "Active" => {a : LayerSamplerAxis I n // ¬P a}
local notation "Output" => (Σ _a : Active, Unit)

theorem forecastNativeFillAxes_lipschitz (frozen : {a : LayerSamplerAxis I n // P a} → ℝ) :
    LipschitzWith 1 (forecastNativeFillAxes P frozen) := by
  apply LipschitzWith.of_dist_le_mul
  intro v w
  simp only [NNReal.coe_one, one_mul]
  apply (dist_pi_le_iff dist_nonneg).mpr
  intro a
  by_cases ha : P a
  · simp only [forecastNativeFillAxes, ha, ↓reduceDIte, dist_self, dist_nonneg]
  · simpa only [forecastNativeFillAxes, ha, ↓reduceDIte] using dist_le_pi_dist v w ⟨⟨a, ha⟩, ()⟩

variable {X : Type*} [Fintype X]
local notation "Spatial" => (Σ _ : X, Unit ⊕ Empty)
local notation "Domain" => ((Spatial → ℝ) × (Output → ℝ))

theorem forecastNativeSpatialInverse_lipschitz (center : X → ℝ) (τ : ℝ) :
    LipschitzWith ‖τ / 8‖₊ (forecastNativeSpatialInverse center τ) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  apply (dist_pi_le_iff (mul_nonneg (norm_nonneg _) dist_nonneg)).mpr
  intro x
  change dist (center x + τ / 8 * z ⟨x, Sum.inl ()⟩)
    (center x + τ / 8 * w ⟨x, Sum.inl ()⟩) ≤ _
  rw [dist_add_left, dist_eq_norm, ← mul_sub, norm_mul]
  exact mul_le_mul_of_nonneg_left (dist_le_pi_dist z w _) (norm_nonneg _)

theorem forecastNativeTorusInverse_lipschitz (d : ℕ) [NeZero d]
    (deck : (Σ j, J j) → ZMod d)
    (frozen : {a : LayerSamplerAxis I n // P a} → ℝ) :
    LipschitzWith (forecastNativeAmbientLip U b o R)
      (forecastNativeTorusInverse U b o R P d deck frozen) := by
  apply LipschitzWith.of_dist_le_mul
  intro v w
  have h := ((forecastNativeAmbientLinear_lipschitz U b o R).comp
    (forecastNativeFillAxes_lipschitz P frozen)).dist_le_mul v w
  simp only [mul_one] at h
  apply (dist_pi_le_iff (mul_nonneg (NNReal.coe_nonneg _) dist_nonneg)).mpr
  intro a
  rw [forecastNativeTorusInverse, forecastNativeTorusInverse, dist_add_right,
    dist_eq_norm, ← AddCircle.coe_sub]
  apply QuotientAddGroup.norm_mk_le_norm.trans
  rw [← sub_div, norm_div]
  have hd : (1 : ℝ) ≤ ‖(d : ℝ)‖ := by
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  exact (div_le_self (norm_nonneg _) hd).trans
    ((dist_le_pi_dist _ _ a).trans h)

namespace NormalizedPolynomialTwist

variable {periodCap coverCap : ℝ} {L : ℝ≥0}

theorem forecastPullback_norm_le
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (residue : X → ZMod W.modulus) (deck : (Σ j, J j) → ZMod W.cover)
    (center : X → ℝ) (τ : ℝ) (frozen : {a : LayerSamplerAxis I n // P a} → ℝ)
    (y : Domain) : ‖W.forecastPullback U b o R P residue deck center τ frozen y‖ ≤ 1 := by
  unfold forecastPullback
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (W.mask_bound _)).trans (W.smooth_bound _)

theorem forecastPullback_lipschitz
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (residue : X → ZMod W.modulus) (deck : (Σ j, J j) → ZMod W.cover)
    (center : X → ℝ) (τ : ℝ) (frozen : {a : LayerSamplerAxis I n // P a} → ℝ) :
    LipschitzWith (L * max ‖τ / 8‖₊ (forecastNativeAmbientLip U b o R))
      (W.forecastPullback U b o R P residue deck center τ frozen) := by
  let : NeZero W.cover := ⟨W.cover_pos.ne'⟩
  have hin := ((forecastNativeSpatialInverse_lipschitz center τ).comp LipschitzWith.prod_fst).prodMk
    ((forecastNativeTorusInverse_lipschitz U b o R P W.cover deck frozen).comp LipschitzWith.prod_snd)
  simp only [mul_one] at hin
  have h := W.smooth_lipschitz.comp hin
  apply LipschitzWith.of_dist_le_mul
  intro y z
  rw [dist_eq_norm]
  change ‖W.mask residue * W.smooth _ - W.mask residue * W.smooth _‖ ≤ _
  rw [← mul_sub, norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (W.mask_bound _)).trans
    (by simpa only [Function.comp_apply, dist_eq_norm] using h.dist_le_mul y z)

end NormalizedPolynomialTwist
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ForecastNativeResidueTest
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module
open scoped Classical NNReal
variable {m : ℕ} {X : Type*} [Fintype X]
variable {I E : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
variable {n : Fin m → ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (R : Fin m → ℝ) (P : LayerSamplerAxis I n → Prop) [DecidablePred P]
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X E P)

namespace NormalizedPolynomialTwist
variable {periodCap coverCap : ℝ} {L : ℝ≥0}
variable (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)

theorem forecastResidueTest_bounds (q : ℕ) [NeZero q] (hm : 0 < m)
    (hperiod : W.modulus ∣ q) (hcover : W.cover ∣ q)
    (sheet : ∀ j, {i : Fin (n j) // P ⟨j, .inr i⟩} → ℤ)
    (frozen : {a : LayerSamplerAxis I n // P a} → ℝ)
    (center : X → ℝ) (τ : ℝ) (out : Out → ZMod q) :
    (∀ y, ‖W.forecastResidueTest U b hb o bW R P q hm hperiod hcover sheet frozen center τ out y‖ ≤ 1) ∧
      LipschitzWith (L * max ‖τ / 8‖₊ (forecastNativeAmbientLip U b o R))
        (W.forecastResidueTest U b hb o bW R P q hm hperiod hcover sheet frozen center τ out) :=
  ⟨W.forecastPullback_norm_le U b o R P _ _ center τ frozen,
    W.forecastPullback_lipschitz U b o R P _ _ center τ frozen⟩

end NormalizedPolynomialTwist
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

variable {δ : ℝ} (hδ : 0 < δ)
  (hw : ∀ a p, δ ≤ width a p) (hl : ∀ a p, 0 ≤ lower a p)
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
  (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
    (allocatedLayerWidths B U basis S j)
    (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))

include hR hσ hδ hw hl hs in
theorem fixedSpatialKernelOriginalForecastDensity_probability_data :
    (∀ y, 0 ≤ density sample y) ∧ Integrable (density sample) ∧
      (∫ y, density sample y) = 1 := by
  have hr := allocatedSampleRestrictedProfileNoise_short_abs_le B U basis hR hσ S sample hs
  have hf := fixedSpatialKernelDensity_probability_density_s2 e W L z h0 h1
  have hf' := fixedSpatialEmptyDensity_probability_data _ hf.1 hf.2.1 hf.2.2
  have hg := allocatedFixedPathLiftDensity_law_probability B short R σ
    (fun j => (hR j).ne') hB lower width hamin hδ
    (fun a => unitProfilePrincipalLowerBound_le B a.val) hw hl (noise sample) hr
  refine ⟨fun y => mul_nonneg (hf'.1 y.1) (hg.2.1 y.2),
    binaryDensity_integrable hf'.2.1 hg.2.2.1, ?_⟩
  change (∫ y, binaryDensity spatial (liftDensity sample) y ∂volume.prod volume) = 1
  rw [binaryDensity_mass, hf'.2.2, hg.2.2.2, one_mul]

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
theorem fixedSpatialKernelSliceOriginalForecastDensity_probability_data :
    (∀ y, 0 ≤ density sample y) ∧ Integrable (density sample) ∧
      (∫ y, density sample y) = 1 :=
  fixedSpatialKernelOriginalForecastDensity_probability_data B U basis hR hσ S
    e W L frame h0slice h1slice hB lowerP widthP hδP hwP hlP sample hs

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastNativeJointTestBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module
open scoped Classical NNReal
variable {m : ℕ} {X : Type*} [Fintype X]
variable {I E : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
variable {n : Fin m → ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (Lsize : ℕ)
local notation "short" => allocatedShortAxis (I := I) U b Lsize
local notation "Grid" => AllocatedShortIntegerAxis U b Lsize →
  ((Finset.univ : Finset (Finset Empty)) : Type) → ℤ

variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (R : Fin m → ℝ)
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X E short)

namespace NormalizedPolynomialTwist
variable {periodCap coverCap : ℝ} {Lip : ℝ≥0}
variable (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)

theorem forecastShortGridTest_bounds (q : ℕ) [NeZero q] (hm : 0 < m)
    (hperiod : W.modulus ∣ q) (hcover : W.cover ∣ q)
    (center : X → ℝ) (τ : ℝ) (grid : Grid) (out : Out → ZMod q) :
    (∀ y, ‖W.forecastShortGridTest U b Lsize hb o bW R q hm hperiod hcover center τ grid out y‖ ≤ 1) ∧
      LipschitzWith (Lip * max ‖τ / 8‖₊ (forecastNativeAmbientLip U b o R))
        (W.forecastShortGridTest U b Lsize hb o bW R q hm hperiod hcover center τ grid out) :=
  W.forecastResidueTest_bounds U b hb o bW R short q hm hperiod hcover _ _ center τ out

end NormalizedPolynomialTwist

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedFixedPathRecoveredJointGridComparison
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory BooleanCubeKernel
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G X T : Type*} [Fintype G] [Fintype X] [Fintype T]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable {periodCap coverCap : ℝ} {Lip : ℝ≥0}
variable (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "degree" => layerSamplerDegree I n
local notation "Sample" => CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n
local notation "Original" => PrincipalIntegerTuples B degree Empty (allocatedPrincipalSides B U basis S)
local notation "selected" => allocatedShortIntegerSelection U basis S.value
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X E short)
local notation "Joint" => X ⊕ AllocatedActiveIntegerAxis U basis S.value
local notation "Cont" => (Σ j : Fin m, I j)

include hR hσ in
theorem fixedSpatialSliceNativeJointGridMean_comparison_s2_oai
    (e : G ≃ X ⊕ (X ⊕ T)) (rootBudget rootLength : ℝ) (z : Option G × X → ℝ)
    (h0 : (fixedSpatialKernelBlock e rootBudget rootLength z false).det ≠ 0)
    (h1 : (fixedSpatialKernelBlock e rootBudget rootLength z true).det ≠ 0)
    (lowerG widthG : G → ℝ) (hwGne : ∀ g, widthG g ≠ 0)
    (hlG : ∀ g, 0 ≤ lowerG g) (hwG : ∀ g, 0 ≤ widthG g)
    (hcontainedG : ∀ g, lowerG g + widthG g ≤ 1)
    (hB : ∀ a : Active, 4 ≤ Fintype.card (B a.val))
    (lowerP widthP : ∀ a : Active, B a.val × Fin (degree a.val) → ℝ)
    {δP : ℝ} (hδP : 0 < δP)
    (hwP : ∀ a p, δP ≤ widthP a p) (hlP : ∀ a p, 0 ≤ lowerP a p)
    (hwidthP : ∀ a p, |lowerP a p| + |widthP a p| ≤ 1)
    (hW : 0 ≤ rootBudget) (hL : 0 ≤ rootLength)
    (hsize : (Fintype.card G : ℝ) * rootLength ≤ rootBudget)
    (hz : ∀ a, |z a| ≤ 1)
    (sample : Sample)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    (hm : 0 < m)
    (τ : ℝ) (base : X → ℤ) (box : X → ℕ)
    (xref : G → IntegerScalarCubeBox Empty S.value)
    {Ω : Type*} [Fintype Ω]
    (law : FiniteProbabilityWeights Original)
    (active : Original → FiniteProbabilityWeights Ω)
    (Y : Original → Ω → Out → ℤ)
    (N q : ℕ) [NeZero N] [NeZero q] (hq : q ∣ N)
    (hperiod : W.modulus ∣ q) (hcover : W.cover ∣ q)
    (gridVolume : ℝ) (hV : gridVolume ≠ 0)
    (center scale : Joint → ℝ) (hscale : ∀ j, 0 < scale j)
    (cutoff : ℕ) (hcutoff : 0 < cutoff)
    {D P δ : ℝ} (hD : 0 ≤ D)
    (hP : ((Fintype.card Out + 2 : ℕ) : ℝ) ≤ P)
    (hdecay : ∀ i (χ : AddChar (Out → ZMod N) ℂ),
      ‖finiteImageCharacteristic (active i) (fun x j => (Y i x j : ZMod N)) χ‖ ≤
        D * (orderOf χ : ℝ) ^ (-P))
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hmesh : ∀ j, ((q * cutoff : ℕ) : ℝ) / scale j ≤ δ) :
    let frame := fixedSpatialKernelSliceFrame rootBudget rootLength z lowerG widthG
    let h0slice := fixedSpatialKernelBlock_slice_det_ne_zero e rootBudget rootLength z
      lowerG widthG false h0 hwGne
    let h1slice := fixedSpatialKernelBlock_slice_det_ne_zero e rootBudget rootLength z
      lowerG widthG true h1 hwGne
    let density := fixedSpatialKernelSliceOriginalForecastDensity B U basis S e rootBudget rootLength z
      lowerG widthG h0 h1 hwGne hB lowerP widthP sample
    let C := fixedSpatialOriginalForecastCap B
      (fixedSpatialKernelBlockEquiv e rootBudget rootLength frame true h1slice) hδP
    let L := fixedSpatialOriginalForecastLip B
      (fixedSpatialKernelBlockEquiv e rootBudget rootLength frame false h0slice)
      (fixedSpatialKernelBlockEquiv e rootBudget rootLength frame true h1slice) hδP
    let K := Lip * max ‖τ / 8‖₊ (forecastNativeAmbientLip U basis o R)
    let c := fun a => (sample (selected a).1).2 (selected a).2
    let grid := forecastInactiveFixedOutput B U basis S selected c xref
    let test := W.forecastShortGridTest U basis S.value hb o bW R q hm hperiod hcover
      (fun a => (base a : ℝ) / box a) τ
    ‖forecastJointOriginalGridMean U basis S.value hm law active grid Y N q hq
        gridVolume density test center scale -
      (∑' g, 𝔼 r : Out → ZMod N,
        ((rationalInactiveForecast law active grid Y N gridVolume g r / gridVolume : ℝ) : ℂ) *
          ∫ y, test g (fun a => ZMod.castHom hq (ZMod q) (r a)) y
            ∂realDensityMeasure volume density)‖ ≤
      ((cutoff : ℝ) ^ (Fintype.card Out + 1) *
        (2 * 8 ^ Fintype.card Joint * ((L : ℝ) + C * K) * δ) +
        (D / cutoff) * (8 ^ Fintype.card Joint * (L : ℝ) * δ)) *
          6 ^ Fintype.card Cont + 2 * (D / cutoff) := by
  classical
  intro frame h0slice h1slice density C L K c grid test
  have hbnd := fixedSpatialKernelSliceOriginalForecastDensity_bounds_s2 B U basis hR hσ S
    e rootBudget rootLength z lowerG widthG h0 h1 hwGne hB lowerP widthP
    hδP hwP hlP sample hs
  have hdata := fixedSpatialKernelSliceOriginalForecastDensity_probability_data B U basis hR hσ S
    e rootBudget rootLength z lowerG widthG h0 h1 hwGne hB lowerP widthP
    hδP hwP hlP sample hs
  have hsupport : ∀ y, (3 : ℝ) < ‖y‖ → density y = 0 := by
    intro y hy
    exact fixedSpatialKernelSliceOriginalForecastDensity_zero_of_norm_gt_two_s2 B U basis hR hσ S
      e rootBudget rootLength z lowerG widthG h0 h1 hwGne hB lowerP widthP
      hδP hwP hlP sample hs hwidthP hW hL hsize hz hlG hwG hcontainedG y
      (lt_trans (by norm_num) hy)
  have htest := W.forecastShortGridTest_bounds U basis S.value hb o bW R q hm hperiod hcover
    (fun a => (base a : ℝ) / box a) τ
  have h := forecastJointOriginalGridMean_comparison_s2 U basis S.value hm law active grid Y N q hq
    gridVolume density test center scale hV cutoff hcutoff hD hP hdecay C L K
    hbnd.2 hdata.1 (fun g r => (htest g r).2)
    (fun y => by rw [abs_of_nonneg (hdata.1 y)]; exact (hbnd.1 y).2)
    (fun g r => (htest g r).1) hscale (radius := 3) (by norm_num) hδ hδ1 hmesh hsupport
  have hmass : (∫ y, density y) = 1 := hdata.2.2
  norm_num only [hmass, mul_one] at h
  exact h

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4, u_5, u_6, u_7, u_8} : type_of% @OAI.Erdos3.VectorPolynomial.fixedSpatialSliceNativeJointGridMean_comparison_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6, u_7, u_8} := @OAI.Erdos3.VectorPolynomial.fixedSpatialSliceNativeJointGridMean_comparison_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6, u_7, u_8}
