-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.fixedSpatialKernelSliceOriginalForecastDensity_bounds_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T05:17:40.705391+00:00
-- url     : https://prove2.me/submissions/e2bbb1f2-6a5a-4124-872a-ed6bbf21b05d

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B197
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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.BinaryDensity
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem binaryDensity_cap {X Y : Type*} (f : X → ℝ) (g : Y → ℝ) (C D : ℝ≥0)
    (hf : ∀ x, f x ∈ Set.Icc (0 : ℝ) C) (hg : ∀ y, g y ∈ Set.Icc (0 : ℝ) D) (p : X × Y) :
    binaryDensity f g p ∈ Set.Icc (0 : ℝ) (C * D) :=
  ⟨mul_nonneg (hf _).1 (hg _).1, mul_le_mul (hf _).2 (hg _).2 (hg _).1 C.coe_nonneg⟩

theorem binaryDensity_lipschitz {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (f : X → ℝ) (g : Y → ℝ) (C D L M : ℝ≥0)
    (hf : ∀ x, f x ∈ Set.Icc (0 : ℝ) C) (hg : ∀ y, g y ∈ Set.Icc (0 : ℝ) D)
    (hL : LipschitzWith L f) (hM : LipschitzWith M g) :
    LipschitzWith (D * L + C * M) (binaryDensity f g) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hdx : dist x.1 y.1 ≤ dist x y := le_max_left _ _
  have hdy : dist x.2 y.2 ≤ dist x y := le_max_right _ _
  have hleft : |f x.1 - f y.1| ≤ (L : ℝ) * dist x y := by
    have h := hL.dist_le_mul x.1 y.1
    rw [Real.dist_eq] at h
    exact h.trans (mul_le_mul_of_nonneg_left hdx L.coe_nonneg)
  have hright : |g x.2 - g y.2| ≤ (M : ℝ) * dist x y := by
    have h := hM.dist_le_mul x.2 y.2
    rw [Real.dist_eq] at h
    exact h.trans (mul_le_mul_of_nonneg_left hdy M.coe_nonneg)
  rw [Real.dist_eq]
  change |f x.1 * g x.2 - f y.1 * g y.2| ≤ _
  calc
    |f x.1 * g x.2 - f y.1 * g y.2| =
        |(f x.1 - f y.1) * g x.2 + f y.1 * (g x.2 - g y.2)| := by congr 1; ring
    _ ≤ |(f x.1 - f y.1) * g x.2| + |f y.1 * (g x.2 - g y.2)| := abs_add_le _ _
    _ = |f x.1 - f y.1| * g x.2 + f y.1 * |g x.2 - g y.2| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (hg _).1, abs_of_nonneg (hf _).1]
    _ ≤ ((L : ℝ) * dist x y) * D + C * ((M : ℝ) * dist x y) :=
      add_le_add (mul_le_mul hleft (hg _).2 (hg _).1 (mul_nonneg L.coe_nonneg dist_nonneg))
        (mul_le_mul (hf _).2 hright (abs_nonneg _) C.coe_nonneg)
    _ = (D * L + C * M : ℝ≥0) * dist x y := by push_cast; ring

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedOriginalSampleForecastAtom
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

variable (P : LayerSamplerAxis I n → Prop) [DecidablePred P]
variable {δ : ℝ} (hδ : 0 < δ)

/-- Backport of `Finset.prod_le_prod_of_injOn` (Mathlib d13f23b), proved as there. -/
theorem allocatedFixedPathLift_prod_le_prod_of_injOn_aux {ι α N : Type*} [CommMonoid N]
    [PartialOrder N] [IsOrderedMonoid N] [DecidableEq α]
    {f : ι → N} {g : α → N} {s : Finset ι} {t : Finset α} (e : ι → α) (he : Set.InjOn e s)
    (ht : Finset.image e s ⊆ t) (h : ∀ i ∈ s, f i ≤ g (e i))
    (hg : ∀ a ∈ t, a ∉ Finset.image e s → 1 ≤ g a) :
    ∏ i ∈ s, f i ≤ ∏ a ∈ t, g a := by
  refine le_trans ?_ <| Finset.prod_le_prod_of_subset_of_one_le' ht hg
  rw [Finset.prod_image he]
  exact Finset.prod_le_prod' h

theorem allocatedFixedPathLift_prod_add_one_le_allAxis :
    (∏ a, (allocatedFixedPathLiftRowCap P (unitProfilePrincipalLowerBound_pos B) hδ a + 1)) ≤
      allocatedForecastAllAxisLiftCap B hδ := by
  classical
  apply allocatedFixedPathLift_prod_le_prod_of_injOn_aux Subtype.val
      (fun _ _ _ _ h => Subtype.val_injective h) (Finset.subset_univ _)
  · intro a _
    exact le_rfl
  · intro a _ _
    exact le_add_of_nonneg_left zero_le

theorem allocatedFixedPathLift_prod_le_allAxis :
    (∏ a, allocatedFixedPathLiftRowCap P (unitProfilePrincipalLowerBound_pos B) hδ a) ≤
      allocatedForecastAllAxisLiftCap B hδ := by
  calc
    _ ≤ ∏ a, (allocatedFixedPathLiftRowCap P
        (unitProfilePrincipalLowerBound_pos B) hδ a + 1) :=
      Finset.prod_le_prod' (fun _ _ => le_add_of_nonneg_right zero_le_one)
    _ ≤ _ := allocatedFixedPathLift_prod_add_one_le_allAxis B P hδ

theorem allocatedFixedPathLift_sum_lip_le_allAxis :
    (∑ a, allocatedFixedPathLiftRowCap P (unitProfilePrincipalLowerBound_pos B) hδ a *
      (2 * allocatedFixedPathLiftRowCap P (unitProfilePrincipalLowerBound_pos B) hδ a)) ≤
    ∑ a, allocatedForecastAllAxisRowCap B hδ a * (2 * allocatedForecastAllAxisRowCap B hδ a) := by
  apply Finset.sum_le_sum_of_injOn Subtype.val
      (fun _ _ _ _ h => Subtype.val_injective h) (Finset.subset_univ _)
  · intro a _
    exact le_rfl
  · intro a _ _
    exact zero_le

theorem allocatedFixedPathLift_lip_le_allAxis :
    (∏ a, (allocatedFixedPathLiftRowCap P (unitProfilePrincipalLowerBound_pos B) hδ a + 1)) *
      (∑ a, allocatedFixedPathLiftRowCap P (unitProfilePrincipalLowerBound_pos B) hδ a *
        (2 * allocatedFixedPathLiftRowCap P (unitProfilePrincipalLowerBound_pos B) hδ a)) ≤
      allocatedForecastAllAxisLiftLip B hδ :=
  mul_le_mul' (allocatedFixedPathLift_prod_add_one_le_allAxis B P hδ)
    (allocatedFixedPathLift_sum_lip_le_allAxis B P hδ)

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

local notation "A₀" => fixedSpatialKernelBlockEquiv e W L z false h0
local notation "A₁" => fixedSpatialKernelBlockEquiv e W L z true h1
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
theorem fixedSpatialKernelOriginalForecastDensity_bounds :
    (∀ y, density sample y ∈ Set.Icc (0 : ℝ) (fixedSpatialOriginalForecastCap B A₁ hδ)) ∧
      LipschitzWith (fixedSpatialOriginalForecastLip B A₀ A₁ hδ) (density sample) := by
  have hf := fixedSpatialKernelDensity_bounds_s2 e W L z h0 h1
  have hf' := fixedSpatialEmptyDensity_bounds _ hf.1 hf.2
  have hr := allocatedSampleRestrictedProfileNoise_short_abs_le B U basis hR hσ S sample hs
  have hg := allocatedFixedPathLiftDensity_cap_lipschitz B short R σ
    (fun j => (hR j).ne') hB lower width hamin hδ
    (fun a => unitProfilePrincipalLowerBound_le B a.val) hw hl (noise sample) hr
  have hgcap : ∀ y, liftDensity sample y ∈ Set.Icc (0 : ℝ) (allocatedForecastAllAxisLiftCap B hδ) := by
    intro y
    exact ⟨(hg.1 y).1, (hg.1 y).2.trans (by
      exact_mod_cast allocatedFixedPathLift_prod_le_allAxis B short hδ)⟩
  have hglip := hg.2.weaken (allocatedFixedPathLift_lip_le_allAxis B short hδ)
  exact ⟨binaryDensity_cap spatial (liftDensity sample) _ _ hf'.1 hgcap,
    binaryDensity_lipschitz spatial (liftDensity sample) _ _ _ _ hf'.1 hgcap hf'.2 hglip⟩

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
local notation "A₀" => fixedSpatialKernelBlockEquiv e W L frame false h0slice
local notation "A₁" => fixedSpatialKernelBlockEquiv e W L frame true h1slice

local notation "density" => fixedSpatialKernelSliceOriginalForecastDensity B U basis S e W L z
  lowerG widthG h0 h1 hwG hB lowerP widthP

variable {δP : ℝ} (hδP : 0 < δP)
  (hwP : ∀ a p, δP ≤ widthP a p) (hlP : ∀ a p, 0 ≤ lowerP a p)
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
  (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
    (allocatedLayerWidths B U basis S j)
    (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))

include hR hσ hδP hwP hlP hs in
theorem fixedSpatialKernelSliceOriginalForecastDensity_bounds_s2_oai :
    (∀ y, density sample y ∈ Set.Icc (0 : ℝ) (fixedSpatialOriginalForecastCap B A₁ hδP)) ∧
      LipschitzWith (fixedSpatialOriginalForecastLip B A₀ A₁ hδP) (density sample) :=
  fixedSpatialKernelOriginalForecastDensity_bounds B U basis hR hσ S
    e W L frame h0slice h1slice hB lowerP widthP hδP hwP hlP sample hs

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4, u_5, u_6} : type_of% @OAI.Erdos3.VectorPolynomial.fixedSpatialKernelSliceOriginalForecastDensity_bounds_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6} := @OAI.Erdos3.VectorPolynomial.fixedSpatialKernelSliceOriginalForecastDensity_bounds_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6}
