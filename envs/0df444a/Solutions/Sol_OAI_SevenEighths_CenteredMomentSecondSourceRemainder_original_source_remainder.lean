-- Prove2me | solution 1 for OAI.SevenEighths.CenteredMomentSecondSourceRemainder.original_source_remainder
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T03:33:19.458051+00:00
-- url     : https://prove2.me/submissions/6f672d01-3b44-4a00-b555-fd95e5db1074

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B025
import Definitions.Def_OAIHecke78B028
import Theorems.Thm_OAI_SevenEighths_CenteredMomentSecondEnergySplit_original_energy_split
import Theorems.Thm_OAI_SevenEighths_CenteredMomentSecondExceptionalFixedQSource_original_exceptional_energy
import Theorems.Thm_OAI_SevenEighths_CenteredMomentSecondLocalization_sourceGaussEnergy_localized

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Poisson.RadialFourier
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff

namespace EisensteinSchwartzPoisson

open ConcreteTraceCRT ActualEisensteinCubic
open scoped SchwartzMap

theorem polynomial_tail_majorant (A : ℕ) (K T q B f : ℝ)
    (hK : 0 < K) (hT : 0 ≤ T) (hq : 0 ≤ q) (hf : 0 ≤ f)
    (htail : T ≤ K * q) (hbound : (1 + K * q) ^ (A + 2) * f ≤ B) :
    f ≤ (B / ((min 1 K) ^ 2 * (1 + T) ^ A)) * ((1 + q) ^ 2)⁻¹ := by
  have hm : 0 < min 1 K := lt_min (by norm_num) hK
  have hm1 : min 1 K ≤ 1 := min_le_left _ _
  have hmK : min 1 K ≤ K := min_le_right _ _
  have hbase : min 1 K * (1 + q) ≤ 1 + K * q := by
    nlinarith [mul_le_mul_of_nonneg_right hmK hq]
  have htwo : (min 1 K) ^ 2 * (1 + q) ^ 2 ≤ (1 + K * q) ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hbase _
  have hpow : (1 + T) ^ A ≤ (1 + K * q) ^ A :=
    pow_le_pow_left₀ (by positivity) (by linarith) _
  have hden : ((min 1 K) ^ 2 * (1 + T) ^ A) * (1 + q) ^ 2 ≤
      (1 + K * q) ^ (A + 2) := by
    have hh := mul_le_mul hpow htwo (by positivity) (by positivity)
    rw [pow_add]
    nlinarith
  have hprod : f * (((min 1 K) ^ 2 * (1 + T) ^ A) * (1 + q) ^ 2) ≤ B := by
    calc
      _ = (((min 1 K) ^ 2 * (1 + T) ^ A) * (1 + q) ^ 2) * f := mul_comm _ _
      _ ≤ (1 + K * q) ^ (A + 2) * f := mul_le_mul_of_nonneg_right hden hf
      _ ≤ B := hbound
  have hraw := (le_div_iff₀ (show 0 < ((min 1 K) ^ 2 * (1 + T) ^ A) * (1 + q) ^ 2
      by positivity)).mpr hprod
  simpa only [div_eq_mul_inv, mul_inv_rev, mul_comm, mul_left_comm, mul_assoc] using hraw

theorem paperRadialFourier_lattice_summable_norm (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) :
    Summable (fun h : O => ‖paperRadialFourier W (K * ‖eisEmbedding h‖ ^ 2)‖) := by
  obtain ⟨s, C, hC, hb⟩ := paperRadialFourier_source_weighted_bound 2
  let B := C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  let D := (min 1 K) ^ 2 * (1 + (0 : ℝ)) ^ (0 : ℕ)
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _
    (eisenstein_cauchy_summable.mul_left (B / D))
  intro h
  exact polynomial_tail_majorant 0 K 0 _ B _ hK (by norm_num)
    (sq_nonneg _) (norm_nonneg _) (by positivity) (hb W _ (by positivity))

theorem paperRadialFourier_lattice_tail (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(ℝ, ℂ)) (K T : ℝ), 0 < K → 0 ≤ T →
        (∑' h : {h : O // T ≤ K * ‖eisEmbedding h‖ ^ 2},
          ‖paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2)‖) ≤
        (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) /
          ((min 1 K) ^ 2 * (1 + T) ^ A) := by
  obtain ⟨s, C, hC, hb⟩ := paperRadialFourier_source_weighted_bound (A + 2)
  refine ⟨s, C * (eisensteinCauchyMass + 1), by
    have := eisensteinCauchyMass_nonneg
    positivity, ?_⟩
  intro W K T hK hT
  let B := C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  let D := (min 1 K) ^ 2 * (1 + T) ^ A
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hm : 0 < min 1 K := lt_min (by norm_num) hK
  have hD : 0 < D := by dsimp [D]; positivity
  let S := {h : O | T ≤ K * ‖eisEmbedding h‖ ^ 2}
  have hp (h : S) :
      ‖paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2)‖ ≤
        (B / D) * ((1 + ‖eisEmbedding h.val‖ ^ 2) ^ 2)⁻¹ := by
    exact polynomial_tail_majorant A K T _ B _ hK hT (sq_nonneg _)
      (norm_nonneg _) h.property (hb W _ (by positivity))
  have hmajor : Summable (fun h : S => (B / D) *
      ((1 + ‖eisEmbedding h.val‖ ^ 2) ^ 2)⁻¹) :=
    (eisenstein_cauchy_summable.subtype S).mul_left (B / D)
  have hs : Summable (fun h : S =>
      ‖paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hp hmajor
  calc
    _ ≤ ∑' h : S, (B / D) * ((1 + ‖eisEmbedding h.val‖ ^ 2) ^ 2)⁻¹ :=
      hs.tsum_le_tsum hp hmajor
    _ = (B / D) * ∑' h : S, ((1 + ‖eisEmbedding h.val‖ ^ 2) ^ 2)⁻¹ := tsum_mul_left
    _ ≤ (B / D) * eisensteinCauchyMass :=
      mul_le_mul_of_nonneg_left (eisensteinCauchyMass_subtype S) (div_nonneg hB hD.le)
    _ ≤ (B / D) * (eisensteinCauchyMass + 1) := by
      gcongr
      linarith
    _ = _ := by dsimp [B, D]; ring

end EisensteinSchwartzPoisson

open scoped BigOperators Classical SchwartzMap ContDiff

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.QuadraticSieve.CoefficientCancellation
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid

open scoped BigOperators Classical

open scoped BigOperators Classical SchwartzMap ContDiff

open scoped BigOperators Classical SchwartzMap
namespace QuadraticInitialBound
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson

theorem norm_finite_character_le_one {R : Type*} [CommRing R] [Fintype R]
    (χ : MulChar R ℂ) (r : R) : ‖χ r‖ ≤ 1 := by
  by_cases hr : IsUnit r
  · obtain ⟨u, rfl⟩ := hr
    simpa only [MulChar.coe_equivToUnitHom] using
      (Complex.norm_eq_one_of_mem_rootsOfUnity (χ.apply_mem_rootsOfUnity u)).le
  · rw [MulChar.map_nonunit χ hr, norm_zero]
    exact zero_le_one

end QuadraticInitialBound

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.Primary
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
open scoped ContDiff
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentPrimary
open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss
open PrimaryIdealUnitReindex (GoodIdeal)
open CubicEisenstein (PrimaryLower primaryLowerIdealEquiv)

theorem primaryIdealCharacter_norm_le_one (c : O) (hc : c ≠ 0)
    (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (I : Ideal O) :
    ‖primaryIdealCharacter c χ I‖ ≤ 1 := by
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  exact QuadraticInitialBound.norm_finite_character_le_one χ _

end SevenEighths.CenteredMomentPrimary
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.Twist
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentTwist
open ActualEisensteinCubic EisensteinSchwartzPoisson
open CenteredMomentLattice

lemma norm_real_imaginary_power (X t : ℝ) (hX : 0 < X) :
    ‖(X : ℂ) ^ (Complex.I * t)‖ = 1 := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hX]
  simp

end SevenEighths.CenteredMomentTwist
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.Extraction
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentExtraction
open CenteredMomentRectangle CenteredMomentPrimary CenteredMomentTwist

theorem idealWeight_norm_le_one (c : O) (hc : c ≠ 0)
    (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (R : Ideal O) (t : ℝ)
    (I : Ideal O) (hI : I ≠ 0) : ‖idealWeight c χ R t I‖ ≤ 1 := by
  have hnorm : (0 : ℝ) < Ideal.absNorm I := by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hpow := norm_real_imaginary_power (Ideal.absNorm I : ℝ) t hnorm
  norm_cast at hpow
  simp only [idealWeight, norm_mul, hpow, mul_one]
  by_cases hcop : IsCoprime I R
  · simpa only [hcop, ite_true, norm_one, one_mul] using primaryIdealCharacter_norm_le_one c hc χ I
  · simp only [hcop, ite_false, norm_zero, zero_mul, zero_le_one]

end SevenEighths.CenteredMomentExtraction
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.Tail
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentTail
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein EisensteinSchwartzPoisson
open CenteredMomentCommonSupport CenteredMomentCorrelation CenteredMomentFourier
open CenteredMomentSupportedCorrelation

theorem fullModulusCorrelation_norm_le (u v : O) (_hu : u ≠ 0) (_hv : v ≠ 0)
    [Fintype (Residue u)] [Fintype (Residue v)]
    (χu : MulChar (Residue u) ℂ) (χv : MulChar (Residue v) ℂ) (j : O) :
    ‖fullModulusCorrelation u v χu χv j‖ ≤
      (Ideal.absNorm (Ideal.span {u}) : ℝ) * (Ideal.absNorm (Ideal.span {v}) : ℝ) := by
  unfold fullModulusCorrelation fullCorrelation
  calc
    _ ≤ ∑ x : Residue u, ‖∑ y : Residue v,
      if scaledResidue u v (u * v) rfl x - scaledResidue v u (u * v) (mul_comm u v) y =
        Ideal.Quotient.mk _ j then χu x * star (χv y) else 0‖ := norm_sum_le _ _
    _ ≤ ∑ _x : Residue u, ∑ _y : Residue v, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro x hx
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro y hy
      split_ifs
      · rw [norm_mul, norm_star]
        exact (mul_le_of_le_one_left (norm_nonneg _)
          (QuadraticInitialBound.norm_finite_character_le_one χu x)).trans
          (QuadraticInitialBound.norm_finite_character_le_one χv y)
      · simp
    _ = _ := by
      simp [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]

theorem actualCorrelation_norm_le (u v : O)
    (hu : CanonicalQuadraticSieve.Supported (Ideal.span {u}))
    (hv : CanonicalQuadraticSieve.Supported (Ideal.span {v})) (j : O) :
    ‖actualCorrelation u v hu hv j‖ ≤
      (Ideal.absNorm (Ideal.span {u}) : ℝ) * (Ideal.absNorm (Ideal.span {v}) : ℝ) := by
  let := finite_quotient_span (supported_element_ne_zero u hu)
  let := finite_quotient_span (supported_element_ne_zero v hv)
  let : Fintype (Residue u) := Fintype.ofFinite _
  let : Fintype (Residue v) := Fintype.ofFinite _
  unfold actualCorrelation
  exact fullModulusCorrelation_norm_le u v (supported_element_ne_zero u hu)
    (supported_element_ne_zero v hv) _ _ j

theorem weighted_set_lattice_tail (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(ℝ, ℂ)) (D : Set O) (K T B : ℝ), 0 < K → 0 ≤ T → 0 ≤ B →
      (∀ h ∈ D, T ≤ K * ‖eisEmbedding h‖ ^ 2) →
      ∀ c δ : O → ℂ, (∀ h ∈ D, ‖c h‖ ≤ B) → (∀ h ∈ D, ‖δ h‖ ≤ 1) →
      ‖∑' h : D, δ h.val * c h.val * paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2)‖ ≤
        B * (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) /
          ((min 1 K) ^ 2 * (1 + T) ^ A) := by
  obtain ⟨s, C, hC, ht⟩ := paperRadialFourier_lattice_tail A
  refine ⟨s, C, hC, ?_⟩
  intro W D K T B hK hT hB hD c δ hc hδ
  let L := {h : O | T ≤ K * ‖eisEmbedding h‖ ^ 2}
  let f : D → L := fun h => ⟨h.val, hD h.val h.property⟩
  have hfi : Function.Injective f := by
    intro x y h
    exact Subtype.ext (congrArg (fun z : L => z.val) h)
  have hs := paperRadialFourier_lattice_summable_norm W K hK
  have hp (h : D) : ‖δ h.val * c h.val * paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2)‖ ≤
      B * ‖paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2)‖ := by
    rw [norm_mul, norm_mul]
    exact mul_le_mul_of_nonneg_right
      ((mul_le_of_le_one_left (norm_nonneg _) (hδ h.val h.property)).trans (hc h.val h.property))
      (norm_nonneg _)
  have hsum : Summable (fun h : D =>
      ‖δ h.val * c h.val * paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hp ((hs.subtype D).mul_left B)
  calc
    _ ≤ ∑' h : D, ‖δ h.val * c h.val * paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2)‖ :=
      norm_tsum_le_tsum_norm hsum
    _ ≤ ∑' h : D, B * ‖paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2)‖ :=
      hsum.tsum_le_tsum hp ((hs.subtype D).mul_left B)
    _ = B * ∑' h : D, ‖paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2)‖ := tsum_mul_left
    _ ≤ B * ∑' h : L, ‖paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2)‖ :=
      mul_le_mul_of_nonneg_left ((hs.subtype D).tsum_le_tsum_of_inj f hfi
        (fun _ _ => norm_nonneg _) (fun _ => le_rfl) (hs.subtype L)) hB
    _ ≤ _ := by
      convert (preTransparency := .instances) mul_le_mul_of_nonneg_left (ht W K T hK hT) hB using 1
      · rfl
      · ring

theorem uniform_sector_lattice_tail (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(ℝ, ℂ)) (D : Set O) (K₀ T B : ℝ), 0 < K₀ → 0 ≤ T → 0 ≤ B →
      (∀ h ∈ D, T ≤ K₀ * ‖eisEmbedding h‖ ^ 2) →
      ∀ K : ℝ, K₀ ≤ K →
      ∀ c δ : O → ℂ, (∀ h ∈ D, ‖c h‖ ≤ B) → (∀ h ∈ D, ‖δ h‖ ≤ 1) →
      ‖∑' h : D, δ h.val * c h.val * paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2)‖ ≤
        B * (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) /
          ((min 1 K₀) ^ 2 * (1 + T) ^ A) := by
  obtain ⟨s, C, hC, ht⟩ := weighted_set_lattice_tail A
  refine ⟨s, C, hC, ?_⟩
  intro W D K₀ T B hK₀ hT hB hD K hK c δ hc hδ
  have hD' (h : O) (hh : h ∈ D) : T ≤ K * ‖eisEmbedding h‖ ^ 2 :=
    (hD h hh).trans (mul_le_mul_of_nonneg_right hK (sq_nonneg _))
  apply (ht W D K T B (hK₀.trans_le hK) hT hB hD' c δ hc hδ).trans
  apply div_le_div_of_nonneg_left (by positivity)
    (by have : 0 < min 1 K₀ := lt_min zero_lt_one hK₀; positivity)
  gcongr

end SevenEighths.CenteredMomentTail
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.AddedZeroUniform
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentAddedZeroUniform
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentGaussEnergy CenteredMomentAddedZero CenteredMomentRectangle
local notation "O" => ActualEisensteinCubic.O

lemma tupleEquiv_slot {ι : Type*} {n : ℕ} (e : ι ≃ Fin n) (v : Tuple ι) (i : ι) :
    tupleEquiv e v ((e i).castAdd 2) = v (Sum.inl i) := by
  change v ((coordinateEquiv e).symm _) = _
  have h : coordinateEquiv e (Sum.inl i) = (e i).castAdd 2 := by
    simp only [coordinateEquiv, Equiv.trans_apply, Equiv.sumCongr_apply,
      Sum.map_inl, finSumFinEquiv_apply_left]
  rw [← h, Equiv.symm_apply_apply]

lemma tupleEquiv_plain {ι : Type*} {n : ℕ} (e : ι ≃ Fin n) (v : Tuple ι) (j : Fin 2) :
    tupleEquiv e v (j.natAdd n) = v (Sum.inr j) := by
  change v ((coordinateEquiv e).symm _) = _
  have h : coordinateEquiv e (Sum.inr j) = j.natAdd n := by
    simp only [coordinateEquiv, Equiv.trans_apply, Equiv.sumCongr_apply,
      Sum.map_inr, finSumFinEquiv_apply_right, Equiv.refl_apply]
  rw [← h, Equiv.symm_apply_apply]

theorem tupleProduct_reindex {ι : Type*} [Fintype ι] {n : ℕ}
    (e : ι ≃ Fin n) (v : Tuple ι) :
    tupleProduct (tupleEquiv e v) = finiteTupleProduct v := by
  exact (coordinateEquiv e).symm.prod_comp v

theorem originalCoefficient_reindex {ι : Type*} [Fintype ι] {n : ℕ}
    (e : ι ≃ Fin n) (c : O) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (R : Ideal O) (t : ℝ) (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (b₁ b₂ s : Ideal O) (v : Tuple ι) :
    originalCoefficient n c χ R t (fun j => ν (e.symm j)) (fun j => Wslot (e.symm j))
      (fun j => P (e.symm j)) W₁ W₂ X₁ X₂ Y₁ Y₂ b₁ b₂ s (tupleEquiv e v) =
    originalFiniteCoefficient c χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ b₁ b₂ s v := by
  have hslot (j : Fin n) : tupleEquiv e v (j.castAdd 2) = v (Sum.inl (e.symm j)) := by
    simpa only [Equiv.apply_symm_apply] using tupleEquiv_slot e v (e.symm j)
  have hp₀ : (⟨n, by omega⟩ : Fin (n + 2)) = (0 : Fin 2).natAdd n := by ext; simp
  have hp₁ : (⟨n + 1, by omega⟩ : Fin (n + 2)) = (1 : Fin 2).natAdd n := by ext; simp
  simp only [originalCoefficient, originalFiniteCoefficient, tupleProduct_reindex,
    hslot, hp₀, hp₁, tupleEquiv_plain]
  rw [e.symm.prod_comp (fun j => ν j (v (Sum.inl j)) * Wslot j ((Ideal.absNorm (v (Sum.inl j)) : ℝ) / P j))]

end SevenEighths.CenteredMomentAddedZeroUniform

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondDiagonal
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondDiagonal
open CenteredMomentCorrelation CenteredMomentCommonSupport CenteredMomentSupportedCorrelation
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
local notation "O" => ActualEisensteinCubic.O

theorem full_zero_off_diagonal (u v : O)
    [Fintype (Residue u)] [Fintype (Residue v)]
    (χ : MulChar (Residue u) ℂ) (ψ : MulChar (Residue v) ℂ)
    (hne : (Ideal.span {u} : Ideal O) ≠ Ideal.span {v}) :
    fullModulusCorrelation u v χ ψ 0 = 0 := by
  unfold fullModulusCorrelation fullCorrelation
  apply Finset.sum_eq_zero
  intro x hx
  apply Finset.sum_eq_zero
  intro y hy
  obtain ⟨x,rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨y,rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [scaledResidue_congruence]
  split_ifs with hc
  · by_cases hx0 : χ (Ideal.Quotient.mk _ x) = 0
    · rw [hx0,zero_mul]
    by_cases hy0 : ψ (Ideal.Quotient.mk _ y) = 0
    · rw [hy0,star_zero,mul_zero]
    have hux : IsCoprime u x := ((Ideal.isCoprime_span_singleton_iff x u).mp
      ((IdealCharacter.isUnit_mk_iff_isCoprime _ _).mp (MulChar.apply_ne_zero_iff.mp hx0))).symm
    have hvy : IsCoprime v y := ((Ideal.isCoprime_span_singleton_iff y v).mp
      ((IdealCharacter.isUnit_mk_iff_isCoprime _ _).mp (MulChar.apply_ne_zero_iff.mp hy0))).symm
    simp only [sub_zero] at hc
    have hu : u ∣ v*x := by
      have he := dvd_add ((dvd_mul_right u v).trans hc) (dvd_mul_right u y)
      convert (preTransparency := .instances) he using 1 ; ring
    have hv : v ∣ u*y := by
      have he := dvd_sub (dvd_mul_right v x) ((dvd_mul_left v u).trans hc)
      convert (preTransparency := .instances) he using 1 ; ring
    have huv := hux.dvd_of_dvd_mul_right hu
    have hvu := hvy.dvd_of_dvd_mul_right hv
    exact False.elim (hne (le_antisymm (Ideal.span_singleton_le_span_singleton.mpr hvu)
      (Ideal.span_singleton_le_span_singleton.mpr huv)))
  · rfl

theorem full_same_zero (u : O) (hu : u ≠ 0) [Fintype (Residue u)]
    (χ : MulChar (Residue u) ℂ) :
    fullModulusCorrelation u u χ χ 0 = ∑ x : Residue u, χ x*star (χ x) := by
  have hcong (x y : Residue u) :
      scaledResidue u u (u*u) rfl x - scaledResidue u u (u*u) (mul_comm u u) y =
        Ideal.Quotient.mk (Ideal.span {u*u}) 0 ↔ x=y := by
    obtain ⟨x,rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y,rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [scaledResidue_congruence,sub_zero,← mul_sub,mul_dvd_mul_iff_left hu]
    exact Ideal.mem_span_singleton.symm.trans Ideal.Quotient.eq.symm
  simp only [fullModulusCorrelation,fullCorrelation,hcong,Finset.sum_ite_eq,Finset.mem_univ,ite_true]

theorem full_same_zero_norm_le (u : O) (hu : u ≠ 0) [Fintype (Residue u)]
    (χ : MulChar (Residue u) ℂ) :
    ‖fullModulusCorrelation u u χ χ 0‖ ≤ (Fintype.card (Residue u) : ℝ) := by
  rw [full_same_zero u hu χ]
  calc
    _ ≤ ∑ x : Residue u, ‖χ x*star (χ x)‖ := norm_sum_le _ _
    _ ≤ ∑ _x : Residue u, (1:ℝ) := by
      apply Finset.sum_le_sum
      intro x hx
      by_cases hn : χ x = 0
      · simp only [hn,zero_mul,norm_zero,zero_le_one]
      · rw [MulChar.star_apply',MulChar.inv_apply_eq_inv',mul_inv_cancel₀ hn,norm_one]
    _ = _ := by simp

theorem actual_zero_off_diagonal (u v : O) (hu : Supported (Ideal.span {u}))
    (hv : Supported (Ideal.span {v}))
    (hpu : ConcretePrimeRowBridge.goodLambda^2 ∣ u-1)
    (hpv : ConcretePrimeRowBridge.goodLambda^2 ∣ v-1) (hne : u ≠ v) :
    actualCorrelation u v hu hv 0 = 0 := by
  let := ConcreteTraceCRT.finite_quotient_span (supported_element_ne_zero u hu)
  let := ConcreteTraceCRT.finite_quotient_span (supported_element_ne_zero v hv)
  let : Fintype (Residue u) := Fintype.ofFinite _
  let : Fintype (Residue v) := Fintype.ofFinite _
  apply full_zero_off_diagonal u v
  intro he
  apply hne
  rw [← primaryGenerator_span u (supported_element_ne_zero u hu) hpu,
    ← primaryGenerator_span v (supported_element_ne_zero v hv) hpv,he]

theorem actual_same_zero_norm_le (u : O) (hu : Supported (Ideal.span {u})) :
    ‖actualCorrelation u u hu hu 0‖ ≤ (Ideal.absNorm (Ideal.span {u}) : ℝ) := by
  let := ConcreteTraceCRT.finite_quotient_span (supported_element_ne_zero u hu)
  let : Fintype (Residue u) := Fintype.ofFinite _
  have hb := full_same_zero_norm_le u (supported_element_ne_zero u hu) (supportedModulusCharacter u hu)
  simpa only [actualCorrelation,supportedCorrelation,Ideal.absNorm_apply,Submodule.cardQuot_apply,Nat.card_eq_fintype_card] using hb

theorem divisible_ideal_card (S : Finset (Ideal O)) (s : Ideal O) (hs : s ≠ 0)
    (hS : ∀ I ∈ S, I ≠ 0) (hdiv : ∀ I ∈ S, s ∣ I)
    (Y : ℝ) (hY : 0 ≤ Y) (hN : ∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ Y) :
    (S.card : ℝ) ≤ 128*Y/(Ideal.absNorm s : ℝ) := by
  by_cases hempty : S.Nonempty
  · have hquot (I : Ideal O) (hI : I ∈ S) : idealQuotient s I ≠ 0 :=
      ne_zero_of_dvd_ne_zero (hS I hI) (idealQuotient_dvd (hdiv I hI))
    have hbound (I : Ideal O) (hI : I ∈ S) := idealQuotient_norm_le hs (hdiv I hI) Y (hN I hI)
    obtain ⟨I,hI⟩ := hempty
    have hscale : 1 ≤ Y/(Ideal.absNorm s : ℝ) := by
      have hn : (1:ℝ) ≤ Ideal.absNorm (idealQuotient s I) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (hquot I hI))
      exact hn.trans (hbound I hI)
    have hc := DescentFiberCost.finite_ideal_count_real (S.image (idealQuotient s)) _ hscale
      (by intro J hJ; obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hJ; exact hquot I hI)
      (by intro J hJ; obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hJ; exact hbound I hI)
    rw [Finset.card_image_of_injOn (fun I hI J hJ he => idealQuotient_injective_on s
      (hdiv I hI) (hdiv J hJ) he)] at hc
    convert (preTransparency := .instances) hc using 1 ; ring
  · rw [Finset.not_nonempty_iff_eq_empty.mp hempty,Finset.card_empty,Nat.cast_zero]
    positivity

theorem secondZeroEnergy_bound {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i}))
    (hp : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ a i-1)
    (hinj : Set.InjOn a S) (c : α → ℂ) :
    ‖secondZeroEnergy S a ha c‖ ≤ ∑ i ∈ S, ‖c i‖^2 := by
  have hroot (i : α) :
      ((Real.sqrt (Ideal.absNorm (Ideal.span {a i}) : ℝ) : ℂ)*
       (Real.sqrt (Ideal.absNorm (Ideal.span {a i}) : ℝ) : ℂ)) =
        (Ideal.absNorm (Ideal.span {a i}) : ℂ) := by
    rw [← Complex.ofReal_mul,Real.mul_self_sqrt (Nat.cast_nonneg _),Complex.ofReal_natCast]
  have he : secondZeroEnergy S a ha c =
      ∑ i ∈ S, (c i*star (c i)) *
        (actualCorrelation (a i) (a i) (ha i) (ha i) 0 /(Ideal.absNorm (Ideal.span {a i}) : ℂ)) := by
    unfold secondZeroEnergy
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_eq_single i]
    · rw [hroot]
    · intro j hj hji
      have hne : a i ≠ a j := fun he => hji (hinj hi hj he).symm
      rw [actual_zero_off_diagonal _ _ (ha i) (ha j) (hp i) (hp j) hne,zero_div,mul_zero]
    · exact fun hnot => False.elim (hnot hi)
  rw [he]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  rw [norm_mul,norm_mul,norm_star,norm_div,Complex.norm_natCast,← pow_two]
  have hN : 0 < (Ideal.absNorm (Ideal.span {a i}) : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (ha i).1)
  exact mul_le_of_le_one_right (sq_nonneg _) ((div_le_one hN).mpr (actual_same_zero_norm_le _ (ha i)))

theorem primary_column_card {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i}))
    (hp : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ a i-1)
    (hinj : Set.InjOn a S) (s : Ideal O) (hs : s ≠ 0)
    (hdiv : ∀ i ∈ S, s ∣ Ideal.span {a i}) (Y : ℝ) (hY : 0 ≤ Y)
    (hN : ∀ i ∈ S, (Ideal.absNorm (Ideal.span {a i}) : ℝ) ≤ Y) :
    (S.card : ℝ) ≤ 128*Y/(Ideal.absNorm s : ℝ) := by
  have hspan : Set.InjOn (fun i => (Ideal.span {a i} : Ideal O)) S := by
    intro i hi j hj he
    dsimp only at he
    apply hinj hi hj
    rw [← primaryGenerator_span (a i) (supported_element_ne_zero _ (ha i)) (hp i),
      ← primaryGenerator_span (a j) (supported_element_ne_zero _ (ha j)) (hp j),he]
  have hb := divisible_ideal_card (S.image (fun i => Ideal.span {a i})) s hs
    (by intro I hI; obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hI; exact (ha i).1)
    (by intro I hI; obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hI; exact hdiv i hi)
    Y hY (by intro I hI; obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hI; exact hN i hi)
  rwa [Finset.card_image_of_injOn hspan] at hb

theorem secondZeroEnergy_divisor_bound {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i}))
    (hp : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ a i-1)
    (hinj : Set.InjOn a S) (c : α → ℂ) (B : ℝ) (_hB : 0 ≤ B)
    (hc : ∀ i ∈ S, ‖c i‖ ≤ B) (s : Ideal O) (hs : s ≠ 0)
    (hdiv : ∀ i ∈ S, s ∣ Ideal.span {a i}) (Y : ℝ) (hY : 0 ≤ Y)
    (hN : ∀ i ∈ S, (Ideal.absNorm (Ideal.span {a i}) : ℝ) ≤ Y) :
    ‖secondZeroEnergy S a ha c‖ ≤ 128*B^2*Y/(Ideal.absNorm s : ℝ) := by
  calc
    _ ≤ ∑ i ∈ S, ‖c i‖^2 := secondZeroEnergy_bound S a ha hp hinj c
    _ ≤ ∑ _i ∈ S, B^2 := Finset.sum_le_sum (fun i hi =>
      pow_le_pow_left₀ (norm_nonneg _) (hc i hi) 2)
    _ = B^2*(S.card : ℝ) := by simp [mul_comm]
    _ ≤ B^2*(128*Y/(Ideal.absNorm s : ℝ)) :=
      mul_le_mul_of_nonneg_left (primary_column_card S a ha hp hinj s hs hdiv Y hY hN) (sq_nonneg _)
    _ = _ := by ring

end SevenEighths.CenteredMomentSecondDiagonal

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SourceMass
namespace OAI

noncomputable section
open scoped BigOperators Classical ContDiff

namespace SevenEighths.CenteredMomentSourceMass
open CenteredMomentAddedZero CenteredMomentRectangle CenteredMomentExtraction
local notation "O" => ActualEisensteinCubic.O

lemma idealBall_card (H : ℝ) (hH : 0 ≤ H) :
    ((idealBall H).card : ℝ) ≤ 128*H := by
  by_cases hs : (idealBall H).Nonempty
  · obtain ⟨I,hI⟩ := hs
    have hI := (mem_idealBall H I).mp hI
    have hn : (1:ℝ) ≤ Ideal.absNorm I := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI.1)
    exact DescentFiberCost.finite_ideal_count_real _ H (hn.trans hI.2)
      (fun J hJ => ((mem_idealBall H J).mp hJ).1)
      (fun J hJ => ((mem_idealBall H J).mp hJ).2)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hs]
    simp only [Finset.card_empty,Nat.cast_zero]
    positivity

lemma tupleBox_card {r : ℕ} (H : Fin r → ℝ) (hH : ∀ i, 0 ≤ H i) :
    ((tupleBox H).card:ℝ) ≤ 128^r * ∏ i, H i := by
  simp only [tupleBox,Fintype.card_piFinset,Nat.cast_prod]
  calc
    (∏ i, ((idealBall (H i)).card:ℝ)) ≤ ∏ i, 128*H i :=
      Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _) (fun i _ => idealBall_card _ (hH i))
    _ = _ := by rw [Finset.prod_mul_distrib]; simp

lemma profileProduct_mem_box {r : ℕ} (W : Fin r → ℝ → ℂ) (b q : Fin r → ℝ)
    (hq : ∀ i, 0<q i) (hzero : ∀ i, W i 0=0)
    (hs : ∀ i x, W i x ≠ 0 → x ≤ b i)
    (v : Fin r → Ideal O) (hv : profileProduct W q v ≠ 0) :
    v ∈ tupleBox (fun i => b i*q i) := by
  apply (mem_tupleBox _ _).mpr
  intro i
  have hw : W i ((Ideal.absNorm (v i):ℝ)/q i) ≠ 0 :=
    (Finset.prod_ne_zero_iff.mp hv) i (Finset.mem_univ i)
  refine ⟨?_,(div_le_iff₀ (hq i)).mp (hs i _ hw)⟩
  intro hz
  apply hw
  simp only [hz,map_zero,Nat.cast_zero,zero_div,hzero]

lemma profileProduct_norm_le {r : ℕ} (W : Fin r → ℝ → ℂ) (q B : Fin r → ℝ)
    (hW : ∀ i x, ‖W i x‖ ≤ B i) (v : Fin r → Ideal O) :
    ‖profileProduct W q v‖ ≤ ∏ i, B i := by
  rw [profileProduct,norm_prod]
  exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ => hW i _)

theorem profileProduct_mass {r : ℕ} (W : Fin r → ℝ → ℂ) (b q B : Fin r → ℝ)
    (hb : ∀ i, 0≤b i) (hq : ∀ i, 0<q i) (hB : ∀ i, 0≤B i)
    (hzero : ∀ i, W i 0=0) (hs : ∀ i x, W i x ≠ 0 → x≤b i)
    (hW : ∀ i x, ‖W i x‖≤B i) (S : Finset (Fin r → Ideal O)) :
    (∑ v ∈ S, ‖profileProduct W q v‖) ≤
      (∏ i, B i) * (128^r * ∏ i, b i*q i) := by
  let F := S.filter (fun v => profileProduct W q v ≠ 0)
  have hsum : (∑ v ∈ S, ‖profileProduct W q v‖) = ∑ v ∈ F, ‖profileProduct W q v‖ := by
    symm
    apply Finset.sum_filter_of_ne
    intro v _ hv
    exact norm_ne_zero_iff.mp hv
  have hsub : F ⊆ tupleBox (fun i => b i*q i) := by
    intro v hv
    exact profileProduct_mem_box W b q hq hzero hs v (Finset.mem_filter.mp hv).2
  have hcard : (F.card:ℝ) ≤ 128^r * ∏ i, b i*q i :=
    (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
      (tupleBox_card _ (fun i => mul_nonneg (hb i) (hq i).le))
  rw [hsum]
  calc
    _ ≤ ∑ _v ∈ F, ∏ i, B i := Finset.sum_le_sum (fun v _ => profileProduct_norm_le W q B hW v)
    _ = (F.card:ℝ)*(∏ i, B i) := by simp
    _ ≤ (128^r * ∏ i, b i*q i)*(∏ i, B i) :=
      mul_le_mul_of_nonneg_right hcard (Finset.prod_nonneg (fun i _ => hB i))
    _ = _ := by ring

lemma sourceProfiles_product {N : ℕ} (Wslot : Fin N → ℝ → ℂ) (W₁ W₂ : ℝ → ℂ)
    (P : Fin N → ℝ) (X₁ X₂ : ℝ) (B₁ B₂ : Ideal O) (v : Fin (N+2) → Ideal O) :
    profileProduct (sourceProfiles Wslot W₁ W₂) (sourceScales P X₁ X₂ B₁ B₂) v =
      (∏ j : Fin N, Wslot j ((Ideal.absNorm (v (j.castAdd 2)):ℝ)/P j)) *
      (W₁ ((Ideal.absNorm (B₁*v ⟨N,by omega⟩):ℝ)/X₁) *
       W₂ ((Ideal.absNorm (B₂*v ⟨N+1,by omega⟩):ℝ)/X₂)) := by
  simp only [profileProduct,Fin.prod_univ_add,sourceProfiles,sourceScales,
    Fin.append_left,Fin.append_right,Fin.prod_univ_two,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_fin_one,map_mul,Nat.cast_mul,div_div_eq_mul_div]
  have h₀ : Fin.natAdd N (0:Fin 2)=⟨N,by omega⟩ := by ext; simp
  have h₁ : Fin.natAdd N (1:Fin 2)=⟨N+1,by omega⟩ := by ext; simp
  rw [h₀,h₁]
  congr 2 <;> congr 1 <;> ring

lemma sourceBounds_product {N : ℕ} (b : Fin N → ℝ) (b₁ b₂ : ℝ) :
    (∏ i, sourceBounds b b₁ b₂ i) = (∏ j,b j)*b₁*b₂ := by
  simp only [sourceBounds,Fin.prod_univ_add,Fin.append_left,Fin.append_right,
    Fin.prod_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
  ring

lemma sourceScales_product {N : ℕ} (P : Fin N → ℝ) (X₁ X₂ : ℝ) (B₁ B₂ : Ideal O) :
    (∏ i, sourceScales P X₁ X₂ B₁ B₂ i) =
      (∏ j,P j)*(X₁*X₂)/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂) := by
  simp only [sourceScales,Fin.prod_univ_add,Fin.append_left,Fin.append_right,
    Fin.prod_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
  ring

lemma sourceBounds_nonneg {N : ℕ} (b : Fin N → ℝ) (b₁ b₂ : ℝ)
    (hb : ∀ j, 0≤b j) (hb₁ : 0≤b₁) (hb₂ : 0≤b₂) :
    ∀ i, 0≤ sourceBounds b b₁ b₂ i := by
  simp only [Fin.forall_fin_add,sourceBounds,Fin.append_left,Fin.append_right,Fin.forall_fin_two]
  exact ⟨hb,hb₁,hb₂⟩

lemma sourceScales_pos {N : ℕ} (P : Fin N → ℝ) (X₁ X₂ : ℝ) (B₁ B₂ : Ideal O)
    (hP : ∀ j, 0<P j) (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hB₁ : B₁≠0) (hB₂ : B₂≠0) :
    ∀ i, 0<sourceScales P X₁ X₂ B₁ B₂ i := by
  have hn₁ : (0:ℝ)<Ideal.absNorm B₁ := by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hB₁)
  have hn₂ : (0:ℝ)<Ideal.absNorm B₂ := by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hB₂)
  simp only [Fin.forall_fin_add,sourceScales,Fin.append_left,Fin.append_right,Fin.forall_fin_two]
  exact ⟨hP,div_pos hX₁ hn₁,div_pos hX₂ hn₂⟩

theorem originalCoefficient_factor (N : ℕ) (c : O) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (R : Ideal O) (t : ℝ) (ν : Fin N → Ideal O → ℂ)
    (Wslot : Fin N → ℝ → ℂ) (P : Fin N → ℝ) (W₁ W₂ : ℝ → ℂ)
    (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s : Ideal O) (v : Fin (N+2) → Ideal O) :
    originalCoefficient N c χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v =
      (∏ j,ν j (v (j.castAdd 2))) * idealWeight c χ R t (tupleProduct v) *
      (profileProduct (sourceProfiles Wslot W₁ W₂) (sourceScales P X₁ X₂ B₁ B₂) v -
       profileProduct (sourceProfiles Wslot W₁ W₂) (sourceScales P Y₁ Y₂ B₁ B₂) v) *
      (if s∣tupleProduct v then 1 else 0) := by
  rw [originalCoefficient,Finset.prod_mul_distrib,sourceProfiles_product,sourceProfiles_product]
  unfold idealRectangle
  ring

lemma sourcePool_nonzero {N : ℕ} (ν : Fin N → Ideal O → ℂ) (b P : Fin N → ℝ)
    (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) (v : Fin (N+2) → Ideal O)
    (hv : v ∈ sourcePool ν b P b₁ b₂ X₁ X₂ Y₁ Y₂ B₁ B₂) : tupleProduct v ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  rcases Finset.mem_union.mp (Finset.mem_filter.mp hv).1 with h|h <;>
    exact ((mem_tupleBox _ _).mp h i).1

theorem originalCoefficient_mem_sourcePool (N : ℕ) (c : O)
    (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (R : Ideal O) (t : ℝ)
    (ν : Fin N → Ideal O → ℂ) (Wslot : Fin N → ℝ → ℂ) (P b : Fin N → ℝ)
    (W₁ W₂ : ℝ → ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s : Ideal O)
    (hP : ∀ j, 0<P j) (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hY₁ : 0<Y₁) (hY₂ : 0<Y₂)
    (hB₁ : B₁≠0) (hB₂ : B₂≠0)
    (hzero : ∀ i, sourceProfiles Wslot W₁ W₂ i 0=0)
    (hs : ∀ i x, sourceProfiles Wslot W₁ W₂ i x≠0 → x≤ sourceBounds b b₁ b₂ i)
    (v : Fin (N+2) → Ideal O)
    (hv : originalCoefficient N c χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v ≠ 0) :
    v ∈ sourcePool ν b P b₁ b₂ X₁ X₂ Y₁ Y₂ B₁ B₂ := by
  rw [originalCoefficient_factor] at hv
  have hslots := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hv).1).1).1
  have hd := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hv).1).2
  apply Finset.mem_filter.mpr
  refine ⟨?_,fun j => (Finset.prod_ne_zero_iff.mp hslots) j (Finset.mem_univ j)⟩
  apply Finset.mem_union.mpr
  by_cases hx : profileProduct (sourceProfiles Wslot W₁ W₂) (sourceScales P X₁ X₂ B₁ B₂) v = 0
  · apply Or.inr
    have hy : profileProduct (sourceProfiles Wslot W₁ W₂) (sourceScales P Y₁ Y₂ B₁ B₂) v ≠ 0 := by
      intro hy; exact hd (by rw [hx,hy,sub_self])
    exact profileProduct_mem_box _ _ _ (sourceScales_pos _ _ _ _ _ hP hY₁ hY₂ hB₁ hB₂) hzero hs v hy
  · exact Or.inl (profileProduct_mem_box _ _ _ (sourceScales_pos _ _ _ _ _ hP hX₁ hX₂ hB₁ hB₂) hzero hs v hx)

lemma source_coordinate_product {N : ℕ} (b P : Fin N → ℝ)
    (b₁ b₂ X₁ X₂ T : ℝ) (B₁ B₂ : Ideal O) (hT : X₁*X₂=T) :
    (∏ i,sourceBounds b b₁ b₂ i*sourceScales P X₁ X₂ B₁ B₂ i) =
      sourceRadius b P b₁ b₂ T B₁ B₂ := by
  rw [Finset.prod_mul_distrib,sourceBounds_product,sourceScales_product,hT]
  unfold sourceRadius
  ring

lemma tupleBox_product_bound {r : ℕ} (H : Fin r → ℝ) (v : Fin r → Ideal O)
    (hv : v ∈ tupleBox H) : (Ideal.absNorm (tupleProduct v):ℝ) ≤ ∏ i,H i := by
  simp only [tupleProduct,map_prod,Nat.cast_prod]
  exact Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _)
    (fun i _ => ((mem_tupleBox H v).mp hv i).2)

theorem sourcePool_product_bound {N : ℕ} (ν : Fin N → Ideal O → ℂ) (b P : Fin N → ℝ)
    (b₁ b₂ X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ : Ideal O)
    (hX : X₁*X₂=T) (hY : Y₁*Y₂=T) (v : Fin (N+2) → Ideal O)
    (hv : v ∈ sourcePool ν b P b₁ b₂ X₁ X₂ Y₁ Y₂ B₁ B₂) :
    (Ideal.absNorm (tupleProduct v):ℝ) ≤ sourceRadius b P b₁ b₂ T B₁ B₂ := by
  rcases Finset.mem_union.mp (Finset.mem_filter.mp hv).1 with hx|hy
  · exact (tupleBox_product_bound _ v hx).trans_eq (source_coordinate_product b P b₁ b₂ X₁ X₂ T B₁ B₂ hX)
  · exact (tupleBox_product_bound _ v hy).trans_eq (source_coordinate_product b P b₁ b₂ Y₁ Y₂ T B₁ B₂ hY)

theorem originalCoefficient_profile_norm_le (N : ℕ) (c : O) (hc : c≠0)
    (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (R : Ideal O) (t : ℝ)
    (ν : Fin N → Ideal O → ℂ) (hν : ∀ j I, ‖ν j I‖≤1)
    (Wslot : Fin N → ℝ → ℂ) (P : Fin N → ℝ) (W₁ W₂ : ℝ → ℂ)
    (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s : Ideal O) (v : Fin (N+2) → Ideal O)
    (hv : tupleProduct v≠0) :
    ‖originalCoefficient N c χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v‖ ≤
      ‖profileProduct (sourceProfiles Wslot W₁ W₂) (sourceScales P X₁ X₂ B₁ B₂) v‖+
      ‖profileProduct (sourceProfiles Wslot W₁ W₂) (sourceScales P Y₁ Y₂ B₁ B₂) v‖ := by
  have hn : ‖∏ j,ν j (v (j.castAdd 2))‖≤1 := by
    rw [norm_prod]
    exact Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun j _ => hν j _)
  have hw := idealWeight_norm_le_one c hc χ R t (tupleProduct v) hv
  rw [originalCoefficient_factor,norm_mul,norm_mul,norm_mul]
  have hm : ‖(if s∣tupleProduct v then 1 else 0 : ℂ)‖≤1 := by split_ifs <;> norm_num
  have hnw : ‖∏ j,ν j (v (j.castAdd 2))‖*‖idealWeight c χ R t (tupleProduct v)‖≤1 := by
    simpa only [one_mul] using mul_le_mul hn hw (norm_nonneg _) zero_le_one
  calc
    _ ≤ (1*‖profileProduct (sourceProfiles Wslot W₁ W₂) (sourceScales P X₁ X₂ B₁ B₂) v-
        profileProduct (sourceProfiles Wslot W₁ W₂) (sourceScales P Y₁ Y₂ B₁ B₂) v‖)*1 :=
      mul_le_mul (mul_le_mul_of_nonneg_right hnw (norm_nonneg _)) hm (norm_nonneg _) (by positivity)
    _ ≤ _ := by
      simpa only [one_mul,mul_one] using norm_sub_le
        (profileProduct (sourceProfiles Wslot W₁ W₂) (sourceScales P X₁ X₂ B₁ B₂) v)
        (profileProduct (sourceProfiles Wslot W₁ W₂) (sourceScales P Y₁ Y₂ B₁ B₂) v)

theorem originalCoefficient_mass (N : ℕ) (c : O) (hc : c≠0)
    (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (R : Ideal O) (t : ℝ)
    (ν : Fin N → Ideal O → ℂ) (hν : ∀ j I, ‖ν j I‖≤1)
    (Wslot : Fin N → ℝ → ℂ) (P b D : Fin N → ℝ) (W₁ W₂ : ℝ → ℂ)
    (b₁ b₂ D₁ D₂ X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ s : Ideal O)
    (hb : ∀ j, 0≤b j) (hb₁ : 0≤b₁) (hb₂ : 0≤b₂)
    (hD : ∀ j, 0≤D j) (hD₁ : 0≤D₁) (hD₂ : 0≤D₂)
    (hP : ∀ j, 0<P j) (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hY₁ : 0<Y₁) (hY₂ : 0<Y₂)
    (hB₁ : B₁≠0) (hB₂ : B₂≠0) (hX : X₁*X₂=T) (hY : Y₁*Y₂=T)
    (hzero : ∀ i, sourceProfiles Wslot W₁ W₂ i 0=0)
    (hs : ∀ i x, sourceProfiles Wslot W₁ W₂ i x≠0 → x≤ sourceBounds b b₁ b₂ i)
    (hW : ∀ i x, ‖sourceProfiles Wslot W₁ W₂ i x‖≤ sourceBounds D D₁ D₂ i)
    (S : Finset (Fin (N+2) → Ideal O)) :
    (∑ v ∈ S, ‖originalCoefficient N c χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v‖) ≤
      sourceMassConstant b D b₁ b₂ D₁ D₂ *
        (T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j,P j) := by
  have hpoint (v : Fin (N+2) → Ideal O) :
      ‖originalCoefficient N c χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v‖ ≤
        ‖profileProduct (sourceProfiles Wslot W₁ W₂) (sourceScales P X₁ X₂ B₁ B₂) v‖+
        ‖profileProduct (sourceProfiles Wslot W₁ W₂) (sourceScales P Y₁ Y₂ B₁ B₂) v‖ := by
    by_cases hv : originalCoefficient N c χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v=0
    · rw [hv,norm_zero]; positivity
    · have hm := originalCoefficient_mem_sourcePool N c χ R t ν Wslot P b W₁ W₂ b₁ b₂
        X₁ X₂ Y₁ Y₂ B₁ B₂ s hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hzero hs v hv
      exact originalCoefficient_profile_norm_le N c hc χ R t ν hν Wslot P W₁ W₂
        X₁ X₂ Y₁ Y₂ B₁ B₂ s v (sourcePool_nonzero _ _ _ _ _ _ _ _ _ _ _ v hm)
  have hx := profileProduct_mass (sourceProfiles Wslot W₁ W₂) (sourceBounds b b₁ b₂)
    (sourceScales P X₁ X₂ B₁ B₂) (sourceBounds D D₁ D₂)
    (sourceBounds_nonneg b b₁ b₂ hb hb₁ hb₂) (sourceScales_pos _ _ _ _ _ hP hX₁ hX₂ hB₁ hB₂)
    (sourceBounds_nonneg D D₁ D₂ hD hD₁ hD₂) hzero hs hW S
  have hy := profileProduct_mass (sourceProfiles Wslot W₁ W₂) (sourceBounds b b₁ b₂)
    (sourceScales P Y₁ Y₂ B₁ B₂) (sourceBounds D D₁ D₂)
    (sourceBounds_nonneg b b₁ b₂ hb hb₁ hb₂) (sourceScales_pos _ _ _ _ _ hP hY₁ hY₂ hB₁ hB₂)
    (sourceBounds_nonneg D D₁ D₂ hD hD₁ hD₂) hzero hs hW S
  rw [source_coordinate_product b P b₁ b₂ X₁ X₂ T B₁ B₂ hX,sourceBounds_product] at hx
  rw [source_coordinate_product b P b₁ b₂ Y₁ Y₂ T B₁ B₂ hY,sourceBounds_product] at hy
  calc
    _ ≤ ∑ v ∈ S, (‖profileProduct (sourceProfiles Wslot W₁ W₂) (sourceScales P X₁ X₂ B₁ B₂) v‖+
        ‖profileProduct (sourceProfiles Wslot W₁ W₂) (sourceScales P Y₁ Y₂ B₁ B₂) v‖) :=
      Finset.sum_le_sum (fun v _ => hpoint v)
    _ ≤ _ := by
      rw [Finset.sum_add_distrib]
      exact (add_le_add hx hy).trans_eq (by unfold sourceRadius sourceMassConstant; ring)

theorem originalCoefficient_product_bound (N : ℕ) (c : O)
    (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (R : Ideal O) (t : ℝ)
    (ν : Fin N → Ideal O → ℂ) (Wslot : Fin N → ℝ → ℂ) (P b : Fin N → ℝ)
    (W₁ W₂ : ℝ → ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ s : Ideal O)
    (hP : ∀ j, 0<P j) (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hY₁ : 0<Y₁) (hY₂ : 0<Y₂)
    (hB₁ : B₁≠0) (hB₂ : B₂≠0) (hX : X₁*X₂=T) (hY : Y₁*Y₂=T)
    (hzero : ∀ i, sourceProfiles Wslot W₁ W₂ i 0=0)
    (hs : ∀ i x, sourceProfiles Wslot W₁ W₂ i x≠0 → x≤ sourceBounds b b₁ b₂ i)
    (v : Fin (N+2) → Ideal O)
    (hv : originalCoefficient N c χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v≠0) :
    tupleProduct v≠0 ∧ (Ideal.absNorm (tupleProduct v):ℝ)≤ sourceRadius b P b₁ b₂ T B₁ B₂ := by
  have hm := originalCoefficient_mem_sourcePool N c χ R t ν Wslot P b W₁ W₂ b₁ b₂
    X₁ X₂ Y₁ Y₂ B₁ B₂ s hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hzero hs v hv
  exact ⟨sourcePool_nonzero _ _ _ _ _ _ _ _ _ _ _ v hm,
    sourcePool_product_bound _ _ _ _ _ _ _ _ _ _ _ _ hX hY v hm⟩

open CenteredMomentAddedZeroUniform

lemma finiteColumnCoefficient_mass {ι : Type*} [Fintype ι] (S : Finset (Tuple ι))
    (β : Tuple ι → ℂ) :
    (∑ I ∈ finiteColumns S, ‖finiteColumnCoefficient S β I‖) ≤ ∑ v ∈ S, ‖β v‖ := by
  calc
    _ ≤ ∑ I ∈ finiteColumns S, ∑ v ∈ S.filter (fun v => finiteTupleProduct v=I), ‖β v‖ :=
      Finset.sum_le_sum (fun I _ => norm_sum_le _ _)
    _ = _ := Finset.sum_fiberwise_of_maps_to (fun v hv => Finset.mem_image.mpr ⟨v,hv,rfl⟩) _

lemma finite_original_mass_reindex {ι : Type*} [Fintype ι] {n : ℕ} (e : ι≃Fin n)
    (c : O) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (R : Ideal O) (t : ℝ)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s : Ideal O) (S : Finset (Tuple ι)) :
    (∑ v ∈ S.image (tupleEquiv e), ‖originalCoefficient n c χ R t
      (fun j => ν (e.symm j)) (fun j => Wslot (e.symm j)) (fun j => P (e.symm j))
      W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v‖) =
    ∑ v ∈ S, ‖originalFiniteCoefficient c χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v‖ := by
  rw [Finset.sum_image (fun v _ w _ he => (tupleEquiv e).injective he)]
  apply Finset.sum_congr rfl
  intro v hv
  rw [originalCoefficient_reindex]

end SevenEighths.CenteredMomentSourceMass

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SourceProfileMass
namespace OAI

noncomputable section
open scoped BigOperators Classical ContDiff

namespace SevenEighths.CenteredMomentSourceProfileMass
open ActualEisensteinCubic CenteredMomentPrimary CenteredMomentRectangle
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass
local notation "O" => ActualEisensteinCubic.O

 theorem primary_mod_one (χ : MulChar (O ⧸ Ideal.span {(1:O)}) ℂ) (I : Ideal O) :
    primaryIdealCharacter 1 χ I=1 := by
  rw [primaryIdealCharacter_apply]
  have he : Ideal.Quotient.mk (Ideal.span {(1:O)}) (CompletedGauss.primaryGenerator I)=1 := by
    rw [← map_one (Ideal.Quotient.mk (Ideal.span {(1:O)}))]
    apply Ideal.Quotient.eq.mpr
    rw [Ideal.span_singleton_one]
    trivial
  rw [he,map_one]

 theorem idealWeight_mod_one (χ : MulChar (O ⧸ Ideal.span {(1:O)}) ℂ) (R I : Ideal O) :
    CenteredMomentRectangle.idealWeight 1 χ R 0 I=(if IsCoprime I R then 1 else 0) := by
  simp only [idealWeight,primary_mod_one,Complex.ofReal_zero,mul_zero,Complex.cpow_zero,mul_one]

 theorem profileCoefficient_eq_original {ι : Type*} [Fintype ι]
    (R : Ideal O) (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s : Ideal O) (v : Tuple ι) :
    profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v=
      originalFiniteCoefficient 1 (1 : MulChar (O ⧸ Ideal.span {(1:O)}) ℂ) R 0
        ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v := by
  rw [originalFiniteCoefficient,idealWeight_mod_one]
  rfl

end SevenEighths.CenteredMomentSourceProfileMass

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondHeightFamily
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondHeightFamily
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentSourceRow CenteredMomentHeckeColumnWindow CenteredMomentHeckeExpansion
open CenteredMomentChildRows CenteredMomentChildAssembly
open CenteredMomentSecondScaled RayFourExpansion ConcretePrimeRowBridge ActualEisensteinCubic
local notation "O" => ActualEisensteinCubic.O

theorem fixedBadMask_coprime (n : O) (hn : Supported (Ideal.span {n})) :
    IsCoprime fixedBadMask n := by
  have hl := PrimaryIdealUnitReindex.lambda_prime_actual.irreducible.coprime_iff_not_dvd.mpr
    ((supported_span_iff n).mp hn).1
  have h2 := negative_two_prime.irreducible.coprime_iff_not_dvd.mpr
    (by simpa only [neg_dvd] using ((supported_span_iff n).mp hn).2)
  have htwo : IsCoprime (2:O) n := h2.of_isCoprime_of_dvd_left ⟨-1,by ring⟩
  exact hl.mul_left htwo

theorem heightCoeff_eq_fixed_rowWeight (τ : Character) (t : ℝ)
    (I : Ideal O) (hI : Supported I) :
    heightCoeff τ t I=rowWeight τ fixedBadMask 1 1 t I := by
  have hc : IsCoprime (Ideal.span {fixedBadMask}) I := by
    rw [←primary_span_supported I hI,Ideal.isCoprime_span_singleton_iff]
    exact fixedBadMask_coprime _ ((supported_span_primaryGenerator_iff I).mpr hI)
  have hs := idealRowHom_sixth_mask fixedBadMask I hI
  rw [if_pos hc.symm] at hs
  change idealCoeff τ I*(Ideal.absNorm I:ℂ)^(Complex.I*t)=
    ((idealCoeff τ I*idealRowHom (fixedBadMask^6*(1*1)) I)*(Ideal.absNorm I:ℂ)^(Complex.I*t))
  simp only [mul_one,hs]

end SevenEighths.CenteredMomentSecondHeightFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SectorLocalization
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentSectorLocalization
open CubicEisenstein ConcreteTraceCRT EisensteinSchwartzPoisson CenteredMomentCommonSupport CenteredMomentCorrelation CenteredMomentFourier
local notation "O" => ActualEisensteinCubic.O

theorem cutoff_bounds (x : ℝ) : 0 ≤ cutoff x ∧ cutoff x ≤ 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

theorem cutoff_antitone : Antitone cutoff := by
  intro x y hxy
  exact Real.smoothTransition.monotone (by linarith)

theorem annulus_bounds (x : ℝ) : 0 ≤ annulus x ∧ annulus x ≤ 1 := by
  by_cases hx : x ≤ 1/4
  · rw [annulus_zero_low x hx]; constructor <;> norm_num
  have hm := cutoff_antitone (show x ≤ 2*x by linarith)
  have h₁ := cutoff_bounds x
  have h₂ := cutoff_bounds (2*x)
  unfold annulus
  constructor <;> linarith

theorem dyadicScale_add (n : ℤ) : dyadicScale (n+1)=2*dyadicScale n := by
  simp only [dyadicScale,zpow_add₀ (by norm_num : (2:ℝ) ≠ 0),zpow_one]
  ring

theorem dyadicWeight_bounds (n : ℤ) (q : ℝ) :
    0 ≤ dyadicWeight n q ∧ dyadicWeight n q ≤ 1 := annulus_bounds _

theorem dyadicWeight_outside_pair (q : ℝ) (k : ℤ)
    (hlo : dyadicScale k ≤ q) (hhi : q < dyadicScale (k+1))
    (n : ℤ) (hn : n ∉ ({k+1,k+2} : Finset ℤ)) : dyadicWeight n q=0 := by
  have hn₁ : n ≠ k+1 := by simpa using fun h => hn (by simp [h])
  have hn₂ : n ≠ k+2 := by simpa using fun h => hn (by simp [h])
  by_cases hnk : n ≤ k
  · exact dyadicWeight_zero_high n q ((zpow_le_zpow_right₀ (by norm_num : (1:ℝ) ≤ 2) hnk).trans hlo)
  · have hkn : k+3 ≤ n := by omega
    have hmono : dyadicScale (k+3) ≤ dyadicScale n :=
      zpow_le_zpow_right₀ (by norm_num : (1:ℝ) ≤ 2) hkn
    have he : dyadicScale (k+3)=4*dyadicScale (k+1) := by
      rw [show k+3=(k+1)+1+1 by omega,dyadicScale_add,dyadicScale_add]
      ring
    apply dyadicWeight_zero_low
    rw [he] at hmono
    linarith

theorem dyadicWeight_finite (q : ℝ) : (Function.support (fun n => dyadicWeight n q)).Finite := by
  by_cases hq : 0 < q
  · obtain ⟨k,hlo,hhi⟩ := exists_mem_Ico_zpow hq (by norm_num : (1:ℝ) < 2)
    apply (Set.toFinite (({k+1,k+2} : Finset ℤ) : Set ℤ)).subset
    intro n hn
    by_contra hh
    exact hn (dyadicWeight_outside_pair q k hlo hhi n hh)
  · have hz : ∀ n,dyadicWeight n q=0 := fun n =>
      dyadicWeight_zero_low n q ((le_of_not_gt hq).trans (div_nonneg (dyadicScale_pos n).le (by norm_num)))
    simp [hz]

theorem dyadicWeight_summable (q : ℝ) : Summable (fun n => dyadicWeight n q) :=
  summable_of_hasFiniteSupport (dyadicWeight_finite q)

theorem dyadicWeight_partition (q : ℝ) (hq : 0 < q) : ∑' n,dyadicWeight n q=1 := by
  obtain ⟨k,hlo,hhi⟩ := exists_mem_Ico_zpow hq (by norm_num : (1:ℝ) < 2)
  rw [tsum_eq_sum (s := {k+1,k+2}) (dyadicWeight_outside_pair q k hlo hhi)]
  change dyadicScale k ≤ q at hlo
  change q < dyadicScale (k+1) at hhi
  have hk : k+1 ≠ k+2 := by omega
  rw [Finset.sum_pair hk]
  simp only [dyadicWeight,annulus]
  have h₁ : 2*(q/dyadicScale (k+1))=q/dyadicScale k := by
    rw [dyadicScale_add]; field_simp
  have h₂ : 2*(q/dyadicScale (k+2))=q/dyadicScale (k+1) := by
    rw [show k+2=(k+1)+1 by omega,dyadicScale_add]; field_simp
  rw [h₁,h₂,cutoff_zero _ ((le_div_iff₀ (dyadicScale_pos k)).mpr (by simpa using hlo))]
  have hs : q/dyadicScale (k+2) ≤ 1/2 := by
    apply (div_le_iff₀ (dyadicScale_pos (k+2))).mpr
    rw [show k+2=(k+1)+1 by omega,dyadicScale_add]
    linarith
  rw [cutoff_one _ hs]
  ring

theorem retained_summable (R q : ℝ) :
    Summable (fun n : ℤ => if Retained R n then dyadicWeight n q else 0) :=
  (dyadicWeight_summable q).indicator {n | Retained R n}

theorem discarded_summable (R q : ℝ) :
    Summable (fun n : ℤ => if Retained R n then 0 else dyadicWeight n q) := by
  have h := (dyadicWeight_summable q).sub (retained_summable R q)
  convert (preTransparency := .instances) h using 1
  ext n
  split_ifs <;> simp

theorem retained_add_discarded (R q : ℝ) (hq : 0 < q) :
    retainedWeight R q+discardedWeight R q=1 := by
  rw [retainedWeight,discardedWeight,← (retained_summable R q).tsum_add (discarded_summable R q)]
  convert (preTransparency := .instances) dyadicWeight_partition q hq using 1
  apply tsum_congr
  intro n
  split_ifs <;> simp

theorem dyadicWeight_zero_nonpos (n : ℤ) (q : ℝ) (hq : q ≤ 0) : dyadicWeight n q=0 :=
  dyadicWeight_zero_low n q (hq.trans (div_nonneg (dyadicScale_pos n).le (by norm_num)))

theorem discardedWeight_zero_nonpos (R q : ℝ) (hq : q ≤ 0) : discardedWeight R q=0 := by
  simp [discardedWeight,dyadicWeight_zero_nonpos _ q hq]

theorem retainedWeight_nonneg (R q : ℝ) : 0 ≤ retainedWeight R q := by
  apply tsum_nonneg
  intro n
  split_ifs
  · exact (dyadicWeight_bounds n q).1
  · exact le_rfl

theorem discardedWeight_nonneg (R q : ℝ) : 0 ≤ discardedWeight R q := by
  apply tsum_nonneg
  intro n
  split_ifs
  · exact le_rfl
  · exact (dyadicWeight_bounds n q).1

theorem discardedWeight_bounds (R q : ℝ) : 0 ≤ discardedWeight R q ∧ discardedWeight R q ≤ 1 := by
  refine ⟨discardedWeight_nonneg R q,?_⟩
  by_cases hq : 0 < q
  · have hp := retained_add_discarded R q hq
    have hd := retainedWeight_nonneg R q
    linarith
  · rw [discardedWeight_zero_nonpos R q (le_of_not_gt hq)]; norm_num

theorem discardedWeight_zero_below (R q : ℝ) (hq : q ≤ R) : discardedWeight R q=0 := by
  by_cases hp : 0 < q
  · unfold discardedWeight
    trans ∑' _n : ℤ, (0:ℝ)
    · apply tsum_congr
      intro n
      split_ifs with hn
      · rfl
      · by_contra hne
        exact hn ⟨q,hp,hq,subset_tsupport _ hne⟩
    · exact tsum_zero
  · exact discardedWeight_zero_nonpos R q (le_of_not_gt hp)

theorem discardedWeight_support (R q : ℝ) (hq : discardedWeight R q ≠ 0) : R < q :=
  lt_of_not_ge (fun h => hq (discardedWeight_zero_below R q h))

theorem kernelReference_pos (Tsec H : ℝ) (hT : 0 < Tsec) : 0 < kernelReference Tsec H :=
  div_pos (Real.exp_pos _) hT

theorem discarded_kernel_argument (Tsec Z Csec H ξ q : ℝ)
    (hT : 0 < Tsec) (hZ : 1 < Z) (hC : 1 ≤ Csec)
    (hthreshold : 2*H/Real.log Z+Real.log (4*Csec)/Real.log Z < ξ/4)
    (hne : discardedWeight (frequencyRadius Tsec Z ξ) q ≠ 0) :
    Z^(ξ/4) ≤ kernelReference Tsec H*q := by
  have hlog := Real.log_nonneg (show 1 ≤ 4*Csec by linarith)
  have hlogdiv := div_nonneg hlog (Real.log_pos hZ).le
  have he : 2*H < ξ/4*Real.log Z :=
    (div_lt_iff₀ (Real.log_pos hZ)).mp (by linarith : 2*H/Real.log Z < ξ/4)
  have hs : Z^(ξ/4) ≤ Real.exp (-2*H)*Z^(ξ/2) := by
    rw [Real.rpow_def_of_pos (zero_lt_one.trans hZ),Real.rpow_def_of_pos (zero_lt_one.trans hZ),← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith
  have hq := (discardedWeight_support _ q hne).le
  have hm := mul_le_mul_of_nonneg_left hq (kernelReference_pos Tsec H hT).le
  have hid : kernelReference Tsec H*frequencyRadius Tsec Z ξ=Real.exp (-2*H)*Z^(ξ/2) := by
    unfold kernelReference frequencyRadius
    field_simp
  rw [hid] at hm
  exact hs.trans hm

theorem actual_discarded_lattice_tail (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(ℝ,ℂ)) (Tsec Z Csec H ξ K B : ℝ),
      0 < Tsec → 1 < Z → 1 ≤ Csec →
      (2*H/Real.log Z+Real.log (4*Csec)/Real.log Z < ξ/4) →
      kernelReference Tsec H ≤ K → 0 ≤ B →
      ∀ c : O → ℂ, (∀ h, ‖c h‖ ≤ B) →
      ‖∑' h : O,(discardedWeight (frequencyRadius Tsec Z ξ) (normValue h):ℂ)*c h*
        paperRadialFourier W (K*normValue h)‖ ≤
      B*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
        ((min 1 (kernelReference Tsec H))^2*(1+Z^(ξ/4))^A) := by
  obtain ⟨s,C,hC,ht⟩ := CenteredMomentTail.uniform_sector_lattice_tail A
  refine ⟨s,C,hC,?_⟩
  intro W Tsec Z Csec H ξ K B hT hZ hCsec hthreshold hK hB c hc
  let D : Set O := {h | discardedWeight (frequencyRadius Tsec Z ξ) (normValue h) ≠ 0}
  have hb := ht W D (kernelReference Tsec H) (Z^(ξ/4)) B
    (kernelReference_pos Tsec H hT) (Real.rpow_nonneg (zero_lt_one.trans hZ).le _) hB
    (fun h hh => by
      rw [← normValue_eq_embedding]
      exact discarded_kernel_argument Tsec Z Csec H ξ (normValue h) hT hZ hCsec hthreshold hh)
    K hK c (fun h => (discardedWeight (frequencyRadius Tsec Z ξ) (normValue h):ℂ))
    (fun h _ => hc h) (fun h _ => by
      rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (discardedWeight_nonneg _ _)]
      exact (discardedWeight_bounds _ _).2)
  simp_rw [← normValue_eq_embedding] at hb
  have he := tsum_subtype_eq_of_support_subset (f := fun h : O =>
    (discardedWeight (frequencyRadius Tsec Z ξ) (normValue h):ℂ)*c h*paperRadialFourier W (K*normValue h))
    (s := D) (by
      intro h hh
      change discardedWeight (frequencyRadius Tsec Z ξ) (normValue h) ≠ 0
      intro hz
      exact hh (by simp [hz]))
  rwa [he] at hb

theorem actual_discarded_second_tail (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(ℝ,ℂ)) (Tsec Z Csec H ξ K : ℝ),
      0 < Tsec → 1 < Z → 1 ≤ Csec →
      (2*H/Real.log Z+Real.log (4*Csec)/Real.log Z < ξ/4) →
      kernelReference Tsec H ≤ K →
      ∀ (u v : O) (hu : CanonicalQuadraticSieve.Supported (Ideal.span {u}))
        (hv : CanonicalQuadraticSieve.Supported (Ideal.span {v})),
      ‖∑' h : O,(discardedWeight (frequencyRadius Tsec Z ξ) (normValue h):ℂ)*
        CenteredMomentSupportedCorrelation.actualCorrelation u v hu hv (-h)*
        paperRadialFourier W (K*normValue h)‖ ≤
      (normValue u*normValue v)*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
        ((min 1 (kernelReference Tsec H))^2*(1+Z^(ξ/4))^A) := by
  obtain ⟨s,C,hC,ht⟩ := actual_discarded_lattice_tail A
  refine ⟨s,C,hC,?_⟩
  intro W Tsec Z Csec H ξ K hT hZ hCsec hthreshold hK u v hu hv
  exact ht W Tsec Z Csec H ξ K (normValue u*normValue v) hT hZ hCsec hthreshold hK
    (by unfold normValue; positivity) _ (fun h => CenteredMomentTail.actualCorrelation_norm_le u v hu hv (-h))

end SevenEighths.CenteredMomentSectorLocalization

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FirstTailAggregate
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentFirstTailAggregate
open ActualEisensteinCubic HeckeFamily CanonicalRowCompletion CanonicalQuadraticSieve
open CenteredMomentFirstDiscardedEnergy CenteredMomentFirstScale CenteredMomentSectorLocalization
open CenteredMomentSourceRow CenteredMomentHeckeExpansion CenteredMomentTwist
local notation "O" => ActualEisensteinCubic.O

theorem rowWeight_norm_le_one (η : Character) (m A z : O) (t : ℝ)
    (I : Ideal O) (hI : I≠0) : ‖rowWeight η m A z t I‖≤1 := by
  have hp := norm_real_imaginary_power (Ideal.absNorm I:ℝ) t (norm_pos I hI)
  norm_cast at hp
  change ‖(idealCoeff η I*idealRowHom (m^6*(A*z)) I)*(Ideal.absNorm I:ℂ)^(Complex.I*t)‖≤1
  rw [norm_mul,norm_mul,hp,mul_one]
  exact (mul_le_of_le_one_left (norm_nonneg _)
    (idealCoeff_norm_le_one η I)).trans (idealRowHom_norm _ _)

end SevenEighths.CenteredMomentFirstTailAggregate

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.ExceptionalAmplitudePair
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentExceptionalAmplitudePair
open HeckeFamily CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentAllocatedDetectorAmplitude CenteredMomentDetectorDictionary
open CenteredMomentExceptionalAllocationShell ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O
universe u

lemma volume_pos {ι:Type u} [Fintype ι] (s:Data ι):0<volume s:=
  mul_pos (mul_pos s.X₁_pos s.X₂_pos) (Finset.prod_pos (fun i _=>s.P_pos i))

end SevenEighths.CenteredMomentExceptionalAmplitudePair

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.NaturalRadialCutoff
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentNaturalRadialCutoff
open HeckeFamily ConcreteTraceCRT CenteredMomentNaturalRowSource
open CenteredMomentOriginalRadialComparison
local notation "O" => HeckeFamily.O

lemma reciprocal_cutoff_bound (Z xi:ℝ) (order:ℕ) (hZ:0<Z) :
    ((1+Z^xi)^order)⁻¹≤Z^(-xi*(order:ℝ)) := by
  have hp : (Z^xi)^order≤(1+Z^xi)^order:=
    pow_le_pow_left₀ (Real.rpow_nonneg hZ.le _) (by linarith) order
  have hh:=inv_anti₀ (pow_pos (Real.rpow_pos_of_pos hZ _) _) hp
  have he : (Z^xi)^order=Z^(xi*(order:ℝ)) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hZ.le]
  apply hh.trans_eq
  rw [he,←Real.rpow_neg hZ.le]
  congr 1
  ring

end SevenEighths.CenteredMomentNaturalRadialCutoff

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SupportedZeroEnergy
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSupportedZeroEnergy
open ActualEisensteinCubic ConcreteTraceCRT CanonicalQuadraticSieve CanonicalRowCompletion IdealMobiusDivisorSum
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass CenteredMomentZeroMode
open CenteredMomentSourceRow CenteredMomentHeckeExpansion CenteredMomentFirstLocalization
open CenteredMomentZeroMeanBridge EisensteinSchwartzPoisson HeckeFamily
local notation "O" => ActualEisensteinCubic.O

theorem finiteColumnCoefficient_witness {ι : Type*} [Fintype ι]
    (S : Finset (Tuple ι)) (β : Tuple ι → ℂ) (I : Ideal O)
    (hI : finiteColumnCoefficient S β I≠0) :
    ∃ v∈S, β v≠0 ∧ finiteTupleProduct v=I := by
  obtain ⟨v,hv,hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hI
  exact ⟨v,(Finset.mem_filter.mp hv).1,hne,(Finset.mem_filter.mp hv).2⟩

theorem finite_tuple_fiber_card {ι : Type*} [Fintype ι]
    (S : Finset (Tuple ι)) (I : Ideal O) (hI : I≠0) :
    (S.filter (fun v => finiteTupleProduct v=I)).card ≤
      (idealDivisors I).card^(Fintype.card ι+2) := by
  let T := S.filter (fun v => finiteTupleProduct v=I)
  let f (v : T) : (ι ⊕ Fin 2) → idealDivisors I := fun i => ⟨v.val i,by
    apply (mem_idealDivisors hI).mpr
    rw [← (Finset.mem_filter.mp v.property).2]
    exact Finset.dvd_prod_of_mem v.val (Finset.mem_univ i)⟩
  have hf : Function.Injective f := by
    intro v w he
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val (congrFun he i)
  simpa only [Fintype.card_coe,Fintype.card_fun,Fintype.card_sum,Fintype.card_fin,T]
    using Fintype.card_le_of_injective f hf

theorem finiteColumnCoefficient_norm_le {ι : Type*} [Fintype ι]
    (S : Finset (Tuple ι)) (β : Tuple ι → ℂ) (B : ℝ) (hB : 0≤B)
    (hβ : ∀ v∈S, finiteTupleProduct v≠0 → ‖β v‖≤B) (I : Ideal O) (hI : I≠0) :
    ‖finiteColumnCoefficient S β I‖ ≤ B*((idealDivisors I).card:ℝ)^(Fintype.card ι+2) := by
  calc
    _ ≤ ∑ v∈S.filter (fun v => finiteTupleProduct v=I),‖β v‖ := norm_sum_le _ _
    _ ≤ ∑ _v∈S.filter (fun v => finiteTupleProduct v=I),B := by
      apply Finset.sum_le_sum
      intro v hv
      exact hβ v (Finset.mem_filter.mp hv).1 ((Finset.mem_filter.mp hv).2 ▸ hI)
    _ = B*((S.filter (fun v => finiteTupleProduct v=I)).card:ℝ) := by simp; ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ hB
      exact_mod_cast finite_tuple_fiber_card S I hI

end SevenEighths.CenteredMomentSupportedZeroEnergy

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SourceZeroEnergy
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentSourceZeroEnergy
open ActualEisensteinCubic HeckeFamily CenteredMomentRectangle
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass
open CenteredMomentSourceProfileMass CenteredMomentSupportedZeroEnergy
open CenteredMomentFirstLocalization CenteredMomentSourceRow
open EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O

theorem profileCoefficient_norm_le {ι : Type*} [Fintype ι]
    (R : Ideal O) (ν : ι → Ideal O → ℂ) (hν : ∀ j I,‖ν j I‖≤1)
    (Wslot : ι → ℝ → ℂ) (P D : ι → ℝ) (W₁ W₂ : ℝ → ℂ) (D₁ D₂ : ℝ)
    (hD : ∀ j,0≤D j) (hD₁ : 0≤D₁) (hD₂ : 0≤D₂)
    (hslot : ∀ j x,‖Wslot j x‖≤D j)
    (h₁ : ∀ x,‖W₁ x‖≤D₁) (h₂ : ∀ x,‖W₂ x‖≤D₂)
    (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s : Ideal O) (v : Tuple ι) :
    ‖profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v‖≤
      2*D₁*D₂*(∏ j,D j) := by
  have hp : ‖∏ j,ν j (v (Sum.inl j))*Wslot j ((Ideal.absNorm (v (Sum.inl j)):ℝ)/P j)‖≤∏ j,D j := by
    rw [norm_prod]
    apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
    intro j _
    rw [norm_mul]
    simpa only [one_mul] using mul_le_mul (hν j _) (hslot j _)
      (norm_nonneg _) zero_le_one
  have hr (I J : Ideal O) : ‖idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J‖≤2*D₁*D₂ := by
    unfold idealRectangle
    apply (norm_sub_le _ _).trans
    rw [norm_mul,norm_mul]
    have hx := mul_le_mul (h₁ ((Ideal.absNorm I:ℝ)/X₁))
      (h₂ ((Ideal.absNorm J:ℝ)/X₂)) (norm_nonneg _) hD₁
    have hy := mul_le_mul (h₁ ((Ideal.absNorm I:ℝ)/Y₁))
      (h₂ ((Ideal.absNorm J:ℝ)/Y₂)) (norm_nonneg _) hD₁
    linarith
  have hm (p : Prop) [Decidable p] : ‖(if p then 1 else 0 : ℂ)‖≤1 := by
    split_ifs <;> norm_num
  have hDp : 0≤∏ j,D j := Finset.prod_nonneg (fun j _ => hD j)
  unfold profileCoefficient
  rw [norm_mul,norm_mul,norm_mul]
  have h := mul_le_mul
    (mul_le_mul (mul_le_mul hp (hm (IsCoprime (finiteTupleProduct v) R)) (norm_nonneg _) (Finset.prod_nonneg (fun j _ => hD j)))
      (hr (B₁*v (Sum.inr 0)) (B₂*v (Sum.inr 1))) (norm_nonneg _) (by positivity))
    (hm (s∣finiteTupleProduct v)) (norm_nonneg _) (by positivity)
  simpa only [mul_one] using h.trans_eq (by ring)

theorem profileCoefficient_product_bound {ι : Type*} [Fintype ι]
    (R : Ideal O) (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ)
    (P b : ι → ℝ) (W₁ W₂ : ℝ → ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ T : ℝ)
    (B₁ B₂ s : Ideal O)
    (hP : ∀ j,0<P j) (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hY₁ : 0<Y₁) (hY₂ : 0<Y₂)
    (hB₁ : B₁≠0) (hB₂ : B₂≠0) (hX : X₁*X₂=T) (hY : Y₁*Y₂=T)
    (hz : ∀ j,Wslot j 0=0) (hz₁ : W₁ 0=0) (hz₂ : W₂ 0=0)
    (hs : ∀ j x,Wslot j x≠0 → x≤b j)
    (hs₁ : ∀ x,W₁ x≠0 → x≤b₁) (hs₂ : ∀ x,W₂ x≠0 → x≤b₂)
    (v : Tuple ι)
    (hv : profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v≠0) :
    finiteTupleProduct v≠0 ∧ (Ideal.absNorm (finiteTupleProduct v):ℝ)≤
      (∏ j,b j)*b₁*b₂*(T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j,P j) := by
  let e := Fintype.equivFin ι
  have hzero : ∀ i,sourceProfiles (fun j => Wslot (e.symm j)) W₁ W₂ i 0=0 := by
    simpa only [Fin.forall_fin_add,sourceProfiles,Fin.append_left,Fin.append_right,
      Fin.forall_fin_two,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
      using And.intro (fun j => hz (e.symm j)) (And.intro hz₁ hz₂)
  have hsup : ∀ i x,sourceProfiles (fun j => Wslot (e.symm j)) W₁ W₂ i x≠0 →
      x≤ sourceBounds (fun j => b (e.symm j)) b₁ b₂ i := by
    simpa only [Fin.forall_fin_add,sourceProfiles,sourceBounds,Fin.append_left,Fin.append_right,
      Fin.forall_fin_two,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
      using And.intro (fun j => hs (e.symm j)) (And.intro hs₁ hs₂)
  have hn : CenteredMomentAddedZero.originalCoefficient (Fintype.card ι) 1
      (1 : MulChar (O ⧸ Ideal.span {(1:O)}) ℂ) R 0
      (fun j => ν (e.symm j)) (fun j => Wslot (e.symm j)) (fun j => P (e.symm j))
      W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s (tupleEquiv e v)≠0 := by
    rw [originalCoefficient_reindex,←profileCoefficient_eq_original]
    exact hv
  have hh := originalCoefficient_product_bound (Fintype.card ι) 1
    (1 : MulChar (O ⧸ Ideal.span {(1:O)}) ℂ) R 0 (fun j => ν (e.symm j))
    (fun j => Wslot (e.symm j)) (fun j => P (e.symm j)) (fun j => b (e.symm j))
    W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ T B₁ B₂ s (fun j => hP (e.symm j))
    hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY hzero hsup (tupleEquiv e v) hn
  simpa only [tupleProduct_reindex,sourceRadius,e.symm.prod_comp] using hh

end SevenEighths.CenteredMomentSourceZeroEnergy

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SourceSecondZeroEnergy
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentSourceSecondZeroEnergy
open ActualEisensteinCubic HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentSourceZeroEnergy CenteredMomentSupportedZeroEnergy
open CenteredMomentSourceRow CenteredMomentHeckeColumnWindow CenteredMomentSecondDiagonal
local notation "O" => ActualEisensteinCubic.O

lemma heightCoeff_norm_le_one (η : Character) (t : ℝ) (I : Ideal O) (hI : I≠0) :
    ‖heightCoeff η t I‖≤1 := by
  have hn : (0:ℝ)<Ideal.absNorm I := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hp : ‖(Ideal.absNorm I:ℂ)^(Complex.I*t)‖=1 := by
    rw [show (Ideal.absNorm I:ℂ)=((Ideal.absNorm I:ℝ):ℂ) by simp,
      Complex.norm_cpow_eq_rpow_re_of_pos hn]
    simp
  rw [heightCoeff,norm_mul,hp,mul_one]
  exact idealCoeff_norm_le_one η I

theorem secondZeroEnergy_filter {α : Type*} (S : Finset α) (a : α→O)
    (ha : ∀ i,Supported (Ideal.span {a i})) (c : α→ℂ)
    (p : α→Prop) [DecidablePred p] (hc : ∀ i∈S,¬p i→c i=0) :
    secondZeroEnergy S a ha c=secondZeroEnergy (S.filter p) a ha c := by
  unfold secondZeroEnergy
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hpi : p i
  · rw [if_pos hpi]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hpj : p j
    · rw [if_pos hpj]
    · simp only [if_neg hpj,hc j hj hpj,star_zero,mul_zero,zero_mul]
  · simp only [if_neg hpi,hc i hi hpi,zero_mul,Finset.sum_const_zero]

lemma sourceGenerator_span (S : Finset (Ideal O)) (I : supportedColumns S) :
    Ideal.span {sourceGenerator S I}=(I:Ideal O) :=
  primary_span_supported I (Finset.mem_filter.mp I.property).2
lemma sourceGenerator_primary (S : Finset (Ideal O)) (I : supportedColumns S) :
    ConcretePrimeRowBridge.goodLambda^2∣sourceGenerator S I-1 :=
  (primaryGenerator_spec I (supported_primaryGenerator_ne_zero I (Finset.mem_filter.mp I.property).2)).2
lemma sourceGenerator_injective (S : Finset (Ideal O)) : Function.Injective (sourceGenerator S) := by
  intro I J h
  apply Subtype.ext
  rw [←sourceGenerator_span S I,←sourceGenerator_span S J,h]

theorem sourceSecondZero_divisor_bound (S : Finset (Ideal O)) (β : Ideal O→ℂ)
    (η : Character) (t B Y : ℝ) (hB : 0≤B) (hY : 0≤Y)
    (s : Ideal O) (hs : s≠0)
    (hc : ∀ I∈supportedColumns S,β I≠0→‖β I‖≤B)
    (hdiv : ∀ I∈supportedColumns S,β I≠0→s∣I)
    (hN : ∀ I∈supportedColumns S,β I≠0→(Ideal.absNorm I:ℝ)≤Y) :
    ‖sourceSecondZero S β η t‖≤128*B^2*Y/(Ideal.absNorm s:ℝ) := by
  let Q : Finset (supportedColumns S) := Finset.univ.filter (fun I => β I≠0)
  rw [sourceSecondZero,secondZeroEnergy_filter Finset.univ (sourceGenerator S)
    (sourceGenerator_supported S) (fun I => β I*heightCoeff η t I) (fun I => β I≠0)
      (by intro I _ h; simp only [not_not] at h; rw [h,zero_mul])]
  refine secondZeroEnergy_divisor_bound Q (sourceGenerator S) (sourceGenerator_supported S)
    (sourceGenerator_primary S) (sourceGenerator_injective S).injOn _ B hB ?_ s hs ?_ Y hY ?_
  · intro I hI
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (heightCoeff_norm_le_one η t I
      (Finset.mem_filter.mp I.property).2.1) (norm_nonneg _)).trans
      (by simpa only [mul_one] using hc I I.property (Finset.mem_filter.mp hI).2)
  · intro I hI
    rw [sourceGenerator_span]
    exact hdiv I I.property (Finset.mem_filter.mp hI).2
  · intro I hI
    rw [sourceGenerator_span]
    exact hN I I.property (Finset.mem_filter.mp hI).2

theorem sourceSecondZero_eq_zero_of_subunit (S : Finset (Ideal O)) (β : Ideal O→ℂ)
    (η : Character) (t Y : ℝ) (hY : Y<1)
    (hN : ∀ I∈supportedColumns S,β I≠0→(Ideal.absNorm I:ℝ)≤Y) :
    sourceSecondZero S β η t=0 := by
  have hc (I : supportedColumns S) : β I=0 := by
    by_contra hn
    have hi : (1:ℝ)≤Ideal.absNorm (I:Ideal O) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr
        (Ideal.absNorm_eq_zero_iff.not.mpr (Finset.mem_filter.mp I.property).2.1)
    linarith [hN I I.property hn]
  simp only [sourceSecondZero,secondZeroEnergy,hc,zero_mul,star_zero,mul_zero,Finset.sum_const_zero]

theorem tuple_second_zero_bound (N : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ {ι : Type*} [Fintype ι], Fintype.card ι≤N →
      ∀ (S : Finset (Tuple ι)) (β : Tuple ι→ℂ) (η : Character) (t B Y : ℝ),
      0≤B → 1≤Y → (∀ v∈S,finiteTupleProduct v≠0→‖β v‖≤B) →
      ∀ (s : Ideal O),s≠0 →
      (∀ v∈S,β v≠0→s∣finiteTupleProduct v) →
      (∀ v∈S,β v≠0→(Ideal.absNorm (finiteTupleProduct v):ℝ)≤Y) →
      ‖sourceSecondZero (finiteColumns S) (finiteColumnCoefficient S β) η t‖≤
        C*B^2*Y^(1+ε)/(Ideal.absNorm s:ℝ) := by
  let δ := ε/(2*(N+2:ℕ))
  have hδ : 0<δ := by dsimp [δ]; positivity
  have hδn : δ*(N+2:ℕ)=ε/2 := by dsimp [δ]; push_cast; field_simp
  obtain ⟨D,hD,hd⟩ := IdealDivisorBound.ideal_divisor_small_power δ hδ
  refine ⟨128*((1+D)^(N+2))^2,by positivity,?_⟩
  intro ι _ hi S β η t B Y hB hY hβ s hs hdiv hN
  let c := finiteColumnCoefficient S β
  have hY0 : 0<Y := zero_lt_one.trans_le hY
  have hbound (I : Ideal O) (hI : I∈supportedColumns (finiteColumns S)) (hn : c I≠0) :
      (Ideal.absNorm I:ℝ)≤Y := by
    obtain ⟨v,hv,hv0,he⟩ := finiteColumnCoefficient_witness S β I hn
    rw [←he]
    exact hN v hv hv0
  have hbase : 1≤(1+D)*Y^δ := by
    have hp := Real.one_le_rpow hY hδ.le
    nlinarith
  have hcoeff (I : Ideal O) (hI : I∈supportedColumns (finiteColumns S)) (hn : c I≠0) :
      ‖c I‖≤B*((1+D)^(N+2)*Y^(ε/2)) := by
    have hI0 := (Finset.mem_filter.mp hI).2.1
    have hdI : ((IdealMobiusDivisorSum.idealDivisors I).card:ℝ)≤(1+D)*Y^δ :=
      (hd I hI0).trans (mul_le_mul (by linarith)
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (hbound I hI hn) hδ.le) (by positivity) (by positivity))
    have hp : ((1+D)*Y^δ)^(N+2)=(1+D)^(N+2)*Y^(ε/2) := by
      rw [mul_pow,←Real.rpow_mul_natCast hY0.le,hδn]
    calc
      _ ≤ B*((IdealMobiusDivisorSum.idealDivisors I).card:ℝ)^(Fintype.card ι+2) :=
        finiteColumnCoefficient_norm_le S β B hB hβ I hI0
      _ ≤ B*((1+D)*Y^δ)^(Fintype.card ι+2) := by gcongr
      _ ≤ B*((1+D)*Y^δ)^(N+2) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hbase (by omega)) hB
      _ = _ := by rw [hp]
  have hb := sourceSecondZero_divisor_bound (finiteColumns S) c η t
    (B*((1+D)^(N+2)*Y^(ε/2))) Y (by positivity) hY0.le s hs hcoeff
    (by
      intro I hI hn
      obtain ⟨v,hv,hv0,he⟩ := finiteColumnCoefficient_witness S β I hn
      rw [←he]
      exact hdiv v hv hv0) hbound
  apply hb.trans_eq
  have hp : (Y^(ε/2))^2*Y=Y^(1+ε) := by
    rw [←Real.rpow_mul_natCast hY0.le]
    norm_num only [Nat.cast_ofNat]
    rw [show ε/2*(2:ℝ)=ε by ring,Real.rpow_add hY0,Real.rpow_one]
    ring
  calc
    _ = (128*((1+D)^(N+2))^2)*B^2*((Y^(ε/2))^2*Y)/(Ideal.absNorm s:ℝ) := by ring
    _ = _ := by rw [hp]

theorem normalized_tuple_second_zero_bound (N : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ {ι : Type*} [Fintype ι], Fintype.card ι≤N →
      ∀ (S : Finset (Tuple ι)) (β : Tuple ι→ℂ) (η : Character) (t B L T : ℝ),
      0≤B → 0<L → 0<T → (∀ v∈S,finiteTupleProduct v≠0→‖β v‖≤B) →
      ∀ (s : Ideal O),s≠0 →
      (∀ v∈S,β v≠0→s∣finiteTupleProduct v) →
      (∀ v∈S,β v≠0→(Ideal.absNorm (finiteTupleProduct v):ℝ)≤L*T) →
      (L*T<1 → sourceSecondZero (finiteColumns S) (finiteColumnCoefficient S β) η t=0) ∧
      ∀ κ : ℂ,‖(κ/(T:ℂ))*sourceSecondZero (finiteColumns S) (finiteColumnCoefficient S β) η t‖≤
        C*‖κ‖*B^2*L^(1+ε)*T^ε/(Ideal.absNorm s:ℝ) := by
  obtain ⟨C,hC,hbound⟩ := tuple_second_zero_bound N ε hε
  refine ⟨C,hC,?_⟩
  intro ι _ hi S β η t B L T hB hL hT hβ s hs hdiv hN
  have hz (hsmall : L*T<1) : sourceSecondZero (finiteColumns S) (finiteColumnCoefficient S β) η t=0 := by
    apply sourceSecondZero_eq_zero_of_subunit _ _ η t (L*T) hsmall
    intro I hI hn
    obtain ⟨v,hv,hv0,he⟩ := finiteColumnCoefficient_witness S β I hn
    rw [←he]
    exact hN v hv hv0
  refine ⟨hz,?_⟩
  intro κ
  by_cases hsmall : L*T<1
  · rw [hz hsmall,mul_zero,norm_zero]
    positivity
  have hb := hbound hi S β η t B (L*T) hB (le_of_not_gt hsmall) hβ s hs hdiv hN
  rw [norm_mul,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hT]
  apply (mul_le_mul_of_nonneg_left hb (div_nonneg (norm_nonneg _) hT.le)).trans_eq
  rw [Real.mul_rpow hL.le hT.le,Real.rpow_add hT,Real.rpow_one]
  field_simp

lemma profileCoefficient_dvd {ι : Type*} [Fintype ι]
    (R : Ideal O) (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P : ι→ℝ)
    (W₁ W₂ : ℝ→ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s : Ideal O) (v : Tuple ι)
    (hv : profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v≠0) :
    s∣finiteTupleProduct v := by
  by_contra h
  exact hv (by simp only [profileCoefficient,if_neg h,mul_zero])

theorem profile_second_zero_energy (N : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ {ι : Type*} [Fintype ι], Fintype.card ι≤N →
      ∀ (η : Character) (t : ℝ) (R : Ideal O) (ν : ι→Ideal O→ℂ),
      (∀ j I,‖ν j I‖≤1) → ∀ (Wslot : ι→ℝ→ℂ) (P D b : ι→ℝ)
      (W₁ W₂ : ℝ→ℂ) (D₁ D₂ b₁ b₂ : ℝ),
      (∀ j,0≤D j) → 0≤D₁ → 0≤D₂ → (∀ j,0≤b j) → 0≤b₁ → 0≤b₂ →
      (∀ j x,‖Wslot j x‖≤D j) → (∀ x,‖W₁ x‖≤D₁) → (∀ x,‖W₂ x‖≤D₂) →
      (∀ j,Wslot j 0=0) → W₁ 0=0 → W₂ 0=0 →
      (∀ j x,Wslot j x≠0→x≤b j) → (∀ x,W₁ x≠0→x≤b₁) → (∀ x,W₂ x≠0→x≤b₂) →
      ∀ (X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ s : Ideal O),
      (∀ j,0<P j) → 0<X₁ → 0<X₂ → 0<Y₁ → 0<Y₂ → B₁≠0 → B₂≠0 → s≠0 →
      X₁*X₂=T → Y₁*Y₂=T → ∀ S : Finset (Tuple ι),
      let Traw := (T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j,P j)
      let L := (∏ j,b j)*b₁*b₂
      let E := sourceSecondZero (finiteColumns S)
        (finiteColumnCoefficient S (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s)) η t
      (L*Traw<1 → E=0) ∧ ∀ κ : ℂ,
        ‖(κ/(Traw:ℂ))*E‖≤C*‖κ‖*(2*D₁*D₂*(∏ j,D j))^2*(1+L)^(1+ε)*Traw^ε/(Ideal.absNorm s:ℝ) := by
  obtain ⟨C,hC,hbound⟩ := normalized_tuple_second_zero_bound N ε hε
  refine ⟨C,hC,?_⟩
  intro ι _ hi η t R ν hν Wslot P D b W₁ W₂ D₁ D₂ b₁ b₂
    hD hD₁ hD₂ hb hb₁ hb₂ hslot h₁ h₂ hz hz₁ hz₂ hs hs₁ hs₂
    X₁ X₂ Y₁ Y₂ T B₁ B₂ s hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hsz hX hY S Traw L E
  let β := profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s
  have hβ (v : Tuple ι) : ‖β v‖≤2*D₁*D₂*(∏ j,D j) :=
    profileCoefficient_norm_le R ν hν Wslot P D W₁ W₂ D₁ D₂ hD hD₁ hD₂
      hslot h₁ h₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v
  have hT : 0<T := hX ▸ mul_pos hX₁ hX₂
  have hn₁ : (0:ℝ)<Ideal.absNorm B₁ := by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hB₁)
  have hn₂ : (0:ℝ)<Ideal.absNorm B₂ := by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hB₂)
  have hraw : 0<Traw := mul_pos (div_pos hT (mul_pos hn₁ hn₂)) (Finset.prod_pos (fun j _=>hP j))
  have hL : 0≤L := mul_nonneg (mul_nonneg (Finset.prod_nonneg (fun j _=>hb j)) hb₁) hb₂
  have hN (v : Tuple ι) (hv : β v≠0) : (Ideal.absNorm (finiteTupleProduct v):ℝ)≤L*Traw := by
    have hh := profileCoefficient_product_bound R ν Wslot P b W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ T B₁ B₂ s
      hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY hz hz₁ hz₂ hs hs₁ hs₂ v hv
    exact hh.2.trans_eq (by dsimp only [L,Traw];ring)
  refine ⟨?_,?_⟩
  · intro hsmall
    apply sourceSecondZero_eq_zero_of_subunit _ _ η t (L*Traw) hsmall
    intro I hI hn
    obtain ⟨v,hv,hv0,he⟩ := finiteColumnCoefficient_witness S β I hn
    rw [←he]
    exact hN v hv0
  · exact (hbound hi S β η t (2*D₁*D₂*(∏ j,D j)) (1+L) Traw
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hD₁) hD₂) (Finset.prod_nonneg (fun j _=>hD j)))
      (by linarith) hraw (fun v _ _=>hβ v) s hsz
      (fun v _ hv=>profileCoefficient_dvd R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v hv)
      (fun v _ hv=>(hN v hv).trans (mul_le_mul_of_nonneg_right (by linarith : L≤1+L) hraw.le))).2

end SevenEighths.CenteredMomentSourceSecondZeroEnergy

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondWholeKernel
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondWholeKernel
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson CompletedGauss
open CanonicalQuadraticSieve CenteredMomentSourceRow CenteredMomentSmooth
open CenteredMomentFirstWholeKernel CenteredMomentSupportedCorrelation
local notation "O" => ActualEisensteinCubic.O

theorem primary_norm_sq (I : Ideal O) (hI : Supported I) :
    ‖eisEmbedding (primaryGenerator I)‖^2=(Ideal.absNorm I:ℝ) := by
  rw [eisEmbedding_norm_sq_eq_absNorm_span,primary_span_supported I hI]

end SevenEighths.CenteredMomentSecondWholeKernel

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondTail
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondTail
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson CompletedGauss
open CanonicalQuadraticSieve CenteredMomentSourceRow CenteredMomentSectorLocalization
open CenteredMomentSupportedCorrelation CenteredMomentSecondWholeKernel
local notation "O" => ActualEisensteinCubic.O

theorem actual_second_kernel_reference (I J : Ideal O) (hI : I≠0) (hJ : J≠0)
    (K X H Tsec : ℝ) (hK : 0<K) (hX : 0<X)
    (hi : (Ideal.absNorm I:ℝ)≤Real.exp H*X) (hj : (Ideal.absNorm J:ℝ)≤Real.exp H*X)
    (hsec : X^2/K≤Tsec) :
    kernelReference Tsec H≤K/((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)) := by
  have hT : 0<Tsec := (div_pos (sq_pos_of_pos hX) hK).trans_le hsec
  have hNi := CenteredMomentFirstScale.norm_pos I hI
  have hNj := CenteredMomentFirstScale.norm_pos J hJ
  have hprod : (Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)≤Real.exp (2*H)*X^2 := by
    apply (mul_le_mul hi hj hNj.le (by positivity)).trans_eq
    rw [show 2*H=H+H by ring,Real.exp_add]
    ring
  unfold kernelReference
  apply (le_div_iff₀ (mul_pos hNi hNj)).mpr
  calc
    _ ≤ (Real.exp (-2*H)/Tsec)*(Real.exp (2*H)*X^2) :=
      mul_le_mul_of_nonneg_left hprod (by positivity)
    _ = X^2/Tsec := by
      rw [show -2*H=-(2*H) by ring,Real.exp_neg]
      field_simp
    _ ≤ K := (div_le_iff₀ hT).mpr (by simpa only [mul_comm] using (div_le_iff₀ hK).mp hsec)

theorem second_discarded_pair_bound (Adec : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ),0<C ∧
      ∀ (W : 𝓢(ℝ,ℂ)) (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
        (K X H Tsec Z Csec ξ : ℝ),0<K → 0<X → 1<Z → 1≤Csec →
      (Ideal.absNorm I:ℝ)≤Real.exp H*X → (Ideal.absNorm J:ℝ)≤Real.exp H*X →
      X^2/K≤Tsec → (2*H/Real.log Z+Real.log (4*Csec)/Real.log Z<ξ/4) →
      ‖secondDiscardedPair I J hI hJ W K Tsec Z ξ‖≤
        K*(Real.exp H*X)^2*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
          ((min 1 (kernelReference Tsec H))^2*(1+Z^(ξ/4))^Adec) := by
  obtain ⟨s,C,hC,ht⟩ := actual_discarded_second_tail Adec
  refine ⟨s,C,hC,?_⟩
  intro W I J hI hJ K X H Tsec Z Csec ξ hK hX hZ hCs hi hj hsec hthreshold
  have hT : 0<Tsec := (div_pos (sq_pos_of_pos hX) hK).trans_le hsec
  have hb := ht W Tsec Z Csec H ξ (K/((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)))
    hT hZ hCs hthreshold (actual_second_kernel_reference I J hI.1 hJ.1 K X H Tsec hK hX hi hj hsec)
    (primaryGenerator I) (primaryGenerator J)
    ((supported_span_primaryGenerator_iff I).mpr hI) ((supported_span_primaryGenerator_iff J).mpr hJ)
  have he (h : O) : K*‖eisEmbedding h‖^2/‖eisEmbedding (primaryGenerator I*primaryGenerator J)‖^2=
      (K/((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)))*normValue h := by
    rw [map_mul,norm_mul,mul_pow,primary_norm_sq I hI,primary_norm_sq J hJ,normValue_eq_embedding]
    ring
  have hu : normValue (primaryGenerator I)=(Ideal.absNorm I:ℝ) := by rw [normValue,primary_span_supported I hI]
  have hv : normValue (primaryGenerator J)=(Ideal.absNorm J:ℝ) := by rw [normValue,primary_span_supported J hJ]
  rw [hu,hv] at hb
  have hNi : (1:ℝ)≤Ideal.absNorm I := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI.1)
  have hNj : (1:ℝ)≤Ideal.absNorm J := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hJ.1)
  have hroot : 1≤Real.sqrt (Ideal.absNorm I:ℝ)*Real.sqrt (Ideal.absNorm J:ℝ) :=
    one_le_mul_of_one_le_of_one_le (Real.one_le_sqrt.mpr hNi) (Real.one_le_sqrt.mpr hNj)
  have hnorm : ‖(K:ℂ)/((Real.sqrt (Ideal.absNorm I:ℝ):ℂ)*(Real.sqrt (Ideal.absNorm J:ℝ):ℂ))‖≤K := by
    rw [norm_div,norm_mul]
    simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hK,abs_of_nonneg (Real.sqrt_nonneg _)]
    exact div_le_self hK.le hroot
  unfold secondDiscardedPair
  simp_rw [he]
  rw [norm_mul]
  apply (mul_le_mul hnorm hb (norm_nonneg _) hK.le).trans
  have hprod := mul_le_mul hi hj (Nat.cast_nonneg _) (by positivity : 0≤Real.exp H*X)
  have hfac : 0≤(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
      ((min 1 (kernelReference Tsec H))^2*(1+Z^(ξ/4))^Adec) := by positivity
  have hb' := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hprod hfac) hK.le
  convert (preTransparency := .instances) hb' using 1 <;> ring

end SevenEighths.CenteredMomentSecondTail

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SupportedTailAggregate
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSupportedTailAggregate
open HeckeFamily CanonicalQuadraticSieve CenteredMomentSourceRow CenteredMomentHeckeColumnWindow
open CenteredMomentSecondTail CenteredMomentFirstTailAggregate CenteredMomentFirstDiscardedEnergy
open CenteredMomentFirstScale CenteredMomentSectorLocalization CenteredMomentSecondHeightFamily
local notation "O" => ActualEisensteinCubic.O

private theorem pair_mass {α : Type*} [Fintype α] (c w : α → ℂ) (F : α → α → ℂ)
    (hw : ∀ i,‖w i‖≤1) (B : ℝ) (_hB : 0≤B)
    (hF : ∀ i j,c i≠0 → c j≠0 → ‖F i j‖≤B) :
    ‖∑ i,∑ j,((c i*w i)*star (c j*w j))*F i j‖≤(∑ i,‖c i‖)^2*B := by
  have ht (i j : α) : ‖((c i*w i)*star (c j*w j))*F i j‖≤‖c i‖*‖c j‖*B := by
    by_cases hi : c i=0
    · simp [hi]
    by_cases hj : c j=0
    · simp [hj]
    rw [norm_mul,norm_mul,norm_star]
    apply mul_le_mul _ (hF i j hi hj) (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    apply mul_le_mul _ _ (norm_nonneg _) (norm_nonneg _)
    · rw [norm_mul];exact mul_le_of_le_one_right (norm_nonneg _) (hw i)
    · rw [norm_mul];exact mul_le_of_le_one_right (norm_nonneg _) (hw j)
  calc
    _ ≤ ∑ i,‖∑ j,((c i*w i)*star (c j*w j))*F i j‖ := norm_sum_le _ _
    _ ≤ ∑ i,∑ j,‖c i‖*‖c j‖*B := Finset.sum_le_sum (fun i _ => (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j _ => ht i j)))
    _ = _ := by rw [pow_two,Finset.sum_mul,Finset.sum_mul];apply Finset.sum_congr rfl;intro i hi;rw [Finset.mul_sum,Finset.sum_mul]

theorem second_discarded_energy_bound (Adec : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ),0<C ∧
      ∀ (η : Character) (t : ℝ) (S : Finset (Ideal O)) (c : Ideal O → ℂ)
        (W : 𝓢(ℝ,ℂ)) (K X H Tsec Z Csec ξ : ℝ),0<K → 0<X → 1<Z → 1≤Csec →
      (∀ I∈S,c I≠0 → (Ideal.absNorm I:ℝ)≤Real.exp H*X) →
      X^2/K≤Tsec → (2*H/Real.log Z+Real.log (4*Csec)/Real.log Z<ξ/4) →
      ‖secondDiscardedEnergy η t S c W K Tsec Z ξ‖≤
        (∑ I∈S,‖c I‖)^2*K*(Real.exp H*X)^2*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
          ((min 1 (kernelReference Tsec H))^2*(1+Z^(ξ/4))^Adec) := by
  obtain ⟨s,C,hC,ht⟩ := second_discarded_pair_bound Adec
  refine ⟨s,C,hC,?_⟩
  intro η t S c W K X H Tsec Z Csec ξ hK hX hZ hCs hN hsec hthreshold
  let B := K*(Real.exp H*X)^2*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
    ((min 1 (kernelReference Tsec H))^2*(1+Z^(ξ/4))^Adec)
  have hB : 0≤B := by dsimp only [B];positivity
  have hweight (I : supportedColumns S) : ‖heightCoeff η t I‖≤1 := by
    rw [heightCoeff_eq_fixed_rowWeight η t I (Finset.mem_filter.mp I.property).2]
    exact rowWeight_norm_le_one η fixedBadMask 1 1 t I (Finset.mem_filter.mp I.property).2.1
  have hp := pair_mass (fun I : supportedColumns S => c I) (fun I => heightCoeff η t I)
    (fun I J => secondDiscardedPair I J (Finset.mem_filter.mp I.property).2
      (Finset.mem_filter.mp J.property).2 W K Tsec Z ξ) hweight B hB
    (fun I J hi hj => ht W I J (Finset.mem_filter.mp I.property).2
      (Finset.mem_filter.mp J.property).2 K X H Tsec Z Csec ξ hK hX hZ hCs
      (hN I (Finset.mem_filter.mp I.property).1 hi) (hN J (Finset.mem_filter.mp J.property).1 hj) hsec hthreshold)
  have hm : (∑ I : supportedColumns S,‖c I‖)≤∑ I∈S,‖c I‖ := by
    rw [Finset.sum_coe_sort (supportedColumns S) (fun I => ‖c I‖)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => norm_nonneg _)
  apply hp.trans
  convert (preTransparency := .instances) mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (show 0 ≤ ∑ I : supportedColumns S, ‖c I‖ from
      Finset.sum_nonneg (fun I _ => norm_nonneg (c I))) hm 2) hB using 1 ; dsimp only [B];ring

end SevenEighths.CenteredMomentSupportedTailAggregate

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.OriginalCommonHarmonic
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentOriginalCommonHarmonic
open HeckeFamily CanonicalQuadraticSieve
open CenteredMomentCommonRadialData CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentSupportedZeroEnergy CenteredMomentSourceZeroEnergy CenteredMomentAddedZeroUniform
open CenteredMomentSecondActiveCount CenteredMomentActiveSource CenteredMomentCommonHarmonicMass
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

attribute [local instance] OAI.SevenEighths.CenteredMomentOriginalCommonHarmonic.instDecidableEqSumFinOfNatNat_solutions
omit [DecidableEq ι] in
 theorem original_column_norm (s:Input ι) (R seed I:Ideal O)
    (hz₁:s.W₁ 0=0) (hz₂:s.W₂ 0=0) (h:coefficient s R seed I≠0):
    I≠0 ∧ (Ideal.absNorm I:ℝ)≤ sourceRadius s:=by
  obtain ⟨v,hv,hv0,he⟩:=finiteColumnCoefficient_witness (Fintype.piFinset s.pools)
    (profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed) I h
  have hz (i:ι):s.W i 0=0:=by
    by_contra hn
    have hh:=(s.support i hn).1
    linarith [s.lo_pos i]
  have hh:=profileCoefficient_product_bound R s.ν s.W s.P s.hi s.W₁ s.W₂ s.b₁ s.b₂
    s.X₁ s.X₂ s.Y₁ s.Y₂ (s.X₁*s.X₂) 1 1 seed s.P_pos s.X₁_pos s.X₂_pos s.Y₁_pos s.Y₂_pos
    one_ne_zero one_ne_zero rfl s.same_product hz hz₁ hz₂
    (fun i x hx=>(s.support i hx).2) (fun x hx=>s.support₁ hx) (fun x hx=>s.support₂ hx) v hv0
  rw [he] at hh
  simpa only [sourceRadius,map_one,Nat.cast_one,mul_one,div_one] using hh

end SevenEighths.CenteredMomentOriginalCommonHarmonic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondExceptionalFamilyUniform
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap Topology

namespace SevenEighths.CenteredMomentSecondExceptionalFamilyUniform
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalNonunit CenteredMomentSecondHeightFamily
open CenteredMomentSecondRadicalBudget CenteredMomentSecondLiveBlock
open CenteredMomentSecondPhysicalBlock CenteredMomentSectorLocalization RayFourExpansion
open CenteredMomentReflectedSource CenteredMomentSecondExceptionalFamily
local notation "O" => HeckeFamily.O

theorem expandedFactor_real (η:Character) :
    (expandedFactor η:ℝ)=fixedExpandedCost*(η.modulus.absNorm:ℝ) := by
  unfold expandedFactor fixedExpandedCost
  push_cast
  ring

end SevenEighths.CenteredMomentSecondExceptionalFamilyUniform

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondExceptionalSourceCaps
namespace OAI

noncomputable section
open scoped BigOperators Classical
open Filter

namespace SevenEighths.CenteredMomentSecondExceptionalSourceCaps
open HeckeFamily CenteredMomentSecondExceptionalFamily
open CenteredMomentSecondExceptionalFamilyUniform
local notation "O" => HeckeFamily.O

theorem eventually_source_caps :
    ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀(η:Character)(R0:Ideal O)(H R B:ℝ),
      0≤B → 0≤H → 0≤R → (η.modulus.absNorm:ℝ)≤Z^B →
      (R0.absNorm:ℝ)≤Z^B → H≤Z^B → R≤Z^B →
      H≤Z^(5*B+1) ∧
      (expandedFactor η:ℝ)*R0.absNorm*H^2*(4*R)≤Z^(5*B+1) := by
  filter_upwards [eventually_gt_atTop (1:ℝ),eventually_ge_atTop (4*fixedExpandedCost)] with Z hZ hfixed
  refine ⟨hZ,?_⟩
  intro η R0 H R B hB hH hR hη hR0 hHN hRN
  have hz:0<Z:=zero_lt_one.trans hZ
  have hH2:H^2≤(Z^B)^2:=pow_le_pow_left₀ hH hHN 2
  have hbig:B≤5*B+1:=by linarith
  refine ⟨hHN.trans (Real.rpow_le_rpow_of_exponent_le hZ.le hbig),?_⟩
  rw [expandedFactor_real]
  calc
    _=(4*fixedExpandedCost)*(η.modulus.absNorm:ℝ)*R0.absNorm*H^2*R:=by ring
    _≤Z*(Z^B)*(Z^B)*(Z^B)^2*(Z^B):=by gcongr
    _=Z^(5*B+1):=by
      rw [show (Z^B)^2=Z^B*Z^B by ring]
      calc
        _=Z^(1:ℝ)*Z^B*Z^B*(Z^B*Z^B)*Z^B:=by rw [Real.rpow_one]
        _=Z^(5*B+1):=by
          repeat rw [←Real.rpow_add hz]
          congr 1
          ring

end SevenEighths.CenteredMomentSecondExceptionalSourceCaps

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondExceptionalUniformSource
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter MeasureTheory

namespace SevenEighths.CenteredMomentSecondExceptionalUniformSource
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss UniqueFactorizationMonoid
open CenteredMomentCommonRadialData CenteredMomentCommonWindowColumn CenteredMomentReflectedSource
open CenteredMomentCommonSectorWindow CenteredMomentSecondSectorColumns
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentExceptionalAmplitudePair
open CenteredMomentLogDyadic RayFourExpansion CenteredMomentSmooth
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonExceptionalCost
open CenteredMomentExceptionalSourceShell CenteredMomentExceptionalHeight CenteredMomentSecondHeightFamily
open CenteredMomentSecondExceptionalPairBound
open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalCommon
open CenteredMomentSecondCanonical
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentForcing CenteredMomentChildRows
open CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondWholeKernel CenteredMomentSectorLocalization
open CenteredMomentSecondDyadicRowSupport

open CenteredMomentRankinRadical
open ConcretePrimeRowBridge CenteredMomentMobiusRegroup CenteredMomentSupportedCorrelation
open CenteredMomentSupport CenteredMomentSecondCanonicalScalar CenteredMomentSecondDivisorSupport
local notation "O" => HeckeFamily.O
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

open CenteredMomentSecondExceptionalFamily
open CenteredMomentSecondEnergySplit CenteredMomentSecondLiveBlock
open CenteredMomentOriginalCommonHarmonic
open CenteredMomentFiniteProfileExceptionalPhysical

open CenteredMomentSecondExceptionalFixedQChosenBlock
open CenteredMomentSecondBlockRadicalHarmonicMass
open CenteredMomentSecondRetainedAggregate
open CenteredMomentActiveSource

attribute [local instance] OAI.SevenEighths.CenteredMomentSecondExceptionalUniformSource.instDecidableEqSumFinOfNatNat_definitions
theorem original_exceptional_energy (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)(lo hi:ι→ℝ)(W:𝓢(ℝ,ℂ))
    (ε δ θ B:ℝ)(hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B):
    ∃J:ℕ,∃Sprofile:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧ ∃Ck:ℝ,0≤Ck ∧
      ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} →
      ∃K:ℝ,0<K ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(s:Input ι)(p:Profiles wlo whi),(∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) →
      (∀i,1≤ s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀(R0 seed:Ideal O),R0≠0 → Squarefree seed → seed≠0 → 0≤ sourceRadius s → sourceRadius s≤Z^B →
      (s.η.modulus.absNorm:ℝ)≤Z^B → (R0.absNorm:ℝ)≤Z^B →
      let S:=finiteColumns (Fintype.piFinset s.pools)
      let β:=coefficient s R0 seed
      ∀χ₀:RayCharacter,∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
      ∀(Tsec ξ Kphys:ℝ),0<Kphys →
      let R:=frequencyRadius Tsec Z ξ
      0<R → R≤Z^B →
      ∀r:ℝ,Z^r≤ s.X₁ → Z^r≤ s.X₂ → Z^r≤ s.Y₁ → Z^r≤ s.Y₂ →
      ‖partEnergy true s.η χ₀ Q m s.t S β W Kphys Tsec Z ξ (sourceRadius s)‖/volume s.toData≤
        Ck*profileFactor Sprofile s p J Q K*
          Z^(2*ε+2*δ+2*(5*B+1)*θ-2*max r 0/3)*
          (volume s.toData)^(1/3:ℝ)*Kphys^(5/6:ℝ)*((∏i,s.lo i)*wlo*wlo)^(-2/3:ℝ)/
          (seed.absNorm:ℝ) :=by
  obtain ⟨J,Sprofile,hSp,Ck,hCk,hsource⟩:=
    CenteredMomentSecondExceptionalFixedQSource.original_exceptional_energy
      wlo whi hwlo hwhi lo hi W ε δ θ (5*B+1) B 1 hε hδ hθ (by positivity) hB zero_lt_one
  refine ⟨J,Sprofile,hSp,Ck,hCk,?_⟩
  intro Q hQ hQt hQ72
  obtain ⟨K,hK,hsource⟩:=hsource Q hQ hQt hQ72
  refine ⟨K,hK,?_⟩
  filter_upwards [hsource,CenteredMomentSecondExceptionalSourceCaps.eventually_source_caps] with Z hZ hcaps
  refine ⟨hZ.1,?_⟩
  intro s p hlo hhi hP hW1 hW2 R0 seed hR0 hseed hseed0 hH0 hH hη hR0N S β χ₀ m hm hml hm2
    Tsec ξ Kphys hKphys R hR hRN r hX1 hX2 hY1 hY2
  obtain ⟨hHlarge,hcond⟩:=hcaps.2 s.η R0 (sourceRadius s) R B hB hH0 hR.le hη hR0N hH hRN
  exact hZ.2 s p hlo hhi hP hW1 hW2 R0 seed hR0 hseed hseed0 hHlarge χ₀ m hm hml hm2
    Tsec ξ Kphys hKphys hR (by simpa using hRN) hcond r hX1 hX2 hY1 hY2

end SevenEighths.CenteredMomentSecondExceptionalUniformSource

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondSourceDiagonal
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentSecondSourceDiagonal
open HeckeFamily CanonicalQuadraticSieve
open CenteredMomentSourceSecondZeroEnergy CenteredMomentCommonRadialData
open CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentExceptionalAmplitudePair CenteredMomentOriginalCommonHarmonic
open CenteredMomentFiniteProfileExceptional
local notation "O"=>HeckeFamily.O

attribute [local instance] OAI.SevenEighths.CenteredMomentSecondSourceDiagonal.instDecidableEqSumFinOfNatNat_definitions
theorem actual_second_zero (N:ℕ)(ε:ℝ)(hε:0<ε):
    ∃C:ℝ,0<C ∧ ∀{ι:Type*}[Fintype ι][DecidableEq ι],Fintype.card ι≤N →
      ∀(a b:ℝ),0<a → 0≤b → ∀(s:Input ι)(p:Profiles a b),
      s.W₁=p.profile 0 → s.W₂=p.profile 1 → ∀(R seed:Ideal O),seed≠0 →
      ∀κ:ℂ,
      ‖κ*sourceSecondZero (finiteColumns (Fintype.piFinset s.pools))
        (coefficient s R seed) s.η s.t‖/volume s.toData≤
      C*‖κ‖*(2*SchwartzMap.seminorm ℝ 0 0 (p.profile 0)*SchwartzMap.seminorm ℝ 0 0 (p.profile 1)*
        (∏i,s.M i))^2*(1+(∏i,max 0 (s.hi i))*b*b)^(1+ε)*(volume s.toData)^ε/(seed.absNorm:ℝ):=by
  obtain ⟨C,hC,hbound⟩:=profile_second_zero_energy N ε hε
  refine ⟨C,hC,?_⟩
  intro ι _ _ hcard a b ha hb s p hw1 hw2 R seed hseed κ
  have hM (i:ι):0≤ s.M i:=zero_le_one.trans (s.M_ge_one i)
  have hhi (i:ι):0≤ max 0 (s.hi i):=le_max_left _ _
  have hz (i:Fin 2):p.profile i 0=0:=by
    by_contra hn
    exact (not_le_of_gt ha) (p.support i hn).1
  have hslotzero (i:ι):s.W i 0=0:=by
    by_contra hn
    exact (not_le_of_gt (s.lo_pos i)) (s.support i hn).1
  have hW1:∀x,‖s.W₁ x‖≤SchwartzMap.seminorm ℝ 0 0 (p.profile 0):=by
    intro x;rw [hw1];exact SchwartzMap.norm_le_seminorm ℝ _ _
  have hW2:∀x,‖s.W₂ x‖≤SchwartzMap.seminorm ℝ 0 0 (p.profile 1):=by
    intro x;rw [hw2];exact SchwartzMap.norm_le_seminorm ℝ _ _
  have hh:=(hbound hcard s.η s.t R s.ν s.ν_bound s.W s.P s.M (fun i=>max 0 (s.hi i)) s.W₁ s.W₂
    (SchwartzMap.seminorm ℝ 0 0 (p.profile 0)) (SchwartzMap.seminorm ℝ 0 0 (p.profile 1)) b b
    hM (apply_nonneg _ _) (apply_nonneg _ _) hhi hb hb s.W_bound hW1 hW2
    hslotzero (by rw [hw1];exact hz 0) (by rw [hw2];exact hz 1)
    (fun i x hx=>((s.support i hx).2).trans (le_max_right _ _))
    (by intro x hx;rw [hw1] at hx;exact (p.support 0 hx).2)
    (by intro x hx;rw [hw2] at hx;exact (p.support 1 hx).2)
    s.X₁ s.X₂ s.Y₁ s.Y₂ (s.X₁*s.X₂) 1 1 seed s.P_pos s.X₁_pos s.X₂_pos s.Y₁_pos s.Y₂_pos
    one_ne_zero one_ne_zero hseed rfl s.same_product (Fintype.piFinset s.pools)).2 κ
  have hV:=volume_pos s.toData
  simpa only [map_one,Nat.cast_one,mul_one,div_one,coefficient,volume,norm_mul,norm_div,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos hV,abs_of_pos s.X₁_pos,abs_of_pos s.X₂_pos,
    abs_of_pos (Finset.prod_pos (fun i _=>s.P_pos i)),mul_div_assoc,div_mul_eq_mul_div] using hh

end SevenEighths.CenteredMomentSecondSourceDiagonal

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SourceProfileMassUniform
namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff SchwartzMap

namespace SevenEighths.CenteredMomentSourceProfileMassUniform
open ActualEisensteinCubic CenteredMomentAddedZeroUniform CenteredMomentSourceMass
open CenteredMomentSourceProfileMass
local notation "O" => ActualEisensteinCubic.O

theorem profile_mass_explicit {ι : Type*} [Fintype ι]
    (Wslot : ι → ℝ → ℂ) (W₁ W₂ : ℝ → ℂ)
    (b D : ι → ℝ) (b₁ b₂ D₁ D₂ : ℝ)
    (hb : ∀ j,0≤b j) (hb₁ : 0≤b₁) (hb₂ : 0≤b₂)
    (hD : ∀ j,0≤D j) (hD₁ : 0≤D₁) (hD₂ : 0≤D₂)
    (hzSlot : ∀ j,Wslot j 0=0) (hz₁ : W₁ 0=0) (hz₂ : W₂ 0=0)
    (hsSlot : ∀ j x,Wslot j x≠0→x≤b j)
    (hs₁ : ∀ x,W₁ x≠0→x≤b₁) (hs₂ : ∀ x,W₂ x≠0→x≤b₂)
    (hbound : ∀ j x,‖Wslot j x‖≤D j)
    (hbound₁ : ∀ x,‖W₁ x‖≤D₁) (hbound₂ : ∀ x,‖W₂ x‖≤D₂)
    (R : Ideal O) (ν : ι → Ideal O → ℂ) (hν : ∀ j I,‖ν j I‖≤1)
    (P : ι → ℝ) (X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ s : Ideal O)
    (hP : ∀ j,0<P j) (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hY₁ : 0<Y₁) (hY₂ : 0<Y₂)
    (hB₁ : B₁≠0) (hB₂ : B₂≠0) (hX : X₁*X₂=T) (hY : Y₁*Y₂=T)
    (S : Finset (Tuple ι)) :
    (∑v∈S,‖profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v‖)≤
      (2*128^(Fintype.card ι+2)*(∏j,D j)*D₁*D₂*(∏j,b j)*b₁*b₂)*
        (T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏j,P j) := by
  let e := Fintype.equivFin ι
  have hzero : ∀ i,sourceProfiles (fun j => Wslot (e.symm j)) W₁ W₂ i 0=0 := by
    simpa only [Fin.forall_fin_add,sourceProfiles,Fin.append_left,Fin.append_right,
      Fin.forall_fin_two,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
      using And.intro (fun j => hzSlot (e.symm j)) (And.intro hz₁ hz₂)
  have hs : ∀ i x,sourceProfiles (fun j => Wslot (e.symm j)) W₁ W₂ i x≠0→
      x≤ sourceBounds (fun j => b (e.symm j)) b₁ b₂ i := by
    simpa only [Fin.forall_fin_add,sourceProfiles,sourceBounds,Fin.append_left,Fin.append_right,
      Fin.forall_fin_two,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
      using And.intro (fun j => hsSlot (e.symm j)) (And.intro hs₁ hs₂)
  have hbound' : ∀ i x,‖sourceProfiles (fun j => Wslot (e.symm j)) W₁ W₂ i x‖≤
      sourceBounds (fun j => D (e.symm j)) D₁ D₂ i := by
    simpa only [Fin.forall_fin_add,sourceProfiles,sourceBounds,Fin.append_left,Fin.append_right,
      Fin.forall_fin_two,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
      using And.intro (fun j => hbound (e.symm j)) (And.intro hbound₁ hbound₂)
  have hm := originalCoefficient_mass (Fintype.card ι) 1 one_ne_zero
    (1 : MulChar (O ⧸ Ideal.span {(1:O)}) ℂ) R 0 (fun j => ν (e.symm j))
    (fun j I => hν _ I) (fun j => Wslot (e.symm j)) (fun j => P (e.symm j))
    (fun j => b (e.symm j)) (fun j => D (e.symm j)) W₁ W₂
    b₁ b₂ D₁ D₂ X₁ X₂ Y₁ Y₂ T B₁ B₂ s
    (fun j => hb _) hb₁ hb₂ (fun j => hD _) hD₁ hD₂
    (fun j => hP _) hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY hzero hs hbound'
    (S.image (tupleEquiv e))
  rw [finite_original_mass_reindex] at hm
  simp_rw [profileCoefficient_eq_original]
  simpa only [sourceMassConstant,e.symm.prod_comp D,e.symm.prod_comp b,e.symm.prod_comp P] using hm

end SevenEighths.CenteredMomentSourceProfileMassUniform

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SourceInputTailUniform
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter

namespace SevenEighths.CenteredMomentSourceInputTailUniform
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass CenteredMomentSourceRow
open CenteredMomentSourceZeroEnergy CenteredMomentSourceLiveColumn CenteredMomentSupportedZeroEnergy
open CenteredMomentSourceProfileMassUniform CenteredMomentSourceProfileMass
open CenteredMomentSupportedTailAggregate CenteredMomentSectorLocalization
open CenteredMomentExceptionalAmplitudePair CenteredMomentNaturalRadialCutoff
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]

attribute [local instance] OAI.SevenEighths.CenteredMomentSourceInputTailUniform.instDecidableEqSumFinOfNatNat_solutions
omit [DecidableEq ι] in
lemma plainControl_nonneg (s:Input ι)(W₁ W₂:𝓢(ℝ,ℂ)):0≤plainControl s W₁ W₂:=by
  unfold plainControl
  exact mul_nonneg (mul_nonneg (Finset.prod_nonneg (fun i _=>(s.M_ge_one i).trans' zero_le_one))
    (apply_nonneg _ _)) (apply_nonneg _ _)

omit [DecidableEq ι] in
lemma volume_pos (s:Input ι):0<volume s.toData:=
  mul_pos (mul_pos s.X₁_pos s.X₂_pos) (Finset.prod_pos (fun i _=>s.P_pos i))

omit [DecidableEq ι] in
theorem input_mass (hi:ι→ℝ)(whi:ℝ)(hhi:∀i,0≤hi i)(hwhi:0≤whi)
    (s:Input ι)(W₁ W₂:𝓢(ℝ,ℂ))(wlo:ℝ)(hwlo:0<wlo)
    (he₁:s.W₁=W₁)(he₂:s.W₂=W₂)
    (hs₁:Function.support (W₁:ℝ→ℂ)⊆Set.Icc wlo whi)
    (hs₂:Function.support (W₂:ℝ→ℂ)⊆Set.Icc wlo whi)
    (hshi:∀i,s.hi i≤hi i)(R seed:Ideal O):
    (∑I∈finiteColumns (Fintype.piFinset s.pools),‖coefficient s R seed I‖)≤
      (2*128^(Fintype.card ι+2)*(∏i,hi i)*whi^2)*plainControl s W₁ W₂*volume s.toData:=by
  have hz (i:ι):s.W i 0=0:=by
    by_contra hn
    exact (not_le_of_gt (s.lo_pos i)) (s.support i hn).1
  have hzW (W:𝓢(ℝ,ℂ))(hs:Function.support (W:ℝ→ℂ)⊆Set.Icc wlo whi):W 0=0:=by
    by_contra hn
    exact (not_le_of_gt hwlo) (hs hn).1
  have hm:=profile_mass_explicit s.W W₁ W₂ hi s.M whi whi
    (SchwartzMap.seminorm ℝ 0 0 W₁) (SchwartzMap.seminorm ℝ 0 0 W₂)
    hhi hwhi hwhi (fun i=>zero_le_one.trans (s.M_ge_one i))
    (apply_nonneg _ _) (apply_nonneg _ _) hz (hzW W₁ hs₁) (hzW W₂ hs₂)
    (fun i x hx=>((s.support i hx).2).trans (hshi i))
    (fun x hx=>(hs₁ hx).2) (fun x hx=>(hs₂ hx).2) s.W_bound
    (SchwartzMap.norm_le_seminorm ℝ W₁) (SchwartzMap.norm_le_seminorm ℝ W₂)
    R s.ν s.ν_bound s.P s.X₁ s.X₂ s.Y₁ s.Y₂ (s.X₁*s.X₂) 1 1 seed
    s.P_pos s.X₁_pos s.X₂_pos s.Y₁_pos s.Y₂_pos one_ne_zero one_ne_zero
    rfl s.same_product (Fintype.piFinset s.pools)
  have hc:=finiteColumnCoefficient_mass (Fintype.piFinset s.pools)
    (profileCoefficient R s.ν s.W s.P W₁ W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
  unfold coefficient
  rw [he₁,he₂]
  change (∑I∈_,‖finiteColumnCoefficient _ _ I‖)≤_
  apply (hc.trans hm).trans_eq
  simp only [map_one,Nat.cast_one,one_mul,div_one,plainControl,volume]
  ring

omit [DecidableEq ι] in
lemma input_column_bound (hi:ι→ℝ)(whi:ℝ)
    (s:Input ι)(W₁ W₂:𝓢(ℝ,ℂ))(wlo:ℝ)(hwlo:0<wlo)
    (he₁:s.W₁=W₁)(he₂:s.W₂=W₂)
    (hs₁:Function.support (W₁:ℝ→ℂ)⊆Set.Icc wlo whi)
    (hs₂:Function.support (W₂:ℝ→ℂ)⊆Set.Icc wlo whi)
    (hshi:∀i,s.hi i≤hi i)(R seed I:Ideal O)(hn:coefficient s R seed I≠0):
    (Ideal.absNorm I:ℝ)≤((∏i,hi i)*whi^2)*volume s.toData:=by
  obtain ⟨v,hv,hv0,hvI⟩:=finiteColumnCoefficient_witness _ _ I hn
  have hz (i:ι):s.W i 0=0:=by
    by_contra h
    exact (not_le_of_gt (s.lo_pos i)) (s.support i h).1
  have hzW (W:𝓢(ℝ,ℂ))(hs:Function.support (W:ℝ→ℂ)⊆Set.Icc wlo whi):W 0=0:=by
    by_contra h
    exact (not_le_of_gt hwlo) (hs h).1
  unfold coefficient at hn
  rw [he₁,he₂] at hv0
  have hp:=profileCoefficient_product_bound R s.ν s.W s.P hi W₁ W₂ whi whi
    s.X₁ s.X₂ s.Y₁ s.Y₂ (s.X₁*s.X₂) 1 1 seed
    s.P_pos s.X₁_pos s.X₂_pos s.Y₁_pos s.Y₂_pos one_ne_zero one_ne_zero rfl s.same_product
    hz (hzW W₁ hs₁) (hzW W₂ hs₂) (fun i x hx=>((s.support i hx).2).trans (hshi i))
    (fun x hx=>(hs₁ hx).2) (fun x hx=>(hs₂ hx).2) v hv0
  rw [hvI] at hp
  apply hp.2.trans_eq
  simp only [map_one,Nat.cast_one,one_mul,div_one,volume]
  ring

lemma kernel_inverse_cap (HN Z B Tsec:ℝ)(hZ:1≤Z)(hB:0≤B)(hT:0<Tsec)(hcap:Tsec≤Z^B):
    ((min 1 (kernelReference Tsec HN))^2)⁻¹≤
      (1+Real.exp (2*HN))^2*(Z^B)^2:=by
  have hz:0<Z:=zero_lt_one.trans_le hZ
  have hpow:1≤Z^B:=Real.one_le_rpow hZ hB
  have he:0<Real.exp (2*HN):=Real.exp_pos _
  have hb:(min 1 (kernelReference Tsec HN))⁻¹≤(1+Real.exp (2*HN))*Z^B:=by
    rw [min_def]
    split_ifs with h
    · simp only [inv_one]
      nlinarith
    · have hi:(kernelReference Tsec HN)⁻¹=Tsec*Real.exp (2*HN):=by
        unfold kernelReference
        rw [show -2*HN= -(2*HN) by ring,Real.exp_neg]
        field_simp
      rw [hi]
      calc
        _≤Z^B*Real.exp (2*HN):=mul_le_mul_of_nonneg_right hcap he.le
        _≤_:=by nlinarith [Real.rpow_pos_of_pos hz B]
  rw [←inv_pow]
  exact (pow_le_pow_left₀ (inv_nonneg.mpr (le_of_lt (lt_min zero_lt_one (kernelReference_pos Tsec HN hT)))) hb 2).trans_eq (mul_pow _ _ _)

lemma eventually_tail_threshold (HN ξ:ℝ)(hξ:0<ξ):
    ∀ᶠZ:ℝ in atTop,1<Z ∧ 2*HN/Real.log Z+Real.log (4:ℝ)/Real.log Z<ξ/4:=by
  filter_upwards [eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_gt_atTop ((2*HN+Real.log (4:ℝ))/(ξ/4)))] with Z hZ hlog
  refine ⟨hZ,?_⟩
  rw [←add_div]
  apply (div_lt_iff₀ (Real.log_pos hZ)).mpr
  have ht:0<ξ/4:=by linarith
  have hh:2*HN+Real.log (4:ℝ)<Real.log Z*(ξ/4):=(div_lt_iff₀ ht).mp hlog
  nlinarith

lemma choose_tail_order (B ξ saving:ℝ)(hB:0≤B)(hξ:0<ξ):
    ∃Adec:ℕ,∀(HN Z V Tsec:ℝ),1≤Z→0<V→V≤Z^B→0<Tsec→Tsec≤Z^B→
      V^3*((min 1 (kernelReference Tsec HN))^2)⁻¹*((1+Z^(ξ/4))^Adec)⁻¹≤
        (1+Real.exp (2*HN))^2*Z^(-saving):=by
  obtain ⟨Adec,hAdec⟩:=exists_nat_ge ((5*B+saving)/(ξ/4))
  have horder:5*B-(ξ/4)*(Adec:ℝ)≤-saving:=by
    have hh:5*B+saving≤(Adec:ℝ)*(ξ/4):=(div_le_iff₀ (by linarith:0<ξ/4)).mp hAdec
    linarith
  refine ⟨Adec,?_⟩
  intro HN Z V Tsec hZ hV hVcap hT hTcap
  have hz:0<Z:=zero_lt_one.trans_le hZ
  have hk:=kernel_inverse_cap HN Z B Tsec hZ hB hT hTcap
  have hd:=reciprocal_cutoff_bound Z (ξ/4) Adec hz
  calc
    _≤(Z^B)^3*((1+Real.exp (2*HN))^2*(Z^B)^2)*Z^(-(ξ/4)*(Adec:ℝ)):=by
      apply mul_le_mul _ hd (by positivity) (by positivity)
      apply mul_le_mul (pow_le_pow_left₀ hV.le hVcap 3) hk
        (inv_nonneg.mpr (sq_nonneg _)) (by positivity)
    _=(1+Real.exp (2*HN))^2*Z^(5*B-(ξ/4)*(Adec:ℝ)):=by
      rw [←Real.rpow_mul_natCast hz.le,←Real.rpow_mul_natCast hz.le]
      norm_num only [Nat.cast_ofNat]
      rw [show Z^(B*(3:ℝ))*((1+Real.exp (2*HN))^2*Z^(B*(2:ℝ)))*Z^(-(ξ/4)*(Adec:ℝ))=
        (1+Real.exp (2*HN))^2*(Z^(B*3)*Z^(B*2)*Z^(-(ξ/4)*(Adec:ℝ))) by ring]
      rw [←Real.rpow_add hz,←Real.rpow_add hz]
      congr 2
      ring
    _≤_:=mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ horder) (sq_nonneg _)

omit [DecidableEq ι] in
theorem second_input_tail_arbitrary_saving (hi:ι→ℝ)(wlo whi B ξ saving:ℝ)
    (hhi:∀i,0≤hi i)(hwlo:0<wlo)(hwhi:0≤whi)(hB:0≤B)(hξ:0<ξ):
    ∃SΦ:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(s:Input ι)(W₁ W₂:𝓢(ℝ,ℂ)),s.W₁=W₁→s.W₂=W₂→
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc wlo whi→
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc wlo whi→
      (∀i,s.hi i≤hi i)→∀(R seed:Ideal O)(Φ:𝓢(ℝ,ℂ))(K Tsec:ℝ),
      0<K→volume s.toData≤Z^B→Tsec≤Z^B→(volume s.toData)^2/K≤Tsec→
      ‖secondDiscardedEnergy s.η s.t (finiteColumns (Fintype.piFinset s.pools))
        (coefficient s R seed) Φ K Tsec Z ξ‖/volume s.toData≤
      C*(plainControl s W₁ W₂)^2*SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K*Z^(-saving):=by
  obtain ⟨Adec,hdecay⟩:=choose_tail_order B ξ saving hB hξ
  obtain ⟨SΦ,Ctail,hCtail,htail⟩:=second_discarded_energy_bound Adec
  let Cmass:=1+2*128^(Fintype.card ι+2)*(∏i,hi i)*whi^2
  have hprodhi:0≤∏i,hi i:=Finset.prod_nonneg (fun i _=>hhi i)
  have hCmass:0<Cmass:=by dsimp [Cmass];positivity
  let HN:=Real.log (max 1 ((∏i,hi i)*whi^2))
  have hexp:(∏i,hi i)*whi^2≤Real.exp HN:=by
    dsimp [HN]
    rw [Real.exp_log (zero_lt_one.trans_le (le_max_left _ _))]
    exact le_max_right _ _
  let C:=Cmass^2*Ctail*(Real.exp HN)^2*(1+Real.exp (2*HN))^2
  refine ⟨SΦ,C,by dsimp [C];positivity,?_⟩
  filter_upwards [eventually_tail_threshold HN ξ hξ] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s W₁ W₂ he₁ he₂ hs₁ hs₂ hshi R seed Φ K Tsec hK hVcap hTcap hnom
  let V:=volume s.toData
  have hV:0<V:=volume_pos s
  have hT:0<Tsec:=(div_pos (sq_pos_of_pos hV) hK).trans_le hnom
  have hmass:=input_mass hi whi hhi hwhi s W₁ W₂ wlo hwlo he₁ he₂ hs₁ hs₂ hshi R seed
  have hcontrol:=plainControl_nonneg s W₁ W₂
  have hm:(∑I∈finiteColumns (Fintype.piFinset s.pools),‖coefficient s R seed I‖)≤
      Cmass*plainControl s W₁ W₂*V:=by
    apply hmass.trans
    apply mul_le_mul_of_nonneg_right _ hV.le
    apply mul_le_mul_of_nonneg_right _ hcontrol
    dsimp [Cmass]
    linarith
  have hn (I:Ideal O)(_hI:I∈finiteColumns (Fintype.piFinset s.pools))
      (hI:coefficient s R seed I≠0):(Ideal.absNorm I:ℝ)≤Real.exp HN*V:=
    (input_column_bound hi whi s W₁ W₂ wlo hwlo he₁ he₂ hs₁ hs₂ hshi R seed I hI).trans
      (mul_le_mul_of_nonneg_right hexp hV.le)
  have ht:=htail s.η s.t (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R seed)
    Φ K V HN Tsec Z 1 ξ hK hV hZ.1 le_rfl hn hnom (by simpa using hZ.2)
  have hsquare:=pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _=>norm_nonneg _)) hm 2
  have hp:0< min 1 (kernelReference Tsec HN):=lt_min zero_lt_one (kernelReference_pos _ _ hT)
  have hzpos:0<Z:=zero_lt_one.trans hZ.1
  have hzpower:0<Z^(ξ/4):=Real.rpow_pos_of_pos hzpos _
  have hden:0<(min 1 (kernelReference Tsec HN))^2*(1+Z^(ξ/4))^Adec:=by positivity
  have hb:=hdecay HN Z V Tsec hZ.1.le hV hVcap hT hTcap
  calc
    _≤((Cmass*plainControl s W₁ W₂*V)^2*K*(Real.exp HN*V)^2*
        (Ctail*SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ)/
        ((min 1 (kernelReference Tsec HN))^2*(1+Z^(ξ/4))^Adec))/V:=by
      apply div_le_div_of_nonneg_right _ hV.le
      apply ht.trans
      apply div_le_div_of_nonneg_right _ hden.le
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      exact mul_le_mul_of_nonneg_right hsquare hK.le
    _=(Cmass^2*Ctail*(Real.exp HN)^2*(plainControl s W₁ W₂)^2*
        SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K)*
        (V^3*((min 1 (kernelReference Tsec HN))^2)⁻¹*((1+Z^(ξ/4))^Adec)⁻¹):=by
      field_simp [ne_of_gt hV,ne_of_gt hp]
    _≤(Cmass^2*Ctail*(Real.exp HN)^2*(plainControl s W₁ W₂)^2*
        SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K)*
        ((1+Real.exp (2*HN))^2*Z^(-saving)):=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _=_:=by dsimp [C];ring

end SevenEighths.CenteredMomentSourceInputTailUniform

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondSourceRemainder
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter MeasureTheory

namespace SevenEighths.CenteredMomentSecondSourceRemainder
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss UniqueFactorizationMonoid
open CenteredMomentCommonRadialData CenteredMomentCommonWindowColumn CenteredMomentReflectedSource
open CenteredMomentCommonSectorWindow CenteredMomentSecondSectorColumns
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentExceptionalAmplitudePair
open CenteredMomentLogDyadic RayFourExpansion CenteredMomentSmooth
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonExceptionalCost
open CenteredMomentExceptionalSourceShell CenteredMomentExceptionalHeight CenteredMomentSecondHeightFamily
open CenteredMomentSecondExceptionalPairBound
open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalCommon
open CenteredMomentSecondCanonical
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentForcing CenteredMomentChildRows
open CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondWholeKernel CenteredMomentSectorLocalization
open CenteredMomentSecondDyadicRowSupport

open CenteredMomentRankinRadical
open ConcretePrimeRowBridge CenteredMomentMobiusRegroup CenteredMomentSupportedCorrelation
open CenteredMomentSupport CenteredMomentSecondCanonicalScalar CenteredMomentSecondDivisorSupport
local notation "O" => HeckeFamily.O
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

open CenteredMomentSecondExceptionalFamily
open CenteredMomentSecondEnergySplit CenteredMomentSecondLiveBlock
open CenteredMomentOriginalCommonHarmonic
open CenteredMomentFiniteProfileExceptionalPhysical

open CenteredMomentSecondExceptionalFixedQChosenBlock
open CenteredMomentSecondBlockRadicalHarmonicMass
open CenteredMomentSecondRetainedAggregate
open CenteredMomentActiveSource

open CenteredMomentOriginalChildEnergy CenteredMomentSecondLocalization
open CenteredMomentSourceSecondZeroEnergy CenteredMomentSourceInputTailUniform
open CenteredMomentSupportedTailAggregate EisensteinSchwartzPoisson

attribute [local instance] OAI.SevenEighths.CenteredMomentSecondSourceRemainder.instDecidableEqSumFinOfNatNat_definitions
theorem original_source_remainder_oai (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)
    (lo hi:ι→ℝ)(hhi:∀i,0≤hi i)(W:𝓢(ℝ,ℂ))
    (ε δ θ B ξ saving:ℝ)(hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hξ:0<ξ):
    ∃J:ℕ,∃Sprofile SΦ:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧
      ∃Cexc Cdiag Ctail:ℝ,0≤Cexc ∧ 0<Cdiag ∧ 0<Ctail ∧
      ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} →
      ∃Kc:ℝ,0<Kc ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(s:Input ι)(p:Profiles wlo whi),(∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) →
      (∀i,1≤ s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀(R0 seed:Ideal O),R0≠0 → Squarefree seed → seed≠0 →
      0≤ sourceRadius s → sourceRadius s≤Z^B →
      (s.η.modulus.absNorm:ℝ)≤Z^B → (R0.absNorm:ℝ)≤Z^B →
      let S:=finiteColumns (Fintype.piFinset s.pools)
      let β:=coefficient s R0 seed
      ∀χ₀:RayCharacter,∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
      ∀(Tsec Kphys:ℝ),0<Kphys → volume s.toData≤Z^B → Tsec≤Z^B →
      (volume s.toData)^2/Kphys≤Tsec →
      let R:=frequencyRadius Tsec Z ξ
      0<R → R≤Z^B →
      ∀r:ℝ,Z^r≤ s.X₁ → Z^r≤ s.X₂ → Z^r≤ s.Y₁ → Z^r≤ s.Y₂ →
      ‖sourceGaussEnergy S β (heightCoeff s.η s.t) W Kphys-
        partEnergy false s.η χ₀ Q m s.t S β W Kphys Tsec Z ξ (sourceRadius s)‖/volume s.toData≤
      Cdiag*Kphys*‖paperRadialFourier W 0‖*
        (2*SchwartzMap.seminorm ℝ 0 0 (p.profile 0)*SchwartzMap.seminorm ℝ 0 0 (p.profile 1)*(∏i,s.M i))^2*
        (1+(∏i,hi i)*whi*whi)^(1+ε)*(volume s.toData)^ε/(seed.absNorm:ℝ)+
      Cexc*profileFactor Sprofile s p J Q Kc*
        Z^(2*ε+2*δ+2*(5*B+1)*θ-2*max r 0/3)*
        (volume s.toData)^(1/3:ℝ)*Kphys^(5/6:ℝ)*((∏i,s.lo i)*wlo*wlo)^(-2/3:ℝ)/(seed.absNorm:ℝ)+
      Ctail*(plainControl s (p.profile 0) (p.profile 1))^2*
        SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) W*Kphys*Z^(-saving):=by
  obtain ⟨J,Sprofile,hSp,Cexc,hCexc,hexc⟩:=
    CenteredMomentSecondExceptionalUniformSource.original_exceptional_energy
      wlo whi hwlo hwhi lo hi W ε δ θ B hε hδ hθ hB
  obtain ⟨Cdiag,hCdiag,hdiag⟩:=CenteredMomentSecondSourceDiagonal.actual_second_zero (Fintype.card ι) ε hε
  obtain ⟨SΦ,Ctail,hCtail,htail⟩:=second_input_tail_arbitrary_saving hi wlo whi B ξ saving hhi hwlo hwhi hB hξ
  refine ⟨J,Sprofile,SΦ,hSp,Cexc,Cdiag,Ctail,hCexc,hCdiag,hCtail,?_⟩
  intro Q hQ hQt hQ72
  obtain ⟨Kc,hKc,hexc⟩:=hexc Q hQ hQt hQ72
  refine ⟨Kc,hKc,?_⟩
  filter_upwards [hexc,htail] with Z hZ htZ
  refine ⟨hZ.1,?_⟩
  intro s p hlo hhis hP hw1 hw2 R0 seed hR0 hseed hseed0 hH0 hH hη hR0N S β χ₀ m hm hml hm2
    Tsec Kphys hKphys hVcap hTcap hnom R hR hRcap r hX1 hX2 hY1 hY2
  have hz (i:Fin 2):p.profile i 0=0:=by
    by_contra hn
    exact (not_le_of_gt hwlo) (p.support i hn).1
  have hz1:s.W₁ 0=0:=by rw [hw1];exact hz 0
  have hz2:s.W₂ 0=0:=by rw [hw2];exact hz 1
  have hboundI:∀I∈S,β I≠0→(I.absNorm:ℝ)≤ sourceRadius s:=
    fun I _ hn=>(original_column_norm s R0 seed I hz1 hz2 hn).2
  have he:=sourceGaussEnergy_localized s.η s.t S β W Kphys Tsec Z ξ hKphys
  rw [original_energy_split s.η χ₀ Q m s.t S β W Kphys Tsec Z ξ (sourceRadius s) hKphys hboundI] at he
  have hrem:sourceGaussEnergy S β (heightCoeff s.η s.t) W Kphys-
      partEnergy false s.η χ₀ Q m s.t S β W Kphys Tsec Z ξ (sourceRadius s)=
      ((Kphys:ℂ)*paperRadialFourier W 0)*sourceSecondZero S β s.η s.t+
      partEnergy true s.η χ₀ Q m s.t S β W Kphys Tsec Z ξ (sourceRadius s)+
      secondDiscardedEnergy s.η s.t S β W Kphys Tsec Z ξ:=by rw [he];ring
  have hd:=hdiag (ι:=ι) le_rfl wlo whi hwlo hwhi s p hw1 hw2 R0 seed hseed0
    ((Kphys:ℂ)*paperRadialFourier W 0)
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hKphys] at hd
  have hhiEq:(∏i,max 0 (s.hi i))=∏i,hi i:=by
    apply Finset.prod_congr rfl
    intro i _
    rw [hhis i,max_eq_right (hhi i)]
  rw [hhiEq] at hd
  have hex:=hZ.2 s p hlo hhis hP hw1 hw2 R0 seed hR0 hseed hseed0 hH0 hH hη hR0N
    χ₀ m hm hml hm2 Tsec ξ Kphys hKphys hR hRcap r hX1 hX2 hY1 hY2
  have ht:=htZ.2 s (p.profile 0) (p.profile 1) hw1 hw2 (p.support 0) (p.support 1)
    (fun i=>(hhis i).le) R0 seed W Kphys Tsec hKphys hVcap hTcap hnom
  rw [hrem]
  calc
    _≤(‖((Kphys:ℂ)*paperRadialFourier W 0)*sourceSecondZero S β s.η s.t‖+
      ‖partEnergy true s.η χ₀ Q m s.t S β W Kphys Tsec Z ξ (sourceRadius s)‖+
      ‖secondDiscardedEnergy s.η s.t S β W Kphys Tsec Z ξ‖)/volume s.toData:=by
      exact div_le_div_of_nonneg_right ((norm_add_le _ _).trans
        (add_le_add (norm_add_le _ _) le_rfl)) (CenteredMomentExceptionalAmplitudePair.volume_pos s.toData).le
    _=_:=by rw [add_div,add_div]
    _≤_:=by
      apply add_le_add (add_le_add _ hex) ht
      simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hKphys]
      convert (preTransparency := .instances) hd using 1 ; ring

end SevenEighths.CenteredMomentSecondSourceRemainder

end

end OAI
end

theorem solution.{u} : type_of% @OAI.SevenEighths.CenteredMomentSecondSourceRemainder.original_source_remainder_oai.{u} := @OAI.SevenEighths.CenteredMomentSecondSourceRemainder.original_source_remainder_oai.{u}
