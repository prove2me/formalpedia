-- Prove2me | solution 1 for NumberField.exists_isCompact_forall_tsum_le_mul_rpow_neg_of_principal_equivariant_of_dilation_bound
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/36ac8b53-a4cd-512b-b724-518b5a48778e

import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_TateGlobalZeta
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Theorems.Thm_NumberField_TateGlobal_exists_isCompact_forall_eq_principal_mul_balanced_mul
import Theorems.Thm_NumberField_mixedEmbedding_exists_forall_tsum_fractionalIdeal_weight_le_rpow_neg
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_algebraMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_exists_isCompact_forall_tsum_le_mul_rpow_neg_of_principal_equivariant_of_dilation_bound
p2m_attr_erase "instance" "instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.InfinitePlace
open scoped NNReal Classical

namespace LTSProof

variable (F : Type) [Field F] [NumberField F]

local notation "𝔸" => AdeleRing (𝓞 F) F

private def mulEquiv (η : Fˣ) : {ξ : F // ξ ≠ 0} ≃ {ξ : F // ξ ≠ 0} where
  toFun ξ := ⟨(ξ : F) * η, mul_ne_zero ξ.2 η.ne_zero⟩
  invFun ξ := ⟨(ξ : F) * (η⁻¹ : Fˣ), mul_ne_zero ξ.2 (η⁻¹).ne_zero⟩
  left_inv ξ := by ext; simp [mul_assoc]
  right_inv ξ := by ext; simp [mul_assoc]

private noncomputable def weight (k Nd : ℕ) (r : ℝ) (ξ : F) : ℝ :=
  (max 1 ((|Algebra.norm ℚ ξ| : ℚ) : ℝ)) ^ k *
    (∏ w : {w : InfinitePlace F // w.IsReal}, (1 + r * |(mixedEmbedding F ξ).1 w|) ^ (-(Nd : ℝ))) *
    ∏ w : {w : InfinitePlace F // w.IsComplex}, (1 + r * ‖(mixedEmbedding F ξ).2 w‖) ^ (-(2 * Nd : ℝ))

private theorem weight_nonneg (k Nd : ℕ) (r : ℝ) (hr : 0 ≤ r) (ξ : F) : 0 ≤ weight F k Nd r ξ := by
  unfold weight
  exact mul_nonneg (mul_nonneg (pow_nonneg (by positivity) _) (Finset.prod_nonneg fun w _ => by positivity))
    (Finset.prod_nonneg fun w _ => by positivity)

private theorem rpow_exp_le {t₀ : ℝ} (ht₀ : 0 < t₀) {n : ℕ} {σ₁ σ₂ σ : ℝ} (h1 : σ₁ ≤ σ) (h2 : σ ≤ σ₂) {N : ℕ} {N' : ℝ}
    (hN' : (n : ℝ) * N + n * (1 / 2 - σ₁) ≤ N') {r : ℝ} (hr : t₀ ≤ r) :
    r ^ ((n : ℝ) * (1 / 2 - σ) - N') ≤ max 1 (t₀ ^ ((n : ℝ) * (1 / 2 - σ₂) - N')) * r ^ (-((n : ℝ) * N)) := by
  have hr0 : 0 < r := ht₀.trans_le hr
  have hn : (0 : ℝ) ≤ n := n.cast_nonneg
  have he : (n : ℝ) * (1 / 2 - σ) - N' ≤ -((n : ℝ) * N) := by nlinarith
  have hemin : (n : ℝ) * (1 / 2 - σ₂) - N' ≤ (n : ℝ) * (1 / 2 - σ) - N' := by nlinarith
  rcases le_or_gt 1 r with h1r | hr1
  · calc r ^ ((n : ℝ) * (1 / 2 - σ) - N') ≤ r ^ (-((n : ℝ) * N)) := Real.rpow_le_rpow_of_exponent_le h1r he
      _ ≤ max 1 (t₀ ^ ((n : ℝ) * (1 / 2 - σ₂) - N')) * r ^ (-((n : ℝ) * N)) :=
        le_mul_of_one_le_left (Real.rpow_nonneg hr0.le _) (le_max_left _ _)
  · have hA : r ^ ((n : ℝ) * (1 / 2 - σ) - N') ≤ r ^ ((n : ℝ) * (1 / 2 - σ₂) - N') :=
      Real.rpow_le_rpow_of_exponent_ge hr0 hr1.le hemin
    have hB : r ^ ((n : ℝ) * (1 / 2 - σ₂) - N') ≤ t₀ ^ ((n : ℝ) * (1 / 2 - σ₂) - N') :=
      Real.rpow_le_rpow_of_nonpos ht₀ hr (by nlinarith)
    have hC : (1 : ℝ) ≤ r ^ (-((n : ℝ) * N)) := by
      rw [Real.rpow_neg hr0.le]
      exact one_le_inv_iff₀.mpr ⟨Real.rpow_pos_of_pos hr0 _, Real.rpow_le_one hr0.le hr1.le (by positivity)⟩
    calc r ^ ((n : ℝ) * (1 / 2 - σ) - N') ≤ t₀ ^ ((n : ℝ) * (1 / 2 - σ₂) - N') := hA.trans hB
      _ ≤ max 1 (t₀ ^ ((n : ℝ) * (1 / 2 - σ₂) - N')) := le_max_right _ _
      _ ≤ max 1 (t₀ ^ ((n : ℝ) * (1 / 2 - σ₂) - N')) * r ^ (-((n : ℝ) * N)) :=
        le_mul_of_one_le_right (by positivity) hC

end LTSProof

open LTSProof in
theorem solution
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (Y : Set (AdeleRing (𝓞 F) F)ˣ), IsCompact Y →
      ∃ U' : Set (AdeleRing (𝓞 F) F)ˣ, IsCompact U' ∧
        ∀ (k : ℕ) (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (σ₁ σ₂ c' : ℝ) (N : ℕ), 0 < c' →
          ∃ Nd : ℕ, ∀ c : ℝ, ∃ M : ℝ,
            ∀ (G : {ξ : F // ξ ≠ 0} → (AdeleRing (𝓞 F) F)ˣ → ℝ) (σ : ℝ), σ₁ ≤ σ → σ ≤ σ₂ →
              (∀ ξ y, 0 ≤ G ξ y) →
              (∀ (ξ : {ξ : F // ξ ≠ 0}) (η : Fˣ) (y : (AdeleRing (𝓞 F) F)ˣ),
                G ξ (Units.map (algebraMap F (AdeleRing (𝓞 F) F)) η * y)
                  = G ⟨(ξ : F) * η, mul_ne_zero ξ.2 η.ne_zero⟩ y) →
              (∀ u ∈ U', ∀ (z : (AdeleRing (𝓞 F) F)ˣ) (r : ℝ), 0 < r →
                (z : AdeleRing (𝓞 F) F).2 = 1 →
                (∀ w : InfinitePlace F, Completion.extensionEmbedding w ((z : AdeleRing (𝓞 F) F).1 w) = (r : ℂ)) →
                ∀ ξ : {ξ : F // ξ ≠ 0},
                  ((ξ : F) ∉ I → G ξ (z * u) = 0) ∧
                  G ξ (z * u) ≤ c * r ^ ((Module.finrank ℚ F : ℝ) * (1 / 2 - σ)) *
                    (max 1 ((|Algebra.norm ℚ (ξ : F)| : ℚ) : ℝ)) ^ k *
                    (∏ w : {w : InfinitePlace F // w.IsReal}, (1 + r * |(mixedEmbedding F (ξ : F)).1 w|) ^ (-(Nd : ℝ))) *
                    ∏ w : {w : InfinitePlace F // w.IsComplex},
                      (1 + r * ‖(mixedEmbedding F (ξ : F)).2 w‖) ^ (-(2 * Nd : ℝ))) →
              ∀ (y₁ y₀ : (AdeleRing (𝓞 F) F)ˣ), y₀ ∈ Y → c' ≤ ((α y₁ : ℝˣ) : ℝ) →
                Summable (fun ξ : {ξ : F // ξ ≠ 0} => G ξ (y₁ * y₀)) ∧
                ∑' ξ : {ξ : F // ξ ≠ 0}, G ξ (y₁ * y₀) ≤ M * ((α y₁ : ℝˣ) : ℝ) ^ (-(N : ℝ)) := by
  intro α Y hY
  have hα : ∀ x : (AdeleRing (𝓞 F) F)ˣ, ((α x : ℝˣ) : ℝ) = (distribHaarChar (AdeleRing (𝓞 F) F) x : ℝ) := fun x => rfl

  obtain ⟨U, hUc, hU1, hdec⟩ := NumberField.TateGlobal.exists_isCompact_forall_eq_principal_mul_balanced_mul F
  set U' : Set (AdeleRing (𝓞 F) F)ˣ := (fun p : (AdeleRing (𝓞 F) F)ˣ × (AdeleRing (𝓞 F) F)ˣ => p.1 * p.2) '' (U ×ˢ Y) with hU'
  refine ⟨U', (hUc.prod hY).image continuous_mul, ?_⟩
  intro k I σ₁ σ₂ c' N hc'
  set n : ℕ := Module.finrank ℚ F with hn
  have hn0 : n ≠ 0 := Module.finrank_pos.ne'
  set t₀ : ℝ := c' ^ ((n : ℝ)⁻¹) with ht₀
  have ht₀0 : 0 < t₀ := Real.rpow_pos_of_pos hc' _

  set N' : ℕ := n * N + ⌈(n : ℝ) * (1 / 2 - σ₁)⌉₊ with hN'def
  have hN' : (n : ℝ) * N + n * (1 / 2 - σ₁) ≤ N' := by
    simp only [hN'def]; push_cast
    linarith [Nat.le_ceil ((n : ℝ) * (1 / 2 - σ₁))]
  obtain ⟨N₀, hN₀⟩ := NumberField.mixedEmbedding.exists_forall_tsum_fractionalIdeal_weight_le_rpow_neg F I k N' t₀ ht₀0
  obtain ⟨C, hC⟩ := hN₀ N₀ le_rfl
  refine ⟨N₀, fun c => ?_⟩
  set Cr : ℝ := max 1 (t₀ ^ ((n : ℝ) * (1 / 2 - σ₂) - N')) with hCr
  set M : ℝ := max c 0 * max C 0 * Cr with hM
  refine ⟨M, ?_⟩
  intro G σ hσ1 hσ2 hG0 hGeq hGbd y₁ y₀ hy₀ hy₁

  obtain ⟨η, z, u, r, hu, hr, hy₁eq, hz2, hz1, hαz⟩ := hdec y₁
  have hαη : ((α (Units.map (algebraMap F (AdeleRing (𝓞 F) F)) η) : ℝˣ) : ℝ) = 1 := by
    rw [hα]
    have h' := @NumberField.AdeleRing.distribHaarChar_algebraMap F _ _ (borel _) (@BorelSpace.mk _ _ (borel _) rfl) η
    have e : (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) η)
        = Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom η := Units.ext rfl
    rw [e, h']; rfl
  have hαy₁ : ((α y₁ : ℝˣ) : ℝ) = r ^ n := by
    rw [hy₁eq, map_mul, map_mul, Units.val_mul, Units.val_mul, hαη, hαz, hU1 u hu, one_mul, mul_one]
  have hrt : t₀ ≤ r := by
    have h1 : t₀ ≤ (r ^ n : ℝ) ^ ((n : ℝ)⁻¹) := Real.rpow_le_rpow hc'.le (hαy₁ ▸ hy₁) (by positivity)
    rwa [Real.pow_rpow_inv_natCast hr.le hn0] at h1

  set u' : (AdeleRing (𝓞 F) F)ˣ := u * y₀ with hu'
  have hu'U : u' ∈ U' := ⟨(u, y₀), ⟨hu, hy₀⟩, rfl⟩
  set g : {ξ : F // ξ ≠ 0} → ℝ := fun ξ => G ξ (z * u') with hg
  have hyg : ∀ ξ : {ξ : F // ξ ≠ 0}, G ξ (y₁ * y₀) = g (mulEquiv F η ξ) := by
    intro ξ
    have : y₁ * y₀ = Units.map (algebraMap F (AdeleRing (𝓞 F) F)) η * (z * u') := by
      rw [hy₁eq, hu']; simp only [mul_assoc]
    rw [this, hGeq]
    rfl

  have hbd := hGbd u' hu'U z r hr hz2 hz1
  set Kc : ℝ := max c 0 * r ^ ((n : ℝ) * (1 / 2 - σ)) with hKc
  have hKc0 : 0 ≤ Kc := by positivity
  have hg_le : ∀ ξ : {ξ : F // ξ ≠ 0}, g ξ ≤ Kc * weight F k N₀ r ξ := by
    intro ξ
    refine ((hbd ξ).2).trans ?_
    simp only [hKc, weight, mul_assoc]
    refine mul_le_mul_of_nonneg_right (le_max_left _ _) ?_
    exact mul_nonneg (Real.rpow_nonneg hr.le _) (by
      have := weight_nonneg F k N₀ r hr.le ξ; simpa only [weight, mul_assoc] using this)
  have hg0 : ∀ ξ, 0 ≤ g ξ := fun ξ => hG0 _ _
  have hgI : ∀ ξ : {ξ : F // ξ ≠ 0}, (ξ : F) ∉ I → g ξ = 0 := fun ξ hξ => (hbd ξ).1 hξ

  set ι : {ξ : F // ξ ≠ 0 ∧ ξ ∈ I} → {ξ : F // ξ ≠ 0} := fun ξ => ⟨ξ.1, ξ.2.1⟩ with hι
  have hιinj : Function.Injective ι := by
    intro a b h
    have := congrArg Subtype.val h
    exact Subtype.ext this
  have hsupp : Function.support g ⊆ Set.range ι := by
    intro ξ hξ
    by_cases hI : (ξ : F) ∈ I
    · exact ⟨⟨ξ.1, ξ.2, hI⟩, rfl⟩
    · exact absurd (hgI ξ hI) hξ
  obtain ⟨hWsum, hWle⟩ := hC r hrt
  have hmaj : Summable (fun ξ : {ξ : F // ξ ≠ 0 ∧ ξ ∈ I} => Kc * weight F k N₀ r ξ.1) := hWsum.mul_left Kc
  have hgιsum : Summable (g ∘ ι) :=
    Summable.of_nonneg_of_le (fun ξ => hg0 _) (fun ξ => hg_le _) hmaj
  have hsupp' : ∀ x, x ∉ Set.range ι → g x = 0 := fun x hx =>
    Classical.byContradiction fun h => hx (hsupp h)
  have hgsum : Summable g := (hιinj.summable_iff hsupp').mp hgιsum
  have hgtsum : ∑' ξ, g ξ ≤ Kc * (C * r ^ (-(N' : ℝ))) := by
    rw [← hιinj.tsum_eq hsupp]
    calc ∑' ξ, g (ι ξ) ≤ ∑' ξ : {ξ : F // ξ ≠ 0 ∧ ξ ∈ I}, Kc * weight F k N₀ r ξ.1 :=
          hgιsum.tsum_le_tsum (fun ξ => hg_le _) hmaj
      _ = Kc * ∑' ξ : {ξ : F // ξ ≠ 0 ∧ ξ ∈ I}, weight F k N₀ r ξ.1 := tsum_mul_left
      _ ≤ Kc * (C * r ^ (-(N' : ℝ))) := mul_le_mul_of_nonneg_left hWle hKc0

  have hsumG : Summable (fun ξ : {ξ : F // ξ ≠ 0} => G ξ (y₁ * y₀)) := by
    have : (fun ξ : {ξ : F // ξ ≠ 0} => G ξ (y₁ * y₀)) = g ∘ mulEquiv F η := funext hyg
    rw [this]
    exact (mulEquiv F η).summable_iff.mpr hgsum
  refine ⟨hsumG, ?_⟩
  have htsumG : ∑' ξ : {ξ : F // ξ ≠ 0}, G ξ (y₁ * y₀) = ∑' ξ, g ξ := by
    rw [show (fun ξ : {ξ : F // ξ ≠ 0} => G ξ (y₁ * y₀)) = fun ξ => g (mulEquiv F η ξ) from funext hyg]
    exact (mulEquiv F η).tsum_eq g
  rw [htsumG]
  refine hgtsum.trans ?_

  have hC0 : C ≤ max C 0 := le_max_left _ _
  have hrpow := rpow_exp_le ht₀0 hσ1 hσ2 hN' hrt (n := n) (N := N)
  rw [hαy₁, ← Real.rpow_natCast r n, ← Real.rpow_mul hr.le]
  have e1 : Kc * (C * r ^ (-(N' : ℝ))) = max c 0 * C * (r ^ ((n : ℝ) * (1 / 2 - σ)) * r ^ (-(N' : ℝ))) := by
    simp only [hKc]; ring
  rw [e1, ← Real.rpow_add hr, show (n : ℝ) * (1 / 2 - σ) + -(N' : ℝ) = (n : ℝ) * (1 / 2 - σ) - N' by ring,
    show (n : ℝ) * -(N : ℝ) = -((n : ℝ) * N) by ring]
  calc max c 0 * C * r ^ ((n : ℝ) * (1 / 2 - σ) - N')
      ≤ max c 0 * max C 0 * r ^ ((n : ℝ) * (1 / 2 - σ) - N') :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hC0 (le_max_right _ _)) (Real.rpow_nonneg hr.le _)
    _ ≤ max c 0 * max C 0 * (Cr * r ^ (-((n : ℝ) * N))) :=
        mul_le_mul_of_nonneg_left hrpow (by positivity)
    _ = M * r ^ (-((n : ℝ) * N)) := by simp only [hM]; ring

end S_NumberField_exists_isCompact_forall_tsum_le_mul_rpow_neg_of_principal_equivariant_of_dilation_bound
end P2MW
export P2MW.S_NumberField_exists_isCompact_forall_tsum_le_mul_rpow_neg_of_principal_equivariant_of_dilation_bound (solution)
