-- Prove2me | solution 1 for GlobalTheory.QNorm.hilbert90_sUnits_quadratic_extension_qnorm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:39:03.356841+00:00
-- url     : https://prove2.me/submissions/2a3f8ed0-b10b-4faa-85d0-8fa206d1ac20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsQuadraticSqrtExtensionBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_WithZeroEqOfLeExpIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_HeightOneSpectrumPlacesOverFiniteSet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ValuationUnramifiedOfUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsSupersetMemSUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUnitValuationEqOfAdm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_Hilbert90SUnitsQuadraticExtension
import Theorems.Thm_GlobalTheory_QNorm_IsQuad_root_ne_zero
import Theorems.Thm_GlobalTheory_QNorm_conj_places_transitive
import Theorems.Thm_GlobalTheory_QNorm_exists_unit_valuation_eq_of_adm
import Theorems.Thm_GlobalTheory_QNorm_finite_valuation_ne_one
import Theorems.Thm_GlobalTheory_QNorm_isQuad_basic
import Theorems.Thm_GlobalTheory_QNorm_mem_sUnits
import Theorems.Thm_GlobalTheory_QNorm_places_over

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
namespace GlobalTheory.QNorm
open NumberField IsDedekindDomain in
open scoped WithZero in
private lemma eq_one_of_sq_eq_one_withZero_int {r : WithZero (Multiplicative ℤ)} (h : r ^ 2 = 1) :
    r = 1 := by
  rcases lt_trichotomy r 1 with hr | hr | hr
  · exact absurd h (ne_of_lt (pow_lt_one₀ zero_le' hr two_ne_zero))
  · exact hr
  · exact absurd h (ne_of_gt (one_lt_pow₀ hr two_ne_zero))
open NumberField IsDedekindDomain in
open scoped WithZero in
private lemma valuation_algebraMap_eq_of_unit_at_under {F E : Type} [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] {δ : F} {θ : E} {σ : E ≃ₐ[F] E}
    (hq : _root_.GlobalTheory.QNorm.IsQuad δ θ σ) (w : HeightOneSpectrum (𝓞 E))
    (h2 : (w.under (𝓞 F)).valuation F 2 = 1) (hδ : (w.under (𝓞 F)).valuation F δ = 1) (c : F) :
    w.valuation E (algebraMap F E c) = (w.under (𝓞 F)).valuation F c := by
  obtain ⟨-, -, hram⟩ := _root_.GlobalTheory.QNorm.places_over F E
  obtain ⟨e, he0, hw⟩ := hram w
  set v := w.under (𝓞 F)
  set V := w.valuation E
  suffices he : e = 1 by rw [hw, he, pow_one]
  have hV2 : V 2 = 1 := by
    have := hw 2
    rw [map_ofNat] at this
    rw [this, h2, one_pow]
  have hθ : V θ = 1 := by
    apply eq_one_of_sq_eq_one_withZero_int
    rw [← map_pow, hq.sq, hw, hδ, one_pow]
  have hσθ := hq.conj
  have hθ0 := hq.root_ne_zero
  obtain ⟨x, hx⟩ := HeightOneSpectrum.valuation_exists_uniformizer E w
  obtain ⟨a, b, hab⟩ := hq.span x
  have hσx : σ x = algebraMap F E a - algebraMap F E b * θ := by
    rw [hab, map_add, map_mul, AlgEquiv.commutes, AlgEquiv.commutes, hσθ]; ring
  obtain ⟨-, -, -, hnorm, -⟩ := _root_.GlobalTheory.QNorm.isQuad_basic F E δ θ σ hq
  obtain ⟨a', b', hN⟩ := hnorm x
  have hbθ : V (algebraMap F E b * θ) = V (algebraMap F E b) := by rw [map_mul, hθ, mul_one]
  have hA : V x ≤ max (V (algebraMap F E a)) (V (algebraMap F E b)) := by
    rw [hab, ← hbθ]; exact Valuation.map_add _ _ _
  have hB : V (σ x) ≤ max (V (algebraMap F E a)) (V (algebraMap F E b)) := by
    rw [hσx, ← hbθ]; exact Valuation.map_sub _ _ _
  have ha : V (algebraMap F E a) ≤ max (V x) (V (σ x)) := by
    have h' : algebraMap F E a = (x + σ x) * (2 : E)⁻¹ := by
      rw [hσx, hab]; field_simp; ring
    rw [h', map_mul, map_inv₀, hV2, inv_one, mul_one]
    exact Valuation.map_add _ _ _
  have hb : V (algebraMap F E b) ≤ max (V x) (V (σ x)) := by
    have h' : algebraMap F E b = (x - σ x) * (2 * θ)⁻¹ := by
      rw [hσx, hab]; field_simp; ring
    rw [h', map_mul, map_inv₀, map_mul, hV2, hθ, one_mul, inv_one, mul_one]
    exact Valuation.map_sub _ _ _
  have hmax : max (V x) (V (σ x)) = max (V (algebraMap F E a)) (V (algebraMap F E b)) :=
    le_antisymm (max_le hA hB) (max_le ha hb)
  have hx0 : V x ≠ 0 := by rw [hx]; exact WithZero.exp_ne_zero
  have key : ∃ d : F, V x = v.valuation F d ^ e := by
    have hmem : max (V x) (V (σ x)) = V (algebraMap F E a) ∨
        max (V x) (V (σ x)) = V (algebraMap F E b) := by
      rw [hmax]; exact max_choice _ _
    rcases le_total (V (σ x)) (V x) with hle | hle
    · rw [max_eq_left hle] at hmem
      rcases hmem with h | h
      · exact ⟨a, h.trans (hw a)⟩
      · exact ⟨b, h.trans (hw b)⟩
    · rw [max_eq_right hle] at hmem
      have hc : ∃ c : F, V (σ x) = V (algebraMap F E c) := by
        rcases hmem with h | h
        · exact ⟨a, h⟩
        · exact ⟨b, h⟩
      obtain ⟨c, hc⟩ := hc
      have hσ0 : V (σ x) ≠ 0 := ne_of_gt (lt_of_lt_of_le (zero_lt_iff.mpr hx0) hle)
      refine ⟨(a' ^ 2 - δ * b' ^ 2) / c, ?_⟩
      rw [← hw, map_div₀, map_div₀, ← hN, ← hc, map_mul, mul_div_cancel_right₀ _ hσ0]
  obtain ⟨d, hd⟩ := key
  rw [hx] at hd
  have hl := congrArg WithZero.log hd
  rw [WithZero.log_exp, WithZero.log_pow, nsmul_eq_mul] at hl
  rcases Int.eq_one_or_neg_one_of_mul_eq_neg_one hl.symm with h1 | h1 <;> omega
end GlobalTheory.QNorm
end

set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
open GlobalTheory GlobalTheory.QNorm
open NumberField IsDedekindDomain
open scoped WithZero
namespace GlobalTheory.QNorm
namespace _root_.GlobalTheory.QNorm
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] (δ : F) (θ : E) (σ : E ≃ₐ[F] E), _root_.GlobalTheory.QNorm.IsQuad δ θ σ →
    ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (SE : Finset (HeightOneSpectrum (𝓞 E))),
    (∀ w : HeightOneSpectrum (𝓞 E), w ∈ SE ↔ w.under (𝓞 F) ∈ S) → _root_.GlobalTheory.QNorm.admitted F S →
    (∀ v, v ∉ S → v.valuation F δ = 1) → ∀ u : Eˣ, u ∈ _root_.GlobalTheory.QNorm.sUnits E SE →
    (u : E) * σ u = 1 → ∃ y : Eˣ, y ∈ _root_.GlobalTheory.QNorm.sUnits E SE ∧ (u : E) = y / σ y := by
  intro F E _ _ _ _ _ δ θ σ hq S SE hSE hS hδ u hu hnu
  classical
  obtain ⟨-, -, -, -, h90, -⟩ := _root_.GlobalTheory.QNorm.isQuad_basic F E δ θ σ hq
  obtain ⟨y, hy0, hy⟩ := h90 u hnu
  obtain ⟨-, hover, -⟩ := _root_.GlobalTheory.QNorm.places_over F E
  obtain ⟨-, hdich⟩ := _root_.GlobalTheory.QNorm.conj_places_transitive F E δ θ σ hq
  choose ch hch using hover
  rw [_root_.GlobalTheory.QNorm.mem_sUnits] at hu
  have hadm := hS
  unfold _root_.GlobalTheory.QNorm.admitted at hadm
  have hinv : ∀ w : HeightOneSpectrum (𝓞 E), w ∉ SE →
      w.valuation E (σ y) = w.valuation E y := by
    intro w hw
    have h1 := hu w hw
    rw [hy, map_div₀] at h1
    have hσy0 : w.valuation E (σ y) ≠ 0 :=
      (Valuation.ne_zero_iff _).mpr ((map_ne_zero σ).mpr hy0)
    exact ((div_eq_one_iff_eq hσy0).mp h1).symm
  have hfib : ∀ w : HeightOneSpectrum (𝓞 E), w ∉ SE →
      w.valuation E y = (ch (w.under (𝓞 F))).valuation E y := by
    intro w hw
    have hv : (ch (w.under (𝓞 F))).under (𝓞 F) = w.under (𝓞 F) := hch _
    have hw0 : ch (w.under (𝓞 F)) ∉ SE := by
      rw [hSE, hv]; rwa [hSE] at hw
    rcases hdich (ch (w.under (𝓞 F))) w hv.symm with h | h
    · rw [← h]
    · rw [h y, hinv _ hw0]
  let n : HeightOneSpectrum (𝓞 F) → ℤ := fun v =>
    if v ∈ S then 0 else -((ch v).valuation E y).log
  have hfin := _root_.GlobalTheory.QNorm.finite_valuation_ne_one E (Units.mk0 y hy0)
  let T : Finset (HeightOneSpectrum (𝓞 F)) :=
    hfin.toFinset.image (fun w => w.under (𝓞 F))
  have hnT : ∀ v ∉ T, n v = 0 := by
    intro v hv
    by_cases hvS : v ∈ S
    · simp [n, hvS]
    · have h1 : (ch v).valuation E y = 1 := by
        by_contra hne
        apply hv
        refine Finset.mem_image.mpr ⟨ch v, ?_, hch v⟩
        rw [Set.Finite.mem_toFinset]
        exact hne
      simp [n, hvS, h1]
  obtain ⟨a, ha⟩ := _root_.GlobalTheory.QNorm.exists_unit_valuation_eq_of_adm F S T n hS hnT
  have ha0 : algebraMap F E a ≠ 0 := by simp
  refine ⟨Units.mk0 (y * algebraMap F E a) (mul_ne_zero hy0 ha0), ?_, ?_⟩
  · rw [_root_.GlobalTheory.QNorm.mem_sUnits]
    intro w hw
    have hvS : w.under (𝓞 F) ∉ S := by rwa [hSE] at hw
    show w.valuation E (y * algebraMap F E a) = 1
    rw [map_mul, valuation_algebraMap_eq_of_unit_at_under hq w (hadm _ hvS).1 (hδ _ hvS), ha _ hvS,
      hfib w hw]
    have h0 : (ch (w.under (𝓞 F))).valuation E y ≠ 0 := (Valuation.ne_zero_iff _).mpr hy0
    simp only [n, if_neg hvS]
    nth_rewrite 1 [← WithZero.exp_log h0]
    rw [← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero]
  · show (u : E) = y * algebraMap F E a / σ (y * algebraMap F E a)
    rw [hy, map_mul, AlgEquiv.commutes, mul_div_mul_right _ _ ha0]
end _root_.GlobalTheory.QNorm
end GlobalTheory.QNorm
