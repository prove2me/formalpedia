-- Prove2me | solution 1 for GlobalTheory.QNorm.two_places_of_isSquare
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:58:57.148934+00:00
-- url     : https://prove2.me/submissions/661203ce-5158-40b4-b2be-5a6aec2c6d03

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsQuadraticSqrtExtensionBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsTwoPlacesOverOfIsSquareLocal
import Theorems.Thm_GlobalTheory_QNorm_val_integer_le_one
import Theorems.Thm_GlobalTheory_QNorm_exists_centre_over
import Theorems.Thm_GlobalTheory_QNorm_IsQuad_exists_embedding_root
import Theorems.Thm_GlobalTheory_QNorm_exists_val_sub_mul_lt_one
import Theorems.Thm_GlobalTheory_QNorm_IsQuad_coord_indep
import Theorems.Thm_GlobalTheory_QNorm_IsQuad_root_ne_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
open GlobalTheory GlobalTheory.QNorm
namespace GlobalTheory.QNorm
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (δ : F) (θ : E) (σ : E ≃ₐ[F] E), IsQuad δ θ σ → ∀ v : HeightOneSpectrum (𝓞 F), IsSquare (algebraMap F (v.adicCompletion F) δ) → ∃ w w' : HeightOneSpectrum (𝓞 E), w ≠ w' ∧ w.under (𝓞 F) = v ∧ w'.under (𝓞 F) = v := by
  intro F E _ _ _ _ _ δ θ σ h v ⟨r, hr⟩
  obtain ⟨ψ, hψ, hθ⟩ := h.exists_embedding_root (algebraMap F (v.adicCompletion F)) r hr
  let u : Valuation E ℤᵐ⁰ := (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰).comap ψ
  let u' : Valuation E ℤᵐ⁰ := u.comap (σ : E →+* E)
  have hu : ∀ a : F, u (algebraMap F E a) = v.valuation F a := by
    intro a
    change Valued.v (ψ _) = _
    rw [hψ]
    exact v.valuedAdicCompletion_eq_valuation' a
  have hu' : ∀ a : F, u' (algebraMap F E a) = v.valuation F a := by
    intro a
    change u (σ _) = _
    rw [AlgEquiv.commutes, hu]
  obtain ⟨w, hw, hwm⟩ := exists_centre_over v u hu
  obtain ⟨w', hw', hwm'⟩ := exists_centre_over v u' hu'
  refine ⟨w, w', ?_, hw, hw'⟩
  rintro rfl
  have hr0 : r ≠ 0 := by
    rw [← hθ]; exact (map_ne_zero ψ).2 h.root_ne_zero
  have h2 : (2 : v.adicCompletion F) ≠ 0 := by
    have : (2 : v.adicCompletion F) = algebraMap F _ 2 := by rw [map_ofNat]
    rw [this]; exact (map_ne_zero _).2 two_ne_zero
  obtain ⟨ρ, hρ⟩ := exists_val_sub_mul_lt_one _ (HeightOneSpectrum.denseRange_algebraMap F v)
    r (2 * r)⁻¹
  set t := (r - algebraMap F (v.adicCompletion F) ρ) * (2 * r)⁻¹ with ht
  have hn : θ - algebraMap F E ρ ≠ 0 := by
    intro h0
    exact one_ne_zero (h.coord_indep (-ρ) 1 (by simp; linear_combination h0)).2
  have hd : -θ - algebraMap F E ρ ≠ 0 := by
    intro h0
    exact one_ne_zero (h.coord_indep ρ 1 (by simp; linear_combination -h0)).2
  set y := (θ - algebraMap F E ρ) / (-θ - algebraMap F E ρ) with hy
  have hy1 : y * σ y = 1 := by
    rw [hy, map_div₀, map_sub, map_sub, map_neg, h.conj, AlgEquiv.commutes, neg_neg]
    field_simp
  have huy : u y < 1 := by
    change Valued.v (ψ y) < 1
    have e1 : r - algebraMap F (v.adicCompletion F) ρ = 2 * r * t := by
      rw [ht]; field_simp
    have e2 : -r - algebraMap F (v.adicCompletion F) ρ = -(2 * r * (1 - t)) := by
      linear_combination e1
    rw [hy, map_div₀, map_sub, map_sub, map_neg, hθ, hψ, e1, e2, map_div₀, Valuation.map_neg,
      map_mul _ _ t, map_mul _ _ (1 - t), Valuation.map_one_sub_of_lt _ hρ, mul_one,
      mul_div_cancel_left₀ _ ((Valuation.ne_zero_iff _).2 (mul_ne_zero h2 hr0))]
    exact hρ
  have huu : u y * u' y = 1 := by
    change u y * u (σ y) = 1
    rw [← map_mul, hy1, map_one]
  obtain ⟨n, ⟨d, hd'⟩, hnd | hnd⟩ := w.exists_primeCompl_mul_eq_or_mul_eq (K := E) y
  · have hd1 : 1 ≤ u' (algebraMap (𝓞 E) E d) := not_lt.1 fun a => hd' ((hwm' d).2 a)
    have h1 : u' y ≤ 1 := by
      have := val_integer_le_one u' n
      rw [← hnd, map_mul] at this
      exact le_trans (le_mul_of_one_le_right' hd1) this
    have : u y * u' y < 1 := lt_of_le_of_lt (mul_le_of_le_one_right' h1) huy
    exact this.ne huu
  · have hd1 : 1 ≤ u (algebraMap (𝓞 E) E d) := not_lt.1 fun a => hd' ((hwm d).2 a)
    rw [← hnd, map_mul] at hd1
    exact absurd (lt_of_le_of_lt (mul_le_of_le_one_right' (val_integer_le_one u n)) huy)
      (not_lt.2 hd1)
end GlobalTheory.QNorm
