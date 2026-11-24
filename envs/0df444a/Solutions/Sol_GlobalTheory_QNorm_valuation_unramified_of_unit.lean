-- Prove2me | solution 1 for GlobalTheory.QNorm.valuation_unramified_of_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:57:42.373229+00:00
-- url     : https://prove2.me/submissions/9a9b172e-4e61-4d46-b23d-5f02acc5fb17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_HeightOneSpectrumPlacesOverFiniteSet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ValuationUnramifiedOfUnit
import Theorems.Thm_GlobalTheory_QNorm_IsQuad_exists_base_value
import Theorems.Thm_GlobalTheory_QNorm_places_over


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
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (δ : F) (θ : E) (σ : E ≃ₐ[F] E), IsQuad δ θ σ → ∀ w : HeightOneSpectrum (𝓞 E), (w.under (𝓞 F)).valuation F 2 = 1 → (w.under (𝓞 F)).valuation F δ = 1 → ∀ x : F, w.valuation E (algebraMap F E x) = (w.under (𝓞 F)).valuation F x := by
  intro F E _ _ _ _ _ δ θ σ hq w h2 hδ
  obtain ⟨e, he, hw⟩ := (places_over F E).2.2 w
  obtain ⟨π, hπ⟩ := w.valuation_exists_uniformizer E
  have h2' : w.valuation E 2 = 1 := by
    have := hw 2
    rwa [map_ofNat, h2, one_pow] at this
  obtain ⟨u, hu⟩ := hq.exists_base_value (w.valuation E) h2' (by rw [hw, hδ, one_pow]) π
  rw [hπ, hw] at hu
  have hu0 : (w.under (𝓞 F)).valuation F u ≠ 0 := by
    intro h0
    rw [h0, zero_pow he.ne'] at hu
    exact WithZero.exp_ne_zero hu
  rw [← WithZero.exp_log hu0, ← WithZero.exp_nsmul, WithZero.exp_inj, nsmul_eq_mul] at hu
  have h1 : (e : ℤ) ∣ 1 := ⟨-WithZero.log ((w.under (𝓞 F)).valuation F u), by linear_combination -hu⟩
  have h3 : e = 1 := by
    have : e ∣ 1 := by exact_mod_cast h1
    exact Nat.dvd_one.1 this
  intro x
  rw [hw, h3, pow_one]
end GlobalTheory.QNorm
