-- Prove2me | solution 1 for GlobalTheory.QNorm.sUnits_over_and_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:39:04.894075+00:00
-- url     : https://prove2.me/submissions/6ad34618-4da4-4610-abe8-9ae140101774

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_HeightOneSpectrumPlacesOverFiniteSet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_WithZeroEqOfLeExpIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SUnitsPlacesOverAndQuadraticConj
import Theorems.Thm_GlobalTheory_QNorm_conj_places_transitive
import Theorems.Thm_GlobalTheory_QNorm_mem_sUnits
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
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (δ : F) (θ : E) (σ : E ≃ₐ[F] E), IsQuad δ θ σ → ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (SE : Finset (HeightOneSpectrum (𝓞 E))), (∀ w : HeightOneSpectrum (𝓞 E), w ∈ SE ↔ w.under (𝓞 F) ∈ S) → (∀ x : Fˣ, Units.map (algebraMap F E : F →* E) x ∈ sUnits E SE ↔ x ∈ sUnits F S) ∧ ∀ y : Eˣ, y ∈ sUnits E SE → Units.map (σ : E →* E) y ∈ sUnits E SE := by
  intro F E _ _ _ _ _ δ θ σ hq S SE hS
  obtain ⟨-, hup, hval⟩ := places_over F E
  obtain ⟨hconj, -⟩ := conj_places_transitive F E δ θ σ hq
  refine ⟨fun x => ⟨fun h => ?_, fun h => ?_⟩, fun y hy => ?_⟩
  · rw [mem_sUnits] at h ⊢
    intro v hv
    obtain ⟨w, rfl⟩ := hup v
    obtain ⟨e, he, hx⟩ := hval w
    have h1 : w.valuation E (algebraMap F E (x : F)) = 1 := h w (fun a => hv ((hS w).1 a))
    rw [hx] at h1
    exact (pow_eq_one_iff_of_nonneg zero_le he.ne').1 h1
  · rw [mem_sUnits] at h ⊢
    intro w hw
    obtain ⟨e, he, hx⟩ := hval w
    change w.valuation E (algebraMap F E (x : F)) = 1
    rw [hx, h _ (fun a => hw ((hS w).2 a)), one_pow]
  · rw [mem_sUnits] at hy ⊢
    intro w hw
    obtain ⟨w', hu, hv⟩ := hconj w
    change w.valuation E (σ (y : E)) = 1
    rw [← hv]
    exact hy w' (fun a => hw ((hS w).2 (hu ▸ (hS w').1 a)))
end GlobalTheory.QNorm
