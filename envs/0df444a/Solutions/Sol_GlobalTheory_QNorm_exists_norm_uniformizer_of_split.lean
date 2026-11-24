-- Prove2me | solution 1 for GlobalTheory.QNorm.exists_norm_uniformizer_of_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:39:01.782172+00:00
-- url     : https://prove2.me/submissions/9275ad2c-24c2-4f2e-97a6-a4d886bd6137

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_EvenNormsOfUnitNonsquare
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsAdmissibleSupersetFinitePlaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsSupersetMemSUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsIsQuadraticSqrtExtensionOfNotSquare
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsQuadraticSqrtExtensionBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_HeightOneSpectrumPlacesOverFiniteSet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_WithZeroEqOfLeExpIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ValuationUnramifiedOfUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsTwoPlacesOverOfIsSquareLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ExistsAdmissibleLocalNormMemSUnitsSupGlobalNorm
import Theorems.Thm_GlobalTheory_QNorm_conj_places_transitive
import Theorems.Thm_GlobalTheory_QNorm_isQuad_basic
import Theorems.Thm_GlobalTheory_QNorm_places_over
import Theorems.Thm_GlobalTheory_QNorm_two_places_of_isSquare
import Theorems.Thm_GlobalTheory_QNorm_valuation_unramified_of_unit


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
theorem _root_.solution {F E : Type} [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] {δ : F} {θ : E} {σ : E ≃ₐ[F] E} (hq : IsQuad δ θ σ)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (SE : Finset (HeightOneSpectrum (𝓞 E)))
    (hS : admitted F S) (hSE : admitted E SE) (hover : ∀ w, w ∈ SE ↔ w.under (𝓞 F) ∈ S)
    (hδ : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → v.valuation F δ = 1)
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ S)
    (hsq : IsSquare (algebraMap F (v.adicCompletion F) δ)) :
    ∃ a b : F, v.valuation F (a ^ 2 - δ * b ^ 2) = WithZero.exp (-1) ∧
      ∀ u : HeightOneSpectrum (𝓞 F), u ∉ S → u ≠ v → u.valuation F (a ^ 2 - δ * b ^ 2) = 1 := by
  obtain ⟨w, w', hne, hw, hw'⟩ := two_places_of_isSquare F E δ θ σ hq v hsq
  obtain ⟨hc1, hc2⟩ := conj_places_transitive F E δ θ σ hq
  have hwS : w ∉ SE := by rw [hover, hw]; exact hv
  have hw'S : w' ∉ SE := by rw [hover, hw']; exact hv
  obtain ⟨-, π, hπ, hπ'⟩ := hSE w hwS
  obtain ⟨a, b, hab⟩ := (isQuad_basic F E δ θ σ hq).2.2.2.1 π
  have hun : ∀ x : HeightOneSpectrum (𝓞 E), x.under (𝓞 F) ∉ S →
      (x.under (𝓞 F)).valuation F (a ^ 2 - δ * b ^ 2) =
        x.valuation E π * x.valuation E (σ π) := by
    intro x hx
    rw [← map_mul, hab,
      valuation_unramified_of_unit F E δ θ σ hq x (hS _ hx).1 (hδ _ hx)]
  refine ⟨a, b, ?_, ?_⟩
  · have := hun w (hw ▸ hv)
    rw [hw] at this
    rw [this, hπ]
    rcases hc2 w w' (hw'.trans hw.symm) with h | h
    · exact absurd h.symm hne
    · rw [← h, hπ' w' hw'S hne.symm, mul_one]
  · intro u hu huv
    obtain ⟨x, hx⟩ := (places_over F E).2.1 u
    obtain ⟨x', hx', hxx⟩ := hc1 x
    have := hun x (hx ▸ hu)
    rw [hx] at this
    rw [this, ← hxx, hπ' x (by rw [hover, hx]; exact hu) (by rintro rfl; exact huv (hx.symm.trans hw)),
      hπ' x' (by rw [hover, hx', hx]; exact hu)
        (by rintro rfl; exact huv ((hx'.trans hx).symm.trans hw)), mul_one]
end GlobalTheory.QNorm
