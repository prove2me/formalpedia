-- Prove2me | solution 1 for GlobalTheory.ZM.DwModel.isGaloisCover_complex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:35:43.004517+00:00
-- url     : https://prove2.me/submissions/22f25135-013f-47f1-aedc-c5f5aca9596e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_NotIsGaloisCoverTrivial
import Theorems.Thm_GlobalTheory_ZM_DwModel_isGaloisCover_field

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZM.DwModel
namespace GlobalTheory.ZM.DwModel
theorem _root_.solution :
    IsGaloisCover (ℂ ≃ₐ[ℝ] ℂ) (fun σ => spMap (σ : ℂ →+* ℂ)) (spMap (algebraMap ℝ ℂ)) ∧ Nat.card (ℂ ≃ₐ[ℝ] ℂ) = 2 := by
  have : IsAlgClosure ℝ ℂ := ⟨Complex.isAlgClosed, inferInstance⟩
  have : IsGalois ℝ ℂ := ⟨⟩
  exact ⟨isGaloisCover_field ℝ ℂ, by rw [IsGalois.card_aut_eq_finrank, Complex.finrank_real_complex]⟩
end GlobalTheory.ZM.DwModel
