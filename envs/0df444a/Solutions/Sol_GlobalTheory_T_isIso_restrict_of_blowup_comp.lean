-- Prove2me | solution 1 for GlobalTheory.T.isIso_restrict_of_blowup_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:24:29.652979+00:00
-- url     : https://prove2.me/submissions/5dfb5b5f-bddd-4b69-be2c-e5743e64867b

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_IsIsoRestrictOfBlowupComp
import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__GeometricallyConnectedOfIsIsoRestrict_f3ea578707b0384e
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_IsIsoRestrictOfBlowupCompStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_Principalise_isIso_restrict_of_isIso_restrict_comp_blowup


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {X X₁ X₂ : Scheme.{0}} (s : X₁ ⟶ X) (π : X₂ ⟶ X₁) (Z : X₁.IdealSheafData) (V : X.Opens), IsIntegral X₁ → IsSeparated s → FinalTheorems.Blowup π Z → Nonempty X₂ → IsIso ((π ≫ s) ∣_ V) → IsIso (s ∣_ V) ∧ IsIso (π ∣_ (s ⁻¹ᵁ V)) := by
  first | exact @GlobalTheory.CompanionTheory.Principalise.isIso_restrict_of_isIso_restrict_comp_blowup | exact GlobalTheory.CompanionTheory.Principalise.isIso_restrict_of_isIso_restrict_comp_blowup | (intros; apply GlobalTheory.CompanionTheory.Principalise.isIso_restrict_of_isIso_restrict_comp_blowup <;> assumption)
end _root_.GlobalTheory.T
