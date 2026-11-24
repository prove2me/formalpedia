-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Principalise.isIso_restrict_of_isIso_restrict_comp_blowup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:39:03.542807+00:00
-- url     : https://prove2.me/submissions/92223774-8333-4261-a1e1-8d5ebb8a9284

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__GeometricallyConnectedOfIsIsoRestrict_f3ea578707b0384e
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_IsIsoRestrictOfBlowupComp
import Theorems.Thm_GlobalTheory_CompanionTheory_Principalise_isIso_of_isIso_comp_of_dense_range
import Theorems.Thm_GlobalTheory_CompanionTheory_Principalise_dense_range_restrict_of_blowup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Principalise
namespace GlobalTheory.CompanionTheory.Principalise
theorem _root_.solution : ∀ {X X₁ X₂ : Scheme.{0}} (s : X₁ ⟶ X) (π : X₂ ⟶ X₁)
    (Z : X₁.IdealSheafData) (V : X.Opens), IsIntegral X₁ → IsSeparated s → FinalTheorems.Blowup π Z → Nonempty X₂ →
    IsIso ((π ≫ s) ∣_ V) → IsIso (s ∣_ V) ∧ IsIso (π ∣_ (s ⁻¹ᵁ V)) := by
  intro X X₁ X₂ s π Z V hX hs hB hne he
  have he' : IsIso (π ∣_ (s ⁻¹ᵁ V) ≫ s ∣_ V) := by
    rw [← morphismRestrict_comp]
    exact he
  exact isIso_of_isIso_comp_of_dense_range (π ∣_ (s ⁻¹ᵁ V)) (s ∣_ V) (dense_range_restrict_of_blowup hB _)
end GlobalTheory.CompanionTheory.Principalise
