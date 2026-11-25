-- Prove2me | solution 1 for GlobalTheory.T.regular_sequence_germs_regular_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:24:09.780951+00:00
-- url     : https://prove2.me/submissions/6d1f87a0-cd79-461a-ac3e-7e5301998e7c

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_RegularSequenceGermsRegularLocal
import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_BlowupProjections_BlowupProjStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_RegularSequenceGermsRegularLocalStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_ResKCoords_stalk_to_localization


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R ReciprocityTheory.ChartRestriction.G.Geo.ResK
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (Y : Scheme.{0}) (U : Y.affineOpens) (y : Y) (hy : y ∈ U.1), IsRegularLocalRing (Y.presheaf.stalk y) → ∀ (m : ℕ) (f : Fin m → Γ(Y, U.1)), FinalTheorems.Rsp (Y.presheaf.stalk y) m (fun i => Y.presheaf.germ U.1 y hy (f i)) → IsRegularLocalRing (Localization.AtPrime (U.2.primeIdealOf ⟨y, hy⟩).asIdeal) ∧ FinalTheorems.Rsp (Localization.AtPrime (U.2.primeIdealOf ⟨y, hy⟩).asIdeal) m (fun i => algebraMap Γ(Y, U.1) _ (f i)) ∧ ∀ s : Γ(Y, U.1), y ∈ Y.basicOpen s ↔ s ∉ (U.2.primeIdealOf ⟨y, hy⟩).asIdeal := by
  first | exact @GlobalTheory.CompanionTheory.ResKCoords.stalk_to_localization | exact GlobalTheory.CompanionTheory.ResKCoords.stalk_to_localization | (intros; apply GlobalTheory.CompanionTheory.ResKCoords.stalk_to_localization <;> assumption)
end _root_.GlobalTheory.T
