-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgExhHecke.qdetEq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:40:16.28514+00:00
-- url     : https://prove2.me/submissions/754b9ac2-353b-4a65-b30c-b602231e2fd6

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_CapelliCentralStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_QuantumDeterminantEquality
import Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_qdet_eq_capelliC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgExhHecke
namespace GlobalTheory.CompanionTheory.RgExhHecke
theorem _root_.solution : ∀ (n : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M]
    (E : Fin n → Fin n → Module.End ℂ M) (x : ℂ), qdet E x = capelliC E x :=
  fun _ _ _ _ E x => qdet_eq_capelliC E x
end GlobalTheory.CompanionTheory.RgExhHecke
