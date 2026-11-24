-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgExhHecke.capEntry_eq_Tm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:08:24.304068+00:00
-- url     : https://prove2.me/submissions/e1d3c005-dac4-4e91-ba55-d76a5d8b7607

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_CapelliCentralStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_QuantumDeterminantEquality

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
theorem _root_.solution {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A)
    (x : ℂ) (a b : Fin n) : capEntry E x a b = Tm E x a b := by
  unfold capEntry Tm
  exact add_comm _ _
end GlobalTheory.CompanionTheory.RgExhHecke
