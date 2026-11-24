-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgExhHecke.qdet_eq_capelliC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:23:38.757818+00:00
-- url     : https://prove2.me/submissions/c6e9fd19-be8f-4dd5-9731-21d0f4706fe3

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_CapelliCentralStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_QuantumDeterminantEquality
import Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_capEntry_eq_Tm

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
    (x : ℂ) : qdet E x = capelliC E x := by
  unfold qdet qminor capelliC cminor
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [capEntry_eq_Tm, zsmul_eq_mul]
end GlobalTheory.CompanionTheory.RgExhHecke
