-- Prove2me | solution 1 for GlobalTheory.IntegralFrameAllCompare.vV_nonneg_iff_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:17:43.847823+00:00
-- url     : https://prove2.me/submissions/f727b543-fbdd-4ac7-83c9-c18b04d10bea

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntAllFree
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_IntegralFrameAcquisition
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_VVNonnegIffLeOne
import Theorems.Thm_Formalism_L2_Pj_valV_ne_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open GlobalTheory GlobalTheory.IntegralFrameAllCompare
open NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.IntegralFrameAcquisition
variable {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
  [IsFractionRing V K]
namespace GlobalTheory.IntegralFrameAllCompare
theorem _root_.solution (x : K) (hx : x ≠ 0) : 0 ≤ vV V x ↔ valV V x ≤ 1 := by
  rw [← WithZero.log_le_log (valV_ne_zero (V := V) hx) one_ne_zero, WithZero.log_one, vV]
  omega
end GlobalTheory.IntegralFrameAllCompare
