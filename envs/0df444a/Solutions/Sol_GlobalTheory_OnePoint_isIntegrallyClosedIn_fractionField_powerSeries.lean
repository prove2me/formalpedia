-- Prove2me | solution 1 for GlobalTheory.OnePoint.isIntegrallyClosedIn_fractionField_powerSeries
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:16:08.665871+00:00
-- url     : https://prove2.me/submissions/9fed5351-fda7-46b3-91c5-153a526fc9fc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsIntegrallyClosedInFractionFieldPowerSeries
import Theorems.Thm_GlobalTheory_OnePoint_isIntegrallyClosedIn_fractionField_of_residue

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped LaurentSeries PowerSeries
open CategoryTheory Limits AlgebraicGeometry
open GlobalTheory GlobalTheory.OnePoint
universe u v w
variable {K : Type u} [Field K]
namespace GlobalTheory.OnePoint
theorem _root_.solution (L : Type w) [Field L] [Algebra K⟦X⟧ L]
    [IsFractionRing K⟦X⟧ L] [Algebra K L] [IsScalarTower K K⟦X⟧ L] :
    IsIntegrallyClosedIn K L := by
  refine isIntegrallyClosedIn_fractionField_of_residue K⟦X⟧ L fun r ↦ ?_
  refine ⟨PowerSeries.constantCoeff r, fun hu ↦ ?_⟩
  simpa using PowerSeries.isUnit_constantCoeff _ hu
end GlobalTheory.OnePoint
