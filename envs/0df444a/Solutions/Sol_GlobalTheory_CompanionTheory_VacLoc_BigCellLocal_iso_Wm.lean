-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.VacLoc.BigCellLocal.iso_Wm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:58:52.598802+00:00
-- url     : https://prove2.me/submissions/46d3ad10-0219-4e61-b88c-82e8ee601ca2

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_GoodChar
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_ExistsSkewOfDiagonal
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_BigCellLocal
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_VacLoc_BigCellLocal_map_one__0ae7550c3513

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.FinHeis GlobalTheory.WeilM MeasureTheory Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.VacLoc.BigCellLocal
variable {A : Type} [CommRing A] {σ : A →+* A} {β : Type} [Fintype β] [DecidableEq β]
namespace GlobalTheory.CompanionTheory.VacLoc.BigCellLocal
theorem _root_.solution : Iso σ (Wm A β) (Wm A β) (Wm A β) := by
  simp [Iso, Wm, fromBlocks_multiply, fromBlocks_transpose, fromBlocks_map, map_one']
end GlobalTheory.CompanionTheory.VacLoc.BigCellLocal
