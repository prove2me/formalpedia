-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.VacLoc.BigCellLocal.iso_col
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:40:51.394241+00:00
-- url     : https://prove2.me/submissions/0c38b93f-4e93-401f-b407-704d0b64ae78

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_GoodChar
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_ExistsSkewOfDiagonal
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_BigCellLocal

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
theorem _root_.solution {a b c d : Matrix β β A} (h : Iso σ (Wm A β) (Wm A β) (fromBlocks a b c d)) :
    cᵀ * a.map σ + aᵀ * c.map σ = 0 := by
  simp only [Iso, Wm, fromBlocks_multiply, fromBlocks_transpose, fromBlocks_map] at h
  simpa using (fromBlocks_inj.mp h).1
end GlobalTheory.CompanionTheory.VacLoc.BigCellLocal
