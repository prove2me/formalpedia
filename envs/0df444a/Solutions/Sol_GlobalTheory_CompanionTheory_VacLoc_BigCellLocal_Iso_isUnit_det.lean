-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.VacLoc.BigCellLocal.Iso.isUnit_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:53:15.862336+00:00
-- url     : https://prove2.me/submissions/3f6b9fcf-7000-4a60-83bc-d1ce37f04f09

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
variable {A : Type} [CommRing A] (σ : A →+* A) {ι : Type} [Fintype ι] [DecidableEq ι]
variable {σ}
namespace GlobalTheory.CompanionTheory.VacLoc.BigCellLocal
namespace Iso
theorem _root_.solution {D₁ D₂ M : Matrix ι ι A} (h : Iso σ D₁ D₂ M) (hD : IsUnit D₂.det) : IsUnit M.det := by
  unfold Iso at h
  rw [← h, det_mul, det_mul, det_transpose] at hD
  exact isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left hD)
end Iso
end GlobalTheory.CompanionTheory.VacLoc.BigCellLocal
