-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.VacLoc.BigCellLocal.Iso.mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:53:17.389184+00:00
-- url     : https://prove2.me/submissions/6f7317ad-c46d-43a4-b066-2b134e0f0153

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
omit [DecidableEq ι]
namespace GlobalTheory.CompanionTheory.VacLoc.BigCellLocal
namespace Iso
theorem _root_.solution {D₁ D₂ D₃ M N : Matrix ι ι A} (h : Iso σ D₁ D₂ M) (h' : Iso σ D₂ D₃ N) : Iso σ D₁ D₃ (M * N) := by
  unfold Iso at *
  rw [transpose_mul, Matrix.map_mul, ← h', ← h]
  simp only [Matrix.mul_assoc]
end Iso
end GlobalTheory.CompanionTheory.VacLoc.BigCellLocal
