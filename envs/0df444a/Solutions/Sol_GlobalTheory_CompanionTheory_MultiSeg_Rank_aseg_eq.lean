-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.MultiSeg.Rank.aseg_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:52:35.685033+00:00
-- url     : https://prove2.me/submissions/f0057a5d-261e-4a41-be1f-60832e8f1014

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_ZelevinskyJacquet_ZelevinskyInterleaving_Interleave
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ShuffleWeightSquareLengthLt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Zc.Comb
open Classical
universe u
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.MultiSeg GlobalTheory.CompanionTheory.MultiSeg.Rank
variable {T : Type u}
namespace GlobalTheory.CompanionTheory.MultiSeg.Rank
theorem _root_.solution {Δ Γ : ASeg T} (h1 : Δ.start = Γ.start) (h2 : Δ.len = Γ.len) : Δ = Γ := by
  cases Δ
  cases Γ
  dsimp only at h1 h2
  subst h1
  subst h2
  rfl
end GlobalTheory.CompanionTheory.MultiSeg.Rank
