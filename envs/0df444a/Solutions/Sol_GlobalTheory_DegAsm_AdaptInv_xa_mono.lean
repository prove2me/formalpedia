-- Prove2me | solution 1 for GlobalTheory.DegAsm.AdaptInv.xa_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:54:51.69101+00:00
-- url     : https://prove2.me/submissions/801f0e9b-dcf7-4215-86e7-1da02dd89865

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_AdaptSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormGeometrySummary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FlagFramesSameGradedDefinitePartLatticeEq
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_Xa_mono


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.DegAsm GlobalTheory.DegAsm.AdaptInv
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : HermSpace K V} {r : ℕ}
open NumberField
open scoped Pointwise ENNReal Classical
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ}
namespace GlobalTheory.DegAsm.AdaptInv
namespace _root_.GlobalTheory.DegAsm.AdaptInv
theorem _root_.solution (F : _root_.Formalism.HermitianLatticeCounting.S6.FlagD H r) {a b : ℕ} (h : a ≤ b) : F.Xa a ≤ F.Xa b :=
  _root_.Formalism.HermitianLatticeCounting.P.Xa_mono F h
end _root_.GlobalTheory.DegAsm.AdaptInv
end GlobalTheory.DegAsm.AdaptInv
