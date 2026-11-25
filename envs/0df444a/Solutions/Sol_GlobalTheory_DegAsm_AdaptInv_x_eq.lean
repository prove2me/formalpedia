-- Prove2me | solution 1 for GlobalTheory.DegAsm.AdaptInv.x_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T06:14:02.197166+00:00
-- url     : https://prove2.me/submissions/e8dd2a4e-0e96-4e02-880c-1139f52d0bd7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_AdaptSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormGeometrySummary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FlagFramesSameGradedDefinitePartLatticeEq
import Theorems.Thm_GlobalTheory_DegAsm_AdaptInv_xa_eq

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
theorem _root_.solution {F G : _root_.Formalism.HermitianLatticeCounting.S6.FlagD H r} (h : _root_.GlobalTheory.DegAsm.SameGr F G) :
    G.X = F.X := by
  unfold _root_.Formalism.HermitianLatticeCounting.S6.FlagD.X
  exact _root_.GlobalTheory.DegAsm.AdaptInv.xa_eq h r
end _root_.GlobalTheory.DegAsm.AdaptInv
end GlobalTheory.DegAsm.AdaptInv
