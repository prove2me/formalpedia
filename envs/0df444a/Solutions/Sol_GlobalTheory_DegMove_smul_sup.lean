-- Prove2me | solution 1 for GlobalTheory.DegMove.smul_sup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:20:05.289167+00:00
-- url     : https://prove2.me/submissions/a20e6da2-242e-4521-a5e4-d438cb745ad0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_AdaptSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsHermFramePairNormalFormMovedByIsometry

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
noncomputable section
open GlobalTheory GlobalTheory.DegMove
variable {G R M : Type*} [Group G] [Ring R] [AddCommGroup M] [Module R M] [DistribMulAction G M]
  [SMulCommClass G R M]
namespace GlobalTheory.DegMove
theorem _root_.solution (s : G) (A B : Submodule R M) : s • A ⊔ s • B = s • (A ⊔ B) :=
  (Submodule.smul_sup' s A B).symm
end GlobalTheory.DegMove
