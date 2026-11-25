-- Prove2me | solution 1 for GlobalTheory.SignedBlockCount.minor_self_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:02:31.251259+00:00
-- url     : https://prove2.me/submissions/782c6a23-506d-42a3-9dbf-0656445fe05f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_AdaptSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SignedBlockAntidiagWithLeadingMinorsEncardLe
import Theorems.Thm_GlobalTheory_SignedBlockCount_sign_ne
import Theorems.Thm_GlobalTheory_SignedBlockCount_minor_self

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
open GlobalTheory GlobalTheory.SignedBlockCount
open Formalism.MainNotions.S.Loc
variable {K : Type} [Field K]
namespace GlobalTheory.SignedBlockCount
theorem _root_.solution (t : Kˣ) (s : ℕ+) (bs : List (Kˣ × ℕ+)) : minor ((t, s) :: bs) s ≠ 0 := by
  rw [minor_self]
  exact mul_ne_zero (sign_ne _) (pow_ne_zero _ t.ne_zero)
end GlobalTheory.SignedBlockCount
