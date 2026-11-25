-- Prove2me | solution 1 for GlobalTheory.SignedBlockCount.minor_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:17:14.405553+00:00
-- url     : https://prove2.me/submissions/743385d3-d988-4103-952d-5db3b88927b4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_AdaptSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SignedBlockAntidiagWithLeadingMinorsEncardLe
import Theorems.Thm_GlobalTheory_SignedBlockCount_minor_zero
import Theorems.Thm_GlobalTheory_SignedBlockCount_minor_add

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
theorem _root_.solution (t : Kˣ) (s : ℕ+) (bs : List (Kˣ × ℕ+)) :
    minor ((t, s) :: bs) s =
      ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin s)) : ℤˣ) : ℤ) * (t : K) ^ (s : ℕ) := by
  have := minor_add t s bs 0
  rwa [minor_zero, mul_one, Nat.add_zero] at this
end GlobalTheory.SignedBlockCount
