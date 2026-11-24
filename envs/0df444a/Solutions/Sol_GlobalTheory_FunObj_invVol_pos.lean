-- Prove2me | solution 1 for GlobalTheory.FunObj.invVol_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:52:40.805424+00:00
-- url     : https://prove2.me/submissions/4ce6090c-210b-43e2-9e86-37a388107e72

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSumRowCol
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Theorems.Thm_GlobalTheory_FunObj_relIndex_ne_zero_of_isOpen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal
noncomputable section
open GlobalTheory GlobalTheory.FunObj
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx
variable (k : Type*) [Field k] (n : Type*) [Fintype n] [DecidableEq n] (c : ℕ)
variable {k n c}
variable {n' : Type*} [Fintype n'] [DecidableEq n']
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.FunObj
theorem _root_.solution {C : Subgroup (GL (n ⊕ Fin c) k)} (ho : IsOpen (C : Set (GL (n ⊕ Fin c) k)))
    (hc : IsCompact (C : Set (GL (n ⊕ Fin c) k))) : 0 < invVol C :=
  div_pos (Nat.cast_pos.2 (Nat.pos_of_ne_zero (relIndex_ne_zero_of_isOpen ho isCompact_KO inf_le_right)))
    (Nat.cast_pos.2 (Nat.pos_of_ne_zero (relIndex_ne_zero_of_isOpen isOpen_KO hc inf_le_right)))
end GlobalTheory.FunObj
