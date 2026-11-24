-- Prove2me | solution 1 for GlobalTheory.FunObj.phase_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:17:06.445144+00:00
-- url     : https://prove2.me/submissions/e06961fd-7ef0-4464-b0b0-68156f0c6271

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MeasurePreservingPiProdSplit
import Theorems.Thm_GlobalTheory_FunObj_stepPt_col
import Theorems.Thm_GlobalTheory_FunObj_stepPt_row

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
variable {k : Type*} [Field k] (G : Grid k)
variable {G}
namespace GlobalTheory.FunObj
theorem _root_.solution (x : ColArgs G) (e : Vars G) :
    phase x e = ∑ j : Fin (G.m - 1), ch (stepPt (x j) (e j)) + pairPhase x fun j => keptPart (e j) := by
  rw [phase, Finset.sum_add_distrib, pairPhase]
  congr 1
  refine Finset.sum_congr rfl fun j _ => if_congr Iff.rfl (Finset.sum_congr rfl fun r _ => ?_) rfl
  congr 1
  · unfold rowVar keptRow
    split_ifs
    · refine Finset.sum_congr rfl fun l _ => ?_
      split_ifs with hl
      · exact stepPt_row _ _ _ hl
      · rfl
    · rfl
  · exact stepPt_col _ _ _ rfl
end GlobalTheory.FunObj
