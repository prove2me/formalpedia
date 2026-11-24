-- Prove2me | solution 1 for GlobalTheory.FunObj.continuous_pairPhase
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:17:01.613127+00:00
-- url     : https://prove2.me/submissions/4a960967-34c1-4ab0-8b40-a5cac82b2d78

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MeasurePreservingPiProdSplit
import Theorems.Thm_GlobalTheory_FunObj_continuous_keptPt
import Theorems.Thm_GlobalTheory_SplitFlip_CondLE_mul


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
variable (hs : 1 ≤ G.s)
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.FunObj
theorem _root_.solution (x : ColArgs G) : Continuous (pairPhase x) := by
  refine continuous_finset_sum _ fun j _ => ?_
  split_ifs
  · refine continuous_finset_sum _ fun r _ => Continuous.mul ?_
      ((continuous_keptPt.comp (continuous_apply j)).matrix_elem _ _)
    unfold keptRow
    split_ifs with h
    · refine continuous_finset_sum _ fun l _ => ?_
      split_ifs
      · exact (continuous_keptPt.comp (continuous_apply (⟨_, h⟩ : Fin (G.m - 1)))).matrix_elem _ _
      · exact continuous_const
    · exact continuous_const
  · exact continuous_const
end GlobalTheory.FunObj
