-- Prove2me | solution 1 for GlobalTheory.FunObj.continuous_phase
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:48:31.624801+00:00
-- url     : https://prove2.me/submissions/5deac251-979a-4392-98af-7f08d7abb47c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasCompactSupportFlatIntegrand
import Theorems.Thm_GlobalTheory_FunObj_continuous_stepPt
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
noncomputable section
open GlobalTheory GlobalTheory.FunObj
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {G : Grid k}
namespace GlobalTheory.FunObj
theorem _root_.solution (x : ColArgs G) : Continuous (phase x) := by
  have hp : ∀ (j : Fin (G.m - 1)) r s, Continuous fun e : Vars G => stepPt (x j) (e j) r s := fun j r s =>
    ((continuous_stepPt _).comp (continuous_apply j)).matrix_elem r s
  refine continuous_finsetSum _ fun j _ => (continuous_finsetSum _ fun i _ => hp j _ _).add ?_
  split_ifs
  · refine continuous_finsetSum _ fun r _ => Continuous.mul ?_ (hp j _ _)
    unfold rowVar
    split_ifs with h
    · refine continuous_finsetSum _ fun l _ => ?_
      split_ifs
      · exact hp ⟨_, h⟩ _ _
      · exact continuous_const
    · exact continuous_const
  · exact continuous_const
end GlobalTheory.FunObj
