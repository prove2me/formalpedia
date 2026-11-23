-- Prove2me | solution 1 for GlobalTheory.RandomTops.ex_const
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:11:44.130104+00:00
-- url     : https://prove2.me/submissions/948c6778-e754-4bcf-beaf-c89e8388b378

import Mathlib
import Definitions.Def_Formalism_SubspaceCounting_GoodOrbitIntervalTileCondition
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ChoiceOfTops
import Theorems.Thm_GlobalTheory_RandomTops_ex_empty
import Theorems.Thm_GlobalTheory_RandomTops_ex_insert

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset Formalism.G0
open GlobalTheory GlobalTheory.RandomTops
variable {δ : ℝ}
namespace GlobalTheory.RandomTops
theorem _root_.solution (S : Finset ℕ) (c : ℝ) : ex δ S (fun _ => c) = c := by
  induction S using Finset.induction_on with
  | empty => simp [ex_empty]
  | insert a S ha ih => rw [ex_insert ha, ih]; ring
end GlobalTheory.RandomTops
