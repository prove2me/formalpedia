-- Prove2me | solution 1 for GlobalTheory.RandomTops.ex_congr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:06:19.149832+00:00
-- url     : https://prove2.me/submissions/33cc4b8d-1992-4ad6-9ab7-e5c3374897fc

import Mathlib
import Definitions.Def_Formalism_SubspaceCounting_GoodOrbitIntervalTileCondition
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ChoiceOfTops

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
theorem _root_.solution {S : Finset ℕ} {f g : Finset ℕ → ℝ} (h : ∀ T ⊆ S, f T = g T) :
    ex δ S f = ex δ S g := by
  unfold ex
  exact sum_congr rfl fun T hT => by rw [h T (mem_powerset.mp hT)]
end GlobalTheory.RandomTops
