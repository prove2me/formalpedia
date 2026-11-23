-- Prove2me | solution 1 for GlobalTheory.RandomTops.ex_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:06:18.061355+00:00
-- url     : https://prove2.me/submissions/2a558d18-88c5-4221-9550-f2a53db5945f

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
theorem _root_.solution {ι : Type*} (S : Finset ℕ) (I : Finset ι) (f : ι → Finset ℕ → ℝ) :
    ex δ S (fun T => ∑ i ∈ I, f i T) = ∑ i ∈ I, ex δ S (f i) := by
  unfold ex
  simp only [mul_sum]
  rw [sum_comm]
end GlobalTheory.RandomTops
