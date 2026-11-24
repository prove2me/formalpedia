-- Prove2me | solution 1 for GlobalTheory.RandomTops.ex_restrict
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:27:20.631647+00:00
-- url     : https://prove2.me/submissions/d181f84d-44e0-47c8-a53d-d264f06b6671

import Mathlib
import Definitions.Def_Formalism_SubspaceCounting_GoodOrbitIntervalTileCondition
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ChoiceOfTops
import Theorems.Thm_GlobalTheory_RandomTops_ex_const
import Theorems.Thm_GlobalTheory_RandomTops_ex_split

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
theorem _root_.solution {A S : Finset ℕ} (hA : A ⊆ S) (f : Finset ℕ → ℝ) :
    ex δ S (fun T => f (T ∩ A)) = ex δ A f := by
  have h := ex_split (δ := δ) hA f (fun _ => 1)
  simp only [mul_one, ex_const] at h
  exact h
end GlobalTheory.RandomTops
