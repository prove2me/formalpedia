-- Prove2me | solution 1 for GlobalTheory.BadShare.Basic.coeff_alg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:56:45.17041+00:00
-- url     : https://prove2.me/submissions/13d8c8f2-e461-4a6d-9cb6-928216db2d3f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_StandardFiveNontrivial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial Classical
open GlobalTheory GlobalTheory.BadShare
variable (g : ℕ) [Fact g.Prime] (N : ℕ)
variable {g N}
open GlobalTheory.BadShare.Basic
variable {G : Type} [Group G] [Fintype G]
namespace GlobalTheory.BadShare.Basic
theorem _root_.solution (e : G → ℂ) (x : G) : (alg e).coeff x = e x := by
  unfold alg
  rw [MonoidAlgebra.coeff_sum, Finset.sum_apply']
  simp [MonoidAlgebra.coeff_single, Finsupp.single_apply]
end GlobalTheory.BadShare.Basic
