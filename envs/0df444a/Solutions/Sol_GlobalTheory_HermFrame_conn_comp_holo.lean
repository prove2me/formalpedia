-- Prove2me | solution 1 for GlobalTheory.HermFrame.conn_comp_holo
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:48:23.68781+00:00
-- url     : https://prove2.me/submissions/bd4cbd7e-75c0-4dbd-92f6-cd16983c9ae3

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EventuallyDifferentiableAtOfContDiffAtTwo
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LeTwoMulOfForallScale
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExtFormAdjEqNegSecondForm
import Theorems.Thm_GlobalTheory_del_comp_holo


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff
noncomputable section
open GlobalTheory GlobalTheory.HermFrame
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E]
variable {m n l : Type*}
variable [Fintype n] [DecidableEq n]
variable {U : Set E} {H H' : E → Matrix n n ℂ} {z : E} {j k : WithTop ℕ∞}
variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E'] [NormedSpace ℝ E']
  [IsScalarTower ℝ ℂ E'] {φ : E' → E} {w : E'}
namespace GlobalTheory.HermFrame
theorem _root_.solution (h : MContDiffAt 1 H (φ w)) (hφ : DifferentiableAt ℂ φ w) (ξ : E') :
    conn (fun x => H (φ x)) w ξ = conn H (φ w) (fderiv ℂ φ w ξ) := by
  rw [conn, conn]
  congr 2
  ext a b
  exact del_comp_holo (u := fun y => H y a b) (h.diff a b) hφ ξ
end GlobalTheory.HermFrame
