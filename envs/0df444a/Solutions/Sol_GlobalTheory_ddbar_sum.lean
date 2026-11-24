-- Prove2me | solution 1 for GlobalTheory.ddbar_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:53:06.984972+00:00
-- url     : https://prove2.me/submissions/a77208fc-f53b-4b96-9c08-999feae97e24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EventuallyDifferentiableAtOfContDiffAtTwo
import Theorems.Thm_GlobalTheory_del_sum
import Theorems.Thm_GlobalTheory_dbar_sum
import Theorems.Thm_GlobalTheory_eventually_differentiableAt_of_contDiffAt_two
import Theorems.Thm_GlobalTheory_differentiableAt_dbar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology ComplexConjugate
noncomputable section
open GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F]
  [IsScalarTower ℝ ℂ F]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G] [NormedSpace ℝ G]
  [IsScalarTower ℝ ℂ G]
variable {u u' : E → F} {z : E}
namespace GlobalTheory
theorem _root_.solution {ι : Type*} {t : Finset ι} {A : ι → E → F}
    (h : ∀ i ∈ t, ContDiffAt ℝ 2 (A i) z) :
    ddbar (fun x => ∑ i ∈ t, A i x) z = ∑ i ∈ t, ddbar (A i) z := by
  simp only [ddbar]
  rw [← del_sum fun i hi => differentiableAt_dbar (h i hi)]
  refine del_congr ?_
  filter_upwards [(Finset.eventually_all t).2
    fun i hi => eventually_differentiableAt_of_contDiffAt_two (h i hi)] with x h1
    using dbar_sum h1
end GlobalTheory
