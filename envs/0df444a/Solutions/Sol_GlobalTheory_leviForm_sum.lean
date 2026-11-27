-- Prove2me | solution 1 for GlobalTheory.leviForm_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:40:44.244545+00:00
-- url     : https://prove2.me/submissions/25c873bb-c2e1-46dc-8571-07bd6b7397ff

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EventuallyDifferentiableAtOfContDiffAtTwo
import Theorems.Thm_GlobalTheory_ddbar_sum

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
variable {u u' : E → ℝ} {z : E}
namespace GlobalTheory
theorem _root_.solution {ι : Type*} {t : Finset ι} {A : ι → E → ℝ}
    (h : ∀ i ∈ t, ContDiffAt ℝ 2 (A i) z) :
    leviForm (fun x => ∑ i ∈ t, A i x) z = ∑ i ∈ t, leviForm (A i) z := by
  simp only [leviForm, ofReal_sum]
  exact ddbar_sum fun i hi => contDiffAt_ofReal_comp (h i hi)
end GlobalTheory
