-- Prove2me | solution 1 for GlobalTheory.leviForm_re_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:14:55.630958+00:00
-- url     : https://prove2.me/submissions/6a6f6854-0b62-4f23-b305-79ce67046095

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EventuallyDifferentiableAtOfContDiffAtTwo
import Theorems.Thm_GlobalTheory_eventually_differentiableAt_of_contDiffAt_two
import Theorems.Thm_GlobalTheory_ddbar_add
import Theorems.Thm_GlobalTheory_ddbar_const_smul
import Theorems.Thm_GlobalTheory_ddbar_eq_zero_of_holomorphic

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
theorem _root_.solution {f : E → ℂ} (hf : ContDiffAt ℂ 2 f z) :
    leviForm (fun x => (f x).re) z = 0 := by
  have hR : ContDiffAt ℝ 2 f z := hf.restrict_scalars ℝ
  have hc : ContDiffAt ℝ 2 (fun x => conj (f x)) z := conjCLE.contDiff.contDiffAt.comp z hR
  have h0 := ddbar_eq_zero_of_holomorphic (eventually_differentiableAt_of_contDiffAt_two hf)
  have : (fun x => ((f x).re : ℂ)) = fun x => (1 / 2 : ℂ) • (f x + conj (f x)) := by
    funext x; rw [add_conj]; simp
  rw [leviForm, this, ddbar_const_smul _ (hR.add hc), ddbar_add hR hc]
  ext v w
  simp [ddbar_conj hR, h0]
end GlobalTheory
