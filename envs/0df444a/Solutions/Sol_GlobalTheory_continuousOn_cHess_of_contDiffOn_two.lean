-- Prove2me | solution 1 for GlobalTheory.continuousOn_cHess_of_contDiffOn_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:44:54.008689+00:00
-- url     : https://prove2.me/submissions/3b620f3f-a69b-4b3d-a0a7-6e241660ef28

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_IsLocalHomeomorph
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOnComplexHessianOfContDiffOnTwo
import Theorems.Thm_GlobalTheory_contDiffOn_one_wdb_of_contDiffOn_two_isOpen
import Theorems.Thm_GlobalTheory_continuousOn_wd_of_contDiffOn_one_isOpen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology MeasureTheory Metric ReciprocityTheory.L2DbarEstimates
open scoped ComplexOrder
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (n : ℕ) (U : Set (V n)) (φ : V n → ℝ), IsOpen U → ContDiffOn ℝ 2 φ U → ∀ j l,
      ContinuousOn (fun z => cHess n (fun v => (φ v : ℂ)) z j l) U := by
  intro n U φ hU hφ j l
  have hc : ContDiffOn ℝ 2 (fun v => (φ v : ℂ)) U :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hφ
  have hb := contDiffOn_one_wdb_of_contDiffOn_two_isOpen hU hc l
  simpa only [cHess, Matrix.of_apply] using continuousOn_wd_of_contDiffOn_one_isOpen hU hb j
end GlobalTheory
