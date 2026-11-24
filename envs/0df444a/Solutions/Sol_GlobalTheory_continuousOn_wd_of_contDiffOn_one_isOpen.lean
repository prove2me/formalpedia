-- Prove2me | solution 1 for GlobalTheory.continuousOn_wd_of_contDiffOn_one_isOpen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:34:00.778015+00:00
-- url     : https://prove2.me/submissions/600606a5-1436-48f3-870c-04b77ad23b8e

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_IsLocalHomeomorph
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOnComplexHessianOfContDiffOnTwo

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
theorem _root_.solution {n : ℕ} {U : Set (V n)} {g : V n → ℂ}
    (hU : IsOpen U) (hg : ContDiffOn ℝ 1 g U) (j : Fin n) :
    ContinuousOn (wd n j g) U := by
  have hD : ContinuousOn (fun y => fderiv ℝ g y) U :=
    hg.continuousOn_fderiv_of_isOpen hU le_rfl
  have h1 : ContinuousOn (fun y => fderiv ℝ g y (bas n j)) U :=
    hD.clm_apply continuousOn_const
  have h2 : ContinuousOn (fun y => fderiv ℝ g y (Complex.I • bas n j)) U :=
    hD.clm_apply continuousOn_const
  have h3 : ContinuousOn
      (fun y => (fderiv ℝ g y (bas n j) - Complex.I * fderiv ℝ g y (Complex.I • bas n j)) / 2) U :=
    (h1.sub (continuousOn_const.mul h2)).div_const 2
  have e : wd n j g = fun y =>
      (fderiv ℝ g y (bas n j) - Complex.I * fderiv ℝ g y (Complex.I • bas n j)) / 2 :=
    funext fun y => rfl
  rw [e]
  exact h3
end GlobalTheory
