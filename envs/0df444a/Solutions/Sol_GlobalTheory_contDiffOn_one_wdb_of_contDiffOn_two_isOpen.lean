-- Prove2me | solution 1 for GlobalTheory.contDiffOn_one_wdb_of_contDiffOn_two_isOpen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:33:53.292795+00:00
-- url     : https://prove2.me/submissions/448dd13f-9188-4fab-85f7-365e0b91980b

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
    (hU : IsOpen U) (hg : ContDiffOn ℝ 2 g U) (l : Fin n) :
    ContDiffOn ℝ 1 (wdb n l g) U := by
  have hD : ContDiffOn ℝ 1 (fun y => fderiv ℝ g y) U :=
    hg.fderiv_of_isOpen hU (by norm_num)
  have h1 : ContDiffOn ℝ 1 (fun y => fderiv ℝ g y (bas n l)) U :=
    hD.clm_apply contDiffOn_const
  have h2 : ContDiffOn ℝ 1 (fun y => fderiv ℝ g y (Complex.I • bas n l)) U :=
    hD.clm_apply contDiffOn_const
  have h3 : ContDiffOn ℝ 1
      (fun y => (fderiv ℝ g y (bas n l) + Complex.I * fderiv ℝ g y (Complex.I • bas n l)) / 2) U :=
    (h1.add (contDiffOn_const.mul h2)).div_const 2
  have e : wdb n l g = fun y =>
      (fderiv ℝ g y (bas n l) + Complex.I * fderiv ℝ g y (Complex.I • bas n l)) / 2 :=
    funext fun y => rfl
  rw [e]
  exact h3
end GlobalTheory
