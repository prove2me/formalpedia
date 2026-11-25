-- Prove2me | solution 1 for GlobalTheory.HermFrame.trace_curv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:13:30.877806+00:00
-- url     : https://prove2.me/submissions/cf1689b7-045f-48b4-be96-74184f15e221

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExtFormAdjEqNegSecondForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ChernOneEqNegDdcLogDet
import Theorems.Thm_GlobalTheory_HermFrame_trace_curv_eq_curv_det
import Theorems.Thm_GlobalTheory_HermFrame_ofReal_re_det
import Theorems.Thm_GlobalTheory_HermFrame_OneFormBound_mono
import Theorems.Thm_GlobalTheory_HermFrame_TwoFormBound_mono
import Theorems.Thm_GlobalTheory_IsPshC2On_mono


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex ComplexConjugate Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.HermFrame
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E]
variable {m n l : Type*}
variable [Fintype n] [DecidableEq n] {H : E → Matrix n n ℂ} {z : E}
namespace GlobalTheory.HermFrame
theorem _root_.solution (h : MContDiffAt 2 H z) (hh : ∀ᶠ x in 𝓝 z, (H x).IsHermitian)
    (hu : IsUnit (H z).det) (ξ η : E) :
    (curv H z ξ η).trace = -leviForm (fun x => Real.log (H x).det.re) z ξ η := by
  rw [trace_curv_eq_curv_det h hu]
  refine curv_line (f := fun x => (H x).det.re) (reCLM.contDiff.contDiffAt.comp z h.det) ?_
    (hh.mono fun x hx => (ofReal_re_det hx).symm) ξ η () ()
  intro h0
  apply hu.ne_zero
  rw [← ofReal_re_det hh.self_of_nhds, ofReal_eq_zero]
  exact h0
end GlobalTheory.HermFrame
