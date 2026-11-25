-- Prove2me | solution 1 for GlobalTheory.HermFrame.trace_conn_eq_sub_add_quot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:06:37.167148+00:00
-- url     : https://prove2.me/submissions/1f4d7550-431f-4f29-8d5f-4073ccb809be

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExtFormAdjEqNegSecondForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ChernOneEqNegDdcLogDet
import Theorems.Thm_GlobalTheory_HermFrame_trace_conn
import Theorems.Thm_GlobalTheory_HermFrame_OneFormBound_mono
import Theorems.Thm_GlobalTheory_HermFrame_TwoFormBound_mono
import Theorems.Thm_GlobalTheory_HermFrame_det_eq_det_subGram_mul
import Theorems.Thm_GlobalTheory_HermFrame_isUnit_det_quotGram
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
variable [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l]
  {H : E → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : E}
namespace GlobalTheory.HermFrame
theorem _root_.solution (h : MContDiffAt 1 H z) (hu : IsUnit (H z).det)
    (hs : IsUnit (subGram (H z)).det) (ξ : E) : (conn H z ξ).trace =
      (conn (fun x => subGram (H x)) z ξ).trace + (conn (fun x => quotGram (H x)) z ξ).trace := by
  have hq := isUnit_det_quotGram hu hs
  have he : (fun x => (H x).det) =ᶠ[𝓝 z] fun x => (subGram (H x)).det * (quotGram (H x)).det :=
    (h.subGram.eventually_isUnit hs).mono fun x hx => det_eq_det_subGram_mul hx
  rw [trace_conn h hu, trace_conn h.subGram hs, trace_conn (h.quotGram hs) hq, del_congr he,
    del_mul (h.subGram.det.differentiableAt one_ne_zero)
      ((h.quotGram hs).det.differentiableAt one_ne_zero), det_eq_det_subGram_mul hs]
  have h1 := hs.ne_zero
  have h2 := hq.ne_zero
  field_simp
  ring
end GlobalTheory.HermFrame
