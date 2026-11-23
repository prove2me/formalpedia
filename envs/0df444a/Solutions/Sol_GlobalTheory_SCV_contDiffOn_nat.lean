-- Prove2me | solution 1 for GlobalTheory.SCV.contDiffOn_nat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:08:23.085373+00:00
-- url     : https://prove2.me/submissions/eed88628-fcba-4473-ad02-030e455a0e13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Theorems.Thm_GlobalTheory_SCV_differentiableOn_fderiv_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Metric Set Filter
open scoped Topology ContDiff Nat
open GlobalTheory GlobalTheory.SCV
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
namespace GlobalTheory.SCV
theorem _root_.solution {U : Set E} (hU : IsOpen U) (n : ℕ) :
    ∀ {f : E → V}, DifferentiableOn ℂ f U → ContDiffOn ℂ n f U := by
  induction n with
  | zero =>
    intro f hf
    simpa using hf.continuousOn
  | succ n ih =>
    intro f hf
    rw [Nat.cast_succ]
    refine contDiffOn_succ_of_fderiv_apply hf (by simp) fun y => ?_
    refine (ih (differentiableOn_fderiv_apply hU hf y)).congr fun x hx => ?_
    rw [fderivWithin_of_isOpen hU hx]
end GlobalTheory.SCV
