-- Prove2me | solution 1 for GlobalTheory.lineDerivList_ofFn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:42:37.441472+00:00
-- url     : https://prove2.me/submissions/3259eb19-af1a-49b8-b89d-f0145b348594

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LineDerivListEqIteratedFDeriv
import Theorems.Thm_GlobalTheory_lineDerivList_nil
import Theorems.Thm_GlobalTheory_lineDerivList_cons
import Theorems.Thm_GlobalTheory_lineDerivList_zero
import Theorems.Thm_GlobalTheory_analyticAt_lineDerivList
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.lineDerivList_nil
attribute [local simp] GlobalTheory.lineDerivList_zero

set_option autoImplicit false
open Filter Topology
open scoped ContDiff
open GlobalTheory
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
variable [CompleteSpace V]
namespace GlobalTheory
theorem _root_.solution {F : E → V} {a : E} (h : AnalyticAt 𝕜 F a) {n : ℕ} (m : Fin n → E) :
    lineDerivList 𝕜 (List.ofFn m) F a = iteratedFDeriv 𝕜 n F a m := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    have hev : lineDerivList 𝕜 (List.ofFn fun i => m i.succ) F
        =ᶠ[𝓝 a] fun z => iteratedFDeriv 𝕜 n F z (Fin.tail m) := by
      filter_upwards [h.eventually_analyticAt] with z hz
      exact ih hz _
    have hd : DifferentiableAt 𝕜 (iteratedFDeriv 𝕜 n F) a :=
      (h.contDiffAt (n := ω)).differentiableAt_iteratedFDeriv (by simp)
    rw [List.ofFn_succ, lineDerivList_cons, iteratedFDeriv_succ_apply_left]
    dsimp only
    rw [(analyticAt_lineDerivList h _).differentiableAt.lineDeriv_eq_fderiv, hev.fderiv_eq,
      fderiv_continuousMultilinear_apply_const_apply hd]
end GlobalTheory
