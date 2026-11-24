-- Prove2me | solution 1 for GlobalTheory.SCV.tendstoLocallyUniformlyOn_iteratedFDeriv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:16:45.410424+00:00
-- url     : https://prove2.me/submissions/5532eed1-49bf-4949-8bd3-ccac62088205

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Theorems.Thm_GlobalTheory_SCV_differentiableOn_iteratedFDeriv
import Theorems.Thm_GlobalTheory_SCV_tendstoLocallyUniformlyOn_fderiv

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
variable {ι : Type*} {l : Filter ι} {F : ι → E → V} {f : E → V} {U : Set E}
namespace GlobalTheory.SCV
theorem _root_.solution (hU : IsOpen U)
    (hlim : TendstoLocallyUniformlyOn F f l U) (hF : ∀ᶠ n in l, DifferentiableOn ℂ (F n) U)
    (k : ℕ) :
    TendstoLocallyUniformlyOn (fun n => iteratedFDeriv ℂ k (F n)) (iteratedFDeriv ℂ k f) l U := by
  induction k with
  | zero =>
    simp only [iteratedFDeriv_zero_eq_comp]
    exact (continuousMultilinearCurryFin0 ℂ E V).symm.isometry.uniformContinuous
      |>.comp_tendstoLocallyUniformlyOn hlim
  | succ k ih =>
    simp only [iteratedFDeriv_succ_eq_comp_left]
    exact (continuousMultilinearCurryLeftEquiv ℂ (fun _ : Fin (k + 1) => E)
      V).symm.isometry.uniformContinuous.comp_tendstoLocallyUniformlyOn
      (tendstoLocallyUniformlyOn_fderiv hU ih
        (hF.mono fun n hn => differentiableOn_iteratedFDeriv hU hn k))
end GlobalTheory.SCV
