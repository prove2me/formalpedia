-- Prove2me | solution 1 for GlobalTheory.AnalyticLineDerivative.analyticAt_eval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:57:46.455173+00:00
-- url     : https://prove2.me/submissions/16b3507a-2d19-4402-8d76-672c4628ef1d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_Imports

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.AnalyticLineDerivative
open MvPolynomial
universe u_1 u_2 u_3 u_4
namespace GlobalTheory.AnalyticLineDerivative
theorem _root_.solution {E : Type*} {S : Type*} {J : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CommRing S] [Fintype J] (χ : E → S →+* ℂ) (z₀ : E) (u₀ : J → ℂ)
    (h : ∀ a : S, AnalyticAt ℂ (fun z : E => χ z a) z₀) (p : MvPolynomial J S) :
    AnalyticAt ℂ (fun w : E × (J → ℂ) => eval₂Hom (χ w.1) w.2 p) (z₀, u₀) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    simp only [eval₂Hom_C]
    exact (h a).comp_of_eq analyticAt_fst rfl
  | add p q hp hq =>
    simp only [map_add]
    exact hp.add hq
  | mul_X p i hp =>
    simp only [map_mul, eval₂Hom_X']
    exact hp.mul (((ContinuousLinearMap.proj i).comp
      (ContinuousLinearMap.snd ℂ E (J → ℂ))).analyticAt _)
end GlobalTheory.AnalyticLineDerivative
