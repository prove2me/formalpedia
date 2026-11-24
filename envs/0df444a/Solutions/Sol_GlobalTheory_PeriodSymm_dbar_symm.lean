-- Prove2me | solution 1 for GlobalTheory.PeriodSymm.dbar_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:24:30.577255+00:00
-- url     : https://prove2.me/submissions/7e1481d0-800f-40cc-aee6-83538ce56864

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SetIntegralFderivEqZeroOfLatticePeriodic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CauchyRiemannIffDifferentiableOnComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_PeriodicCechCocycleSmoothCoboundaryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ThetaCocyclePeriodicNonvanishingSections
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Complex Matrix
open scoped ContDiff BigOperators Real
open Filter Topology
namespace GlobalTheory.PeriodSymm
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
private lemma fderiv_apply_lemma {f : E → ℂ} {z : E}
    (hD : DifferentiableAt ℝ (fderiv ℝ f) z) (u w : E) :
    fderiv ℝ (fun x => fderiv ℝ f x u) z w = fderiv ℝ (fderiv ℝ f) z w u := by
  rw [fderiv_clm_apply hD (differentiableAt_const u)]
  simp
end GlobalTheory.PeriodSymm
end

set_option autoImplicit false
open Complex Matrix
open scoped ContDiff BigOperators Real
open Filter Topology
open GlobalTheory GlobalTheory.PeriodSymm
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace GlobalTheory.PeriodSymm
theorem _root_.solution {f : E → ℂ} {z : E} (h : ContDiffAt ℝ 2 f z) (u v : E) :
    dbar (dbar f u) v z = dbar (dbar f v) u z := by
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ f) z := h.fderiv_right (by norm_num)
  have hD : DifferentiableAt ℝ (fderiv ℝ f) z := h1.differentiableAt (by norm_num)
  have hs := h.isSymmSndFDerivAt (by simp)
  have e : ∀ a w : E, fderiv ℝ (dbar f a) z w
      = fderiv ℝ (fderiv ℝ f) z w a + I * fderiv ℝ (fderiv ℝ f) z w (I • a) := by
    intro a w
    have d1 : DifferentiableAt ℝ (fun x => fderiv ℝ f x a) z :=
      hD.clm_apply (differentiableAt_const _)
    have d2 : DifferentiableAt ℝ (fun x => fderiv ℝ f x (I • a)) z :=
      hD.clm_apply (differentiableAt_const _)
    have H : HasFDerivAt (dbar f a) (fderiv ℝ (fun x => fderiv ℝ f x a) z
        + I • fderiv ℝ (fun x => fderiv ℝ f x (I • a)) z) z :=
      d1.hasFDerivAt.add (d2.hasFDerivAt.const_mul I)
    rw [H.fderiv, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
      fderiv_apply_lemma hD, fderiv_apply_lemma hD]
  rw [dbar, dbar, e, e, e, e, hs v u, hs v (I • u), hs (I • v) u, hs (I • v) (I • u)]
  ring
end GlobalTheory.PeriodSymm
