-- Prove2me | solution 1 for GlobalTheory.ThetaRational.analyticAt_eval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:33:00.254834+00:00
-- url     : https://prove2.me/submissions/89a6e99b-6a61-404d-a596-52d4715e7b1a

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsIntegralAndRationalTheta

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real ContDiff
open GlobalTheory GlobalTheory.ThetaRational
variable {E : Type*} {n : ℕ}
namespace GlobalTheory.ThetaRational
theorem _root_.solution (r : Polynomial (MvPolynomial (Fin n) ℂ)) (w : (Fin n → ℂ) × ℂ) :
    AnalyticAt ℂ (fun w : (Fin n → ℂ) × ℂ => (r.map (MvPolynomial.eval w.1)).eval w.2) w := by
  induction r using Polynomial.induction_on' with
  | add p q hp hq => simpa only [Polynomial.map_add, Polynomial.eval_add] using hp.fun_add hq
  | monomial k c =>
    simp only [Polynomial.map_monomial, Polynomial.eval_monomial]
    refine AnalyticAt.fun_mul ?_ (analyticAt_snd.fun_pow k)
    exact AnalyticAt.aeval_mvPolynomial (A := ℂ) (f := fun w : (Fin n → ℂ) × ℂ => w.1)
      (fun i => ((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.fst ℂ (Fin n → ℂ) ℂ)).analyticAt w) c
end GlobalTheory.ThetaRational
