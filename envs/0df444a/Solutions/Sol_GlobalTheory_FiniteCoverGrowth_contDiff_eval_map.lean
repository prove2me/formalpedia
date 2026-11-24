-- Prove2me | solution 1 for GlobalTheory.FiniteCoverGrowth.contDiff_eval_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:08:05.746136+00:00
-- url     : https://prove2.me/submissions/7b14283a-d2a5-4fdc-b5e9-4b26bfa70181

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IntegralAndRationalOfPolynomialGrowth

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory GlobalTheory.FiniteCoverGrowth
namespace GlobalTheory.FiniteCoverGrowth
theorem _root_.solution {d : ℕ} (p : Polynomial (MvPolynomial (Fin d) ℂ)) :
    ContDiff ℂ 1 (fun z : (Fin d → ℂ) × ℂ => (p.map (MvPolynomial.eval z.1)).eval z.2) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa [Polynomial.map_add] using hp.add hq
  | monomial n a =>
    simp only [Polynomial.map_monomial, Polynomial.eval_monomial]
    refine ContDiff.mul ?_ (contDiff_snd.pow n)
    have : ContDiff ℂ 1 (fun x : Fin d → ℂ => MvPolynomial.eval x a) :=
      (AnalyticOnNhd.eval_mvPolynomial a).contDiff
    exact this.comp contDiff_fst
end GlobalTheory.FiniteCoverGrowth
