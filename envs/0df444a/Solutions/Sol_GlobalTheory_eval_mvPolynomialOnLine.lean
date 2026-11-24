-- Prove2me | solution 1 for GlobalTheory.eval_mvPolynomialOnLine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:38:08.533851+00:00
-- url     : https://prove2.me/submissions/72cb4fd2-5152-487b-bdd2-29a1cb77337a

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsConnectedAndDenseComplHypersurface

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
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {d : ℕ} (q : MvPolynomial (Fin d) ℂ) (a b : Fin d → ℂ) (t : ℂ) :
    (mvPolynomialOnLine q a b).eval t = MvPolynomial.eval (a + t • (b - a)) q := by
  unfold mvPolynomialOnLine
  induction q using MvPolynomial.induction_on with
  | C c => simp
  | add p r hp hr => rw [map_add, Polynomial.eval_add, hp, hr, map_add]
  | mul_X p i hp =>
    simp only [map_mul, Polynomial.eval_mul, hp, MvPolynomial.aeval_X, MvPolynomial.eval_X,
      Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X, Pi.add_apply, Pi.smul_apply,
      Pi.sub_apply, smul_eq_mul]
    ring
end GlobalTheory
