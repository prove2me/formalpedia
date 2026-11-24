-- Prove2me | solution 1 for GlobalTheory.SimpleRoots.analyticAt_eval_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:04:02.549865+00:00
-- url     : https://prove2.me/submissions/82d2c130-450e-4bdd-b63a-7e8a1ed0bb86

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_NodupRootsOfDerivativeNeZero
import Theorems.Thm_GlobalTheory_SimpleRoots_eval_map_eq_sum
import Theorems.Thm_GlobalTheory_SimpleRoots_analyticAt_mvPolynomial_eval

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Polynomial
open GlobalTheory GlobalTheory.SimpleRoots
variable {d : ℕ}
namespace GlobalTheory.SimpleRoots
theorem _root_.solution (p : Polynomial (MvPolynomial (Fin d) ℂ)) (z : (Fin d → ℂ) × ℂ) :
    AnalyticAt ℂ (fun w : (Fin d → ℂ) × ℂ => (p.map (MvPolynomial.eval w.1)).eval w.2) z := by
  simp only [eval_map_eq_sum]
  refine Finset.analyticAt_fun_sum _ fun i _ => ?_
  exact ((analyticAt_mvPolynomial_eval _ _).comp analyticAt_fst).mul (analyticAt_snd.pow i)
end GlobalTheory.SimpleRoots
