-- Prove2me | solution 1 for GlobalTheory.SimpleRoots.analyticAt_mvPolynomial_eval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:48:15.34139+00:00
-- url     : https://prove2.me/submissions/c88befc0-6f9c-4da9-96e6-9dc200d60ffa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_NodupRootsOfDerivativeNeZero

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
theorem _root_.solution (a : MvPolynomial (Fin d) ℂ) (x : Fin d → ℂ) :
    AnalyticAt ℂ (fun x : Fin d → ℂ => MvPolynomial.eval x a) x :=
  AnalyticOnNhd.eval_mvPolynomial a x (Set.mem_univ x)
end GlobalTheory.SimpleRoots
