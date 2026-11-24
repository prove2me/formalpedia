-- Prove2me | solution 1 for GlobalTheory.SimpleRoots.eq_of_map_eval_eq_of_dense
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:48:16.826963+00:00
-- url     : https://prove2.me/submissions/ab43a705-8da7-462a-b80d-978f1754ba94

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_NodupRootsOfDerivativeNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsConnectedUnramifiedCoverOfIrreducible

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory GlobalTheory.SimpleRoots
open Polynomial
variable {d : ℕ}
namespace GlobalTheory.SimpleRoots
theorem _root_.solution {a b : Polynomial (MvPolynomial (Fin d) ℂ)}
    {U : Set (Fin d → ℂ)} (hU : Dense U)
    (h : ∀ x ∈ U, a.map (MvPolynomial.eval x) = b.map (MvPolynomial.eval x)) : a = b := by
  ext i
  have hfun : (fun x => MvPolynomial.eval x (a.coeff i)) = fun x => MvPolynomial.eval x (b.coeff i) := by
    refine Continuous.ext_on hU (MvPolynomial.continuous_eval _) (MvPolynomial.continuous_eval _) ?_
    intro x hx
    have := congrArg (fun P => Polynomial.coeff P i) (h x hx)
    simpa [Polynomial.coeff_map] using this
  exact congrArg (fun c => MvPolynomial.coeff _ c) (MvPolynomial.funext fun x => congrFun hfun x)
end GlobalTheory.SimpleRoots
