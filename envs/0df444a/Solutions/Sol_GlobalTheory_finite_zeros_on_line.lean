-- Prove2me | solution 1 for GlobalTheory.finite_zeros_on_line
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:50:07.034973+00:00
-- url     : https://prove2.me/submissions/ac4ca5fc-64c0-4de5-a1f7-405fd4844274

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsConnectedAndDenseComplHypersurface
import Theorems.Thm_GlobalTheory_eval_mvPolynomialOnLine

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
theorem _root_.solution {d : ℕ} (q : MvPolynomial (Fin d) ℂ) (a b : Fin d → ℂ)
    (hb : MvPolynomial.eval b q ≠ 0) :
    {t : ℂ | MvPolynomial.eval (a + t • (b - a)) q = 0}.Finite := by
  have hP : mvPolynomialOnLine q a b ≠ 0 := by
    intro h
    apply hb
    have := eval_mvPolynomialOnLine q a b 1
    simpa [h] using this.symm
  convert Polynomial.finite_setOfPred_isRoot hP using 1
  ext t
  simp only [Set.mem_ofPred_eq, Polynomial.IsRoot, eval_mvPolynomialOnLine]
end GlobalTheory
