-- Prove2me | solution 1 for GlobalTheory.Capelli.pderiv_swap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:51:14.359814+00:00
-- url     : https://prove2.me/submissions/aba6c20e-522f-42c0-87ba-2d75a6853adb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CommuteRowOpRightMixedOp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory GlobalTheory.Capelli
variable {K σ : Type*} [CommRing K]
namespace GlobalTheory.Capelli
theorem _root_.solution (u v : σ) (P : MvPolynomial σ K) :
    pderiv u (pderiv v P) = pderiv v (pderiv u P) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    simp only [Derivation.leibniz, map_add, smul_eq_mul, pderiv_X, Pi.single_apply, hp]
    split_ifs <;> simp <;> ring
end GlobalTheory.Capelli
