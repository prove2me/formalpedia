-- Prove2me | solution 1 for GlobalTheory.hasDerivAt_eval_line
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:40:53.721836+00:00
-- url     : https://prove2.me/submissions/fcae2099-0bea-4292-98bb-a8cec381f0c2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LineDerivListEqIteratedFDeriv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NormPderivIterLeOfAnalyticAt
import Theorems.Thm_GlobalTheory_polyDerivLinear_apply
import Theorems.Thm_GlobalTheory_polyDeriv_zero
import Theorems.Thm_GlobalTheory_polyDeriv_monomial
import Theorems.Thm_GlobalTheory_polyDeriv_C
import Theorems.Thm_GlobalTheory_polyDeriv_one
import Theorems.Thm_GlobalTheory_polyDeriv_zero_fun
import Theorems.Thm_GlobalTheory_lineDerivList_nil
import Theorems.Thm_GlobalTheory_lineDerivList_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.lineDerivList_nil
attribute [local simp] GlobalTheory.lineDerivList_zero


attribute [local simp] GlobalTheory.polyDerivLinear_apply
attribute [local simp] GlobalTheory.polyDeriv_zero
attribute [local simp] GlobalTheory.polyDeriv_monomial
attribute [local simp] GlobalTheory.polyDeriv_C
attribute [local simp] GlobalTheory.polyDeriv_one
attribute [local simp] GlobalTheory.polyDeriv_zero_fun

set_option autoImplicit false
open Filter Topology
open GlobalTheory
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {ι : Type*} [DecidableEq ι]
namespace GlobalTheory
theorem _root_.solution (Q : MvPolynomial ι 𝕜) (z : ι → 𝕜) (k : ι) :
    HasDerivAt (fun t : 𝕜 => MvPolynomial.eval (z + t • (Pi.single k 1 : ι → 𝕜)) Q)
      (MvPolynomial.eval z (MvPolynomial.pderiv k Q)) 0 := by
  induction Q using MvPolynomial.induction_on with
  | C c => simpa using hasDerivAt_const (0 : 𝕜) c
  | add P Q hP hQ => simpa using hP.fun_add hQ
  | mul_X P j hP =>
    have hj : HasDerivAt (fun t : 𝕜 => z j + t * (Pi.single k 1 : ι → 𝕜) j)
        ((Pi.single k 1 : ι → 𝕜) j) 0 := by
      simpa using ((hasDerivAt_id (0 : 𝕜)).mul_const ((Pi.single k 1 : ι → 𝕜) j)).const_add (z j)
    have := hP.fun_mul hj
    have e : (fun t : 𝕜 => MvPolynomial.eval (z + t • (Pi.single k 1 : ι → 𝕜))
        (P * MvPolynomial.X j)) = fun t : 𝕜 =>
          MvPolynomial.eval (z + t • (Pi.single k 1 : ι → 𝕜)) P
            * (z j + t * (Pi.single k 1 : ι → 𝕜) j) := by
      funext t; simp
    rw [e]
    refine this.congr_deriv ?_
    by_cases h : j = k
    · subst h; simp [add_comm, mul_comm]
    · simp [h, mul_comm]
end GlobalTheory
