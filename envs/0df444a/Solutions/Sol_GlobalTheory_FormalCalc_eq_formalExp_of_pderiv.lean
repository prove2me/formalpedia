-- Prove2me | solution 1 for GlobalTheory.FormalCalc.eq_formalExp_of_pderiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:26:21.396813+00:00
-- url     : https://prove2.me/submissions/06a3ac79-aa69-4be5-9eeb-afeee6edc672

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FormalExpMulFormalExpNeg
import Theorems.Thm_GlobalTheory_FormalCalc_constantCoeff_formalExp
import Theorems.Thm_GlobalTheory_FormalCalc_isUnit_formalExp
import Theorems.Thm_GlobalTheory_FormalCalc_pderiv_formalExp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.FormalCalc
open MvPowerSeries
variable {σ τ A B : Type*} [CommRing A] [Algebra ℚ A] [CommRing B] [Algebra ℚ B]
namespace GlobalTheory.FormalCalc
theorem _root_.solution {f u : MvPowerSeries σ A} (hf : constantCoeff f = 0)
    (hu : constantCoeff u = 1) (h : ∀ i, pderiv A i u = u * pderiv A i f) :
    u = formalExp f := by
  haveI : IsAddTorsionFree A := .of_module_rat A
  have hn : constantCoeff (-f) = 0 := by simp [hf]
  have key : ∀ v : MvPowerSeries σ A, constantCoeff v = 1 →
      (∀ i, pderiv A i v = v * pderiv A i f) → v * formalExp (-f) = 1 := by
    intro v hv hd
    refine pderiv.ext (fun i => ?_) (by simp [hv, constantCoeff_formalExp hn])
    rw [Derivation.leibniz, pderiv_formalExp hn, hd, map_neg, pderiv_one, smul_eq_mul,
      smul_eq_mul]
    ring
  exact (isUnit_formalExp hn).mul_right_cancel
    ((key u hu h).trans (key _ (constantCoeff_formalExp hf) (pderiv_formalExp hf)).symm)
end GlobalTheory.FormalCalc
