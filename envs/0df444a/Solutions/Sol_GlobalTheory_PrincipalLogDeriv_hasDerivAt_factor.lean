-- Prove2me | solution 1 for GlobalTheory.PrincipalLogDeriv.hasDerivAt_factor
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:44:13.179579+00:00
-- url     : https://prove2.me/submissions/d8f8169b-95e8-4488-9489-b2f8d0b867c3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LogDerivRiemannZetaLocalZeroSumStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NegReLogDerivPrincipalLFunctionLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory GlobalTheory.PrincipalLogDeriv
namespace GlobalTheory.PrincipalLogDeriv
theorem _root_.solution {p : ℕ} (hp : p.Prime) (s : ℂ) :
    HasDerivAt (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) ((p : ℂ) ^ (-s) * Complex.log p) s := by
  have hc : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have h : HasDerivAt (fun z : ℂ => (p : ℂ) ^ (-z)) ((p : ℂ) ^ (-s) * Complex.log p * (-1)) s :=
    ((hasDerivAt_id' s).neg).const_cpow (Or.inl hc)
  have h2 : HasDerivAt (fun z : ℂ => 1 - (p : ℂ) ^ (-z))
      (-((p : ℂ) ^ (-s) * Complex.log p * (-1))) s := h.const_sub 1
  convert h2 using 1
  ring
end GlobalTheory.PrincipalLogDeriv
