-- Prove2me | solution 1 for GlobalTheory.JetConj.second_deriv_sigma_product_at_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:28:24.323148+00:00
-- url     : https://prove2.me/submissions/a80ad45d-6823-497b-8bba-36cae663f36f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassPAddOfNeOfDerivNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_JetRelOfWeierstrassSystem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SecondDerivSigmaProductAtZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology PeriodPair
open GlobalTheory GlobalTheory.JetConj
variable {L : PeriodPair} {σ : ℂ → ℂ}
namespace GlobalTheory.JetConj
theorem _root_.solution (hσ : Differentiable ℂ σ) (a k l : ℂ) :
    deriv (deriv fun v => σ (a + v) * σ (a - v) * k + l * σ v ^ 2) 0 =
      2 * wr σ a * k + l * (2 * (deriv σ 0 ^ 2 + σ 0 * deriv (deriv σ) 0)) := by
  have p : ∀ {g : ℂ → ℂ}, Differentiable ℂ g → ∀ v, HasDerivAt (fun v => g (a + v)) (deriv g (a + v)) v :=
    fun hg v => (hg _).hasDerivAt.comp_const_add a v
  have m : ∀ {g : ℂ → ℂ}, Differentiable ℂ g → ∀ v, HasDerivAt (fun v => g (a - v)) (-deriv g (a - v)) v :=
    fun hg v => (hg _).hasDerivAt.comp_const_sub a v
  have e : (deriv fun v => σ (a + v) * σ (a - v) * k + l * σ v ^ 2) = fun v =>
      (deriv σ (a + v) * σ (a - v) - σ (a + v) * deriv σ (a - v)) * k + l * (2 * (σ v * deriv σ v)) := by
    funext v
    rw [((((p hσ v).fun_mul (m hσ v)).mul_const k).fun_add
      (((hσ v).hasDerivAt.fun_pow 2).const_mul l)).deriv]
    simp
    ring
  rw [e, (((((p hσ.deriv 0).fun_mul (m hσ 0)).fun_sub ((p hσ 0).fun_mul (m hσ.deriv 0))).mul_const k).fun_add
    ((((hσ 0).hasDerivAt.fun_mul (hσ.deriv 0).hasDerivAt).const_mul 2).const_mul l)).deriv]
  simp only [wr, add_zero, sub_zero]
  ring
end GlobalTheory.JetConj
