-- Prove2me | solution 1 for GlobalTheory.Mem.GelfCheck.upper_kill
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:55:44.255996+00:00
-- url     : https://prove2.me/submissions/b1b2cefb-d477-40fd-b2c1-8c0bb5ad22aa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_GelfA
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementB
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_TracePowApply
import Theorems.Thm_GlobalTheory_Mem_GelfCheck_pow_cov
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.GelfCheck
open MvPolynomial GlobalTheory.Mem.Gelf
variable {R : Type} [CommRing R] {V : Type} [AddCommGroup V] [Module R V] {N : ℕ}
  {E : Matrix (Fin N) (Fin N) (Module.End R V)} {μ : Fin N → R} {v : V}
namespace GlobalTheory.Mem.GelfCheck
theorem _root_.solution (h : GlRel E) (hv : ∀ a b, a < b → E a b v = 0) (k : ℕ) (a b : Fin N) (hab : a < b) :
    (E ^ k) a b v = 0 := by
  induction k generalizing a b with
  | zero => simp [Matrix.one_apply, hab.ne]
  | succ k ih =>
    rw [pow_succ', Matrix.mul_apply, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    rcases lt_or_ge c b with hc | hc
    · simp [ih c b hc]
    · have := congrArg (fun f : Module.End R V => f v) (pow_cov h k c b a c)
      simp only [LinearMap.sub_apply, Module.End.mul_apply, hv a c (hab.trans_le hc), map_zero, sub_zero,
        if_true, if_neg hab.ne', LinearMap.zero_apply, ih a b hab] at this
      simpa using this
end GlobalTheory.Mem.GelfCheck
