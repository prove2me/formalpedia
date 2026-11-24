-- Prove2me | solution 1 for GlobalTheory.RowSpan.fisch_mul_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:32:42.676476+00:00
-- url     : https://prove2.me/submissions/2fafa609-b5d1-45d7-a740-7043d98ddd08

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RowDeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_InvariantOperatorValueTriangularChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_EqZeroOfFischSelf
import Theorems.Thm_GlobalTheory_RowSpan_fisch_monomial
import Theorems.Thm_GlobalTheory_Wick_dividedContraction_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Wick.dividedContraction_one



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.RowSpan
open MvPolynomial Formalism.L2.Pj
variable {T : Type} {r : T → ℕ} {n : ℕ} {k : Type} [Field k]
variable {σ : Type}
namespace GlobalTheory.RowSpan
theorem _root_.solution (P Q : MvPolynomial σ ℚ) (v : σ) : fisch (P * X v) Q = fisch P (pderiv v Q) := by
  classical
  induction P using MvPolynomial.induction_on' with
  | add p q hp hq => simp only [add_mul, map_add, LinearMap.add_apply, hp, hq]
  | monomial m a =>
    rw [X, monomial_mul, mul_one, fisch_monomial, fisch_monomial, coeff_pderiv]
    have : ((m + Finsupp.single v 1).prod fun _ e => e.factorial : ℕ) =
        (m.prod fun _ e => e.factorial) * (m v + 1) := by
      rw [← Finsupp.mul_prod_erase' (m + Finsupp.single v 1) v _ (by simp),
        ← Finsupp.mul_prod_erase' m v _ (by simp), Finsupp.erase_add, Finsupp.erase_single, add_zero]
      simp [Nat.factorial_succ]
      ring
    rw [this]
    push_cast
    ring
end GlobalTheory.RowSpan
