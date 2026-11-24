-- Prove2me | solution 1 for GlobalTheory.RowSpan.fisch_rowAct
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:39:42.599545+00:00
-- url     : https://prove2.me/submissions/c65d31b8-0568-4e89-a0e6-8e74c463685e

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RowDeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_InvariantOperatorValueTriangularChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_EqZeroOfFischSelf
import Theorems.Thm_GlobalTheory_RowSpan_rowAct_X
import Theorems.Thm_GlobalTheory_RowSpan_pderiv_rowAct
import Theorems.Thm_GlobalTheory_RowSpan_fisch_monomial
import Theorems.Thm_GlobalTheory_RowSpan_fisch_mul_X
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
namespace GlobalTheory.RowSpan
theorem _root_.solution (g : ∀ σ, Matrix (Fin (r σ)) (Fin (r σ)) ℚ) (P Q : MvPolynomial (Letter T r n) ℚ) :
    fisch (rowAct g P) Q = fisch P (rowAct (fun σ => (g σ).transpose) Q) := by
  induction P using MvPolynomial.induction_on generalizing Q with
  | C c =>
    have key : (constantCoeff : MvPolynomial (Letter T r n) ℚ →+* ℚ).comp
        (rowAct (fun σ => (g σ).transpose)).toRingHom = constantCoeff := by
      apply MvPolynomial.ringHom_ext
      · intro r
        simp [rowAct]
      · intro i
        simp [rowAct_X, constantCoeff_X]
    have e : rowAct g (C c : MvPolynomial (Letter T r n) ℚ) = C c := by simp [rowAct]
    rw [e, C_apply, fisch_monomial, fisch_monomial]
    exact congrArg (fun x => c * (_ * x)) (congrArg (fun f => f Q) key).symm
  | add p q hp hq => simp only [map_add, LinearMap.add_apply, hp, hq]
  | mul_X p s hp =>
    obtain ⟨σ, i, b⟩ := s
    rw [map_mul, rowAct_X, Finset.mul_sum, map_sum, LinearMap.sum_apply, fisch_mul_X, pderiv_rowAct, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← smul_eq_C_mul, mul_smul_comm, map_smul, LinearMap.smul_apply, fisch_mul_X, hp, map_smul]
    rfl
end GlobalTheory.RowSpan
