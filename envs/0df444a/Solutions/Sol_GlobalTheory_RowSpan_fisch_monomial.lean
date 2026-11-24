-- Prove2me | solution 1 for GlobalTheory.RowSpan.fisch_monomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:26:51.422028+00:00
-- url     : https://prove2.me/submissions/9a09e967-9e35-4511-b7e5-d8298f81a492

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RowDeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_InvariantOperatorValueTriangularChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_EqZeroOfFischSelf
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
theorem _root_.solution (m : σ →₀ ℕ) (a : ℚ) (Q : MvPolynomial σ ℚ) :
    fisch (monomial m a) Q = a * (((m.prod fun _ e => e.factorial : ℕ) : ℚ) * Q.coeff m) := by
  have : (monomial m a : MvPolynomial σ ℚ) = a • basisMonomials σ ℚ m := by simp [smul_monomial]
  rw [this, map_smul, fisch, Module.Basis.constr_basis]
  simp
end GlobalTheory.RowSpan
