-- Prove2me | solution 1 for GlobalTheory.RowSpan.pderiv_rowAct
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:06:11.217299+00:00
-- url     : https://prove2.me/submissions/26d8eec6-2ac9-431d-9584-01b954ac71e9

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RowDeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_InvariantOperatorValueTriangularChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_EqZeroOfFischSelf
import Theorems.Thm_GlobalTheory_RowSpan_rowAct_X
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
theorem _root_.solution (g : ∀ σ, Matrix (Fin (r σ)) (Fin (r σ)) k) (σ : T) (j : Fin (r σ)) (b : Fin n)
    (Q : MvPolynomial (Letter T r n) k) :
    pderiv (⟨σ, j, b⟩ : Letter T r n) (rowAct g Q) =
      ∑ i, g σ i j • rowAct g (pderiv (⟨σ, i, b⟩ : Letter T r n) Q) := by
  classical
  have hX : ∀ ℓ : Letter T r n, pderiv (⟨σ, j, b⟩ : Letter T r n) (rowAct g (X ℓ)) =
      ∑ i, g σ i j • rowAct g (pderiv (⟨σ, i, b⟩ : Letter T r n) (X ℓ)) := by
    rintro ⟨σ', i', b'⟩
    rw [rowAct_X, map_sum]
    simp only [pderiv_C_mul, pderiv_X, Pi.single_apply]
    by_cases h : σ' = σ
    · subst h
      by_cases hb : b' = b
      · subst hb
        simp [apply_ite, smul_eq_C_mul]
      · simp [hb]
    · simp [h]
  induction Q using MvPolynomial.induction_on with
  | C c => simp [rowAct]
  | add p q hp hq => simp only [map_add, hp, hq, smul_add, Finset.sum_add_distrib]
  | mul_X p s hp =>
    rw [map_mul, pderiv_mul, hp, hX]
    simp only [pderiv_mul, map_add, map_mul, smul_add, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum,
      smul_mul_assoc, mul_smul_comm]
end GlobalTheory.RowSpan
