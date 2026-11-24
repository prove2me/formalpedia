-- Prove2me | solution 1 for GlobalTheory.RowSpan.mem_harmK_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:06:19.963701+00:00
-- url     : https://prove2.me/submissions/9614efe4-e8e4-415e-9c6a-923d86632539

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
namespace GlobalTheory.RowSpan
theorem _root_.solution (cc : T → T) (isX : T → Prop) (P : MvPolynomial (Letter T r n) k) :
    P ∈ harmK r n k cc isX (fun _ => 1) ↔ ∀ τ, isX τ → ∀ (i : Fin (r τ)) (i' : Fin (r (cc τ))),
      ∑ b : Fin n, pderiv (⟨τ, i, b⟩ : Letter T r n) (pderiv (⟨cc τ, i', b⟩ : Letter T r n) P) = 0 := by
  simp only [harmK, Submodule.mem_iInf, LinearMap.mem_ker, lap,
    LinearMap.sum_apply, LinearMap.smul_apply, Matrix.one_apply, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rfl
end GlobalTheory.RowSpan
