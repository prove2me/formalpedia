-- Prove2me | solution 1 for GlobalTheory.RowSpan.RowStable.rowShift_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:06:11.611042+00:00
-- url     : https://prove2.me/submissions/1698c965-614c-4fa3-a057-e3fbbe3d3edc

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
namespace RowStable
theorem _root_.solution {U : Submodule k (MvPolynomial (Letter T r n) k)} (hU : RowStable U)
    (σ : T) (i i' : Fin (r σ)) (hi : i' < i) (t : k) {P : MvPolynomial (Letter T r n) k} (hP : P ∈ U) :
    rowShift r n k σ i i' t P ∈ U := by
  classical
  have e : rowShift r n k σ i i' t =
      rowAct (Function.update (β := fun σ => Matrix (Fin (r σ)) (Fin (r σ)) k) (fun _ => 1) σ
        (Matrix.transvection i i' t)) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨σ', j, b⟩
    rw [rowAct_X, rowShift, aeval_X]
    by_cases h : σ' = σ
    · subst h
      simp only [Function.update_self, Matrix.transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single,
        Matrix.of_apply, map_add, add_mul, Finset.sum_add_distrib]
      by_cases hj : j = i
      · subst hj
        simp [apply_ite, ite_mul]
      · simp [apply_ite, ite_mul, hj, Ne.symm hj]
    · simp [h, Function.update_of_ne h, Matrix.one_apply, apply_ite, ite_mul]
  rw [e]
  refine hU _ (fun σ' => ?_) P hP
  by_cases h : σ' = σ
  · subst h
    rw [Function.update_self, Matrix.det_transvection_of_ne _ _ hi.ne']
    exact isUnit_one
  · simp [Function.update_of_ne h]
end RowStable
end GlobalTheory.RowSpan
