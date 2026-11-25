-- Prove2me | solution 1 for NFOne.projection_vector_coordinate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:30:46.753001+00:00
-- url     : https://prove2.me/submissions/da1984a7-efbf-4fe5-9cc7-c15b800c57db

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_NormFormOneUnitary_UnitaryP
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_NormFormOneUnitary_HermitianOrthogonalProjectionVector
import Theorems.Thm_NFOne_y_esI_zero
import Theorems.Thm_NFOne_sg_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] NFOne.sg_val



set_option autoImplicit false
open Matrix Finset Formalism.QuantumDeterminants Formalism.FourierDecayAlt.C3
noncomputable section
open NFOne
namespace NFOne
theorem _root_.solution (k r j : ℕ) (hj : j ≤ r) (y : Fin j → Fin (2 * r + k + 1) → ℂ)
    (N : Matrix (Fin j) (Fin j) ℂ)
    (hy2 : ∀ (a : Fin j) (b : Fin r), j ≤ b.val → y a (esI k r b) = 0)
    (hNM : N * (Matrix.of fun a b : Fin j => y a (sR k r j hj b)) = 1)
    (b : ℕ) (hb : b < j) (q : Fin (2 * r + k + 1)) (hq : r + k < q.val) :
    Vv y N b q = if (sg k r q).val = b then 1 else 0 := by
  have hq2 := q.isLt
  unfold Vv
  rw [dif_pos hb]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hs : (sg k r q).val < j
  · have hsr : sR k r j hj ⟨(sg k r q).val, hs⟩ = q := by
      apply Fin.ext
      show 2 * r + k - (sg k r q).val = q.val
      simp only [sg_val]
      omega
    have h := congrFun (congrFun hNM ⟨b, hb⟩) ⟨(sg k r q).val, hs⟩
    rw [Matrix.mul_apply] at h
    simp only [Matrix.of_apply, hsr, Matrix.one_apply, Fin.ext_iff] at h
    rw [h]
    split_ifs <;> first | rfl | (exfalso; omega)
  · have h0 : ∀ a, y a q = 0 := fun a => y_esI_zero k r j y hy2 a q hq hs
    simp only [h0, mul_zero, Finset.sum_const_zero]
    rw [if_neg (by omega)]
end NFOne
