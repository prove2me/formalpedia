-- Prove2me | solution 1 for NFOne.z_fix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:59:57.383319+00:00
-- url     : https://prove2.me/submissions/902a6ff4-e711-4916-9da2-163aa67e2e27

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_NormFormOneUnitary_UnitaryP
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_NormFormOneUnitary_HermitianOrthogonalProjectionVector
import Theorems.Thm_NFOne_Hpk_mulVec
import Theorems.Thm_NFOne_P_XW
import Theorems.Thm_NFOne_P_rowWS_colW
import Theorems.Thm_NFOne_herm_eq
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
theorem _root_.solution (k r j : ℕ) (V : ℕ → Fin (2 * r + k + 1) → ℂ) (z' : Fin (2 * r + k + 1) → ℂ)
    (hz : inWb k r z') (Vz : ∀ c, herm (Hpk k r) z' (V c) = 0) :
    (1 + Pm k r j V) *ᵥ z' = z' := by
  funext p
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Pi.add_apply]
  suffices h : (Pm k r j V *ᵥ z') p = 0 by rw [h, add_zero]
  have hterm : ∀ q : Fin (2 * r + k + 1), Pm k r j V p q * z' q =
      if p.val < r then -(star (V p.val q) * (Hpk k r *ᵥ z') q) else 0 := by
    intro q
    have hq2 := q.isLt
    by_cases hW : r ≤ q.val ∧ q.val ≤ r + k
    · rw [Hpk_mulVec, if_pos hW]
      by_cases hp : p.val < r
      · rw [P_XW k r j V p q hp hW.1 hW.2, if_pos hp]
        ring
      · rw [P_rowWS_colW k r j V p q (by omega) hW.2, if_neg hp, zero_mul]
    · have hzq : z' q = 0 := hz q (by omega)
      have hz2 : z' (sg k r q) = 0 := hz (sg k r q) (by simp only [sg_val]; omega)
      rw [hzq, mul_zero, Hpk_mulVec, if_neg hW, hz2, mul_zero, neg_zero, ite_self]
  rw [show (Pm k r j V *ᵥ z') p = ∑ q, Pm k r j V p q * z' q from rfl]
  simp only [hterm]
  by_cases hp : p.val < r
  · simp only [if_pos hp, Finset.sum_neg_distrib, neg_eq_zero]
    have := Vz p.val
    rw [herm_eq] at this
    exact this
  · simp [if_neg hp]
end NFOne
