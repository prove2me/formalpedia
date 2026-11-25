-- Prove2me | solution 1 for NFOne.unitary_P
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:28:50.338199+00:00
-- url     : https://prove2.me/submissions/50e9446a-b32a-48ea-9607-65a68d79464a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_NormFormOneUnitary_PRowWSColW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_NormFormOneUnitary_UnitaryP
import Theorems.Thm_NFOne_E_zero
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
open Matrix Finset Formalism.QuantumDeterminants
noncomputable section
open NFOne
namespace NFOne
theorem _root_.solution (k r j : ℕ) (V : ℕ → Fin (2 * r + k + 1) → ℂ)
    (V0 : ∀ c, j ≤ c → V c = 0)
    (Vs : ∀ b, b < j → ∀ q : Fin (2 * r + k + 1), r + k < q.val →
      V b q = if (sg k r q).val = b then 1 else 0)
    (Viso : ∀ b c, b < j → c < j → herm (Hpk k r) (V b) (V c) = 0) :
    (1 + Pm k r j V)ᴴ * Hpk k r * (1 + Pm k r j V) = Hpk k r := by
  have hE : (Pm k r j V)ᴴ * Hpk k r + Hpk k r * Pm k r j V +
      (Pm k r j V)ᴴ * (Hpk k r * Pm k r j V) = 0 := by
    ext p q
    simp only [Matrix.add_apply, Matrix.zero_apply]
    exact E_zero k r j V V0 Vs Viso p q
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_one]
  calc (1 + (Pm k r j V)ᴴ) * Hpk k r * (1 + Pm k r j V)
      = Hpk k r + ((Pm k r j V)ᴴ * Hpk k r + Hpk k r * Pm k r j V +
          (Pm k r j V)ᴴ * (Hpk k r * Pm k r j V)) := by
        simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]
        abel
    _ = Hpk k r := by rw [hE, add_zero]
end NFOne
