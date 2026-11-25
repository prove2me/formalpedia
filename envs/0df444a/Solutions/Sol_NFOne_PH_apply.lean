-- Prove2me | solution 1 for NFOne.PH_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:51:22.847969+00:00
-- url     : https://prove2.me/submissions/34ee3f27-fbdd-4a0d-b2e9-974b6c66740e

import Definitions.Def_Formalism_HermitianCurvature_OperatorsCommuteTranslations
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_NormFormOneUnitary_PRowWSColW
import Theorems.Thm_NFOne_Hpk_symm
import Theorems.Thm_NFOne_H_row

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Formalism.QuantumDeterminants
noncomputable section
open NFOne
namespace NFOne
theorem _root_.solution (k r j : ℕ) (V : ℕ → Fin (2 * r + k + 1) → ℂ) (p q : Fin (2 * r + k + 1)) :
    ((Pm k r j V)ᴴ * Hpk k r) p q = if r ≤ q.val ∧ q.val ≤ r + k then dW k r q * star (Pm k r j V q p)
      else star (Pm k r j V (sg k r q) p) := by
  have h : ∑ l, Hpk k r q l * star (Pm k r j V l p) =
      if r ≤ q.val ∧ q.val ≤ r + k then dW k r q * star (Pm k r j V q p)
      else star (Pm k r j V (sg k r q) p) := H_row k r q (fun l => star (Pm k r j V l p))
  rw [Matrix.mul_apply, ← h]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Matrix.conjTranspose_apply, Hpk_symm k r l q, mul_comm]
end NFOne
