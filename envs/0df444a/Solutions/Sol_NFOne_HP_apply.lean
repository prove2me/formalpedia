-- Prove2me | solution 1 for NFOne.HP_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:50:09.924289+00:00
-- url     : https://prove2.me/submissions/88eb403a-bc7f-4644-ba57-63b628b082f1

import Definitions.Def_Formalism_HermitianCurvature_OperatorsCommuteTranslations
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_NormFormOneUnitary_PRowWSColW
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
    (Hpk k r * Pm k r j V) p q = if r ≤ p.val ∧ p.val ≤ r + k then dW k r p * Pm k r j V p q
      else Pm k r j V (sg k r p) q := by
  rw [Matrix.mul_apply]
  exact H_row k r p (fun l => Pm k r j V l q)
end NFOne
