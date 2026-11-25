-- Prove2me | solution 1 for NFOne.H_row
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:39:03.529813+00:00
-- url     : https://prove2.me/submissions/a3131a33-3682-4e5d-ae2c-b1f0a38a8436

import Definitions.Def_Formalism_HermitianCurvature_OperatorsCommuteTranslations
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_NormFormOneUnitary_PRowWSColW
import Theorems.Thm_NFOne_sg_val
import Theorems.Thm_NFOne_Hpk_eq
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
theorem _root_.solution (k r : ℕ) (p : Fin (2 * r + k + 1)) (f : Fin (2 * r + k + 1) → ℂ) :
    ∑ l, Hpk k r p l * f l =
      if r ≤ p.val ∧ p.val ≤ r + k then dW k r p * f p else f (sg k r p) := by
  by_cases h : r ≤ p.val ∧ p.val ≤ r + k
  · simp [Hpk_eq, h, ite_mul]
  · simp [Hpk_eq, h, ite_mul]
end NFOne
