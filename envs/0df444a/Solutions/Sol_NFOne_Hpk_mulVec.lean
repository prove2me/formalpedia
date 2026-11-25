-- Prove2me | solution 1 for NFOne.Hpk_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:50:10.932344+00:00
-- url     : https://prove2.me/submissions/c294777b-de61-4f0b-8409-6ad4e116449b

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
theorem _root_.solution (k r : ℕ) (v : Fin (2 * r + k + 1) → ℂ) (p : Fin (2 * r + k + 1)) :
    (Hpk k r *ᵥ v) p = if r ≤ p.val ∧ p.val ≤ r + k then dW k r p * v p else v (sg k r p) := by
  exact H_row k r p v
end NFOne
