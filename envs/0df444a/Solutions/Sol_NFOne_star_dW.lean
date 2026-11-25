-- Prove2me | solution 1 for NFOne.star_dW
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:30:49.338065+00:00
-- url     : https://prove2.me/submissions/a21ad3cc-89a6-4062-9f29-c75f9f77a7bb

import Definitions.Def_Formalism_HermitianCurvature_OperatorsCommuteTranslations
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_NormFormOneUnitary_PRowWSColW
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
theorem _root_.solution (k r : ℕ) (i : Fin (2 * r + k + 1)) : star (dW k r i) = dW k r i := by
  unfold dW
  split_ifs <;> simp
end NFOne
