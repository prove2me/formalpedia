-- Prove2me | solution 1 for NFOne.sg_sg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:30:48.120915+00:00
-- url     : https://prove2.me/submissions/c3af8194-65fa-497d-9b86-914e60161066

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
theorem _root_.solution (k r : ℕ) (i : Fin (2 * r + k + 1)) : sg k r (sg k r i) = i := by
  apply Fin.ext
  simp only [sg_val]
  have := i.isLt
  omega
end NFOne
