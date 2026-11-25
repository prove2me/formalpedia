-- Prove2me | solution 1 for NFOne.Hpk_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:30:56.103833+00:00
-- url     : https://prove2.me/submissions/575b1508-35df-4029-8d94-ab3830d1376c

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
theorem _root_.solution (k r : ℕ) (p l : Fin (2 * r + k + 1)) : Hpk k r p l = Hpk k r l p := by
  have := p.isLt
  have := l.isLt
  simp only [Hpk, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)
end NFOne
