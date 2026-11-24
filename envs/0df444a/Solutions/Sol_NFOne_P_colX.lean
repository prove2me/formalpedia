-- Prove2me | solution 1 for NFOne.P_colX
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:42:20.120833+00:00
-- url     : https://prove2.me/submissions/7086a5c2-54a0-48ba-b3af-a2a529743ce1

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
theorem _root_.solution (k r j : ℕ) (V : ℕ → Fin (2 * r + k + 1) → ℂ) (p q : Fin (2 * r + k + 1))
    (hq : q.val < r) : Pm k r j V p q = 0 := by
  simp only [Pm]
  split_ifs <;> first | rfl | (exfalso; omega)
end NFOne
