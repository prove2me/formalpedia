-- Prove2me | solution 1 for NFOne.Hpk_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:30:54.214732+00:00
-- url     : https://prove2.me/submissions/fbaf3a97-8286-40b3-ad0f-bea194f315f0

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
theorem _root_.solution (k r : ℕ) (p l : Fin (2 * r + k + 1)) :
    Hpk k r p l = if r ≤ p.val ∧ p.val ≤ r + k then (if l = p then dW k r p else 0)
      else (if l = sg k r p then 1 else 0) := by
  have := p.isLt
  have := l.isLt
  simp only [Hpk, dW, Fin.ext_iff, sg_val]
  split_ifs <;> first | rfl | (exfalso; omega)
end NFOne
