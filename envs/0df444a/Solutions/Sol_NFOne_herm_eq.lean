-- Prove2me | solution 1 for NFOne.herm_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:42:21.155067+00:00
-- url     : https://prove2.me/submissions/88441f47-2590-44ca-8765-27c280d3d706

import Definitions.Def_Formalism_HermitianCurvature_OperatorsCommuteTranslations
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_NormFormOneUnitary_PRowWSColW

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
theorem _root_.solution (k r : ℕ) (v w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) v w = ∑ i, star (w i) * (Hpk k r *ᵥ v) i := rfl
end NFOne
