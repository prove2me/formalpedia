-- Prove2me | solution 1 for GlobalTheory.mvExp_coeff_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:16:24.103798+00:00
-- url     : https://prove2.me/submissions/568130c5-a39c-4e70-abd3-62477cbef9be

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BiadditiveInSingleVariables
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_MfactMulCoeffMvExpLinear

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.UnitaryBoundIntegral
open GlobalTheory
variable {C : Type} [Field C] [CharZero C] {σ : Type}
omit [CharZero C]
namespace GlobalTheory
theorem _root_.solution (a : MvPowerSeries σ C) (m : σ →₀ ℕ) :
    MvPowerSeries.coeff m (mvExp a) =
      ∑ k ∈ Finset.range (m.degree + 1), MvPowerSeries.coeff m (a ^ k) / (k.factorial : C) := rfl
end GlobalTheory
