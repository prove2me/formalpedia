-- Prove2me | solution 1 for GlobalTheory.GaugeDeriv.hPullW_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:34:22.905997+00:00
-- url     : https://prove2.me/submissions/f386102b-97f6-44f8-857f-e7dc94f41133

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TwoMulChainStartIndexAddOneOfOdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_SubstEqOfCoeffEqOfKilled
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PderivLeafGaugeEqPairingAddIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical
noncomputable section
open GlobalTheory GlobalTheory.GaugeDeriv
variable {C : Type} [Field C] {I : Fin 2 → Type} [∀ g, Fintype (I g)]
variable {ι ι' : Type} [Fintype ι] [Fintype ι']
namespace GlobalTheory.GaugeDeriv
theorem _root_.solution (H : MvPowerSeries (WV I) C) (e : ι → WV I → C) (e' : ι' → WV I → C) :
    hPullW H e e' = MvPowerSeries.subst (linForm e e') H := rfl
end GlobalTheory.GaugeDeriv
