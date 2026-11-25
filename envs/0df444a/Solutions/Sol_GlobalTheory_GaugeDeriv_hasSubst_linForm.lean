-- Prove2me | solution 1 for GlobalTheory.GaugeDeriv.hasSubst_linForm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:45:35.848136+00:00
-- url     : https://prove2.me/submissions/e3284167-b09c-4f22-9288-1f60aceaca3f

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TwoMulChainStartIndexAddOneOfOdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_SubstEqOfCoeffEqOfKilled
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PderivLeafGaugeEqPairingAddIntegral
import Theorems.Thm_GlobalTheory_GaugeDeriv_constantCoeff_linForm

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
theorem _root_.solution (e : ι → WV I → C) (e' : ι' → WV I → C) :
    MvPowerSeries.HasSubst (linForm e e') := MvPowerSeries.hasSubst_of_constantCoeff_zero (fun w => constantCoeff_linForm e e' w)
end GlobalTheory.GaugeDeriv
