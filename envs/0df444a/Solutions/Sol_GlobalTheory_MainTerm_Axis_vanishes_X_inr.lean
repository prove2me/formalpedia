-- Prove2me | solution 1 for GlobalTheory.MainTerm.Axis.vanishes_X_inr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:35:06.130745+00:00
-- url     : https://prove2.me/submissions/95dd270c-8563-4457-8e44-c8b77f869119

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TwoMulChainStartIndexAddOneOfOdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_CoeffLeafGaugeSubMainTermEqZeroOnFirstAxis
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical
open GlobalTheory GlobalTheory.MainTerm GlobalTheory.MainTerm.Axis
variable {C : Type} [Field C] {ι ι' : Type}
namespace GlobalTheory.MainTerm.Axis
theorem _root_.solution (b : ι') :
    VanishesOnFirstAxis (MvPowerSeries.X (Sum.inr b) : MvPowerSeries (ι ⊕ ι') C) := by
  intro μ hμ
  rw [MvPowerSeries.coeff_X, if_neg]
  intro h
  have h1 := hμ b
  rw [h] at h1
  simp at h1
end GlobalTheory.MainTerm.Axis
