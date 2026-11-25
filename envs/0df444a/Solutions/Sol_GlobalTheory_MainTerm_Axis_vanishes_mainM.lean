-- Prove2me | solution 1 for GlobalTheory.MainTerm.Axis.vanishes_mainM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:45:29.390028+00:00
-- url     : https://prove2.me/submissions/0103a56d-ce78-4154-8c93-f728144875e3

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TwoMulChainStartIndexAddOneOfOdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_CoeffLeafGaugeSubMainTermEqZeroOnFirstAxis
import Theorems.Thm_GlobalTheory_MainTerm_Axis_VanishesOnFirstAxis_mul_left
import Theorems.Thm_GlobalTheory_MainTerm_Axis_VanishesOnFirstAxis_smul
import Theorems.Thm_GlobalTheory_MainTerm_Axis_VanishesOnFirstAxis_sum
import Theorems.Thm_GlobalTheory_MainTerm_Axis_vanishes_X_inr
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_sum
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_sum


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
theorem _root_.solution [Fintype ι] [Fintype ι'] (V : VF C) (i : ℕ) (Φ : ι' → ι → C) :
    VanishesOnFirstAxis (mainM V i Φ) :=
  (VanishesOnFirstAxis.sum _ fun b => VanishesOnFirstAxis.sum _ fun _ =>
    ((vanishes_X_inr b).mul_left _).smul _).smul _
end GlobalTheory.MainTerm.Axis
