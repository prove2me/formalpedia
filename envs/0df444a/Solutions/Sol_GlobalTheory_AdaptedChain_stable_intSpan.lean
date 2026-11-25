-- Prove2me | solution 1 for GlobalTheory.AdaptedChain.stable_intSpan
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:27:35.004797+00:00
-- url     : https://prove2.me/submissions/84f9195d-6563-4d8d-82da-a089f85c248b

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ScaledSecondIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_RowDataAdaptedChainData
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_mul_int


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism.L2.FormalSeriesBounds
open GlobalTheory GlobalTheory.AdaptedChain
variable {C : Type} [Field C] {V : VF C} {d : ℕ} {I J : Type} [Fintype I] [Fintype J]
variable {X : Cart V d I J}
namespace GlobalTheory.AdaptedChain
theorem _root_.solution {ι : Type} [Fintype ι] (U : ι → I → C) : Stable V (intSpan V U) := by
  rintro r hr u ⟨A, h1, h2⟩
  exact ⟨fun b => r * A b, fun b => hr.mul_int (h1 b), fun x => by
    simp [h2, Finset.mul_sum, mul_assoc]⟩
end GlobalTheory.AdaptedChain
