-- Prove2me | solution 1 for GlobalTheory.eq_of_inner_eq_on_dense_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:43:43.465405+00:00
-- url     : https://prove2.me/submissions/a77f13f1-8237-4f3a-acf5-846d388ee595

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsContinuousMultilinearMapOfInnerProd
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open Formalism.MainNotions.S NumberField
open scoped InnerProductSpace
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {s : Set E} (hs : Dense (Submodule.span ℂ s : Set E)) {a b : E}
    (h : ∀ y ∈ s, ⟪y, a⟫_ℂ = ⟪y, b⟫_ℂ) : a = b := by
  have h1 : ∀ y ∈ Submodule.span ℂ s, ⟪y, a⟫_ℂ = ⟪y, b⟫_ℂ := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact h y hy
    | zero => simp
    | add y z _ _ hy hz => rw [inner_add_left, inner_add_left, hy, hz]
    | smul c y _ hy => rw [inner_smul_left, inner_smul_left, hy]
  have h2 : (fun y : E => ⟪y, a⟫_ℂ) = fun y => ⟪y, b⟫_ℂ :=
    Continuous.ext_on hs (by fun_prop) (by fun_prop) h1
  exact ext_inner_left ℂ fun y => congrFun h2 y
end GlobalTheory
