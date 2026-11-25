-- Prove2me | solution 1 for GlobalTheory.GoodCorank.div_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:35:56.863561+00:00
-- url     : https://prove2.me/submissions/e1bf1388-44e5-4c3c-9135-82ea82521449

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_Interface
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ScaledSecondIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_RowDataAdaptedChainData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsSaturatedGoodVectorsSmallCorank
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_zero


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
open Formalism.L2.FormalSeriesBounds
open GlobalTheory GlobalTheory.GoodCorank
variable {C : Type} [Field C] {V : VF C}
namespace GlobalTheory.GoodCorank
theorem _root_.solution {x y : C} (h : V.v y ≤ V.v x) : V.Ge 0 (x / y) := by
  by_cases hy : y = 0
  · subst hy; simpa using VF.Ge.zero (V := V) 0
  · have e : V.v x = V.v y + V.v (x / y) := by
      rw [← V.v.map_mul, mul_div_cancel₀ _ hy]
    have hy' : V.v y ≠ ⊤ := by
      intro h0
      have h1 : V.v (y * y⁻¹) = 0 := by rw [mul_inv_cancel₀ hy, V.v.map_one]
      rw [V.v.map_mul, h0, top_add] at h1
      exact WithTop.top_ne_zero h1
    unfold VF.Ge
    rw [e] at h
    have h2 : V.v y + 0 ≤ V.v y + V.v (x / y) := by simpa using h
    simpa using (WithTop.add_le_add_iff_left hy').mp h2
end GlobalTheory.GoodCorank
