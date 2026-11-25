-- Prove2me | solution 1 for GlobalTheory.GoodCorank.isSat_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:35:10.05028+00:00
-- url     : https://prove2.me/submissions/93e0c352-c51e-4e96-bad5-9218dfb5e929

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_Interface
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ScaledSecondIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_RowDataAdaptedChainData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsSaturatedGoodVectorsSmallCorank
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_sum
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_mul_int
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_sum


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
theorem _root_.solution {M N : ℕ} {σ : Type} [Fintype σ] {A : Fin M → Fin N → C} {w : Fin N → σ → C}
    (hA : IsSat V A) (hw : IsSat V w) : IsSat V (fun ν c => ∑ k, A ν k * w k c) := by
  obtain ⟨hA0, A', hA', hAA⟩ := hA
  obtain ⟨hw0, w', hw', hww⟩ := hw
  refine ⟨fun ν c => VF.Ge.sum fun k _ => (hA0 _ _).mul_int (hw0 _ _),
    fun x c => ∑ k, w' x k * A' k c, fun x c => VF.Ge.sum fun k _ => (hw' _ _).mul_int (hA' _ _),
    fun c c' => ?_⟩
  have e1 : Matrix.of A * Matrix.of A' = 1 := by
    ext i j; simpa [Matrix.mul_apply, Matrix.one_apply] using hAA i j
  have e2 : Matrix.of w * Matrix.of w' = 1 := by
    ext i j; simpa [Matrix.mul_apply, Matrix.one_apply] using hww i j
  have e3 : (Matrix.of A * Matrix.of w) * (Matrix.of w' * Matrix.of A') = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (Matrix.of w), e2, Matrix.one_mul, e1]
  simpa [Matrix.mul_apply, Matrix.one_apply] using congrFun (congrFun e3 c) c'
end GlobalTheory.GoodCorank
