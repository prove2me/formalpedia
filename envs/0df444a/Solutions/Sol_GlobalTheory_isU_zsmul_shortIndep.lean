-- Prove2me | solution 1 for GlobalTheory.isU_zsmul_shortIndep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:04:44.891595+00:00
-- url     : https://prove2.me/submissions/129ccced-252b-400d-9f51-4b8b51362dbd

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GaussianTailBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitC
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_ExistsShortIndependentIsU
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_Hf_im_smul_left


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex ReciprocityTheory.ChartRestriction.G.I2
open scoped InnerProductSpace
open GlobalTheory
noncomputable section
variable {E : Type} [Field E] [NumberField E]
variable {dim : (E →+* ℂ) → ℕ}
namespace GlobalTheory
theorem _root_.solution {I : Submodule ℤ (Vsp dim)} {x u : Vsp dim} (k : ℤ) (hu : IsU I x u) :
    IsU I (k • x) (k • u) := by
  rw [← Int.cast_smul_eq_zsmul ℝ k x, ← Int.cast_smul_eq_zsmul ℝ k u]
  exact ⟨(IR I).smul_mem _ hu.1, fun a ha => by
    rw [real_inner_smul_left, hu.2 a ha, Hf_im_smul_left]⟩
end GlobalTheory
