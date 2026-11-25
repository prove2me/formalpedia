-- Prove2me | solution 1 for GlobalTheory.TensorLat.eq_zero_of_contr_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:32:46.72331+00:00
-- url     : https://prove2.me/submissions/8f8d1d6d-29a9-46a4-99c1-54d9e6ec7d07

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ActEMemSpanOmega
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_ETSymmApply
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_InhabSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_FlatMemLatIffStdLat
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_DimC_key
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_actE_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_actE_zero_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_dim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.I2.actE_apply



set_option autoImplicit false
open GlobalTheory GlobalTheory.TensorLat
open NumberField Complex ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.GeometryOfNumbersTheory (stdLat)
noncomputable section
variable {E : Type} [Field E] [NumberField E] {dim : (E →+* ℂ) → ℕ} {n : ℕ}
variable [IsCMField E]
namespace GlobalTheory.TensorLat
theorem _root_.solution {S : Set (Fin n → E)} (hS : Submodule.span E S = ⊤)
    {γ : Fin n → Vsp dim} (h : ∀ w ∈ S, contr γ w = 0) : γ = 0 := by
  have key : ∀ w ∈ Submodule.span E S, contr γ w = 0 := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw => exact h w hw
    | zero => simp
    | add a b _ _ ha hb => rw [contr_add_right, ha, hb, add_zero]
    | smul α a _ ha => rw [contr_smul_right, ha, actE_zero_right]
  funext k
  rw [← contr_single γ k]
  exact key _ (hS ▸ Submodule.mem_top)
end GlobalTheory.TensorLat
