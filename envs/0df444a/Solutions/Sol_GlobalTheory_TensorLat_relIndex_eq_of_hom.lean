-- Prove2me | solution 1 for GlobalTheory.TensorLat.relIndex_eq_of_hom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:39:25.488008+00:00
-- url     : https://prove2.me/submissions/cc01b45e-a63a-4afc-b4ae-04479453c9bd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_FlatMemLatIffStdLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_NsmulApplyMemOfMemTensorLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsSmulMemOfMemSpanFraction
import Definitions.Def_ReciprocityTheory_SemistableReduction_ExistsIntSmulMemSpan
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegCE
import Definitions.Def_ReciprocityTheory_DualLattices_WedgeNeZeroOfLinearIndependent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsCoeEqSpanDetOfIntVecLe
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_actE_apply
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_consZero_succ
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_consZero_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.I2.actE_apply
attribute [local simp] ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.consZero_succ
attribute [local simp] ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.consZero_zero



set_option autoImplicit false
open GlobalTheory GlobalTheory.TensorLat
open NumberField Complex ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.GeometryOfNumbersTheory (stdLat)
open scoped nonZeroDivisors
namespace GlobalTheory.TensorLat
theorem _root_.solution {M M' : Type*} [AddCommGroup M] [AddCommGroup M']
    {A₁ A₂ : AddSubgroup M} {B₁ B₂ : AddSubgroup M'} (f : M →+ M')
    (hf : ∀ v ∈ A₂, f v ∈ B₂) (hker : ∀ v ∈ A₂, f v ∈ B₁ ↔ v ∈ A₁)
    (hsurj : ∀ u ∈ B₂, ∃ v ∈ A₂, u - f v ∈ B₁) : A₁.relIndex A₂ = B₁.relIndex B₂ := by
  have h1 : A₁ ⊓ A₂ = B₁.comap f ⊓ A₂ := by
    ext v
    simp only [AddSubgroup.mem_inf, AddSubgroup.mem_comap]
    exact ⟨fun h => ⟨(hker v h.2).2 h.1, h.2⟩, fun h => ⟨(hker v h.2).1 h.1, h.2⟩⟩
  have h2 : B₁ ⊔ A₂.map f = B₁ ⊔ B₂ := by
    refine le_antisymm (sup_le_sup_left ?_ _) (sup_le le_sup_left fun u hu => ?_)
    · rintro _ ⟨v, hv, rfl⟩
      exact hf v hv
    · obtain ⟨v, hv, h⟩ := hsurj u hu
      exact AddSubgroup.mem_sup.2 ⟨_, h, f v, ⟨v, hv, rfl⟩, sub_add_cancel _ _⟩
  rw [← AddSubgroup.inf_relIndex_right, h1, AddSubgroup.inf_relIndex_right,
    AddSubgroup.relIndex_comap, ← AddSubgroup.relIndex_sup_left, h2,
    AddSubgroup.relIndex_sup_left]
end GlobalTheory.TensorLat
