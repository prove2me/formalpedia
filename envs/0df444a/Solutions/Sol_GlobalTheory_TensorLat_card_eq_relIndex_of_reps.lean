-- Prove2me | solution 1 for GlobalTheory.TensorLat.card_eq_relIndex_of_reps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:33:46.218817+00:00
-- url     : https://prove2.me/submissions/a284fff4-b4e9-45e5-b0dd-9ecea5594c8b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_FlatMemLatIffStdLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_NsmulApplyMemOfMemTensorLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsSmulMemOfMemSpanFraction
import Definitions.Def_ReciprocityTheory_SemistableReduction_ExistsIntSmulMemSpan
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegCE
import Definitions.Def_ReciprocityTheory_DualLattices_WedgeNeZeroOfLinearIndependent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsCoeEqSpanDetOfIntVecLe
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_IsU_unique
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
theorem _root_.solution {M : Type*} [AddCommGroup M] {A B : AddSubgroup M} {R : Finset M}
    (hR : ∀ y ∈ R, y ∈ B) (hR' : ∀ y ∈ B, ∃! r ∈ R, y - r ∈ A) : R.card = A.relIndex B := by
  rw [← Fintype.card_coe, ← Nat.card_eq_fintype_card]
  refine Nat.card_eq_of_bijective
    (fun y : R => (QuotientAddGroup.mk ⟨y, hR y y.2⟩ : B ⧸ A.addSubgroupOf B)) ⟨?_, ?_⟩
  · intro y y' h
    have h1 : (y : M) - y' ∈ A := by
      simpa [AddSubgroup.mem_addSubgroupOf] using QuotientAddGroup.eq_iff_sub_mem.1 h
    exact Subtype.ext ((hR' y (hR y y.2)).unique ⟨y.2, by simp⟩ ⟨y'.2, h1⟩)
  · intro q
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective q
    obtain ⟨r, ⟨hr, h⟩, -⟩ := hR' y y.2
    refine ⟨⟨r, hr⟩, (QuotientAddGroup.eq_iff_sub_mem.2 ?_).symm⟩
    simpa [AddSubgroup.mem_addSubgroupOf] using h
end GlobalTheory.TensorLat
