-- Prove2me | solution 1 for GlobalTheory.TensorLat.exists_reps_of_relIndex_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:34:03.687922+00:00
-- url     : https://prove2.me/submissions/f69635ce-e53b-4491-a52a-9b7079f464a3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_FlatMemLatIffStdLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_NsmulApplyMemOfMemTensorLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsSmulMemOfMemSpanFraction
import Definitions.Def_ReciprocityTheory_SemistableReduction_ExistsIntSmulMemSpan
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegCE
import Definitions.Def_ReciprocityTheory_DualLattices_WedgeNeZeroOfLinearIndependent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsCoeEqSpanDetOfIntVecLe
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_DimC_key
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
theorem _root_.solution {M : Type*} [AddCommGroup M] {A B : AddSubgroup M}
    (h : A.relIndex B ≠ 0) :
    ∃ R : Finset M, (∀ y ∈ R, y ∈ B) ∧ ∀ y ∈ B, ∃! r ∈ R, y - r ∈ A := by
  classical
  haveI : Fintype (B ⧸ A.addSubgroupOf B) := AddSubgroup.fintypeOfIndexNeZero h
  refine ⟨Finset.univ.image fun q : B ⧸ A.addSubgroupOf B => (q.out : M), ?_, fun y hy => ?_⟩
  · intro y hy
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hy
    exact q.out.2
  · have key : ∀ q : B ⧸ A.addSubgroupOf B,
        y - (q.out : M) ∈ A ↔ QuotientAddGroup.mk ⟨y, hy⟩ = q := fun q => by
      conv_rhs => rw [← QuotientAddGroup.out_eq' q, QuotientAddGroup.eq_iff_sub_mem]
      simp [AddSubgroup.mem_addSubgroupOf]
    refine ⟨_, ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), (key _).2 rfl⟩, ?_⟩
    rintro r ⟨hr, h⟩
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hr
    rw [(key q).1 h]
end GlobalTheory.TensorLat
