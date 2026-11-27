-- Prove2me | solution 1 for GlobalTheory.TensorLat.relIndex_pi_univ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:34:16.135804+00:00
-- url     : https://prove2.me/submissions/eac07423-4164-4e0d-b163-e54d4eea8968

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
theorem _root_.solution {ι : Type*} [Fintype ι] {G : ι → Type*} [∀ i, AddCommGroup (G i)]
    (L' L : ∀ i, AddSubgroup (G i)) :
    (AddSubgroup.pi Set.univ L').relIndex (AddSubgroup.pi Set.univ L) =
      ∏ i, (L' i).relIndex (L i) := by
  let f : (AddSubgroup.pi Set.univ L) →+ (∀ i, L i ⧸ (L' i).addSubgroupOf (L i)) :=
    { toFun := fun x i => QuotientAddGroup.mk ⟨x.1 i, x.2 i (Set.mem_univ i)⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hf : Function.Surjective f := fun y =>
    ⟨⟨fun i => (y i).out, fun i _ => (y i).out.2⟩, funext fun i => (y i).out_eq⟩
  have hc : (AddSubgroup.pi Set.univ L').addSubgroupOf (AddSubgroup.pi Set.univ L) = f.ker := by
    ext x
    rw [AddMonoidHom.mem_ker, funext_iff, AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_pi]
    refine forall_congr' fun i => ?_
    change _ ↔ (QuotientAddGroup.mk ⟨x.1 i, x.2 i (Set.mem_univ i)⟩ :
      L i ⧸ (L' i).addSubgroupOf (L i)) = 0
    simp [AddSubgroup.mem_addSubgroupOf]
  rw [AddSubgroup.relIndex, hc, AddSubgroup.index_ker, AddMonoidHom.range_eq_top.2 hf,
    AddSubgroup.card_top, Nat.card_pi]
  rfl
end GlobalTheory.TensorLat
