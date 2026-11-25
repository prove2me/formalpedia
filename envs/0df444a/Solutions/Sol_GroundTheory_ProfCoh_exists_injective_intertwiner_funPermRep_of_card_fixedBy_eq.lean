-- Prove2me | solution 1 for GroundTheory.ProfCoh.exists_injective_intertwiner_funPermRep_of_card_fixedBy_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:04:21.520431+00:00
-- url     : https://prove2.me/submissions/213f3df6-0907-4af9-874d-834cd9d8d3d5

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_Additive
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Lattice
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_SUnitsPerm
import Definitions.Def_GroundTheory_ProfiniteCohomology_GlobalEulerCharacteristic_PermLatticeDefs
import Definitions.Def_GroundTheory_ProfiniteCohomology_GlobalEulerCharacteristic_PermLatticeCharacter
import Definitions.Def_GroundTheory_ProfiniteCohomology_GlobalEulerCharacteristic_PermLattice
import Theorems.Thm_GroundTheory_ProfCoh_nonempty_equiv_funPermRep_of_card_fixedBy_eq
import Theorems.Thm_GroundTheory_ProfCoh_piScalarRight_baseChange_funPermRep
import Theorems.Thm_GroundTheory_Global_SemiLocal_tensorHomeomorph_apply
import Theorems.Thm_GroundTheory_Global_coeff_permOfFun
import Theorems.Thm_GroundTheory_Global_cycSub_apply
import Theorems.Thm_GroundTheory_Global_exists_injective_intertwiner_of_real_equiv
import Theorems.Thm_GroundTheory_Global_normHom_apply
import Theorems.Thm_GroundTheory_Global_piRep_apply
import Theorems.Thm_GroundTheory_GroupCoh_restrictEnd_apply
import Theorems.Thm_GroundTheory_ProfCoh_coe_torsNRep_apply
import Theorems.Thm_GroundTheory_ProfCoh_modNRep_mk
import Theorems.Thm_P2M_GroundTheory_Global_SemiLocal_tensorEquiv__tmul_7bea2d8929c7
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.SemiLocal.tensorHomeomorph_apply
attribute [local simp] GroundTheory.Global.coeff_permOfFun
attribute [local simp] GroundTheory.Global.cycSub_apply
attribute [local simp] GroundTheory.Global.normHom_apply
attribute [local simp] GroundTheory.Global.piRep_apply
attribute [local simp] GroundTheory.GroupCoh.restrictEnd_apply
attribute [local simp] GroundTheory.ProfCoh.coe_torsNRep_apply
attribute [local simp] GroundTheory.ProfCoh.modNRep_mk
attribute [local simp] P2M_GroundTheory_Global_SemiLocal_tensorEquiv__tmul_7bea2d8929c7



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open Module Representation GroundTheory.Global
open scoped TensorProduct
universe u v
variable {Γ : Type*} [Group Γ]
namespace GroundTheory.ProfCoh
theorem _root_.solution [Finite Γ] {X X' : Type*}
    [MulAction Γ X] [MulAction Γ X'] [Finite X] [Finite X']
    (h : ∀ γ : Γ, Nat.card (MulAction.fixedBy X γ) = Nat.card (MulAction.fixedBy X' γ)) :
    ∃ φ : (X → ℤ) →ₗ[ℤ] (X' → ℤ), Function.Injective φ ∧
      (∃ n : ℤ, n ≠ 0 ∧ ∀ y, ∃ x, φ x = n • y) ∧
      ∀ γ x, φ (funPermRep ℤ Γ X γ x) = funPermRep ℤ Γ X' γ (φ x) := by
  classical
  have := Fintype.ofFinite X
  have := Fintype.ofFinite X'
  obtain ⟨E⟩ := nonempty_equiv_funPermRep_of_card_fixedBy_eq (k := ℝ) h
  let P := TensorProduct.piScalarRight ℤ ℝ ℝ X
  let P' := TensorProduct.piScalarRight ℤ ℝ ℝ X'
  let e : ℝ ⊗[ℤ] (X → ℤ) ≃ₗ[ℝ] ℝ ⊗[ℤ] (X' → ℤ) := P.trans (E.toLinearEquiv.trans P'.symm)
  have he : ∀ γ x, e ((funPermRep ℤ Γ X γ).baseChange ℝ x) =
      (funPermRep ℤ Γ X' γ).baseChange ℝ (e x) := by
    intro γ x
    apply P'.injective
    simp only [e, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
    rw [piScalarRight_baseChange_funPermRep, piScalarRight_baseChange_funPermRep,
      LinearEquiv.apply_symm_apply]
    exact LinearMap.congr_fun (E.toIntertwiningMap.isIntertwining' γ) (P x)
  exact exists_injective_intertwiner_of_real_equiv _ _ e he
end GroundTheory.ProfCoh
