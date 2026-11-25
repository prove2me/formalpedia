-- Prove2me | solution 1 for GroundTheory.Global.Artin.indFun_mulEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:09:59.699936+00:00
-- url     : https://prove2.me/submissions/24ff18a0-444e-41e0-a346-43d083b01907

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Artin_IsProjEigenspaceNegOneOfMulSelfEqOne
import Definitions.Def_GroundTheory_GlobalFields_Artin_PlacesGalois
import Definitions.Def_GroundTheory_GlobalFields_Artin_Mackey
import Definitions.Def_GroundTheory_GlobalFields_Artin_GammaInduction
import Theorems.Thm_GroundTheory_Global_Artin_extendByZero_coe
import Theorems.Thm_GroundTheory_Global_Artin_fixedFieldMulEquiv_apply
import Theorems.Thm_GroundTheory_Global_Artin_subfieldInfinitePlaceEquiv_mk
import Theorems.Thm_GroundTheory_Global_Artin_subfieldPlaceEquiv_mk
import Theorems.Thm_GroundTheory_GroupCoh_doubleCosetMap_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.Artin.extendByZero_coe
attribute [local simp] GroundTheory.Global.Artin.fixedFieldMulEquiv_apply
attribute [local simp] GroundTheory.Global.Artin.subfieldInfinitePlaceEquiv_mk
attribute [local simp] GroundTheory.Global.Artin.subfieldPlaceEquiv_mk
attribute [local simp] GroundTheory.GroupCoh.doubleCosetMap_mk



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open scoped Pointwise
open NumberField NumberField.InfinitePlace IntermediateField Module GroundTheory.LocalField _root_.Complex
open GroundTheory GroundTheory.Global GroundTheory.Global.Artin
variable {Γ Δ : Type*} [Group Γ] [Group Δ] [Fintype Γ] [Fintype Δ]
namespace GroundTheory.Global.Artin
theorem _root_.solution (e : Γ ≃* Δ) {ψ : Γ → ℂ} (hψ : IsClassFun ψ) :
    indFun e.toMonoidHom ψ = ψ ∘ e.symm := by
  classical
  funext s
  rw [indFun_apply]
  have h1 : ∀ t : Δ, (∑ h : Γ, if e.toMonoidHom h = t⁻¹ * s * t then ψ h else 0) =
      ψ (e.symm s) := by
    intro t
    rw [Finset.sum_eq_single (e.symm (t⁻¹ * s * t))]
    · rw [if_pos (by simp), map_mul, map_mul, map_inv]
      have := hψ (e.symm s) (e.symm t)⁻¹
      rwa [inv_inv] at this
    · intro h _ hh
      rw [if_neg]
      intro h'
      apply hh
      rw [← h']
      simp
    · simp
  simp_rw [h1]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Function.comp_apply]
  have : (Fintype.card Δ : ℂ) = Nat.card Γ := by
    rw [Nat.card_eq_fintype_card, Fintype.card_congr e.toEquiv]
  rw [this, inv_mul_cancel_left₀ (Nat.cast_ne_zero.2 Nat.card_pos.ne')]
end GroundTheory.Global.Artin
