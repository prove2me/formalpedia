-- Prove2me | solution 1 for GroundTheory.ProfCoh.AdditiveFunction.g_funPermRep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:56:51.551114+00:00
-- url     : https://prove2.me/submissions/8093d7d9-25e0-4941-8797-83d6d4941676

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_GlobalEulerCharacteristic_UnitsDefs
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_ModNEquivOfSurjectiveApplyModNRep
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_SUnits
import Definitions.Def_GroundTheory_ProfiniteCohomology_GlobalEulerCharacteristic_GEqAddOfExactOfFiniteCokernel
import Theorems.Thm_GroundTheory_ProfCoh_finite_modN_of_moduleFinite
import Theorems.Thm_GroundTheory_Global_SemiLocal_tensorHomeomorph_apply
import Theorems.Thm_GroundTheory_Global_coeff_permOfFun
import Theorems.Thm_GroundTheory_Global_cycSub_apply
import Theorems.Thm_GroundTheory_Global_normHom_apply
import Theorems.Thm_GroundTheory_Global_piRep_apply
import Theorems.Thm_GroundTheory_GroupCoh_restrictEnd_apply
import Theorems.Thm_GroundTheory_LocalField_coe_smul_integerUnits
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
import Theorems.Thm_GroundTheory_ProfCoh_AdditiveFunction_g_eq_of_torsion_trivial
import Theorems.Thm_GroundTheory_ProfCoh_AdditiveFunction_toFun_congr
import Theorems.Thm_GroundTheory_ProfCoh_coe_torsNRep_apply
import Theorems.Thm_GroundTheory_ProfCoh_modNEquivOfSurjective_apply_modNRep
import Theorems.Thm_GroundTheory_ProfCoh_modNRep_mk
import Theorems.Thm_P2M_GroundTheory_Global_SemiLocal_tensorEquiv__tmul_7bea2d8929c7
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_AdicCompleteRootExistence_exists_root_of_dvd__8130b8fccf10
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_CyclicSubtraction_apply_eq_of_cycSub_eq_zero__fe379387d69c
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
attribute [local simp] GroundTheory.LocalField.coe_smul_integerUnits
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply
attribute [local simp] GroundTheory.ProfCoh.coe_torsNRep_apply
attribute [local simp] GroundTheory.ProfCoh.modNRep_mk
attribute [local simp] P2M_GroundTheory_Global_SemiLocal_tensorEquiv__tmul_7bea2d8929c7



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
universe u v
open NumberField NumberField.Units NumberField.InfinitePlace IsDedekindDomain Module
open GroundTheory.Global
open scoped TensorProduct
open GroundTheory.ProfCoh.AdditiveFunction
variable {l : ℕ} [NeZero l] {Γ : Type v} [Group Γ] (d : AdditiveFunction.{u} l Γ)
namespace GroundTheory.ProfCoh.AdditiveFunction
theorem _root_.solution (X : Type u) [MulAction Γ X] [Finite X] :
    letI := repAction (funPermRep ℤ Γ X)
    d.g (X → ℤ) = d.toFun (X → ZMod l) (funPermRep (ZMod l) Γ X) := by
  let := repAction (funPermRep ℤ Γ X)
  have ht : ∀ a : X → ℤ, l • a = 0 → a = 0 := fun a ha ↦ by
    funext x
    have h := congrFun ha x
    simp only [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul] at h
    exact (mul_eq_zero.1 h).resolve_left (by exact_mod_cast NeZero.ne l)
  let φ : (X → ℤ) →+ (X → ZMod l) :=
    { toFun := fun a x ↦ (a x : ZMod l)
      map_zero' := by
        funext x
        simp
      map_add' := fun a b ↦ by
        funext x
        simp }
  have hs : Function.Surjective φ := fun b ↦
    ⟨fun x ↦ (ZMod.intCast_surjective (b x)).choose,
      funext fun x ↦ (ZMod.intCast_surjective (b x)).choose_spec⟩
  have hker : ∀ a, φ a = 0 ↔ a ∈ LinearMap.range (LinearMap.lsmul ℤ (X → ℤ) l) := by
    intro a
    rw [mem_range_lsmul_iff]
    constructor
    · intro h
      have hd : ∀ x, (l : ℤ) ∣ a x := fun x ↦
        (ZMod.intCast_zmod_eq_zero_iff_dvd (a x) l).1 (congrFun h x)
      choose c hc using hd
      refine ⟨c, funext fun x ↦ ?_⟩
      simp only [Pi.smul_apply, nsmul_eq_mul]
      rw [hc x]
    · rintro ⟨y, rfl⟩
      funext x
      change (((l • y) x : ℤ) : ZMod l) = 0
      simp
  have hφ : ∀ (γ : Γ) (a : X → ℤ), φ (γ • a) = funPermRep (ZMod l) Γ X γ (φ a) :=
    fun _ _ ↦ rfl
  have := finite_modN_of_moduleFinite (A := X → ℤ) l
  rw [d.g_eq_of_torsion_trivial _ ht]
  exact d.toFun_congr _ _ (modNEquivOfSurjective φ hs hker)
    (modNEquivOfSurjective_apply_modNRep _ φ hs hker hφ)
end GroundTheory.ProfCoh.AdditiveFunction
