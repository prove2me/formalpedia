-- Prove2me | solution 1 for GroundTheory.ProfCoh.AdditiveFunction.g_funPermAction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:09:35.34627+00:00
-- url     : https://prove2.me/submissions/d299ac6e-716b-48f2-af53-6456b4279b3b

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_Additive
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Lattice
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_SUnitsPerm
import Definitions.Def_GroundTheory_ProfiniteCohomology_GlobalEulerCharacteristic_PermLatticeDefs
import Definitions.Def_GroundTheory_ProfiniteCohomology_GlobalEulerCharacteristic_PermLatticeCharacter
import Definitions.Def_GroundTheory_ProfiniteCohomology_GlobalEulerCharacteristic_PermLattice
import Theorems.Thm_GroundTheory_Global_SemiLocal_tensorHomeomorph_apply
import Theorems.Thm_GroundTheory_Global_coeff_permOfFun
import Theorems.Thm_GroundTheory_Global_cycSub_apply
import Theorems.Thm_GroundTheory_Global_normHom_apply
import Theorems.Thm_GroundTheory_Global_piRep_apply
import Theorems.Thm_GroundTheory_GroupCoh_restrictEnd_apply
import Theorems.Thm_GroundTheory_ProfCoh_AdditiveFunction_g_eq_of_torsion_trivial
import Theorems.Thm_GroundTheory_ProfCoh_AdditiveFunction_toFun_congr
import Theorems.Thm_GroundTheory_ProfCoh_coe_torsNRep_apply
import Theorems.Thm_GroundTheory_ProfCoh_modNRep_mk
import Theorems.Thm_P2M_GroundTheory_Global_SemiLocal_tensorEquiv__tmul_7bea2d8929c7
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
attribute [local simp] GroundTheory.ProfCoh.coe_torsNRep_apply
attribute [local simp] GroundTheory.ProfCoh.modNRep_mk
attribute [local simp] P2M_GroundTheory_Global_SemiLocal_tensorEquiv__tmul_7bea2d8929c7



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open Module Representation GroundTheory.Global
open scoped TensorProduct
universe u v
open GroundTheory.ProfCoh.AdditiveFunction
variable {l : ℕ} {Γ : Type v} [Group Γ] (d : AdditiveFunction.{u} l Γ)
namespace GroundTheory.ProfCoh.AdditiveFunction
theorem _root_.solution [NeZero l] (X : Type u) [MulAction Γ X] [Finite X] :
    letI := funPermAction Γ X ℤ
    d.g (X → ℤ) = d.toFun (X → ZMod l) (funPermRep (ZMod l) Γ X) := by
  let _ := funPermAction Γ X ℤ
  have hl : (l : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne l
  have htors : ∀ f : X → ℤ, l • f = 0 → f = 0 := fun f hf => funext fun x => by
    have h1 := congrFun hf x
    simp only [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul] at h1
    exact (mul_eq_zero.1 h1).resolve_left hl
  let c : (X → ℤ) →ₗ[ℤ] (X → ZMod l) :=
    LinearMap.pi fun x => (Int.castAddHom (ZMod l)).toIntLinearMap ∘ₗ LinearMap.proj x
  have hc : ∀ f x, c f x = (f x : ZMod l) := fun _ _ => rfl
  have hker : LinearMap.range (LinearMap.lsmul ℤ (X → ℤ) (l : ℤ)) ≤ LinearMap.ker c := by
    rintro _ ⟨f, rfl⟩
    rw [LinearMap.mem_ker]
    funext x
    simp [hc]
  let ψ := (LinearMap.range (LinearMap.lsmul ℤ (X → ℤ) (l : ℤ))).liftQ c hker
  have hψ : Function.Bijective (ψ.toAddMonoidHom.toZModLinearMap l) := by
    refine ⟨?_, fun y => ?_⟩
    · rw [injective_iff_map_eq_zero]
      intro x hx
      obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      have h1 : ∀ y, (l : ℤ) ∣ f y := fun y => by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        exact congrFun hx y
      choose a ha using h1
      rw [Submodule.Quotient.mk_eq_zero]
      exact ⟨a, funext fun y => by simp [ha y]⟩
    · refine ⟨Submodule.Quotient.mk (fun x => ((y x).val : ℤ)), funext fun x => ?_⟩
      show c _ x = y x
      rw [hc, Int.cast_natCast, ZMod.natCast_zmod_val]
  let E : ModN (X → ℤ) l ≃ₗ[ZMod l] (X → ZMod l) := LinearEquiv.ofBijective _ hψ
  have : Finite (ModN (X → ℤ) l) := Finite.of_equiv _ E.symm.toEquiv
  rw [d.g_eq_of_torsion_trivial _ htors]
  refine d.toFun_congr _ _ E fun γ x => ?_
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [modNRep_mk]
  rfl
end GroundTheory.ProfCoh.AdditiveFunction
