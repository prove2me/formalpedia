-- Prove2me | solution 1 for GroundTheory.ProfCoh.AdditiveFunction.g_eq_add_of_exact_of_finite_cokernel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:39:45.697855+00:00
-- url     : https://prove2.me/submissions/62d46030-883a-4beb-a2d9-16a0270dc629

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_GlobalEulerCharacteristic_UnitsDefs
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_ModNEquivOfSurjectiveApplyModNRep
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_SUnits
import Definitions.Def_GroundTheory_ProfiniteCohomology_GlobalEulerCharacteristic_GEqAddOfExactOfFiniteCokernel
import Theorems.Thm_GroundTheory_ProfCoh_finite_modN_of_moduleFinite
import Theorems.Thm_GroundTheory_ProfCoh_finite_torsN_of_moduleFinite
import Theorems.Thm_GroundTheory_ProfCoh_AdditiveFunction_g_add
import Theorems.Thm_GroundTheory_ProfCoh_AdditiveFunction_g_eq_of_finite_cokernel
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_AdicCompleteRootExistence_exists_root_of_dvd__8130b8fccf10
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_CyclicSubtraction_apply_eq_of_cycSub_eq_zero__fe379387d69c


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
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
theorem _root_.solution {A B C : Type u} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] [DistribMulAction Γ A] [DistribMulAction Γ B] [DistribMulAction Γ C]
    [Module.Finite ℤ A] [Module.Finite ℤ C] (f : A →+ B) (p : B →+ C)
    (hfγ : ∀ (γ : Γ) (a : A), f (γ • a) = γ • f a) (hpγ : ∀ (γ : Γ) (b : B), p (γ • b) = γ • p b)
    (hf : Function.Injective f) (hfp : Function.Exact f p) [Finite (C ⧸ p.range)] :
    d.g B = d.g A + d.g C := by
  have hR : ∀ (γ : Γ) (c : C), c ∈ p.range → γ • c ∈ p.range := by
    rintro γ _ ⟨b, rfl⟩
    exact ⟨γ • b, hpγ γ b⟩
  let _ := subgroupDistribMulAction p.range hR
  have : Module.Finite ℤ p.range :=
    Module.Finite.of_injective p.range.subtype.toIntLinearMap Subtype.val_injective
  have := finite_modN_of_moduleFinite (A := A) l
  have := finite_torsN_of_moduleFinite (A := A) l
  have := finite_modN_of_moduleFinite (A := p.range) l
  have := finite_torsN_of_moduleFinite (A := p.range) l
  have : Finite (C ⧸ p.range.subtype.range) := by
    rw [AddSubgroup.range_subtype]
    infer_instance
  rw [d.g_add f p.rangeRestrict hfγ (fun γ b ↦ Subtype.ext (hpγ γ b)) hf
      (fun y ↦ by
        rw [← hfp y]
        exact ⟨fun h ↦ congrArg Subtype.val h, fun h ↦ Subtype.ext h⟩)
      p.rangeRestrict_surjective,
    d.g_eq_of_finite_cokernel p.range.subtype (fun _ _ ↦ rfl) p.range.subtype_injective]
end GroundTheory.ProfCoh.AdditiveFunction
