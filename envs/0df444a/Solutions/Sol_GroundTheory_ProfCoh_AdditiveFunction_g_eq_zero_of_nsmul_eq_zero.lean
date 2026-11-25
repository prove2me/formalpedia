-- Prove2me | solution 1 for GroundTheory.ProfCoh.AdditiveFunction.g_eq_zero_of_nsmul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:30:45.023376+00:00
-- url     : https://prove2.me/submissions/4c289210-d754-4026-8d53-4fdc3ef06f7a

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_AdditiveSnake
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_Additive
import Theorems.Thm_GroundTheory_ProfCoh_AdditiveFunction_g_eq
import Theorems.Thm_GroundTheory_ProfCoh_AdditiveFunction_g_of_not_finite
import Theorems.Thm_GroundTheory_ProfCoh_AdditiveFunction_toFun_congr
import Theorems.Thm_GroundTheory_ProfCoh_coe_torsNRep_apply
import Theorems.Thm_GroundTheory_ProfCoh_modNRep_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.ProfCoh.coe_torsNRep_apply
attribute [local simp] GroundTheory.ProfCoh.modNRep_mk



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
universe u v
open Representation
open GroundTheory.ProfCoh.AdditiveFunction
variable {l : ℕ} {Γ : Type v} [Group Γ] (d : AdditiveFunction.{u} l Γ)
namespace GroundTheory.ProfCoh.AdditiveFunction
theorem _root_.solution (A : Type u) [AddCommGroup A] [DistribMulAction Γ A]
    (hA : ∀ a : A, l • a = 0) : d.g A = 0 := by
  by_cases hfin : Finite (ModN A l) ∧ Finite (TorsN A l)
  · obtain ⟨_, _⟩ := hfin
    rw [d.g_eq A, sub_eq_zero]
    let φ : A →ₗ[ℤ] TorsN A l :=
      LinearMap.codRestrict _ LinearMap.id (fun a => (mem_ker_lsmul_iff l a).2 (hA a))
    let ψ := (LinearMap.range (LinearMap.lsmul ℤ A (l : ℤ))).liftQ φ (by
      rintro _ ⟨y, rfl⟩
      rw [LinearMap.mem_ker]
      exact Subtype.ext (by simpa [φ] using hA y))
    refine d.toFun_congr _ _ (LinearEquiv.ofBijective (ψ.toAddMonoidHom.toZModLinearMap l)
      ⟨fun x y hxy => ?_, fun t => ⟨Submodule.Quotient.mk (t : A), Subtype.ext rfl⟩⟩) ?_
    · obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      exact congrArg _ (congrArg Subtype.val hxy : (a : A) = b)
    · intro γ x
      obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rfl
  · exact d.g_of_not_finite A hfin
end GroundTheory.ProfCoh.AdditiveFunction
