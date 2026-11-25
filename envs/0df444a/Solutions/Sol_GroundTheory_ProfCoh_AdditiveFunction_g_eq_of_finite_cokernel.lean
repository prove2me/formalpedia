-- Prove2me | solution 1 for GroundTheory.ProfCoh.AdditiveFunction.g_eq_of_finite_cokernel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:55:55.160858+00:00
-- url     : https://prove2.me/submissions/7ff28cb8-e922-40e0-b603-19e0db2aa5ba

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_AdditiveSnake
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_Additive
import Theorems.Thm_GroundTheory_ProfCoh_AdditiveFunction_g_eq_zero_of_finite
import Theorems.Thm_GroundTheory_ProfCoh_AdditiveFunction_g_add


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
open Representation
open GroundTheory.ProfCoh.AdditiveFunction
variable {l : ℕ} {Γ : Type v} [Group Γ] (d : AdditiveFunction.{u} l Γ)
namespace GroundTheory.ProfCoh.AdditiveFunction
theorem _root_.solution {A B : Type u} [AddCommGroup A] [AddCommGroup B]
    [DistribMulAction Γ A] [DistribMulAction Γ B] (f : B →+ A)
    (hfγ : ∀ (γ : Γ) (b : B), f (γ • b) = γ • f b) (hf : Function.Injective f)
    [Finite (A ⧸ f.range)] [Finite (ModN B l)] [Finite (TorsN B l)] : d.g A = d.g B := by
  have hR : ∀ (γ : Γ) (a : A), a ∈ f.range → γ • a ∈ f.range := by
    rintro γ _ ⟨b, rfl⟩
    exact ⟨γ • b, hfγ γ b⟩
  let _ := quotientDistribMulAction f.range hR
  rw [d.g_add f (QuotientAddGroup.mk' f.range) hfγ (fun _ _ => rfl) hf
    (fun y => by rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]; rfl)
    (QuotientAddGroup.mk'_surjective _), d.g_eq_zero_of_finite (A ⧸ f.range), add_zero]
end GroundTheory.ProfCoh.AdditiveFunction
