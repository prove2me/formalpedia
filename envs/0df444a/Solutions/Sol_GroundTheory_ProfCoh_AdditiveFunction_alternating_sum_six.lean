-- Prove2me | solution 1 for GroundTheory.ProfCoh.AdditiveFunction.alternating_sum_six
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:32:35.786964+00:00
-- url     : https://prove2.me/submissions/63bfd69f-7bc3-40c6-82bc-434afe6fab1f

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_AdditiveDefs
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_AdditiveSnake
import Theorems.Thm_GroundTheory_ProfCoh_AdditiveFunction_toFun_eq_ker_add_range
import Theorems.Thm_GroundTheory_ProfCoh_AdditiveFunction_toFun_subrep_congr
import Theorems.Thm_GroundTheory_ProfCoh_AdditiveFunction_toFun_range_of_injective
import Theorems.Thm_GroundTheory_ProfCoh_AdditiveFunction_toFun_range_of_surjective

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
theorem _root_.solution {T₁ T₂ T₃ Q₁ Q₂ Q₃ : Type u}
    [AddCommGroup T₁] [Module (ZMod l) T₁] [Finite T₁]
    [AddCommGroup T₂] [Module (ZMod l) T₂] [Finite T₂]
    [AddCommGroup T₃] [Module (ZMod l) T₃] [Finite T₃]
    [AddCommGroup Q₁] [Module (ZMod l) Q₁] [Finite Q₁]
    [AddCommGroup Q₂] [Module (ZMod l) Q₂] [Finite Q₂]
    [AddCommGroup Q₃] [Module (ZMod l) Q₃] [Finite Q₃]
    (τ₁ : Representation (ZMod l) Γ T₁) (τ₂ : Representation (ZMod l) Γ T₂)
    (τ₃ : Representation (ZMod l) Γ T₃) (κ₁ : Representation (ZMod l) Γ Q₁)
    (κ₂ : Representation (ZMod l) Γ Q₂) (κ₃ : Representation (ZMod l) Γ Q₃)
    (φ₁ : T₁ →ₗ[ZMod l] T₂) (φ₂ : T₂ →ₗ[ZMod l] T₃) (φ₃ : T₃ →ₗ[ZMod l] Q₁)
    (φ₄ : Q₁ →ₗ[ZMod l] Q₂) (φ₅ : Q₂ →ₗ[ZMod l] Q₃)
    (i₁ : τ₁.IsIntertwiningMap τ₂ φ₁) (i₂ : τ₂.IsIntertwiningMap τ₃ φ₂)
    (i₃ : τ₃.IsIntertwiningMap κ₁ φ₃) (i₄ : κ₁.IsIntertwiningMap κ₂ φ₄)
    (i₅ : κ₂.IsIntertwiningMap κ₃ φ₅)
    (h₁ : Function.Injective φ₁) (e₁₂ : Function.Exact φ₁ φ₂) (e₂₃ : Function.Exact φ₂ φ₃)
    (e₃₄ : Function.Exact φ₃ φ₄) (e₄₅ : Function.Exact φ₄ φ₅) (h₅ : Function.Surjective φ₅) :
    d.toFun T₁ τ₁ - d.toFun T₂ τ₂ + d.toFun T₃ τ₃ - d.toFun Q₁ κ₁ + d.toFun Q₂ κ₂ -
      d.toFun Q₃ κ₃ = 0 := by
  have a₂ := d.toFun_eq_ker_add_range τ₂ τ₃ φ₂ i₂
  have a₃ := d.toFun_eq_ker_add_range τ₃ κ₁ φ₃ i₃
  have a₄ := d.toFun_eq_ker_add_range κ₁ κ₂ φ₄ i₄
  have a₅ := d.toFun_eq_ker_add_range κ₂ κ₃ φ₅ i₅
  have k₂ := (d.toFun_subrep_congr τ₂ (LinearMap.exact_iff.1 e₁₂)
    (ker_le_comap_of_isIntertwiningMap i₂) (range_le_comap_of_isIntertwiningMap i₁)).trans
    (d.toFun_range_of_injective τ₁ τ₂ φ₁ i₁ h₁)
  have k₃ := d.toFun_subrep_congr τ₃ (LinearMap.exact_iff.1 e₂₃)
    (ker_le_comap_of_isIntertwiningMap i₃) (range_le_comap_of_isIntertwiningMap i₂)
  have k₄ := d.toFun_subrep_congr κ₁ (LinearMap.exact_iff.1 e₃₄)
    (ker_le_comap_of_isIntertwiningMap i₄) (range_le_comap_of_isIntertwiningMap i₃)
  have k₅ := d.toFun_subrep_congr κ₂ (LinearMap.exact_iff.1 e₄₅)
    (ker_le_comap_of_isIntertwiningMap i₅) (range_le_comap_of_isIntertwiningMap i₄)
  have r₅ := d.toFun_range_of_surjective κ₂ κ₃ φ₅ i₅ h₅
  omega
end GroundTheory.ProfCoh.AdditiveFunction
