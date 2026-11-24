-- Prove2me | solution 1 for GlobalTheory.eq_zero_of_lTensor_eq_zero_of_balanced
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:37:07.44691+00:00
-- url     : https://prove2.me/submissions/9dcf96f4-eccd-40a5-a16c-3cacf8ed8795

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DvdTraceOfBalancedTensor
import Theorems.Thm_GlobalTheory_exists_common_eigenvector_mem
import Theorems.Thm_GlobalTheory_lTensor_comp_mulLeft_of_balanced

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
variable {O H : Type*} [CommRing O] [CommRing H] [Algebra O H]
namespace GlobalTheory
theorem _root_.solution [Module.Free O H] [Module.Finite O H]
    (Θ : H ⊗[O] H) (hΘ : ∀ h : H, (h ⊗ₜ[O] (1 : H)) * Θ = ((1 : H) ⊗ₜ[O] h) * Θ)
    (K : Type*) [Field K] [IsAlgClosed K] [Algebra O K]
    (hK : ∀ ga : H →ₐ[O] K, Algebra.TensorProduct.map (AlgHom.id O H) ga Θ ≠ 0)
    (α : H →ₗ[O] K) (hα : LinearMap.lTensor H α Θ = 0) : α = 0 := by
  classical
  by_contra hne
  let b := Module.Free.chooseBasis O H
  haveI : FiniteDimensional K (H →ₗ[O] K) := Module.Finite.equiv (b.constr K)
  have hsm : ∀ (l : K) (a : H →ₗ[O] K), LinearMap.lTensor H a Θ = 0 →
      LinearMap.lTensor H (l • a) Θ = 0 := by
    intro l a ha
    have : l • a = LinearMap.mulLeft O l ∘ₗ a := by ext; simp
    rw [this, LinearMap.lTensor_comp, LinearMap.comp_apply, ha, map_zero]
  let W : Submodule K (H →ₗ[O] K) :=
    { carrier := {a | LinearMap.lTensor H a Θ = 0}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at *
        simp [LinearMap.lTensor_add, ha, hb]
      zero_mem' := by simp
      smul_mem' := fun l a ha => hsm l a ha }
  let T : H → (H →ₗ[O] K) →ₗ[K] (H →ₗ[O] K) := fun h =>
    { toFun := fun a => a ∘ₗ LinearMap.mulLeft O h
      map_add' := fun a b => by ext; simp
      map_smul' := fun l a => by ext; simp }
  obtain ⟨v, hvW, hv0, hv⟩ := exists_common_eigenvector_mem T
    (fun i j a => by ext; simp [T, mul_left_comm]) W
    ((Submodule.ne_bot_iff _).2 ⟨α, hα, hne⟩)
    (fun h a ha => by
      change LinearMap.lTensor H (a ∘ₗ LinearMap.mulLeft O h) Θ = 0
      rw [lTensor_comp_mulLeft_of_balanced Θ hΘ, show LinearMap.lTensor H a Θ = 0 from ha,
        smul_zero])
  choose l hl using hv
  have hl' : ∀ h x, v (h * x) = l h * v x := fun h x => by
    simpa [T] using LinearMap.congr_fun (hl h) x
  have hv1 : v 1 ≠ 0 := by
    intro h0
    apply hv0
    ext x
    simpa [h0] using hl' x 1
  let ga : H →ₐ[O] K := AlgHom.ofLinearMap ((v 1)⁻¹ • v) (by simp [hv1]) (by
    intro x y
    have h1 := hl' x y
    have h2 := hl' x 1
    rw [mul_one] at h2
    simp only [LinearMap.smul_apply, smul_eq_mul, h1, h2]
    field_simp)
  apply hK ga
  have : ∀ t : H ⊗[O] H, Algebra.TensorProduct.map (AlgHom.id O H) ga t
      = LinearMap.lTensor H ((v 1)⁻¹ • v) t := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [ga]
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [this]
  exact hsm _ _ hvW
end GlobalTheory
