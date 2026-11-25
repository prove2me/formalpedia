-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ModuleReduction.exists_reduction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:37:22.123292+00:00
-- url     : https://prove2.me/submissions/7922e74d-04a8-4edc-9516-ea59560dc472

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_DivisibilityProofs_MemSmulOfTmulEqZero
import Theorems.Thm_GlobalTheory_CompanionTheory_ModuleReduction_mem_smul_of_tmul_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory TensorProduct ChangeOfRings
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ModuleReduction
namespace GlobalTheory.CompanionTheory.ModuleReduction
theorem _root_.solution (A O : Type) [CommRing A] [CommRing O] (θ : A →+* O)
    (hθ : Function.Surjective θ) (ξ : A) (hker : RingHom.ker θ = Ideal.span {ξ})
    (𝒞 : Type 1) [CategoryTheory.Category.{0} 𝒞] (M : CategoryTheory.Functor 𝒞 (ModuleCat.{0} A)) :
    ∃ (D : CategoryTheory.Functor 𝒞 (ModuleCat.{0} O)) (r : ∀ X : 𝒞, M.obj X →ₛₗ[θ] D.obj X),
      (∀ X, Function.Surjective (r X) ∧ ∀ m, r X m = 0 ↔ ∃ n, m = ξ • n) ∧
      ∀ (X Y : 𝒞) (f : X ⟶ Y) (m : M.obj X), D.map f (r X m) = r Y (M.map f m) := by
  let Q := (ModuleCat.restrictScalars θ).obj (ModuleCat.of O O)
  let one : Q := (1 : O)
  let g : A →ₗ[A] Q := LinearMap.toSpanSingleton A Q one
  have hgθ : ∀ a, (g a : O) = θ a := fun a => mul_one (θ a)
  have hsm : ∀ (X : 𝒞) (a : A) (m : M.obj X),
      (1 : O) ⊗ₜ[A,θ] (a • m) = (θ a) ⊗ₜ[A,θ] m := by
    intro X a m
    have h := TensorProduct.smul_tmul (R := A) (R' := A) a one m
    have e : a • one = (θ a : O) := hgθ a
    rw [e] at h
    exact h.symm
  let r : ∀ X : 𝒞, M.obj X →ₛₗ[θ] (M ⋙ ModuleCat.extendScalars θ).obj X := fun X =>
    { toFun := fun m => (1 : O) ⊗ₜ[A,θ] m
      map_add' := fun a b => TensorProduct.tmul_add _ _ _
      map_smul' := fun a m => by
        refine (hsm X a m).trans ?_
        have := ModuleCat.ExtendScalars.smul_tmul θ (M := M.obj X) (θ a) (1 : O) m
        rw [mul_one] at this
        exact this.symm }
  refine ⟨M ⋙ ModuleCat.extendScalars θ, r, fun X => ⟨?_, fun m => ⟨?_, ?_⟩⟩, ?_⟩
  · intro y
    change Q ⊗[A] (M.obj X) at y
    induction y using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero _⟩
    | tmul o n =>
      obtain ⟨a, ha⟩ := hθ o
      refine ⟨a • n, ?_⟩
      refine (hsm X a n).trans ?_
      rw [ha]
      rfl
    | add x y hx hy =>
      obtain ⟨u, hu⟩ := hx
      obtain ⟨v, hv⟩ := hy
      refine ⟨u + v, ?_⟩
      rw [map_add, hu, hv]
      rfl
  · intro h
    refine mem_smul_of_tmul_eq_zero g ?_ ξ ?_ m ?_
    · intro q
      obtain ⟨a, ha⟩ := hθ q
      exact ⟨a, (hgθ a).trans ha⟩
    · intro a
      have : g a = 0 ↔ θ a = 0 := by
        rw [← hgθ a]
        rfl
      rw [this, ← RingHom.mem_ker, hker, Ideal.mem_span_singleton']
      constructor
      · rintro ⟨b, rfl⟩
        exact ⟨b, mul_comm _ _⟩
      · rintro ⟨b, rfl⟩
        exact ⟨b, mul_comm _ _⟩
    · have e : g 1 = one := one_smul A one
      rw [e]
      exact h
  · rintro ⟨n, rfl⟩
    have : θ ξ = 0 := by
      rw [← RingHom.mem_ker, hker]
      exact Ideal.mem_span_singleton_self ξ
    change (1 : O) ⊗ₜ[A,θ] (ξ • n) = 0
    rw [hsm X ξ n, this]
    exact TensorProduct.zero_tmul (R := A) Q n
  · intro X Y f m
    rfl
end GlobalTheory.CompanionTheory.ModuleReduction
