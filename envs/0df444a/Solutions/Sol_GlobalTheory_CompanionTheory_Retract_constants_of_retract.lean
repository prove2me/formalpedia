-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Retract.constants_of_retract
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:00:00.770035+00:00
-- url     : https://prove2.me/submissions/3bf96440-18c7-46fe-87d3-b03bf1c5b745

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RetractBaseChangeKernelCompatible

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Retract
namespace GlobalTheory.CompanionTheory.Retract
theorem _root_.solution :
    ∀ (R R' M A₀ A₁ B₀ B₁ : Type) [CommRing R] [CommRing R'] [Algebra R R'] [AddCommGroup M] [Module R M] [AddCommGroup A₀] [Module R A₀] [AddCommGroup A₁] [Module R A₁] [AddCommGroup B₀] [Module R' B₀] [AddCommGroup B₁] [Module R' B₁] (i : M →ₗ[R] R') (j : R' →ₗ[R] M) (d₀ : A₀ →ₗ[R] A₁) (d' : B₀ →ₗ[R'] B₁) (E₀ : R' ⊗[R] A₀ ≃ₗ[R'] B₀) (E₁ : R' ⊗[R] A₁ ≃ₗ[R'] B₁) (e : A₀), j ∘ₗ i = LinearMap.id → (∀ x, E₁ (d₀.baseChange R' x) = d' (E₀ x)) → (∀ r : R', r • E₀ (1 ⊗ₜ e) = 0 → r = 0) → (∀ z, d' z = 0 → ∃ r : R', r • E₀ (1 ⊗ₜ e) = z) → Function.Injective (fun m : M ↦ m ⊗ₜ[R] e) ∧ ∀ x : M ⊗[R] A₀, d₀.lTensor M x = 0 → ∃ m : M, m ⊗ₜ[R] e = x := by
  intro R R' M A₀ A₁ B₀ B₁ _ _ _ _ _ _ _ _ _ _ _ _ _ i j d₀ d' E₀ E₁ e hji hcomm hfree hker
  have htm : ∀ r : R', r • E₀ (1 ⊗ₜ e) = E₀ (r ⊗ₜ[R] e) := by
    intro r
    rw [← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have hinjR : ∀ r : R', r ⊗ₜ[R] e = 0 → r = 0 := by
    intro r hr
    apply hfree
    rw [htm, hr, map_zero]
  have hkerR : ∀ y : R' ⊗[R] A₀, d₀.baseChange R' y = 0 → ∃ r : R', r ⊗ₜ[R] e = y := by
    intro y hy
    obtain ⟨r, hr⟩ := hker (E₀ y) (by rw [← hcomm, hy, map_zero])
    exact ⟨r, E₀.injective (by rw [← htm, hr])⟩
  have hji' : ∀ m : M, j (i m) = m := fun m => by
    rw [← LinearMap.comp_apply, hji, LinearMap.id_apply]
  have hret : ∀ x : M ⊗[R] A₀, j.rTensor A₀ (i.rTensor A₀ x) = x := by
    intro x
    rw [← LinearMap.rTensor_comp_apply, hji, LinearMap.rTensor_id_apply]
  have hnat : ∀ x : M ⊗[R] A₀,
      d₀.baseChange R' (i.rTensor A₀ x) = i.rTensor A₁ (d₀.lTensor M x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul m a => simp [LinearMap.baseChange_tmul]
    | add x y hx hy => simp only [map_add, hx, hy]
  refine ⟨?_, ?_⟩
  · intro m m' h
    have h0 : m ⊗ₜ[R] e = m' ⊗ₜ[R] e := h
    have h1 : (i m - i m') ⊗ₜ[R] e = 0 := by
      have h2 := congrArg (i.rTensor A₀) h0
      simp only [LinearMap.rTensor_tmul] at h2
      rw [TensorProduct.sub_tmul, h2, sub_self]
    have h3 : i m = i m' := sub_eq_zero.mp (hinjR _ h1)
    rw [← hji' m, ← hji' m', h3]
  · intro x hx
    obtain ⟨r, hr⟩ := hkerR (i.rTensor A₀ x) (by rw [hnat, hx, map_zero])
    refine ⟨j r, ?_⟩
    rw [← hret x, ← hr, LinearMap.rTensor_tmul]
end GlobalTheory.CompanionTheory.Retract
