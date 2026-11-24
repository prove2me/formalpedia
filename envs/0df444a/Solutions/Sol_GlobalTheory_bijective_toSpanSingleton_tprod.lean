-- Prove2me | solution 1 for GlobalTheory.bijective_toSpanSingleton_tprod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:24:30.646804+00:00
-- url     : https://prove2.me/submissions/c477a71f-aac2-4807-9636-97fd0efa9ed2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUnitSmulEqOfBijectiveToSpanSingleton

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct Pointwise
open GlobalTheory
variable {A : Type*} [CommRing A]
namespace GlobalTheory
theorem _root_.solution {ι : Type*} [Finite ι] {M : ι → Type*}
    [∀ i, AddCommGroup (M i)] [∀ i, Module A (M i)] (e : ∀ i, M i)
    (he : ∀ i, Function.Bijective (LinearMap.toSpanSingleton A (M i) (e i))) :
    Function.Bijective
      (LinearMap.toSpanSingleton A (⨂[A] i, M i) (PiTensorProduct.tprod A e)) := by
  classical
  cases nonempty_fintype ι
  let φ : ∀ i, M i ≃ₗ[A] A := fun i ↦ (LinearEquiv.ofBijective _ (he i)).symm
  have hφ : ∀ i x, φ i x • e i = x := fun i x ↦
    (LinearEquiv.ofBijective _ (he i)).apply_symm_apply x
  have hφe : ∀ i, φ i (e i) = 1 := fun i ↦ by
    rw [LinearEquiv.symm_apply_eq]; simp
  constructor
  · let l : (⨂[A] i, M i) →ₗ[A] A := PiTensorProduct.lift
      ((MultilinearMap.mkPiAlgebra A ι A).compLinearMap fun i ↦ (φ i).toLinearMap)
    have hl : l (PiTensorProduct.tprod A e) = 1 := by simp [l, hφe]
    intro a b hab
    simpa [hl] using congrArg l hab
  · intro y
    induction y using PiTensorProduct.induction_on with
    | smul_tprod r x =>
      refine ⟨r * ∏ i, φ i (x i), ?_⟩
      rw [LinearMap.toSpanSingleton_apply, mul_smul, ← MultilinearMap.map_smul_univ]
      simp only [hφ]
    | add x y hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      exact ⟨a + b, map_add _ _ _⟩
end GlobalTheory
