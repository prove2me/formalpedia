-- Prove2me | solution 1 for GlobalTheory.tensor_fractionRing_of_tensor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:36:54.630939+00:00
-- url     : https://prove2.me/submissions/fd83ebdb-9fbb-4847-af59-86fa5f27c20f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsFractionRingTensorOfFractionFields

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
namespace GlobalTheory
theorem _root_.solution
    {k R B K κ L : Type} [Field k] [CommRing R] [CommRing B] [Field K] [Field κ]
    [Field L] [Algebra k R] [Algebra k B] [Algebra k K] [Algebra k κ] [Algebra R K] [Algebra B κ]
    [IsScalarTower k R K] [IsScalarTower k B κ] [IsFractionRing R K] [IsFractionRing B κ]
    [Algebra (K ⊗[k] κ) L] [IsFractionRing (K ⊗[k] κ) L] :
    Function.Injective ((algebraMap (K ⊗[k] κ) L).comp (Algebra.TensorProduct.map
      (IsScalarTower.toAlgHom k R K) (IsScalarTower.toAlgHom k B κ)).toRingHom) ∧
    ∀ z : L, ∃ x y : R ⊗[k] B,
      (algebraMap (K ⊗[k] κ) L).comp (Algebra.TensorProduct.map
        (IsScalarTower.toAlgHom k R K) (IsScalarTower.toAlgHom k B κ)).toRingHom y ≠ 0 ∧
      z * (algebraMap (K ⊗[k] κ) L).comp (Algebra.TensorProduct.map
        (IsScalarTower.toAlgHom k R K) (IsScalarTower.toAlgHom k B κ)).toRingHom y =
      (algebraMap (K ⊗[k] κ) L).comp (Algebra.TensorProduct.map
        (IsScalarTower.toAlgHom k R K) (IsScalarTower.toAlgHom k B κ)).toRingHom x := by
  set f := Algebra.TensorProduct.map
    (IsScalarTower.toAlgHom k R K) (IsScalarTower.toAlgHom k B κ) with hfdef
  set g := algebraMap (K ⊗[k] κ) L

  have key : ∀ w : K ⊗[k] κ, ∃ (x : R ⊗[k] B) (s : nonZeroDivisors R) (t : nonZeroDivisors B),
      w * (algebraMap R K (s : R) ⊗ₜ[k] algebraMap B κ (t : B)) = f x := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => exact ⟨0, 1, 1, by simp⟩
    | tmul a b =>
      obtain ⟨⟨r, s⟩, hs⟩ := IsLocalization.surj (nonZeroDivisors R) a
      obtain ⟨⟨c, t⟩, ht⟩ := IsLocalization.surj (nonZeroDivisors B) b
      refine ⟨r ⊗ₜ[k] c, s, t, ?_⟩
      simp only [Algebra.TensorProduct.tmul_mul_tmul] at *
      rw [hs, ht, hfdef, Algebra.TensorProduct.map_tmul]
      rfl
    | add w₁ w₂ h₁ h₂ =>
      obtain ⟨x₁, s₁, t₁, e₁⟩ := h₁
      obtain ⟨x₂, s₂, t₂, e₂⟩ := h₂
      refine ⟨x₁ * ((s₂ : R) ⊗ₜ[k] (t₂ : B)) + x₂ * ((s₁ : R) ⊗ₜ[k] (t₁ : B)), s₁ * s₂, t₁ * t₂, ?_⟩
      have hm : ∀ (s : R) (t : B), f (s ⊗ₜ[k] t) = algebraMap R K s ⊗ₜ[k] algebraMap B κ t := by
        intro s t; rw [hfdef, Algebra.TensorProduct.map_tmul]; rfl
      rw [map_add, map_mul, map_mul, hm, hm, ← e₁, ← e₂]
      simp only [Submonoid.coe_mul, map_mul, ← Algebra.TensorProduct.tmul_mul_tmul]
      ring

  have unit_st : ∀ (s : nonZeroDivisors R) (t : nonZeroDivisors B),
      IsUnit (algebraMap R K (s : R) ⊗ₜ[k] algebraMap B κ (t : B)) := by
    intro s t
    have hs : IsUnit (algebraMap R K (s : R)) :=
      IsLocalization.map_units K s
    have ht : IsUnit (algebraMap B κ (t : B)) :=
      IsLocalization.map_units κ t
    have : algebraMap R K (s : R) ⊗ₜ[k] algebraMap B κ (t : B) =
        Algebra.TensorProduct.includeLeft (R := k) (S := k) (B := κ) (algebraMap R K (s : R)) *
        Algebra.TensorProduct.includeRight (R := k) (A := K) (algebraMap B κ (t : B)) := by
      simp [Algebra.TensorProduct.tmul_mul_tmul]
    rw [this]
    exact (hs.map _).mul (ht.map _)
  refine ⟨?_, ?_⟩
  · refine (IsFractionRing.injective (K ⊗[k] κ) L).comp ?_
    change Function.Injective (TensorProduct.map (IsScalarTower.toAlgHom k R K).toLinearMap
      (IsScalarTower.toAlgHom k B κ).toLinearMap)
    exact TensorProduct.map_injective_of_flat_flat _ _
      (IsFractionRing.injective R K) (IsFractionRing.injective B κ)
  · intro z
    obtain ⟨⟨u, v⟩, huv⟩ := IsLocalization.surj (nonZeroDivisors (K ⊗[k] κ)) z
    obtain ⟨xu, su, tu, eu⟩ := key u
    obtain ⟨xv, sv, tv, ev⟩ := key (v : K ⊗[k] κ)
    refine ⟨xu * ((sv : R) ⊗ₜ[k] (tv : B)), xv * ((su : R) ⊗ₜ[k] (tu : B)), ?_, ?_⟩
    all_goals
      have hm : ∀ (s : R) (t : B), f (s ⊗ₜ[k] t) = algebraMap R K s ⊗ₜ[k] algebraMap B κ t := by
        intro s t; rw [hfdef, Algebra.TensorProduct.map_tmul]; rfl
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, map_mul, hm]
    · rw [← ev]; simp only [map_mul]
      refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_
      · exact (IsLocalization.map_units L v).ne_zero
      · exact ((unit_st sv tv).map g).ne_zero
      · exact ((unit_st su tu).map g).ne_zero
    · rw [← ev, ← eu]; simp only [map_mul]
      have huv' : z * g (v : K ⊗[k] κ) = g u := huv
      linear_combination (g (algebraMap R K ↑sv ⊗ₜ[k] algebraMap B κ ↑tv) *
        g (algebraMap R K ↑su ⊗ₜ[k] algebraMap B κ ↑tu)) * huv'
end GlobalTheory
