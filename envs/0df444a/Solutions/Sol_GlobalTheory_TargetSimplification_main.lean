-- Prove2me | solution 1 for GlobalTheory.TargetSimplification.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:25:29.175229+00:00
-- url     : https://prove2.me/submissions/b49b018b-9996-4f74-bc8c-248b3f24bb9c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ImportsMoreBis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.TargetSimplification
namespace GlobalTheory.TargetSimplification
theorem _root_.solution {E V : Type} [Field E] [CharZero E] [AddCommGroup V] [Module E V] {s : E →+* E} {r : ℕ}
  (B : V →ₛₗ[s] V →ₗ[E] E) (hB : ∀ u v : V, B u v = s (B v u))
  {x y : Fin r → V} (hx : ∀ i j, B (x i) (x j) = 0) (hy : ∀ i j, B (y i) (y j) = 0)
  (hxy : ∀ i j, B (x i) (y j) = if i = j then 1 else 0)
  {z w₀ : V} (hxz : ∀ i, B (x i) z = 0) (hyz : ∀ i, B (y i) z = 0) (hzz : B z z = 0)
  (hzw : B z w₀ = 1) :
  ∃ (x' y' : Fin (r+1) → V), (∀ i j, B (x' i) (x' j) = 0) ∧ (∀ i j, B (y' i) (y' j) = 0) ∧
    (∀ i j, B (x' i) (y' j) = if i = j then 1 else 0) ∧ ∀ i : Fin r, x' (Fin.castSucc i) = x i := by
  have hyx : ∀ i j, B (y i) (x j) = if i = j then 1 else 0 := by
    intro i j; rw [hB, hxy]; by_cases h : j = i
    · subst h; simp
    · simp [h, Ne.symm h]
  have hzx : ∀ i, B z (x i) = 0 := fun i => by rw [hB, hxz, map_zero]
  have hzy : ∀ i, B z (y i) = 0 := fun i => by rw [hB, hyz, map_zero]
  obtain ⟨w₁, hw₁⟩ : ∃ w₁ : V, w₁ = w₀ - ∑ j, B (y j) w₀ • x j - ∑ j, B (x j) w₀ • y j := ⟨_, rfl⟩
  have hxw₁ : ∀ i, B (x i) w₁ = 0 := by
    intro i; simp [hw₁, map_sub, map_sum, hx, hxy]
  have hyw₁ : ∀ i, B (y i) w₁ = 0 := by
    intro i; simp [hw₁, map_sub, map_sum, hy, hyx]
  have hzw₁ : B z w₁ = 1 := by simp [hw₁, map_sub, map_sum, hzx, hzy, hzw]
  have h1 : B w₁ z = 1 := by rw [hB, hzw₁, map_one]
  have ht : s (B w₁ w₁) = B w₁ w₁ := (hB w₁ w₁).symm
  obtain ⟨c, hc⟩ : ∃ c : E, c = -(B w₁ w₁ / 2) := ⟨_, rfl⟩
  have hsc : s c = c := by rw [hc, map_neg, map_div₀, ht, map_ofNat]
  obtain ⟨w, hw⟩ : ∃ w : V, w = w₁ + c • z := ⟨_, rfl⟩
  have hxw : ∀ i, B (x i) w = 0 := by intro i; simp [hw, hxw₁, hxz]
  have hyw : ∀ i, B (y i) w = 0 := by intro i; simp [hw, hyw₁, hyz]
  have hwy : ∀ i, B w (y i) = 0 := fun i => by rw [hB, hyw, map_zero]
  have hzw' : B z w = 1 := by simp [hw, hzw₁, hzz]
  have hww : B w w = 0 := by
    simp only [hw, map_add, LinearMap.add_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply,
      smul_eq_mul, hzz, h1, hsc, hzw₁]
    rw [hc]; simp only [RingHom.id_apply]; ring
  refine ⟨Fin.snoc x z, Fin.snoc y w, ?_, ?_, ?_, ?_⟩
  · intro i j
    cases i using Fin.lastCases <;> cases j using Fin.lastCases <;>
      simp [Fin.snoc_castSucc, Fin.snoc_last, hx, hxz, hzx, hzz]
  · intro i j
    cases i using Fin.lastCases <;> cases j using Fin.lastCases <;>
      simp [Fin.snoc_castSucc, Fin.snoc_last, hy, hyw, hwy, hww]
  · intro i j
    cases i using Fin.lastCases <;> cases j using Fin.lastCases <;>
      simp [Fin.snoc_castSucc, Fin.snoc_last, hxy, hxw, hzy, hzw', Fin.castSucc_ne_last, (Fin.castSucc_ne_last _).symm]
  · intro i; simp
end GlobalTheory.TargetSimplification
