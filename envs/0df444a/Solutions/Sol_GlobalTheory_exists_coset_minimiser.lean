-- Prove2me | solution 1 for GlobalTheory.exists_coset_minimiser
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:31:27.082996+00:00
-- url     : https://prove2.me/submissions/f1ce146e-34fc-4e71-865d-b8cbba0cd011

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsPosZsmulMemRange
import Theorems.Thm_GlobalTheory_quad_add_zsmul
import Theorems.Thm_GlobalTheory_quad_zero
import Theorems.Thm_GlobalTheory_quad_nonneg
import Theorems.Thm_GlobalTheory_quad_round_sum
import Theorems.Thm_GlobalTheory_exists_pos_zsmul_mem_range

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (X : Type) [AddCommGroup X] (Bf : X →+ X →+ ℤ) (Q : X → ℤ), (∀ x y, Bf x y = Bf y x) → (∀ x, 2 * Q x = Bf x x) → (∀ x, x ≠ 0 → 1 ≤ Q x) → ∀ (n : ℕ) (b : Module.Basis (Fin n) ℤ X) (Cc : ℝ), (∀ j, (Q (b j) : ℝ) ≤ Cc) → ∀ (φ : X →+ X) (g : ℕ), 1 ≤ g → (∀ x y, Bf (φ x) (φ y) = g * Bf x y) → ∀ x : X, ∃ χ : X, ((Q (x + φ χ) : ℝ) ≤ g * n * Cc / 4) ∧ ∀ (q : ℕ) (z : X), (q : ℤ) * (q - 1) * Q (φ z) ≤ Q (x + φ χ + q • φ z) - Q (x + φ χ) := by
  classical
  intro X _ Bf Q hs hQ hp n b Cc hC φ g hg hφ x
  have hQφ : ∀ z, Q (φ z) = g * Q z := by
    intro z
    have h : 2 * Q (φ z) = 2 * (g * Q z) := by
      rw [hQ, hφ, ← hQ z]; ring
    exact mul_left_cancel₀ two_ne_zero h
  have hinj : Function.Injective φ := by
    intro u v huv
    by_contra hne
    have h0 : φ (u - v) = 0 := by rw [map_sub, huv, sub_self]
    have h1 := hp (u - v) (sub_ne_zero.mpr hne)
    have h2 := hQφ (u - v)
    rw [h0, quad_zero hQ] at h2
    have : (1 : ℤ) ≤ g := by exact_mod_cast hg
    nlinarith
  obtain ⟨N, hN, y, hy⟩ := exists_pos_zsmul_mem_range b φ hinj x
  obtain ⟨m, hm⟩ := quad_round_sum hs hQ (fun j => φ (b j))
    (fun j => quad_nonneg hQ hp _) N hN (fun j => b.repr y j) Finset.univ
  set χ0 : X := ∑ j, m j • b j with hχ0
  have hNx : N • (x + φ χ0) = ∑ j, (b.repr y j + N * m j) • φ (b j) := by
    have hyφ : φ y = ∑ j, b.repr y j • φ (b j) := by
      calc φ y = φ (∑ j, b.repr y j • b j) := by rw [b.sum_repr]
        _ = ∑ j, b.repr y j • φ (b j) := by rw [map_sum]; simp only [map_zsmul]
    rw [smul_add, ← hy, hyφ, hχ0, map_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_zsmul, smul_smul, add_smul]
  have hsc : ∀ z : X, Q (N • z) = N ^ 2 * Q z := by
    intro z
    have := quad_add_zsmul hs hQ 0 z N
    simp only [zero_add, quad_zero hQ, map_zero, AddMonoidHom.zero_apply, mul_zero] at this
    linarith
  have hbound : 4 * Q (x + φ χ0) ≤ g * ∑ j, Q (b j) := by
    have h1 : 4 * Q (N • (x + φ χ0)) ≤ N ^ 2 * ∑ j, Q (φ (b j)) := by
      rw [hNx]; exact hm
    rw [hsc] at h1
    simp only [hQφ, ← Finset.mul_sum] at h1
    have hN2 : 0 < N ^ 2 := by positivity
    have h2 : N ^ 2 * (4 * Q (x + φ χ0)) ≤ N ^ 2 * (g * ∑ j, Q (b j)) := by linarith
    exact le_of_mul_le_mul_left h2 hN2
  have hex : ∃ k : ℕ, ∃ χ : X, Q (x + φ χ) = k :=
    ⟨(Q (x + φ χ0)).toNat, χ0, (Int.toNat_of_nonneg (quad_nonneg hQ hp _)).symm⟩
  obtain ⟨χ, hχ⟩ := Nat.find_spec hex
  have hmin : ∀ χ' : X, Q (x + φ χ) ≤ Q (x + φ χ') := by
    intro χ'
    rw [hχ]
    have := Nat.find_min' hex ⟨χ', (Int.toNat_of_nonneg (quad_nonneg hQ hp (x + φ χ'))).symm⟩
    calc (Nat.find hex : ℤ) ≤ ((Q (x + φ χ')).toNat : ℤ) := by exact_mod_cast this
      _ = Q (x + φ χ') := Int.toNat_of_nonneg (quad_nonneg hQ hp _)
  refine ⟨χ, ?_, ?_⟩
  · have h1 : 4 * Q (x + φ χ) ≤ g * ∑ j, Q (b j) := by linarith [hmin χ0]
    have h2 : (∑ j, (Q (b j) : ℝ)) ≤ n * Cc := by
      calc (∑ j, (Q (b j) : ℝ)) ≤ ∑ _j : Fin n, Cc := Finset.sum_le_sum fun j _ => hC j
        _ = n * Cc := by simp
    have h3 : 4 * (Q (x + φ χ) : ℝ) ≤ g * ∑ j, (Q (b j) : ℝ) := by exact_mod_cast h1
    have hg' : (0 : ℝ) ≤ g := by positivity
    nlinarith
  · intro q z
    have hz := hmin (χ + z)
    rw [map_add, ← add_assoc] at hz
    have e1 := quad_add_zsmul hs hQ (x + φ χ) (φ z) 1
    have e2 := quad_add_zsmul hs hQ (x + φ χ) (φ z) q
    rw [one_smul] at e1
    rw [natCast_zsmul] at e2
    rw [e2]
    have hq0 : (0 : ℤ) ≤ q := by positivity
    nlinarith
end GlobalTheory
