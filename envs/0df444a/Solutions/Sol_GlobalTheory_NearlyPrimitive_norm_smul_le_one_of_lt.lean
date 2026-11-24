-- Prove2me | solution 1 for GlobalTheory.NearlyPrimitive.norm_smul_le_one_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:37:38.257695+00:00
-- url     : https://prove2.me/submissions/93108cc6-3bdb-4430-888b-d84dd1dec393

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_NormSmulLeOneOfPrimitiveBoundedPowers
import Theorems.Thm_GlobalTheory_NearlyPrimitive_norm_factorial_inv_le
import Theorems.Thm_GlobalTheory_NearlyPrimitive_dpow_add
import Theorems.Thm_GlobalTheory_NearlyPrimitive_map_dpow
import Theorems.Thm_GlobalTheory_NearlyPrimitive_sum_lt
import Theorems.Thm_GlobalTheory_NearlyPrimitive_sum_le
import Theorems.Thm_GlobalTheory_NearlyPrimitive_exists_last_max

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.NearlyPrimitive
open Finset Filter Topology
namespace GlobalTheory.NearlyPrimitive
theorem _root_.solution (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C]
    [CharZero C] (p : ℕ) [hp : Fact p.Prime] (hpn : ‖(p : C)‖ = (p : ℝ)⁻¹)
    (B₁ B₂ : Type) [CommRing B₁] [Algebra C B₁] [CommRing B₂] [Algebra C B₂]
    (N₁ : B₁ → ℝ) (N₂ : B₂ → ℝ) (Δ i j : B₁ →ₐ[C] B₂)
    (hs₁ : ∀ (c : C) x, N₁ (c • x) = ‖c‖ * N₁ x) (hs₂ : ∀ (c : C) x, N₂ (c • x) = ‖c‖ * N₂ x)
    (hn₁ : ∀ x, 0 ≤ N₁ x) (hn₂ : ∀ x, 0 ≤ N₂ x)
    (hadd : ∀ x y, N₂ (x + y) ≤ max (N₂ x) (N₂ y)) (hmul : ∀ x y, N₂ (x * y) ≤ N₂ x * N₂ y)
    (hΔ : ∀ x, N₂ (Δ x) ≤ N₁ x) (hij : ∀ x y, N₂ (i x * j y) = N₁ x * N₁ y)
    (y : B₁) (K : ℝ) (hK : ∀ k : ℕ, N₁ (y ^ k) ≤ K) (he : N₂ (Δ y - i y - j y) ≤ 1)
    (c : C) (hc : ‖c‖ < (p : ℝ) ^ (-(1 / ((p : ℝ) - 1)))) : N₁ (c • y) ≤ 1 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  set q : ℝ := (p : ℝ) ^ (1 / ((p : ℝ) - 1)) with hq
  have hq0 : 0 < q := Real.rpow_pos_of_pos hp0 _
  set ρ : ℝ := q * ‖c‖ with hρ
  have hρ0 : 0 ≤ ρ := mul_nonneg hq0.le (norm_nonneg _)
  have hρ1 : ρ < 1 := by
    rw [Real.rpow_neg hp0.le, ← hq] at hc
    calc ρ < q * q⁻¹ := mul_lt_mul_of_pos_left hc hq0
      _ = 1 := mul_inv_cancel₀ hq0.ne'
  have hcoef : ∀ n : ℕ, ‖((n.factorial : C))⁻¹‖ * ‖c ^ n‖ ≤ ρ ^ n := fun n => by
    rw [hρ, mul_pow, norm_pow]
    exact mul_le_mul_of_nonneg_right (norm_factorial_inv_le p hpn n) (by positivity)
  have h0 : N₂ 0 = 0 := by simpa using hs₂ 0 0
  have hneg : ∀ x, N₂ (-x) = N₂ x := fun x => by simpa using hs₂ (-1) x
  set e := Δ y - i y - j y with hedef
  have hepow : ∀ l : ℕ, N₂ (e ^ (l + 1)) ≤ 1 := fun l => by
    induction l with
    | zero => simpa using he
    | succ l ih =>
      rw [pow_succ]
      exact (hmul _ _).trans (mul_le_one₀ ih (hn₂ _) he)
  have hd : ∀ l : ℕ, l ≠ 0 → N₂ (dpow C l (c • e)) < 1 := fun l hl => by
    obtain ⟨l', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hl
    rw [dpow, smul_pow, hs₂, hs₂, ← mul_assoc]
    calc _ ≤ ρ ^ (l' + 1) * 1 := mul_le_mul (hcoef _) (hepow _) (hn₂ _) (by positivity)
      _ < 1 := by rw [mul_one]; exact pow_lt_one₀ hρ0 hρ1 hl
  set t : ℕ → ℝ := fun n => N₁ (dpow C n (c • y)) with ht
  have ht0 : ∀ n, 0 ≤ t n := fun n => hn₁ _
  have htle : ∀ n, t n ≤ ρ ^ n * K := fun n => by
    simp only [ht]
    rw [dpow, smul_pow, hs₁, hs₁, ← mul_assoc]
    exact mul_le_mul (hcoef _) (hK _) (hn₁ _) (by positivity)
  have hlim : Tendsto t atTop (𝓝 0) := by
    refine squeeze_zero ht0 htle ?_
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).mul_const K
  by_contra hcon
  have h1 : 1 < t 1 := by simpa [ht, dpow] using hcon
  obtain ⟨k, hk1, hmax, hlast⟩ := exists_last_max t hlim 1 h1
  have hk0 : 0 < t k := by linarith
  have hT : 0 < t k * t k := mul_pos hk0 hk0
  set s := i (c • y) + j (c • y) with hsdef
  have hγs : ∀ m, dpow C m s =
      ∑ x ∈ antidiagonal m, i (dpow C x.1 (c • y)) * j (dpow C x.2 (c • y)) := fun m => by
    rw [hsdef, dpow_add]
    simp only [map_dpow]
  have hsle : ∀ m, N₂ (dpow C m s) ≤ t k * t k := fun m => by
    rw [hγs]
    refine sum_le N₂ h0 hadd hT.le _ _ fun x _ => ?_
    rw [hij]
    exact mul_le_mul (hmax _) (hmax _) (ht0 _) hk0.le
  have hΔz : Δ (c • y) = s + c • e := by
    simp only [hsdef, hedef, map_smul, smul_sub]
    abel
  have hkk : (k, k) ∈ antidiagonal (k + k) := by simp
  have h2k : (k + k, 0) ∈ antidiagonal (k + k) := by simp
  have E1 := dpow_add (C := C) (k + k) s (c • e)
  rw [← hΔz, ← map_dpow, ← Finset.add_sum_erase _ _ h2k] at E1
  have E2 := hγs (k + k)
  rw [← Finset.add_sum_erase _ _ hkk] at E2
  have hz : dpow C 0 (c • e) = 1 := by simp [dpow]
  simp only [hz, mul_one] at E1 E2
  have hA : N₂ (Δ (dpow C (k + k) (c • y))) < t k * t k := by
    refine (hΔ _).trans_lt ((hmax (k + k)).trans_lt ?_)
    nlinarith
  have hB : N₂ (∑ x ∈ (antidiagonal (k + k)).erase (k + k, 0),
      dpow C x.1 s * dpow C x.2 (c • e)) < t k * t k := by
    refine sum_lt N₂ h0 hadd hT _ _ fun x hx => ?_
    rw [mem_erase, Finset.HasAntidiagonal.mem_antidiagonal] at hx
    have hx2 : x.2 ≠ 0 := fun h => hx.1 (Prod.ext (by have := hx.2; simp only; omega) h)
    calc _ ≤ N₂ (dpow C x.1 s) * N₂ (dpow C x.2 (c • e)) := hmul _ _
      _ ≤ t k * t k * N₂ (dpow C x.2 (c • e)) := mul_le_mul_of_nonneg_right (hsle _) (hn₂ _)
      _ < t k * t k := mul_lt_of_lt_one_right hT (hd _ hx2)
  have hC : N₂ (∑ x ∈ (antidiagonal (k + k)).erase (k, k),
      i (dpow C x.1 (c • y)) * j (dpow C x.2 (c • y))) < t k * t k := by
    refine sum_lt N₂ h0 hadd hT _ _ fun x hx => ?_
    rw [mem_erase, Finset.HasAntidiagonal.mem_antidiagonal] at hx
    rw [hij]
    change t x.1 * t x.2 < _
    have : k < x.1 ∨ k < x.2 := by
      by_contra h
      push Not at h
      have := hx.2
      exact hx.1 (Prod.ext (by simp only; omega) (by simp only; omega))
    rcases this with h | h
    · exact (mul_le_mul_of_nonneg_left (hmax _) (ht0 _)).trans_lt
        (mul_lt_mul_of_pos_right (hlast _ h) hk0)
    · exact mul_lt_mul' (hmax _) (hlast _ h) (ht0 _) hk0
  have E3 : i (dpow C k (c • y)) * j (dpow C k (c • y)) =
      Δ (dpow C (k + k) (c • y)) + -(∑ x ∈ (antidiagonal (k + k)).erase (k + k, 0),
      dpow C x.1 s * dpow C x.2 (c • e)) + -(∑ x ∈ (antidiagonal (k + k)).erase (k, k),
      i (dpow C x.1 (c • y)) * j (dpow C x.2 (c • y))) := by
    rw [E1, E2]; abel
  have hfin : N₂ (i (dpow C k (c • y)) * j (dpow C k (c • y))) < t k * t k := by
    rw [E3]
    refine (hadd _ _).trans_lt (max_lt ((hadd _ _).trans_lt (max_lt hA ?_)) ?_)
    · rwa [hneg]
    · rwa [hneg]
  rw [hij] at hfin
  exact lt_irrefl _ hfin
end GlobalTheory.NearlyPrimitive
