-- Prove2me | solution 1 for GlobalTheory.exists_lattice_norm_one_of_norm_one_mod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:44:42.682532+00:00
-- url     : https://prove2.me/submissions/115e9219-3081-40c6-b6c0-0fc2192b8d8d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_HermitianLatticeNormOneOfNormOneModPrime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (K V : Type) [Field K] [CharZero K]
    [AddCommGroup V] [Module K V] (σ : K →+* K) (h : V →ₗ[K] V →ₛₗ[σ] K) (p d : ℕ) (θ : K)
    (O : Subring K) (L : AddSubgroup V) (hp : p.Prime) (_hd : d.Prime) (hθ : θ ^ 2 = -(d : K))
    (hσ : σ θ = -θ) (hK : ∀ x : K, ∃ a b : ℚ, x = (a : K) + (b : K) * θ)
    (hOσ : ∀ x ∈ O, σ x ∈ O) (hω : (1 + θ) / 2 ∈ O)
    (hO : ∀ r : ℚ, (r : K) ∈ O ↔ padicNorm p r ≤ 1) (hh : ∀ x y : V, h y x = σ (h x y))
    (_hdef : ∀ x : V, h x x = 0 → x = 0) (hL : ∀ a ∈ O, ∀ x ∈ L, a • x ∈ L)
    (_hint : ∀ x ∈ L, ∀ y ∈ L, h x y ∈ O) (hfull : ∀ x : V, ∃ m : ℕ, (p : K) ^ m • x ∈ L)
    (W : Submodule K V) (he : ∃ e ∈ W, h e e = 1)
    (hy : ∃ y ∈ L, y ∈ W ∧ ∃ u : ℚ, h y y = (u : K) ∧ padicNorm p (u - 1) < 1) :
    ∃ z ∈ L, z ∈ W ∧ h z z = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨e, heW, hee⟩ := he
  obtain ⟨y₀, hy₀L, hy₀W, u₀, hu₀, hr⟩ := hy
  have hσω : σ ((1 + θ) / 2) = (1 - θ) / 2 := by
    rw [map_div₀, map_add, map_one, hσ, map_ofNat, sub_eq_add_neg]
  have hn : padicNorm p ((1 + d) / 4) ≤ 1 := by
    rw [← hO]
    have := O.mul_mem hω (hOσ _ hω)
    rw [hσω] at this
    convert this using 1
    push_cast
    linear_combination (1 / 4 : K) * hθ

  have step : ∀ y ∈ L, y ∈ W → ∀ u : ℚ, h y y = (u : K) → padicNorm p (u - 1) ≤ 1 →
      ∃ y' ∈ L, y' ∈ W ∧ ∃ u' : ℚ, h y' y' = (u' : K) ∧
        padicNorm p (u' - 1) ≤ padicNorm p (u - 1) * padicNorm p (u - 1) := by
    intro y hyL hyW u hu hu1
    have hc : ((1 - u : ℚ) : K) ∈ O := by
      rw [hO, ← padicNorm.neg]; simpa using hu1
    have hu' : padicNorm p u ≤ 1 := by
      have := padicNorm.nonarchimedean (p := p) (q := u - 1) (r := 1)
      rw [sub_add_cancel, padicNorm.one] at this
      exact this.trans (max_le hu1 le_rfl)
    refine ⟨(1 + ((1 - u : ℚ) : K) * ((1 + θ) / 2)) • y,
      hL _ (O.add_mem O.one_mem (O.mul_mem hc hω)) y hyL, W.smul_mem _ hyW,
      1 + (u - 1) * (u - 1) * ((1 + d) / 4 * u - 1), ?_, ?_⟩
    · simp only [map_smul, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, hu, map_add, map_mul,
        map_one, hσω, map_ratCast]
      push_cast
      linear_combination (-(1 - (u : K)) ^ 2 * u / 4) * hθ
    · rw [add_sub_cancel_left, padicNorm.mul, padicNorm.mul]
      have h1 : padicNorm p ((1 + d) / 4 * u - 1) ≤ 1 := by
        refine padicNorm.sub.trans (max_le ?_ (by rw [padicNorm.one]))
        rw [padicNorm.mul]
        exact mul_le_one₀ hn (padicNorm.nonneg _) hu'
      exact mul_le_of_le_one_right
        (mul_nonneg (padicNorm.nonneg _) (padicNorm.nonneg _)) h1
  have hr0 : 0 ≤ padicNorm p (u₀ - 1) := padicNorm.nonneg _
  have iter : ∀ k : ℕ, ∃ y ∈ L, y ∈ W ∧ ∃ u : ℚ, h y y = (u : K) ∧
      padicNorm p (u - 1) ≤ padicNorm p (u₀ - 1) ^ (k + 1) := by
    intro k
    induction k with
    | zero => exact ⟨y₀, hy₀L, hy₀W, u₀, hu₀, by simp⟩
    | succ k ih =>
      obtain ⟨y, hyL, hyW, u, hu, hk⟩ := ih
      have hk1 : padicNorm p (u - 1) ≤ padicNorm p (u₀ - 1) :=
        hk.trans (by
          rw [pow_succ]
          exact mul_le_of_le_one_left hr0 (pow_le_one₀ hr0 hr.le))
      obtain ⟨y', hy'L, hy'W, u', hu', hle⟩ := step y hyL hyW u hu (hk1.trans hr.le)
      refine ⟨y', hy'L, hy'W, u', hu', hle.trans ?_⟩
      rw [pow_succ _ (k + 1)]
      exact mul_le_mul hk hk1 (padicNorm.nonneg _) (pow_nonneg hr0 _)
  obtain ⟨m, hm⟩ := hfull e
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hpos : ∀ q : ℚ, q ≠ 0 → 0 < padicNorm p q := fun q hq =>
    lt_of_le_of_ne (padicNorm.nonneg _) (padicNorm.nonzero hq).symm
  have hP0 : 0 < padicNorm p ((p : ℚ) ^ m) := hpos _ (pow_ne_zero _ hp0)
  have hP1 : padicNorm p ((p : ℚ) ^ m) ≤ 1 := by
    have := padicNorm.of_nat (p := p) (p ^ m)
    rwa [Nat.cast_pow] at this
  have h40 : 0 < padicNorm p 4 := hpos _ (by norm_num)
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (mul_pos h40 hP0) hr
  obtain ⟨y, hyL, hyW, u, hu, hyk⟩ := iter k
  have hsmall : padicNorm p (u - 1) < padicNorm p 4 * padicNorm p ((p : ℚ) ^ m) := by
    refine lt_of_le_of_lt (hyk.trans ?_) hk
    rw [pow_succ]
    exact mul_le_of_le_one_right (pow_nonneg hr0 _) hr.le

  have secant : ∀ y ∈ L, y ∈ W → h y y = (u : K) → ∀ T : ℚ, h e y + h y e = (T : K) →
      padicNorm p 4 ≤ padicNorm p (u + 1 - T) → ∃ z ∈ L, z ∈ W ∧ h z z = 1 := by
    intro y hyL hyW hu T hT hQ
    have hQpos : 0 < padicNorm p (u + 1 - T) := h40.trans_le hQ
    have hQ0 : u + 1 - T ≠ 0 := by
      intro h0; rw [h0, padicNorm.zero] at hQpos; exact lt_irrefl _ hQpos
    set t : ℚ := (1 - u) / ((u + 1 - T) * (p : ℚ) ^ m) with ht
    have htO : (t : K) ∈ O := by
      rw [hO, ht, padicNorm.div, padicNorm.mul, div_le_one (mul_pos hQpos hP0), ← padicNorm.neg,
        neg_sub]
      exact hsmall.le.trans (mul_le_mul_of_nonneg_right hQ hP0.le)
    have hpO : (p : K) ^ m ∈ O := O.pow_mem (natCast_mem O p) m
    have hs : t * (p : ℚ) ^ m * (u + 1 - T) = 1 - u := by
      rw [ht]; field_simp
    have hs' : (t : K) * (p : K) ^ m * (u + 1 - T) = 1 - u := by
      exact_mod_cast congrArg (fun q : ℚ => (q : K)) hs
    refine ⟨y + ((t : K) * (p : K) ^ m) • y - (t : K) • ((p : K) ^ m • e),
      L.sub_mem (L.add_mem hyL (hL _ (O.mul_mem htO hpO) y hyL)) (hL _ htO _ hm),
      W.sub_mem (W.add_mem hyW (W.smul_mem _ hyW)) (W.smul_mem _ (W.smul_mem _ heW)), ?_⟩
    simp only [map_smul, map_smulₛₗ, map_add, map_sub, LinearMap.smul_apply, LinearMap.add_apply,
      LinearMap.sub_apply, smul_eq_mul, hu, hee, map_mul, map_pow, map_ratCast, map_natCast,
      RingHom.id_apply]
    linear_combination (1 + (t : K) * (p : K) ^ m) * hs' -
      ((t : K) * (p : K) ^ m) * (1 + (t : K) * (p : K) ^ m) * hT
  obtain ⟨T, hT⟩ : ∃ T : ℚ, h e y + h y e = (T : K) := by
    obtain ⟨a, b, hab⟩ := hK (h e y)
    refine ⟨2 * a, ?_⟩
    rw [hh e y, hab, map_add, map_mul, map_ratCast, map_ratCast, hσ]
    push_cast
    ring
  by_cases hQ : padicNorm p 4 ≤ padicNorm p (u + 1 - T)
  · exact secant y hyL hyW hu T hT hQ
  · refine secant (-y) (L.neg_mem hyL) (W.neg_mem hyW) (by simpa using hu) (-T)
      (by
        simp only [map_neg, LinearMap.neg_apply]
        push_cast
        linear_combination -hT) ?_
    by_contra hQ'
    push Not at hQ hQ'
    have h2 : padicNorm p (2 * (u - 1)) < padicNorm p 4 := by
      rw [padicNorm.mul]
      have h21 : padicNorm p 2 ≤ 1 := by simpa using padicNorm.of_nat (p := p) 2
      refine lt_of_le_of_lt (mul_le_of_le_one_left (padicNorm.nonneg _) h21) ?_
      exact hsmall.trans_le (mul_le_of_le_one_right h40.le hP1)
    have h3 : padicNorm p 4 < padicNorm p 4 := by
      calc padicNorm p 4
          = padicNorm p ((u + 1 - T) + (u + 1 - -T) - 2 * (u - 1)) := by congr 1; ring
        _ ≤ _ := padicNorm.sub
        _ < padicNorm p 4 :=
          max_lt (lt_of_le_of_lt padicNorm.nonarchimedean (max_lt hQ hQ')) h2
    exact lt_irrefl _ h3
end GlobalTheory
