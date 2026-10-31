-- Prove2me | solution 1 for KellyStochasticNetworks.ImpliedCosts.revenue_sensitivity
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T05:01:39.959985+00:00
-- url     : https://prove2.me/submissions/2709f93a-0f8c-4be6-88d7-c0be877941ca

import Definitions.Def_KellyStochasticNetworks_ImpliedCosts_Model
import Theorems.Thm_KellyStochasticNetworks_erlang_deriv
import Theorems.Thm_KellyStochasticNetworks_erlang_fixed_point_unique
import Theorems.Thm_KellyStochasticNetworks_ImpliedCosts_matrix_characterization


namespace KellyStochasticNetworks.ImpliedCosts.ICproof

open Finset

/-! ### Scalar Erlang facts -/

noncomputable def S (N : ℕ) (ν : ℝ) : ℝ := ∑ k ∈ range (N + 1), ν ^ k / (k.factorial : ℝ)

lemma erlang_eq (ν : ℝ) (N : ℕ) : erlang ν N = (ν ^ N / (N.factorial : ℝ)) / S N ν := rfl

lemma S_ge (N : ℕ) (ν : ℝ) :
    ν ^ N / (N.factorial : ℝ) + ∑ k ∈ range N, ν ^ k / (k.factorial : ℝ) = S N ν := by
  unfold S; rw [sum_range_succ]; ring

lemma S_pos (N : ℕ) {ν : ℝ} (hν : 0 ≤ ν) : 1 ≤ S N ν := by
  unfold S
  rw [sum_range_succ']
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one]
  have : 0 ≤ ∑ k ∈ range N, ν ^ (k + 1) / ((k + 1).factorial : ℝ) :=
    sum_nonneg (fun k _ => by positivity)
  linarith

lemma erlang_nonneg (N : ℕ) {ν : ℝ} (hν : 0 ≤ ν) : 0 ≤ erlang ν N := by
  rw [erlang_eq]
  have := S_pos N hν
  positivity

lemma erlang_zero (ν : ℝ) : erlang ν 0 = 1 := by
  simp [erlang]

lemma erlang_le_one (N : ℕ) {ν : ℝ} (hν : 0 ≤ ν) : erlang ν N ≤ 1 := by
  rw [erlang_eq, div_le_one (by linarith [S_pos N hν]), ← S_ge N ν]
  have : 0 ≤ ∑ k ∈ range N, ν ^ k / (k.factorial : ℝ) := sum_nonneg (fun k _ => by positivity)
  linarith

lemma erlang_lt_one (N : ℕ) (hN : 1 ≤ N) {ν : ℝ} (hν : 0 ≤ ν) : erlang ν N < 1 := by
  rw [erlang_eq, div_lt_one (by linarith [S_pos N hν]), ← S_ge N ν]
  have h1 : 1 ≤ ∑ k ∈ range N, ν ^ k / (k.factorial : ℝ) := by
    obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    rw [sum_range_succ']
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one]
    have : 0 ≤ ∑ k ∈ range M, ν ^ (k + 1) / ((k + 1).factorial : ℝ) :=
      sum_nonneg (fun k _ => by positivity)
    linarith
  linarith

lemma pow_le_aux {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) {i k : ℕ} (hki : k ≤ i) :
    a ^ i * b ^ k ≤ b ^ i * a ^ k := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hki
  have h1 : a ^ d ≤ b ^ d := pow_le_pow_left₀ ha hab d
  have h2 : 0 ≤ a ^ k := pow_nonneg ha k
  have h3 : 0 ≤ b ^ k := pow_nonneg (le_trans ha hab) k
  calc a ^ (k + d) * b ^ k = (a ^ k * b ^ k) * a ^ d := by ring
    _ ≤ (a ^ k * b ^ k) * b ^ d := mul_le_mul_of_nonneg_left h1 (mul_nonneg h2 h3)
    _ = b ^ (k + d) * a ^ k := by ring

lemma erlang_strict (N : ℕ) (hN : 1 ≤ N) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    erlang a N < erlang b N := by
  have hb : 0 ≤ b := le_of_lt (lt_of_le_of_lt ha hab)
  rw [erlang_eq, erlang_eq,
    div_lt_div_iff₀ (by linarith [S_pos N ha]) (by linarith [S_pos N hb])]
  unfold S
  rw [Finset.mul_sum, Finset.mul_sum, ← sub_neg, ← Finset.sum_sub_distrib]
  have key : ∀ k ∈ range (N + 1), a ^ N / (N.factorial : ℝ) * (b ^ k / (k.factorial : ℝ))
      - b ^ N / (N.factorial : ℝ) * (a ^ k / (k.factorial : ℝ))
      = (a ^ N * b ^ k - b ^ N * a ^ k) / ((N.factorial : ℝ) * k.factorial) := by
    intro k _; ring
  rw [Finset.sum_congr rfl key]
  have hle : ∀ k ∈ range (N + 1),
      (a ^ N * b ^ k - b ^ N * a ^ k) / ((N.factorial : ℝ) * k.factorial) ≤ 0 := by
    intro k hk
    have hk' : k ≤ N := by simp at hk; omega
    exact div_nonpos_of_nonpos_of_nonneg (by linarith [pow_le_aux ha (le_of_lt hab) hk'])
      (by positivity)
  have hlt : (a ^ N * b ^ 0 - b ^ N * a ^ 0) / ((N.factorial : ℝ) * (Nat.factorial 0 : ℕ)) < 0 := by
    simp only [pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one]
    apply div_neg_of_neg_of_pos _ (by positivity)
    have := pow_lt_pow_left₀ hab ha (by omega : N ≠ 0)
    linarith
  have h := Finset.sum_lt_sum (s := range (N + 1))
    (f := fun k => (a ^ N * b ^ k - b ^ N * a ^ k) / ((N.factorial : ℝ) * k.factorial))
    (g := fun _ => (0 : ℝ)) hle ⟨0, by simp, hlt⟩
  simp only [Finset.sum_const_zero] at h
  exact h

lemma erlang_mono (N : ℕ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    erlang a N ≤ erlang b N := by
  rcases Nat.eq_zero_or_pos N with h | h
  · subst h; simp [erlang_zero]
  rcases eq_or_lt_of_le hab with h' | h'
  · rw [h']
  · exact le_of_lt (erlang_strict N h ha h')

lemma carried_eq (N : ℕ) {ν : ℝ} (hν : 0 ≤ ν) :
    ν * (1 - erlang ν N)
      = (∑ k ∈ range (N + 1), (k : ℝ) * (ν ^ k / (k.factorial : ℝ))) / S N ν := by
  have hS := S_pos N hν
  have hS0 : S N ν ≠ 0 := by linarith
  rw [erlang_eq, eq_div_iff hS0]
  have e1 : ν * (1 - ν ^ N / (N.factorial : ℝ) / S N ν) * S N ν
      = ν * (S N ν - ν ^ N / (N.factorial : ℝ)) := by field_simp
  rw [e1, ← S_ge N ν, sum_range_succ']
  simp only [Nat.cast_zero, zero_mul, add_zero, add_sub_cancel_left, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [Nat.factorial_succ]
  push_cast
  have : (k.factorial : ℝ) ≠ 0 := by positivity
  have : (k : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

lemma carried_strict (N : ℕ) (hN : 1 ≤ N) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    a * (1 - erlang a N) < b * (1 - erlang b N) := by
  have hb : 0 ≤ b := le_of_lt (lt_of_le_of_lt ha hab)
  rw [carried_eq N ha, carried_eq N hb,
    div_lt_div_iff₀ (by linarith [S_pos N ha]) (by linarith [S_pos N hb])]
  unfold S
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum, ← sub_pos]
  set w : ℕ → ℝ → ℝ := fun k ν => ν ^ k / (k.factorial : ℝ) with hw
  set X : ℕ → ℕ → ℝ := fun i k => w i b * w k a - w i a * w k b with hX
  have hD1 : (∑ i ∈ range (N + 1), ∑ k ∈ range (N + 1), (i : ℝ) * w i b * w k a)
      - (∑ i ∈ range (N + 1), ∑ k ∈ range (N + 1), (i : ℝ) * w i a * w k b)
      = ∑ i ∈ range (N + 1), ∑ k ∈ range (N + 1), (i : ℝ) * X i k := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro i _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro k _
    simp only [hX]; ring
  have hD2 : ∑ i ∈ range (N + 1), ∑ k ∈ range (N + 1), (i : ℝ) * X i k
      = ∑ i ∈ range (N + 1), ∑ k ∈ range (N + 1), -((k : ℝ) * X i k) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro k _
    simp only [hX]; ring
  have hterm : ∀ i k : ℕ, 0 ≤ ((i : ℝ) - k) * X i k := by
    intro i k
    simp only [hX, hw]
    have e : b ^ i / (i.factorial : ℝ) * (a ^ k / (k.factorial : ℝ))
        - a ^ i / (i.factorial : ℝ) * (b ^ k / (k.factorial : ℝ))
        = (b ^ i * a ^ k - a ^ i * b ^ k) / ((i.factorial : ℝ) * k.factorial) := by ring
    rw [e]
    rcases le_total k i with hki | hik
    · have hc : (k : ℝ) ≤ i := by exact_mod_cast hki
      apply mul_nonneg (by linarith)
      apply div_nonneg _ (by positivity)
      linarith [pow_le_aux ha (le_of_lt hab) hki]
    · have hc : (i : ℝ) ≤ k := by exact_mod_cast hik
      apply mul_nonneg_of_nonpos_of_nonpos (by linarith)
      apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
      linarith [pow_le_aux ha (le_of_lt hab) hik]
  have h2D : 2 * ((∑ i ∈ range (N + 1), ∑ k ∈ range (N + 1), (i : ℝ) * w i b * w k a)
      - (∑ i ∈ range (N + 1), ∑ k ∈ range (N + 1), (i : ℝ) * w i a * w k b))
      = ∑ i ∈ range (N + 1), ∑ k ∈ range (N + 1), ((i : ℝ) - k) * X i k := by
    rw [hD1, two_mul]
    nth_rewrite 2 [hD2]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro k _
    ring
  have hpos : 0 < ∑ i ∈ range (N + 1), ∑ k ∈ range (N + 1), ((i : ℝ) - k) * X i k := by
    apply Finset.sum_pos' (fun i _ => Finset.sum_nonneg (fun k _ => hterm i k))
    refine ⟨1, by simp; omega, ?_⟩
    apply Finset.sum_pos' (fun k _ => hterm 1 k)
    refine ⟨0, by simp, ?_⟩
    simp only [hX, hw]
    norm_num
    linarith
  have hconv : ∀ ν₁ ν₂ : ℝ, (∑ i ∈ range (N + 1), ∑ j ∈ range (N + 1),
      (i : ℝ) * (ν₁ ^ i / (i.factorial : ℝ)) * (ν₂ ^ j / (j.factorial : ℝ)))
      = ∑ i ∈ range (N + 1), ∑ k ∈ range (N + 1), (i : ℝ) * w i ν₁ * w k ν₂ := fun _ _ => rfl
  rw [hconv b a, hconv a b]
  linarith

lemma carried_mono (N : ℕ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    a * (1 - erlang a N) ≤ b * (1 - erlang b N) := by
  rcases Nat.eq_zero_or_pos N with h | h
  · subst h; simp [erlang_zero]
  rcases eq_or_lt_of_le hab with h' | h'
  · rw [h']
  · exact le_of_lt (carried_strict N h ha h')

/-! ### The interpolated Erlang function -/

lemma interp_nat (ρ : ℝ) (n : ℕ) : interpolatedErlang ρ (n : ℝ) = erlang ρ n := by
  simp [interpolatedErlang]

lemma interp_left (ρ : ℝ) (n : ℕ) (hn : 1 ≤ n) (t : ℝ) (h1 : (n : ℝ) - 1 < t)
    (h2 : t ≤ n) :
    interpolatedErlang ρ t = erlang ρ n + (t - n) * (erlang ρ n - erlang ρ (n - 1)) := by
  rcases eq_or_lt_of_le h2 with h | h
  · subst h; rw [interp_nat]; ring
  · have hfl : Nat.floor t = n - 1 := by
      rw [Nat.floor_eq_iff (by
        have : (1 : ℝ) ≤ n := by exact_mod_cast hn
        linarith)]
      push_cast [hn]
      constructor <;> linarith
    simp only [interpolatedErlang, hfl]
    have : n - 1 + 1 = n := by omega
    rw [this]
    push_cast [hn]
    ring

/-- Properties of the interpolated Erlang function used for uniqueness. -/
lemma interp_props (x : ℝ) (hx : 0 < x) :
    (∀ ρ, 0 ≤ ρ → 0 ≤ interpolatedErlang ρ x) ∧
    (∀ ρ, 0 ≤ ρ → interpolatedErlang ρ x < 1) ∧
    (∀ a b, 0 ≤ a → a ≤ b → interpolatedErlang a x ≤ interpolatedErlang b x) ∧
    (∀ a b, 0 ≤ a → a < b →
      a * (1 - interpolatedErlang a x) < b * (1 - interpolatedErlang b x)) := by
  set n := Nat.floor x with hn
  set θ := x - (n : ℝ) with hθ
  have hθ0 : 0 ≤ θ := by rw [hθ]; linarith [Nat.floor_le hx.le]
  have hθ1 : θ < 1 := by rw [hθ]; linarith [Nat.lt_floor_add_one x]
  have hform : ∀ ρ, interpolatedErlang ρ x = (1 - θ) * erlang ρ n + θ * erlang ρ (n + 1) := by
    intro ρ; rfl
  -- either n ≥ 1, or n = 0 and θ > 0
  have hcase : 1 ≤ n ∨ (n = 0 ∧ 0 < θ) := by
    rcases Nat.eq_zero_or_pos n with h | h
    · right; refine ⟨h, ?_⟩; rw [hθ, h]; simpa using hx
    · left; exact h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ρ hρ
    rw [hform]
    have := erlang_nonneg n hρ; have := erlang_nonneg (n + 1) hρ
    nlinarith
  · intro ρ hρ
    rw [hform]
    have h1 := erlang_le_one n hρ
    have h2 := erlang_lt_one (n + 1) (by omega) hρ
    rcases hcase with h | ⟨_, h⟩
    · have h3 := erlang_lt_one n h hρ
      nlinarith
    · nlinarith
  · intro a b ha hab
    rw [hform, hform]
    have := erlang_mono n ha hab; have := erlang_mono (n + 1) ha hab
    nlinarith
  · intro a b ha hab
    have e : ∀ ρ, ρ * (1 - interpolatedErlang ρ x)
        = (1 - θ) * (ρ * (1 - erlang ρ n)) + θ * (ρ * (1 - erlang ρ (n + 1))) := by
      intro ρ; rw [hform]; ring
    rw [e, e]
    have h2 := carried_strict (n + 1) (by omega) ha hab
    have h1 := carried_mono n ha hab.le
    rcases hcase with h | ⟨_, h⟩
    · have h3 := carried_strict n h ha hab
      nlinarith
    · nlinarith

end KellyStochasticNetworks.ImpliedCosts.ICproof


namespace KellyStochasticNetworks.ImpliedCosts.ICproof

open Finset

/-- Uniqueness of the fixed point for any per-link blocking functions that are monotone,
take values in `[0,1)`, and have strictly increasing carried load. -/
lemma fp_unique {J R : ℕ} (A : Fin J → Fin R → ℕ) (ν : Fin R → ℝ)
    (hν : ∀ r, 0 < ν r) (f : Fin J → ℝ → ℝ)
    (hf0 : ∀ j ρ, 0 ≤ ρ → 0 ≤ f j ρ)
    (hmono : ∀ j a b, 0 ≤ a → a ≤ b → f j a ≤ f j b)
    (hcarS : ∀ j a b, 0 ≤ a → a < b → a * (1 - f j a) < b * (1 - f j b))
    (E E' : Fin J → ℝ)
    (hK : ∀ j, E j ∈ Set.Ico (0 : ℝ) 1) (hF : ∀ j, E j = f j (reducedLoad A ν E j))
    (hK' : ∀ j, E' j ∈ Set.Ico (0 : ℝ) 1) (hF' : ∀ j, E' j = f j (reducedLoad A ν E' j)) :
    E = E' := by
  set L : (Fin J → ℝ) → Fin J → ℝ := fun E j => linkLoad A (carried A ν E) j with hLdef
  have hLnn : ∀ (E : Fin J → ℝ), (∀ j, E j ∈ Set.Ico (0 : ℝ) 1) → ∀ j, 0 ≤ L E j := by
    intro E hK j
    apply Finset.sum_nonneg; intro r _
    apply mul_nonneg (by positivity)
    apply mul_nonneg (le_of_lt (hν r))
    apply Finset.prod_nonneg; intro i _
    exact pow_nonneg (by linarith [(hK i).2]) _
  have hρdef : ∀ E j, reducedLoad A ν E j = (1 - E j)⁻¹ * L E j := fun _ _ => rfl
  have hρ0 : ∀ (E : Fin J → ℝ), (∀ j, E j ∈ Set.Ico (0 : ℝ) 1) →
      ∀ j, 0 ≤ (1 - E j)⁻¹ * L E j := by
    intro E hK j
    exact mul_nonneg (inv_nonneg.2 (by linarith [(hK j).2])) (hLnn E hK j)
  have hcar : ∀ (E : Fin J → ℝ), (∀ j, E j ∈ Set.Ico (0 : ℝ) 1) →
      (∀ j, E j = f j (reducedLoad A ν E j)) →
      ∀ j, (1 - E j)⁻¹ * L E j * (1 - f j ((1 - E j)⁻¹ * L E j)) = L E j := by
    intro E hK hF j
    rw [← hρdef, ← hF j, hρdef]
    have : 1 - E j ≠ 0 := by linarith [(hK j).2]
    field_simp
  set x : (Fin J → ℝ) → Fin J → ℝ := fun E j => -Real.log (1 - E j) with hx
  have hexp : ∀ (E : Fin J → ℝ), (∀ j, E j < 1) → ∀ j, Real.exp (-x E j) = 1 - E j := by
    intro E h j; simp only [hx, neg_neg]; exact Real.exp_log (by linarith [h j])
  have hprod : ∀ (E : Fin J → ℝ), (∀ j, E j < 1) → ∀ r,
      ∏ i, (1 - E i) ^ (A i r) = Real.exp (-∑ i, (A i r : ℝ) * x E i) := by
    intro E h r
    rw [← Finset.sum_neg_distrib, Real.exp_sum]
    apply Finset.prod_congr rfl; intro i _
    rw [← hexp E h i, ← Real.exp_nat_mul]; congr 1; ring
  have hl : ∀ j, E j < 1 := fun j => (hK j).2
  have hl' : ∀ j, E' j < 1 := fun j => (hK' j).2
  set T : Fin J → ℝ := fun j => (x E j - x E' j) * (L E j - L E' j) with hT
  have hTpos : ∀ j, E j ≠ E' j → 0 < T j := by
    intro j hne
    have key : ∀ (E E' : Fin J → ℝ), (∀ j, E j ∈ Set.Ico (0 : ℝ) 1) →
        (∀ j, E j = f j (reducedLoad A ν E j)) →
        (∀ j, E' j ∈ Set.Ico (0 : ℝ) 1) → (∀ j, E' j = f j (reducedLoad A ν E' j)) →
        E j < E' j → x E j < x E' j ∧ L E j < L E' j := by
      intro E E' hK hF hK' hF' hlt'
      have h1 := (hK j).2
      have h2 := (hK' j).2
      constructor
      · simp only [hx, neg_lt_neg_iff]
        exact Real.log_lt_log (by linarith) (by linarith)
      · have hρ : (1 - E j)⁻¹ * L E j < (1 - E' j)⁻¹ * L E' j := by
          by_contra hc
          push Not at hc
          have := hmono j _ _ (hρ0 E' hK' j) hc
          rw [← hρdef, ← hρdef, ← hF j, ← hF' j] at this
          linarith
        rw [← hcar E hK hF j, ← hcar E' hK' hF' j]
        exact hcarS j _ _ (hρ0 E hK j) hρ
    rcases lt_or_gt_of_ne hne with h | h
    · obtain ⟨h1, h2⟩ := key E E' hK hF hK' hF' h
      simp only [hT]; nlinarith
    · obtain ⟨h1, h2⟩ := key E' E hK' hF' hK hF h
      simp only [hT]; nlinarith
  have hTnn : ∀ j, 0 ≤ T j := by
    intro j
    by_cases h : E j = E' j
    · simp only [hT, hx, h, sub_self, zero_mul, le_refl]
    · exact le_of_lt (hTpos j h)
  set s : (Fin J → ℝ) → Fin R → ℝ := fun E r => ∑ i, (A i r : ℝ) * x E i with hs
  have hLe : ∀ (E : Fin J → ℝ), (∀ j, E j < 1) → ∀ j,
      L E j = ∑ r, (A j r : ℝ) * ν r * Real.exp (-s E r) := by
    intro E h j
    simp only [hLdef, hs, linkLoad, carried, acceptance]
    apply Finset.sum_congr rfl; intro r _
    rw [hprod E h r]; ring
  have hsum : ∑ j, T j = ∑ r, ν r * ((s E r - s E' r) *
      (Real.exp (-s E r) - Real.exp (-s E' r))) := by
    simp only [hT]
    rw [show (∑ j, (x E j - x E' j) * (L E j - L E' j))
        = ∑ j, ∑ r, (x E j - x E' j) * ((A j r : ℝ) * ν r *
            (Real.exp (-s E r) - Real.exp (-s E' r))) from by
      apply Finset.sum_congr rfl; intro j _
      rw [hLe E hl j, hLe E' hl' j, ← Finset.sum_sub_distrib, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro r _; ring]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro r _
    simp only [hs]
    rw [← Finset.sum_sub_distrib, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _; ring
  have hroute : ∀ r, ν r * ((s E r - s E' r) * (Real.exp (-s E r) - Real.exp (-s E' r))) ≤ 0 := by
    intro r
    apply mul_nonpos_of_nonneg_of_nonpos (le_of_lt (hν r))
    rcases le_total (s E r) (s E' r) with h | h
    · have := Real.exp_le_exp.2 (neg_le_neg h)
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
    · have := Real.exp_le_exp.2 (neg_le_neg h)
      exact mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
  have hle0 : ∑ j, T j ≤ 0 := by
    rw [hsum]; exact Finset.sum_nonpos (fun r _ => hroute r)
  have hzero : ∀ j ∈ Finset.univ, T j = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hTnn j)).1
      (le_antisymm hle0 (Finset.sum_nonneg (fun j _ => hTnn j)))
  funext j
  by_contra hne
  have := hTpos j hne
  rw [hzero j (Finset.mem_univ j)] at this
  exact lt_irrefl _ this

/-- Uniqueness for interpolated fixed points at positive real capacities. -/
lemma interp_fp_unique {J R : ℕ} (A : Fin J → Fin R → ℕ) (ν : Fin R → ℝ)
    (hν : ∀ r, 0 < ν r) (C : Fin J → ℝ) (hC : ∀ j, 0 < C j) (E E' : Fin J → ℝ)
    (h : InterpolatedFixedPoint A ν C E) (h' : InterpolatedFixedPoint A ν C E') : E = E' :=
  fp_unique A ν hν (fun j ρ => interpolatedErlang ρ (C j))
    (fun j => (interp_props (C j) (hC j)).1)
    (fun j => (interp_props (C j) (hC j)).2.2.1)
    (fun j => (interp_props (C j) (hC j)).2.2.2)
    E E' h.1 h.2 h'.1 h'.2

lemma blocking_eq {J R : ℕ} (A : Fin J → Fin R → ℕ) (ν : Fin R → ℝ)
    (hν : ∀ r, 0 < ν r) (C : Fin J → ℝ) (hC : ∀ j, 0 < C j) (E : Fin J → ℝ)
    (h : InterpolatedFixedPoint A ν C E) : blocking A ν C = E := by
  have hex : ∃ B, InterpolatedFixedPoint A ν C B := ⟨E, h⟩
  have hb : blocking A ν C = Classical.choose hex := by
    simp only [blocking, dif_pos hex]
  rw [hb]
  exact interp_fp_unique A ν hν C hC _ _ (Classical.choose_spec hex) h

end KellyStochasticNetworks.ImpliedCosts.ICproof


namespace KellyStochasticNetworks.ImpliedCosts.ICproof

open Finset

lemma contDiffAt_erlang (n : ℕ) {ρ : ℝ} (hρ : 0 < ρ) :
    ContDiffAt ℝ 1 (fun v : ℝ => erlang v n) ρ := by
  have hS : (∑ j ∈ Finset.range (n + 1), ρ ^ j / (Nat.factorial j : ℝ)) ≠ 0 := by
    have := S_pos n hρ.le; unfold S at this; linarith
  unfold erlang
  refine ContDiffAt.div (by fun_prop) ?_ hS
  exact ContDiffAt.sum (fun j _ => by fun_prop)

lemma hasDerivAt_erlang (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) :
    HasDerivAt (fun v : ℝ => erlang v n)
      (-(1 - erlang ρ n) * (erlang ρ n - erlang ρ (n - 1))) ρ := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simpa using erlang_deriv ρ m hρ

/-- Derivative of route acceptance along a curve of blocking vectors. -/
lemma hasDerivAt_acceptance {J R : ℕ} (A : Fin J → Fin R → ℕ) (Bc : ℝ → Fin J → ℝ)
    (b : Fin J → ℝ) (s0 : ℝ) (hB : ∀ k, HasDerivAt (fun s => Bc s k) (b k) s0)
    (hlt : ∀ k, Bc s0 k < 1) (r : Fin R) :
    HasDerivAt (fun s => acceptance A (Bc s) r)
      (-(acceptance A (Bc s0) r) * ∑ k, (A k r : ℝ) * (b k / (1 - Bc s0 k))) s0 := by
  unfold acceptance
  have hk : ∀ k ∈ (Finset.univ : Finset (Fin J)),
      HasDerivAt (fun s => (1 - Bc s k) ^ A k r)
        ((A k r : ℝ) * (1 - Bc s0 k) ^ (A k r - 1) * (-(b k))) s0 := by
    intro k _
    have h1 : HasDerivAt (fun s => 1 - Bc s k) (-(b k)) s0 := by
      simpa using (hB k).const_sub 1
    exact h1.fun_pow (A k r)
  refine (HasDerivAt.fun_finsetProd hk).congr_deriv ?_
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  have hne : 1 - Bc s0 k ≠ 0 := by linarith [hlt k]
  have hpe := Finset.prod_erase_mul (Finset.univ : Finset (Fin J))
    (fun j => (1 - Bc s0 j) ^ A j r) (Finset.mem_univ k)
  rcases Nat.eq_zero_or_pos (A k r) with h0 | hpos
  · simp [h0]
  · have hp : (1 - Bc s0 k) ^ A k r = (1 - Bc s0 k) ^ (A k r - 1) * (1 - Bc s0 k) := by
      rw [← pow_succ]; congr 1; omega
    rw [← hpe, hp, smul_eq_mul]
    field_simp

end KellyStochasticNetworks.ImpliedCosts.ICproof


namespace KellyStochasticNetworks.ImpliedCosts.ICproof

open Finset

/-- Offered traffic along the perturbation direction `μ`. -/
noncomputable def νt {R : ℕ} (ν μ : Fin R → ℝ) (t0 t : ℝ) : Fin R → ℝ :=
  fun r => ν r + (t - t0) * μ r

/-- Smooth extension of the link blocking function along the capacity direction `κ`. -/
noncomputable def Gf {J : ℕ} (C : Fin J → ℕ) (κ : Fin J → ℝ) (t0 t ρ : ℝ) (i : Fin J) : ℝ :=
  erlang ρ (C i) + (t - t0) * κ i * (erlang ρ (C i) - erlang ρ (C i - 1))

/-- The fixed-point residual map. -/
noncomputable def Fm {J R : ℕ} (A : Fin J → Fin R → ℕ) (ν μ : Fin R → ℝ) (C : Fin J → ℕ)
    (κ : Fin J → ℝ) (t0 : ℝ) (p : ℝ × (Fin J → ℝ)) : Fin J → ℝ :=
  fun i => p.2 i - Gf C κ t0 p.1 (reducedLoad A (νt ν μ t0 p.1) p.2 i) i

lemma reducedLoad_expand {J R : ℕ} (A : Fin J → Fin R → ℕ) (ν : Fin R → ℝ) (B : Fin J → ℝ)
    (i : Fin J) : reducedLoad A ν B i =
      (1 - B i)⁻¹ * ∑ r, (A i r : ℝ) * (ν r * ∏ k, (1 - B k) ^ A k r) := rfl

/-- Derivative of the reduced load along a curve. -/
lemma hasDerivAt_rho {J R : ℕ} (A : Fin J → Fin R → ℕ) (ν μ : Fin R → ℝ) (t0 : ℝ)
    (T : ℝ → ℝ) (τ : ℝ) (Bc : ℝ → Fin J → ℝ) (b : Fin J → ℝ) (s0 : ℝ)
    (hT : HasDerivAt T τ s0) (hT0 : T s0 = t0)
    (hB : ∀ k, HasDerivAt (fun s => Bc s k) (b k) s0)
    (hlt : ∀ k, Bc s0 k < 1) (i : Fin J) :
    HasDerivAt (fun s => reducedLoad A (νt ν μ t0 (T s)) (Bc s) i)
      (b i / (1 - Bc s0 i) ^ 2 * linkLoad A (carried A ν (Bc s0)) i +
        (1 - Bc s0 i)⁻¹ * ∑ r, (A i r : ℝ) * (τ * μ r * acceptance A (Bc s0) r +
          ν r * (-(acceptance A (Bc s0) r) * ∑ k, (A k r : ℝ) * (b k / (1 - Bc s0 k)))))
      s0 := by
  have hne : 1 - Bc s0 i ≠ 0 := by linarith [hlt i]
  have h1 : HasDerivAt (fun s => (1 - Bc s i)⁻¹) (-(-(b i)) / (1 - Bc s0 i) ^ 2) s0 := by
    have : HasDerivAt (fun s => 1 - Bc s i) (-(b i)) s0 := by
      simpa using (hB i).const_sub 1
    exact this.fun_inv hne
  have h2 : ∀ r ∈ (Finset.univ : Finset (Fin R)),
      HasDerivAt (fun s => (A i r : ℝ) * ((ν r + (T s - t0) * μ r) * acceptance A (Bc s) r))
        ((A i r : ℝ) * (τ * μ r * acceptance A (Bc s0) r +
          ν r * (-(acceptance A (Bc s0) r) * ∑ k, (A k r : ℝ) * (b k / (1 - Bc s0 k))))) s0 := by
    intro r _
    have hν : HasDerivAt (fun s => ν r + (T s - t0) * μ r) (τ * μ r) s0 := by
      have := ((hT.sub_const t0).mul_const (μ r)).const_add (ν r)
      simpa using this
    have := (hν.mul (hasDerivAt_acceptance A Bc b s0 hB hlt r)).const_mul (A i r : ℝ)
    refine this.congr_deriv ?_
    rw [hT0]; simp only [sub_self, zero_mul, add_zero]
  have h3 := h1.fun_mul (HasDerivAt.fun_sum h2)
  have e : (fun s => reducedLoad A (νt ν μ t0 (T s)) (Bc s) i) =
      fun s => (1 - Bc s i)⁻¹ *
        ∑ r, (A i r : ℝ) * ((ν r + (T s - t0) * μ r) * acceptance A (Bc s) r) := by
    funext s; rfl
  rw [e]
  refine h3.congr_deriv ?_
  simp only [linkLoad, carried, hT0, sub_self, zero_mul, add_zero]
  ring


/-- The derivative of the reduced load along a curve (explicit formula). -/
noncomputable def drho {J R : ℕ} (A : Fin J → Fin R → ℕ) (ν μ : Fin R → ℝ) (τ : ℝ)
    (B b : Fin J → ℝ) (i : Fin J) : ℝ :=
  b i / (1 - B i) ^ 2 * linkLoad A (carried A ν B) i +
    (1 - B i)⁻¹ * ∑ r, (A i r : ℝ) * (τ * μ r * acceptance A B r +
      ν r * (-(acceptance A B r) * ∑ k, (A k r : ℝ) * (b k / (1 - B k))))

lemma νt_self {R : ℕ} (ν μ : Fin R → ℝ) (t0 : ℝ) : νt ν μ t0 t0 = ν := by
  funext r; simp [νt]

lemma hasDerivAt_Fm {J R : ℕ} (A : Fin J → Fin R → ℕ) (ν μ : Fin R → ℝ) (C : Fin J → ℕ)
    (κ : Fin J → ℝ) (t0 : ℝ) (hC : ∀ i, 1 ≤ C i)
    (T : ℝ → ℝ) (τ : ℝ) (Bc : ℝ → Fin J → ℝ) (b : Fin J → ℝ) (s0 : ℝ)
    (hT : HasDerivAt T τ s0) (hT0 : T s0 = t0)
    (hB : ∀ k, HasDerivAt (fun s => Bc s k) (b k) s0)
    (hlt : ∀ k, Bc s0 k < 1) (hρ : ∀ k, 0 < reducedLoad A ν (Bc s0) k) (i : Fin J) :
    HasDerivAt (fun s => Fm A ν μ C κ t0 (T s, Bc s) i)
      (b i - (-(1 - erlang (reducedLoad A ν (Bc s0) i) (C i)) *
          (erlang (reducedLoad A ν (Bc s0) i) (C i) -
            erlang (reducedLoad A ν (Bc s0) i) (C i - 1)) * drho A ν μ τ (Bc s0) b i +
        τ * κ i * (erlang (reducedLoad A ν (Bc s0) i) (C i) -
            erlang (reducedLoad A ν (Bc s0) i) (C i - 1)))) s0 := by
  set ρf : ℝ → ℝ := fun s => reducedLoad A (νt ν μ t0 (T s)) (Bc s) i with hρf
  have hval : ρf s0 = reducedLoad A ν (Bc s0) i := by
    simp only [hρf, hT0, νt_self]
  have hr : HasDerivAt ρf (drho A ν μ τ (Bc s0) b i) s0 :=
    hasDerivAt_rho A ν μ t0 T τ Bc b s0 hT hT0 hB hlt i
  have hE0 := hasDerivAt_erlang (C i) (hC i) (hρ i)
  rw [← hval] at hE0
  have hE := hE0.comp s0 hr
  have hE10 := ((contDiffAt_erlang (C i - 1) (hρ i)).differentiableAt
    (by norm_num)).hasDerivAt
  rw [← hval] at hE10
  have hE1 := hE10.comp s0 hr
  have hlin : HasDerivAt (fun s => (T s - t0) * κ i) (τ * κ i) s0 := by
    simpa using (hT.sub_const t0).mul_const (κ i)
  have hterm := hlin.fun_mul (hE.sub hE1)
  have hall := (hB i).sub (hE.add hterm)
  refine hall.congr_deriv ?_
  simp only [Pi.sub_apply, Function.comp_apply, hval, hT0, sub_self, zero_mul, add_zero]

end KellyStochasticNetworks.ImpliedCosts.ICproof


namespace KellyStochasticNetworks.ImpliedCosts.ICproof

open Finset

lemma sum_quad {J R : ℕ} (A : Fin J → Fin R → ℕ) (lam : Fin R → ℝ) (u : Fin J → ℝ) :
    ∑ i, u i * ∑ r, (A i r : ℝ) * (lam r * ∑ k, (A k r : ℝ) * u k)
      = ∑ r, lam r * (∑ k, (A k r : ℝ) * u k) ^ 2 := by
  set S : Fin R → ℝ := fun r => ∑ k, (A k r : ℝ) * u k with hS
  calc ∑ i, u i * ∑ r, (A i r : ℝ) * (lam r * S r)
      = ∑ i, ∑ r, ((A i r : ℝ) * u i) * (lam r * S r) := by
        apply Finset.sum_congr rfl; intro i _
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro r _; ring
    _ = ∑ r, ∑ i, ((A i r : ℝ) * u i) * (lam r * S r) := Finset.sum_comm
    _ = ∑ r, S r * (lam r * S r) := by
        apply Finset.sum_congr rfl; intro r _
        rw [← Finset.sum_mul]
    _ = ∑ r, lam r * S r ^ 2 := by
        apply Finset.sum_congr rfl; intro r _; ring

lemma inj_alg {J R : ℕ} (A : Fin J → Fin R → ℕ) (lam : Fin R → ℝ) (L δ u : Fin J → ℝ)
    (hlam : ∀ r, 0 ≤ lam r) (hL : ∀ i, 0 < L i) (hδ0 : ∀ i, 0 ≤ δ i) (hδ1 : ∀ i, δ i < 1)
    (h : ∀ i, L i * (1 - δ i) * u i =
      δ i * (-(∑ r, (A i r : ℝ) * (lam r * ∑ k, (A k r : ℝ) * u k)))) : u = 0 := by
  set Z : Fin J → ℝ := fun i => ∑ r, (A i r : ℝ) * (lam r * ∑ k, (A k r : ℝ) * u k) with hZ
  have hz : ∀ i, δ i = 0 → u i = 0 := by
    intro i hi
    have := h i
    rw [hi] at this
    have h0 : L i * u i = 0 := by linarith
    rcases mul_eq_zero.1 h0 with h | h
    · linarith [hL i]
    · exact h
  have hle : ∀ i, u i * Z i ≤ 0 := by
    intro i
    rcases eq_or_lt_of_le (hδ0 i) with hd | hd
    · rw [hz i hd.symm]; simp
    · have e : δ i * (u i * Z i) = -(L i * (1 - δ i) * u i ^ 2) := by
        have := h i
        simp only [hZ] at this ⊢
        linear_combination (u i) * this
      have : δ i * (u i * Z i) ≤ 0 := by
        rw [e]; have := hL i; have := hδ1 i
        have : 0 ≤ L i * (1 - δ i) * u i ^ 2 := by
          apply mul_nonneg (mul_nonneg (le_of_lt (hL i)) (by linarith)) (sq_nonneg _)
        linarith
      exact nonpos_of_mul_nonpos_right (by linarith) hd
  have hsum : ∑ i, u i * Z i = ∑ r, lam r * (∑ k, (A k r : ℝ) * u k) ^ 2 := sum_quad A lam u
  have hge : 0 ≤ ∑ i, u i * Z i := by
    rw [hsum]; exact Finset.sum_nonneg (fun r _ => mul_nonneg (hlam r) (sq_nonneg _))
  have hzero : ∀ i ∈ Finset.univ, u i * Z i = 0 := by
    have := (Finset.sum_eq_zero_iff_of_nonpos (fun i _ => hle i)).1
      (le_antisymm (Finset.sum_nonpos (fun i _ => hle i)) hge)
    exact this
  funext i
  rcases eq_or_lt_of_le (hδ0 i) with hd | hd
  · exact hz i hd.symm
  · have e : δ i * (u i * Z i) = -(L i * (1 - δ i) * u i ^ 2) := by
      have := h i
      simp only [hZ] at this ⊢
      linear_combination (u i) * this
    rw [hzero i (Finset.mem_univ i), mul_zero] at e
    have hpos : 0 < L i * (1 - δ i) := mul_pos (hL i) (by linarith [hδ1 i])
    have : u i ^ 2 = 0 := by
      have : L i * (1 - δ i) * u i ^ 2 = 0 := by linarith
      rcases mul_eq_zero.1 this with h1 | h1
      · linarith
      · exact h1
    simpa using this

lemma ident_alg {J R : ℕ} (A : Fin J → Fin R → ℕ) (a lam μ w s : Fin R → ℝ)
    (L δ u c κ : Fin J → ℝ) (hL : ∀ i, 0 < L i) (hδ1 : ∀ i, δ i < 1)
    (hu : ∀ i, L i * (1 - δ i) * u i =
      δ i * (∑ r, (A i r : ℝ) * (μ r * a r - lam r * ∑ k, (A k r : ℝ) * u k) - κ i))
    (hs : ∀ r, s r = w r - ∑ j, c j * (A j r : ℝ))
    (hc : ∀ j, c j * L j * (1 - δ j) = δ j * ∑ r, (A j r : ℝ) * lam r * s r) :
    ∑ r, w r * (μ r * a r - lam r * ∑ k, (A k r : ℝ) * u k)
      = ∑ r, a r * s r * μ r + ∑ j, c j * κ j := by
  set S : Fin R → ℝ := fun r => ∑ k, (A k r : ℝ) * u k with hS
  set D : Fin R → ℝ := fun r => μ r * a r - lam r * S r with hD
  set Y : Fin J → ℝ := fun i => ∑ r, (A i r : ℝ) * D r with hY
  set X : Fin J → ℝ := fun i => ∑ r, (A i r : ℝ) * lam r * s r with hX
  have hper : ∀ k, u k * X k = c k * (Y k - κ k) := by
    intro k
    have h1 : L k * (1 - δ k) * u k = δ k * (Y k - κ k) := hu k
    have h2 : c k * L k * (1 - δ k) = δ k * X k := hc k
    by_cases hd : δ k = 0
    · have hu0 : u k = 0 := by
        have h0 : L k * u k = 0 := by rw [hd] at h1; linarith
        rcases mul_eq_zero.1 h0 with h | h
        · linarith [hL k]
        · exact h
      have hc0 : c k = 0 := by
        have h0 : c k * L k = 0 := by rw [hd] at h2; linarith
        rcases mul_eq_zero.1 h0 with h | h
        · exact h
        · linarith [hL k]
      rw [hu0, hc0]; ring
    · apply mul_left_cancel₀ hd
      linear_combination (c k) * h1 - (u k) * h2
  have hw : ∀ r, w r = s r + ∑ j, c j * (A j r : ℝ) := by intro r; rw [hs r]; ring
  have e1 : ∑ r, w r * D r = ∑ r, s r * D r + ∑ j, c j * Y j := by
    calc ∑ r, w r * D r = ∑ r, (s r * D r + ∑ j, c j * ((A j r : ℝ) * D r)) := by
          apply Finset.sum_congr rfl; intro r _
          rw [hw r, add_mul, Finset.sum_mul]
          congr 1; apply Finset.sum_congr rfl; intro j _; ring
      _ = ∑ r, s r * D r + ∑ r, ∑ j, c j * ((A j r : ℝ) * D r) := Finset.sum_add_distrib
      _ = ∑ r, s r * D r + ∑ j, c j * Y j := by
          rw [Finset.sum_comm]; congr 1
          apply Finset.sum_congr rfl; intro j _
          rw [Finset.mul_sum]
  have e2 : ∑ r, s r * D r = ∑ r, a r * s r * μ r - ∑ k, u k * X k := by
    have : ∑ k, u k * X k = ∑ r, s r * (lam r * S r) := by
      calc ∑ k, u k * X k = ∑ k, ∑ r, u k * ((A k r : ℝ) * lam r * s r) := by
            apply Finset.sum_congr rfl; intro k _; rw [Finset.mul_sum]
        _ = ∑ r, ∑ k, u k * ((A k r : ℝ) * lam r * s r) := Finset.sum_comm
        _ = ∑ r, s r * (lam r * S r) := by
            apply Finset.sum_congr rfl; intro r _
            simp only [hS, Finset.mul_sum]
            apply Finset.sum_congr rfl; intro k _; ring
    rw [this, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro r _
    simp only [hD]; ring
  show ∑ r, w r * D r = _
  rw [e1, e2, Finset.sum_congr rfl (fun k _ => hper k)]
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

end KellyStochasticNetworks.ImpliedCosts.ICproof


namespace KellyStochasticNetworks.ImpliedCosts.ICproof

open Finset

/-- The explicit directional derivative of the residual map at the base point. -/
noncomputable def dF {J R : ℕ} (A : Fin J → Fin R → ℕ) (ν μ : Fin R → ℝ) (C : Fin J → ℕ)
    (κ : Fin J → ℝ) (B0 : Fin J → ℝ) (τ : ℝ) (b : Fin J → ℝ) (i : Fin J) : ℝ :=
  b i - (-(1 - erlang (reducedLoad A ν B0 i) (C i)) *
          (erlang (reducedLoad A ν B0 i) (C i) -
            erlang (reducedLoad A ν B0 i) (C i - 1)) * drho A ν μ τ B0 b i +
        τ * κ i * (erlang (reducedLoad A ν B0 i) (C i) -
            erlang (reducedLoad A ν B0 i) (C i - 1)))

lemma rho_dF {J R : ℕ} (A : Fin J → Fin R → ℕ) (ν μ : Fin R → ℝ) (C : Fin J → ℕ)
    (κ : Fin J → ℝ) (B0 : Fin J → ℝ) (τ : ℝ) (b : Fin J → ℝ) (i : Fin J)
    (hlt : B0 i < 1) (hfix : B0 i = erlang (reducedLoad A ν B0 i) (C i)) :
    reducedLoad A ν B0 i * dF A ν μ C κ B0 τ b i =
      linkLoad A (carried A ν B0) i * (1 - improvement A ν C B0 i) * (b i / (1 - B0 i)) -
        improvement A ν C B0 i * (∑ r, (A i r : ℝ) * (τ * μ r * acceptance A B0 r -
          carried A ν B0 r * ∑ k, (A k r : ℝ) * (b k / (1 - B0 k))) - τ * κ i) := by
  have hsum : ∑ r, (A i r : ℝ) * (τ * μ r * acceptance A B0 r +
      ν r * (-(acceptance A B0 r) * ∑ k, (A k r : ℝ) * (b k / (1 - B0 k)))) =
      ∑ r, (A i r : ℝ) * (τ * μ r * acceptance A B0 r -
          carried A ν B0 r * ∑ k, (A k r : ℝ) * (b k / (1 - B0 k))) := by
    apply Finset.sum_congr rfl; intro r _; simp only [carried]; ring
  have hne : 1 - B0 i ≠ 0 := by linarith
  have hρ : reducedLoad A ν B0 i = (1 - B0 i)⁻¹ * linkLoad A (carried A ν B0) i := rfl
  simp only [dF, drho, improvement]
  rw [hsum]
  set SS := ∑ r, (A i r : ℝ) * (τ * μ r * acceptance A B0 r -
          carried A ν B0 r * ∑ k, (A k r : ℝ) * (b k / (1 - B0 k)))
  set E1 := erlang (reducedLoad A ν B0 i) (C i - 1)
  rw [← hfix]
  rw [hρ]
  set L := linkLoad A (carried A ν B0) i
  field_simp
  ring

lemma contDiffAt_Fm {J R : ℕ} (A : Fin J → Fin R → ℕ) (ν μ : Fin R → ℝ) (C : Fin J → ℕ)
    (κ : Fin J → ℝ) (t0 : ℝ) (B0 : Fin J → ℝ) (hlt : ∀ i, B0 i < 1)
    (hρ : ∀ i, 0 < reducedLoad A ν B0 i) :
    ContDiffAt ℝ 1 (Fm A ν μ C κ t0) (t0, B0) := by
  rw [contDiffAt_pi]
  intro i
  have hne : 1 - (t0, B0).2 i ≠ 0 := by simp only; linarith [hlt i]
  have hr : ContDiffAt ℝ 1
      (fun p : ℝ × (Fin J → ℝ) => reducedLoad A (νt ν μ t0 p.1) p.2 i) (t0, B0) := by
    simp only [reducedLoad, linkLoad, carried, acceptance, νt]
    refine ContDiffAt.mul ?_ ?_
    · exact ContDiffAt.inv (by fun_prop) hne
    · fun_prop
  have hval : (fun p : ℝ × (Fin J → ℝ) => reducedLoad A (νt ν μ t0 p.1) p.2 i) (t0, B0)
      = reducedLoad A ν B0 i := by simp only [νt_self]
  have hE : ∀ n : ℕ, ContDiffAt ℝ 1
      (fun p : ℝ × (Fin J → ℝ) => erlang (reducedLoad A (νt ν μ t0 p.1) p.2 i) n) (t0, B0) := by
    intro n
    have h := contDiffAt_erlang n (hρ i)
    rw [← hval] at h
    exact h.comp (t0, B0) hr
  simp only [Fm, Gf]
  have h1 := hE (C i)
  have h2 := hE (C i - 1)
  have hp : ContDiffAt ℝ 1 (fun p : ℝ × (Fin J → ℝ) => p.2 i) (t0, B0) := by fun_prop
  have hq : ContDiffAt ℝ 1 (fun p : ℝ × (Fin J → ℝ) => (p.1 - t0) * κ i) (t0, B0) := by fun_prop
  exact hp.sub (h1.add (hq.mul (h1.sub h2)))

end KellyStochasticNetworks.ImpliedCosts.ICproof


namespace KellyStochasticNetworks.ImpliedCosts.ICproof

open Finset Filter
open scoped Topology

lemma fderiv_Fm_apply {J R : ℕ} (A : Fin J → Fin R → ℕ) (ν μ : Fin R → ℝ) (C : Fin J → ℕ)
    (κ : Fin J → ℝ) (t0 : ℝ) (hC : ∀ i, 1 ≤ C i) (B0 : Fin J → ℝ) (hlt : ∀ i, B0 i < 1)
    (hρ : ∀ i, 0 < reducedLoad A ν B0 i)
    (f' : ℝ × (Fin J → ℝ) →L[ℝ] (Fin J → ℝ))
    (hf : HasFDerivAt (Fm A ν μ C κ t0) f' (t0, B0)) (τ : ℝ) (b : Fin J → ℝ) (i : Fin J) :
    f' (τ, b) i = dF A ν μ C κ B0 τ b i := by
  set γ : ℝ → ℝ × (Fin J → ℝ) := fun s => (t0 + s * τ, B0 + s • b) with hγ
  have hγd : HasDerivAt γ (τ, b) 0 := by
    have h1 : HasDerivAt (fun s : ℝ => t0 + s * τ) τ 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const τ).const_add t0
    have h2 : HasDerivAt (fun s : ℝ => B0 + s • b) b 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const b).const_add B0
    exact h1.prodMk h2
  have hc := hf.comp_hasDerivAt_of_eq (0 : ℝ) hγd (by simp [hγ])
  have hci := (hasDerivAt_pi.1 hc) i
  have hB : ∀ k, HasDerivAt (fun s : ℝ => (B0 + s • b) k) (b k) 0 := by
    intro k
    have : HasDerivAt (fun s : ℝ => B0 k + s * b k) (b k) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (b k)).const_add (B0 k)
    simpa using this
  have hT : HasDerivAt (fun s : ℝ => t0 + s * τ) τ 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const τ).const_add t0
  have hlt' : ∀ k, (fun s : ℝ => B0 + s • b) 0 k < 1 := by intro k; simpa using hlt k
  have hρ' : ∀ k, 0 < reducedLoad A ν ((fun s : ℝ => B0 + s • b) 0) k := by
    intro k; simpa using hρ k
  have hm := hasDerivAt_Fm A ν μ C κ t0 hC (fun s => t0 + s * τ) τ (fun s => B0 + s • b) b 0
    hT (by simp) hB hlt' hρ' i
  simp only [zero_smul, add_zero] at hm
  exact hci.unique hm

lemma isInvertible_of_injective {J : ℕ} (g : (Fin J → ℝ) →L[ℝ] (Fin J → ℝ))
    (hg : Function.Injective g) : g.IsInvertible := by
  let e := LinearEquiv.ofInjectiveEndo g.toLinearMap hg
  exact ⟨e.toContinuousLinearEquiv, ContinuousLinearMap.ext fun x => rfl⟩

lemma costSystem_alg {J R : ℕ} (A : Fin J → Fin R → ℕ) (w lam : Fin R → ℝ) (δ : Fin J → ℝ)
    (s : Fin R → ℝ) (c : Fin J → ℝ) (hL : ∀ j, 0 < linkLoad A lam j)
    (h : CostSystem A w lam δ s c) :
    (∀ r, s r = w r - ∑ j, c j * (A j r : ℝ)) ∧
    (∀ j, c j * linkLoad A lam j * (1 - δ j) = δ j * ∑ r, (A j r : ℝ) * lam r * s r) := by
  obtain ⟨hs, hc⟩ := h
  refine ⟨fun r => by rw [hs]; rfl, fun j => ?_⟩
  have h1 := hc j
  have hne : linkLoad A lam j ≠ 0 := (hL j).ne'
  have hsplit : ∑ r, (A j r : ℝ) * lam r * (s r + c j)
      = ∑ r, (A j r : ℝ) * lam r * s r + c j * linkLoad A lam j := by
    simp only [linkLoad, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro r _; ring
  rw [hsplit] at h1
  have h2 : c j * linkLoad A lam j =
      δ j * (∑ r, (A j r : ℝ) * lam r * s r + c j * linkLoad A lam j) := by
    rw [eq_div_iff hne] at h1; exact h1
  linear_combination h2

end KellyStochasticNetworks.ImpliedCosts.ICproof


namespace KellyStochasticNetworks.ImpliedCosts.ICproof

open Finset Filter
open scoped Topology

lemma core {J R : ℕ} (A : Fin J → Fin R → ℕ) (ν μ : Fin R → ℝ) (C : Fin J → ℕ)
    (κ : Fin J → ℝ) (t0 : ℝ) (hC : ∀ i, 1 ≤ C i) (hν : ∀ r, 0 < ν r)
    (B0 : Fin J → ℝ) (hlt : ∀ i, B0 i < 1)
    (hfix : ∀ i, B0 i = erlang (reducedLoad A ν B0 i) (C i))
    (hL : ∀ i, 0 < linkLoad A (carried A ν B0) i)
    (hδ : ∀ i, 0 ≤ improvement A ν C B0 i ∧ improvement A ν C B0 i < 1) :
    ∃ ψ : ℝ → Fin J → ℝ, ψ t0 = B0 ∧ Tendsto ψ (𝓝 t0) (𝓝 B0) ∧
      (∀ᶠ t in 𝓝 t0, ∀ i, ψ t i = Gf C κ t0 t (reducedLoad A (νt ν μ t0 t) (ψ t) i) i) ∧
      ∀ (w s : Fin R → ℝ) (c : Fin J → ℝ),
        CostSystem A w (carried A ν B0) (improvement A ν C B0) s c →
        HasDerivAt (fun t => ∑ r, w r * (νt ν μ t0 t r * acceptance A (ψ t) r))
          (∑ r, acceptance A B0 r * s r * μ r + ∑ j, c j * κ j) t0 := by
  have hρ : ∀ i, 0 < reducedLoad A ν B0 i := by
    intro i
    have : 0 < (1 - B0 i)⁻¹ := inv_pos.2 (by linarith [hlt i])
    exact mul_pos this (hL i)
  set F := Fm A ν μ C κ t0 with hFdef
  have hF0 : F (t0, B0) = 0 := by
    funext i
    simp only [hFdef, Fm, Gf, νt_self, sub_self, zero_mul, add_zero, Pi.zero_apply]
    rw [← hfix i]; ring
  have hcd := contDiffAt_Fm A ν μ C κ t0 B0 hlt hρ
  have hstrict : HasStrictFDerivAt F (fderiv ℝ F (t0, B0)) (t0, B0) :=
    hcd.hasStrictFDerivAt (by norm_num)
  set f' := fderiv ℝ F (t0, B0) with hf'
  have hform : ∀ τ b i, f' (τ, b) i = dF A ν μ C κ B0 τ b i :=
    fun τ b i => fderiv_Fm_apply A ν μ C κ t0 hC B0 hlt hρ f' hstrict.hasFDerivAt τ b i
  -- basic positivity data
  set lam := carried A ν B0 with hlam
  set δ := improvement A ν C B0 with hδdef
  set Lk := fun i => linkLoad A lam i with hLk
  have hlam0 : ∀ r, 0 ≤ lam r := by
    intro r
    simp only [hlam, carried, acceptance]
    exact mul_nonneg (hν r).le
      (Finset.prod_nonneg fun k _ => pow_nonneg (by linarith [hlt k]) _)
  -- the per-link relation
  have hrel : ∀ τ b i, dF A ν μ C κ B0 τ b i = 0 →
      Lk i * (1 - δ i) * (b i / (1 - B0 i)) =
        δ i * (∑ r, (A i r : ℝ) * (τ * μ r * acceptance A B0 r -
          lam r * ∑ k, (A k r : ℝ) * (b k / (1 - B0 k))) - τ * κ i) := by
    intro τ b i h
    have := rho_dF A ν μ C κ B0 τ b i (hlt i) (hfix i)
    rw [h, mul_zero] at this
    simp only [hLk, hδdef, hlam]
    linarith
  -- invertibility of the partial derivative
  have hinj : Function.Injective (f' ∘L ContinuousLinearMap.inr ℝ ℝ (Fin J → ℝ)) := by
    rw [injective_iff_map_eq_zero]
    intro b hb
    have hz : ∀ i, dF A ν μ C κ B0 0 b i = 0 := by
      intro i
      rw [← hform]
      have := congrFun hb i
      simpa using this
    have hu := inj_alg A lam Lk δ (fun k => b k / (1 - B0 k)) hlam0 hL
      (fun i => (hδ i).1) (fun i => (hδ i).2) (by
        intro i
        have := hrel 0 b i (hz i)
        rw [this]
        congr 1
        simp only [zero_mul, zero_sub, sub_zero, Finset.sum_neg_distrib, mul_neg])
    funext k
    have := congrFun hu k
    simp only [Pi.zero_apply] at this ⊢
    have hne : 1 - B0 k ≠ 0 := by linarith [hlt k]
    rcases div_eq_zero_iff.1 this with h | h
    · exact h
    · exact absurd h hne
  have hinv := isInvertible_of_injective _ hinj
  set ψ := hstrict.implicitFunctionOfProdDomain hinv with hψdef
  have hψ0 : ψ t0 = B0 :=
    (hstrict.eventually_apply_eq_iff_implicitFunctionOfProdDomain hinv).self_of_nhds.mp rfl
  have hψt : Tendsto ψ (𝓝 t0) (𝓝 B0) := hstrict.tendsto_implicitFunctionOfProdDomain hinv
  have hψev : ∀ᶠ t in 𝓝 t0, F (t, ψ t) = F (t0, B0) :=
    hstrict.eventually_apply_implicitFunctionOfProdDomain hinv
  have hψd := (hstrict.hasStrictFDerivAt_implicitFunctionOfProdDomain hinv).hasFDerivAt
  rw [hasFDerivAt_iff_hasDerivAt] at hψd
  set v := (-(f' ∘L ContinuousLinearMap.inr ℝ ℝ (Fin J → ℝ)).inverse ∘L
      (f' ∘L ContinuousLinearMap.inl ℝ ℝ (Fin J → ℝ))) 1 with hv
  have hψk : ∀ k, HasDerivAt (fun t => ψ t k) (v k) t0 := fun k => hasDerivAt_pi.1 hψd k
  refine ⟨ψ, hψ0, hψt, ?_, ?_⟩
  · filter_upwards [hψev] with t ht i
    have := congrFun ht i
    rw [hF0] at this
    simp only [hFdef, Fm, Pi.zero_apply] at this
    linarith
  · intro w s c hcs
    have hlt0 : ∀ k, ψ t0 k < 1 := by rw [hψ0]; exact hlt
    have hρ0 : ∀ k, 0 < reducedLoad A ν (ψ t0) k := by rw [hψ0]; exact hρ
    -- derivative of the residual along the implicit branch vanishes
    have hz : ∀ i, dF A ν μ C κ B0 1 v i = 0 := by
      intro i
      have h1 := hasDerivAt_Fm A ν μ C κ t0 hC (fun t => t) 1 ψ v t0 (hasDerivAt_id' t0) rfl
        hψk hlt0 hρ0 i
      rw [hψ0] at h1
      have h2 : HasDerivAt (fun t => Fm A ν μ C κ t0 (t, ψ t) i) 0 t0 := by
        apply (hasDerivAt_const t0 (0 : ℝ)).congr_of_eventuallyEq
        filter_upwards [hψev] with t ht
        have := congrFun ht i
        rw [hF0] at this
        exact this
      exact h1.unique h2
    have hu : ∀ i, Lk i * (1 - δ i) * (v i / (1 - B0 i)) =
        δ i * (∑ r, (A i r : ℝ) * (μ r * acceptance A B0 r -
          lam r * ∑ k, (A k r : ℝ) * (v k / (1 - B0 k))) - κ i) := by
      intro i
      have := hrel 1 v i (hz i)
      simpa only [one_mul] using this
    obtain ⟨hs, hc⟩ := costSystem_alg A w lam δ s c hL hcs
    have hid := ident_alg A (acceptance A B0) lam μ w s Lk δ (fun k => v k / (1 - B0 k)) c κ
      hL (fun i => (hδ i).2) hu hs hc
    -- derivative of the revenue along the branch
    have hr : ∀ r ∈ (Finset.univ : Finset (Fin R)),
        HasDerivAt (fun t => w r * (νt ν μ t0 t r * acceptance A (ψ t) r))
          (w r * (μ r * acceptance A B0 r -
            lam r * ∑ k, (A k r : ℝ) * (v k / (1 - B0 k)))) t0 := by
      intro r _
      have hacc := hasDerivAt_acceptance A ψ v t0 hψk hlt0 r
      rw [hψ0] at hacc
      have hnu : HasDerivAt (fun t => νt ν μ t0 t r) (μ r) t0 := by
        have h0 : HasDerivAt (fun t : ℝ => ν r + (t - t0) * μ r) (1 * μ r) t0 :=
          (((hasDerivAt_id' t0).sub_const t0).mul_const (μ r)).const_add (ν r)
        rw [one_mul] at h0
        exact h0
      have := (hnu.mul hacc).const_mul (w r)
      refine this.congr_deriv ?_
      simp only [νt, sub_self, zero_mul, add_zero, hlam, carried, hψ0]
      ring
    have hW := HasDerivAt.fun_sum hr
    refine hW.congr_deriv ?_
    rw [hid]

end KellyStochasticNetworks.ImpliedCosts.ICproof


namespace KellyStochasticNetworks.ImpliedCosts.ICproof

open Finset Filter
open scoped Topology

lemma ifp_of {J R : ℕ} (A : Fin J → Fin R → ℕ) (ν : Fin R → ℝ) (hν : ∀ r, 0 < ν r)
    (C : Fin J → ℝ) (hC : ∀ j, 0 < C j) (E : Fin J → ℝ) (hlt : ∀ j, E j < 1)
    (h : ∀ j, E j = interpolatedErlang (reducedLoad A ν E j) (C j)) :
    InterpolatedFixedPoint A ν C E := by
  refine ⟨fun j => ⟨?_, hlt j⟩, h⟩
  rw [h j]
  apply (interp_props (C j) (hC j)).1
  apply mul_nonneg (inv_nonneg.2 (by linarith [hlt j]))
  apply Finset.sum_nonneg; intro r _
  apply mul_nonneg (by positivity)
  apply mul_nonneg (hν r).le
  exact Finset.prod_nonneg fun k _ => pow_nonneg (by linarith [hlt k]) _

lemma eventually_lt_one {J : ℕ} (ψ : ℝ → Fin J → ℝ) (t0 : ℝ) (B0 : Fin J → ℝ)
    (hψ : Tendsto ψ (𝓝 t0) (𝓝 B0)) (hlt : ∀ i, B0 i < 1) :
    ∀ᶠ t in 𝓝 t0, ∀ i, ψ t i < 1 := by
  rw [Filter.eventually_all]
  intro i
  exact ((continuous_apply i).tendsto B0 |>.comp hψ).eventually_lt_const (hlt i)

end KellyStochasticNetworks.ImpliedCosts.ICproof

open KellyStochasticNetworks KellyStochasticNetworks.ImpliedCosts
open KellyStochasticNetworks.ImpliedCosts.ICproof
open Finset Filter
open scoped Topology

theorem solution {J R : ℕ} (A : Fin J → Fin R → ℕ)
    (w ν : Fin R → ℝ) (C : Fin J → ℕ)
    (hν : ∀ r, 0 < ν r) (hC : ∀ j, 1 ≤ C j)
    (hused : ∀ j, ∃ r, 0 < A j r) :
    let CReal : Fin J → ℝ := fun j => (C j : ℝ)
    let B := blocking A ν CReal
    let lam := carried A ν B
    let δ := improvement A ν C B
    ErlangFixedPoint A ν C B ∧ (∀ j, B j ∈ Set.Ico (0 : ℝ) 1) ∧
    (∀ j, 0 < linkLoad A lam j) ∧
    ∃ sc : (Fin R → ℝ) × (Fin J → ℝ),
      CostSystem A w lam δ sc.1 sc.2 ∧
      (∀ sc' : (Fin R → ℝ) × (Fin J → ℝ),
        CostSystem A w lam δ sc'.1 sc'.2 → sc' = sc) ∧
      (∀ r, HasDerivAt
        (fun x : ℝ => revenue A w (Function.update ν r x) CReal)
        (acceptance A B r * sc.1 r) (ν r)) ∧
      (∀ j, HasDerivWithinAt
        (fun x : ℝ => revenue A w ν (Function.update CReal j x))
        (sc.2 j) (Set.Iic (CReal j)) (CReal j)) := by
  intro CReal B lam δ
  have hCpos : ∀ j, 0 < CReal j := by
    intro j; show (0 : ℝ) < (C j : ℝ); exact_mod_cast hC j
  -- the base point
  obtain ⟨E, ⟨hEI, hEF⟩, -⟩ := erlang_fixed_point_unique A ν C hν hC
  have hred : ∀ (ν' : Fin R → ℝ) (E' : Fin J → ℝ) j, reducedLoad A ν' E' j =
      (1 - E' j)⁻¹ * ∑ r, (A j r : ℝ) * ν' r * ∏ i, (1 - E' i) ^ (A i r) := by
    intro ν' E' j
    simp only [reducedLoad, linkLoad, carried, acceptance]
    congr 1; apply Finset.sum_congr rfl; intro r _; ring
  have hElt : ∀ j, E j < 1 := by
    intro j
    rw [hEF j]
    apply erlang_lt_one _ (hC j)
    apply mul_nonneg (inv_nonneg.2 (by linarith [(hEI j).2]))
    apply Finset.sum_nonneg; intro r _
    apply mul_nonneg (mul_nonneg (by positivity) (hν r).le)
    exact Finset.prod_nonneg fun k _ => pow_nonneg (by linarith [(hEI k).2]) _
  have hEifp : InterpolatedFixedPoint A ν CReal E := by
    refine ⟨fun j => ⟨(hEI j).1, hElt j⟩, fun j => ?_⟩
    show E j = interpolatedErlang (reducedLoad A ν E j) (C j : ℝ)
    rw [interp_nat, hred]; exact hEF j
  have hBE : B = E := blocking_eq A ν hν CReal hCpos E hEifp
  have hBifp : InterpolatedFixedPoint A ν CReal B := hBE ▸ hEifp
  have hBlt : ∀ j, B j < 1 := fun j => (hBifp.1 j).2
  have hBfix : ∀ i, B i = erlang (reducedLoad A ν B i) (C i) := by
    intro i
    have := hBifp.2 i
    rw [this]; exact interp_nat _ _
  -- matrix characterization
  have hm := matrix_characterization A w ν C hν hC hused
  obtain ⟨h1, -, -, -, h5⟩ := hm
  have hL : ∀ j, 0 < linkLoad A lam j := fun j => (h1 j).1
  have hδ : ∀ j, 0 ≤ δ j ∧ δ j < 1 := fun j => ⟨(h1 j).2.1, (h1 j).2.2⟩
  set cStar := explicitCosts A w lam δ with hcStar
  refine ⟨?_, fun j => hBifp.1 j, hL, (surplus A w cStar, cStar), ?_, ?_, ?_, ?_⟩
  · intro j
    rw [hBE]; exact hEF j
  · exact (h5 _ _).2 ⟨rfl, rfl⟩
  · intro sc' hsc'
    obtain ⟨e1, e2⟩ := (h5 _ _).1 hsc'
    exact Prod.ext e1 e2
  · -- sensitivity to offered traffic
    intro r
    have hcs : CostSystem A w (carried A ν B) (improvement A ν C B) (surplus A w cStar) cStar :=
      (h5 _ _).2 ⟨rfl, rfl⟩
    set μ : Fin R → ℝ := fun r' => if r' = r then 1 else 0 with hμ
    obtain ⟨ψ, hψ0, hψt, hψeq, hψd⟩ := core A ν μ C 0 (ν r) hC hν B hBlt hBfix hL hδ
    have hW := hψd w (surplus A w cStar) cStar hcs
    have hval : ∑ r', acceptance A B r' * surplus A w cStar r' * μ r' +
        ∑ j, cStar j * (0 : Fin J → ℝ) j = acceptance A B r * surplus A w cStar r := by
      simp [hμ]
    rw [hval] at hW
    have hupd : ∀ t, Function.update ν r t = νt ν μ (ν r) t := by
      intro t; funext r'
      by_cases h : r' = r
      · subst h; simp [νt, hμ]
      · simp [νt, hμ, h, Function.update_of_ne h]
    refine hW.congr_of_eventuallyEq ?_
    filter_upwards [hψeq, eventually_lt_one ψ (ν r) B hψt hBlt,
      lt_mem_nhds (hν r)] with t ht hlt1 htpos
    have hνpos : ∀ r', 0 < Function.update ν r t r' := by
      intro r'
      by_cases h : r' = r
      · subst h; simpa using htpos
      · rw [Function.update_of_ne h]; exact hν r'
    have hifp : InterpolatedFixedPoint A (Function.update ν r t) CReal (ψ t) := by
      apply ifp_of A _ hνpos CReal hCpos (ψ t) hlt1
      intro i
      rw [ht i, hupd]
      show _ = interpolatedErlang _ (C i : ℝ)
      rw [interp_nat]
      simp [Gf]
    have hb := blocking_eq A _ hνpos CReal hCpos (ψ t) hifp
    rw [hupd] at hb
    simp only [revenue, carried, hupd, hb]
  · -- sensitivity to capacity
    intro j
    have hcs : CostSystem A w (carried A ν B) (improvement A ν C B) (surplus A w cStar) cStar :=
      (h5 _ _).2 ⟨rfl, rfl⟩
    set κ : Fin J → ℝ := fun i => if i = j then 1 else 0 with hκ
    obtain ⟨ψ, hψ0, hψt, hψeq, hψd⟩ := core A ν 0 C κ (CReal j) hC hν B hBlt hBfix hL hδ
    have hW := hψd w (surplus A w cStar) cStar hcs
    have hval : ∑ r', acceptance A B r' * surplus A w cStar r' * (0 : Fin R → ℝ) r' +
        ∑ i, cStar i * κ i = cStar j := by
      simp [hκ]
    rw [hval] at hW
    have hν0 : ∀ t, νt ν 0 (CReal j) t = ν := by intro t; funext r; simp [νt]
    refine hW.hasDerivWithinAt.congr_of_eventuallyEq ?_ ?_
    · rw [Filter.EventuallyEq, eventually_nhdsWithin_iff]
      have hCj : (1 : ℝ) ≤ CReal j := by show (1 : ℝ) ≤ (C j : ℝ); exact_mod_cast hC j
      filter_upwards [hψeq, eventually_lt_one ψ (CReal j) B hψt hBlt,
        lt_mem_nhds (show CReal j - 1 < CReal j by linarith)] with t ht hlt1 htlo htle
      have htle' : t ≤ CReal j := htle
      have hCpos' : ∀ i, 0 < Function.update CReal j t i := by
        intro i
        by_cases h : i = j
        · subst h; simp only [Function.update_self]; linarith
        · rw [Function.update_of_ne h]; exact hCpos i
      have hifp : InterpolatedFixedPoint A ν (Function.update CReal j t) (ψ t) := by
        apply ifp_of A ν hν _ hCpos' (ψ t) hlt1
        intro i
        rw [ht i, hν0]
        by_cases h : i = j
        · subst h
          simp only [Function.update_self, Gf, hκ, if_pos rfl, mul_one]
          rw [interp_left _ (C i) (hC i) t htlo htle']
        · rw [Function.update_of_ne h]
          show _ = interpolatedErlang _ (C i : ℝ)
          rw [interp_nat]
          simp [Gf, hκ, h]
      have hb := blocking_eq A ν hν _ hCpos' (ψ t) hifp
      simp only [revenue, carried, hb, hν0]
    · simp only [Function.update_eq_self, revenue, carried, hν0, hψ0]
      rfl
