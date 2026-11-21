-- Prove2me | solution 1 for MultiStageAlloc.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T03:12:01.541489+00:00
-- url     : https://prove2.me/submissions/7ee3f4b0-abfd-4ee2-9bcd-e5b292978923

import Mathlib
import Definitions.Def_MultiStageAlloc_Regularizers

open Filter Topology

namespace Aux_MultiStageAlloc_proposition_1

open MultiStageAlloc

lemma tangent (b c : ℝ) (hb : 0 < b) (hc : 0 ≤ c) (n : ℕ) :
    b ^ (n + 1) + (n + 1) * b ^ n * (c - b) ≤ c ^ (n + 1) := by
  have hcb : (c - b) / b = c / b - 1 := by rw [sub_div, div_self hb.ne']
  have hge : -2 ≤ (c - b) / b := by
    have : 0 ≤ c / b := div_nonneg hc hb.le
    rw [hcb]; linarith
  have h := one_add_mul_le_pow hge (n + 1)
  have h1 : 1 + (c - b) / b = c / b := by rw [hcb]; ring
  rw [h1, div_pow] at h
  have hbn : 0 < b ^ (n + 1) := pow_pos hb _
  rw [le_div_iff₀ hbn] at h
  have hbb : (c - b) / b * b = c - b := div_mul_cancel₀ _ hb.ne'
  have heq : (1 + ((n + 1 : ℕ) : ℝ) * ((c - b) / b)) * b ^ (n + 1) =
      b ^ (n + 1) + (n + 1) * b ^ n * (c - b) := by
    push_cast
    calc (1 + ((n:ℝ) + 1) * ((c - b) / b)) * b ^ (n + 1)
        = b ^ (n + 1) + ((n:ℝ) + 1) * ((c - b) / b * b) * b ^ n := by ring
      _ = b ^ (n + 1) + (n + 1) * b ^ n * (c - b) := by rw [hbb]; ring
  linarith

lemma amgm (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (m : ℕ) :
    a * b ^ m ≤ ((a + m * b) / (m + 1)) ^ (m + 1) := by
  have hm1 : (0:ℝ) < m + 1 := by positivity
  obtain ⟨c, hc⟩ : ∃ c, c = (a + m * b) / (m + 1) := ⟨_, rfl⟩
  rw [← hc]
  have hc0 : 0 ≤ c := by rw [hc]; exact div_nonneg (by positivity) hm1.le
  have hcm : c * (m + 1) = a + m * b := by rw [hc]; exact div_mul_cancel₀ _ hm1.ne'
  rcases eq_or_lt_of_le hb with hb0 | hbpos
  · rw [← hb0]
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      rw [← hb0] at hcm
      simp only [pow_zero, mul_one, zero_add, pow_one]
      push_cast at hcm
      linarith
    · rw [zero_pow (by omega), mul_zero]
      exact pow_nonneg hc0 _
  · have ht := tangent b c hbpos hc0 m
    have hac : a = (m + 1) * c - m * b := by linarith
    rw [hac]
    have : ((m + 1) * c - m * b) * b ^ m = b ^ (m + 1) + (m + 1) * b ^ m * (c - b) := by ring
    linarith

lemma key_max (K j : ℕ) (hjK : j ≤ K) (x : ℝ) (hx : x ∈ Set.Icc (0:ℝ) 1) :
    IsGreatest ((fun y => (1 - y) * regPoly K j (x + y)) '' Set.Icc 0 (1 - x))
      ((1 - (1 - x) / (((K - j : ℕ) : ℝ) + 1)) ^ (K - j + 1)) := by
  obtain ⟨hx0, hx1⟩ := hx
  rcases Nat.lt_or_ge j K with hj | hj
  · obtain ⟨m, hm⟩ : ∃ m, m = K - j := ⟨_, rfl⟩
    rw [← hm]
    have hm1 : 1 ≤ m := by omega
    have hmR : (1:ℝ) ≤ m := by exact_mod_cast hm1
    have hm0 : (m:ℝ) ≠ 0 := by positivity
    have hreg : ∀ z, regPoly K j z = (1 - (1 - z) / (m:ℝ)) ^ m := fun z => by
      unfold regPoly; rw [if_pos hj, hm]
    have hm1R : (0:ℝ) < (m:ℝ) + 1 := by positivity
    constructor
    · refine ⟨(1 - x) / ((m:ℝ) + 1), ⟨div_nonneg (by linarith) hm1R.le,
        div_le_self (by linarith) (by linarith)⟩, ?_⟩
      show (1 - (1 - x) / ((m:ℝ) + 1)) * regPoly K j (x + (1 - x) / ((m:ℝ) + 1)) = _
      rw [hreg]
      have h1 : 1 - (x + (1 - x) / ((m:ℝ) + 1)) = (1 - x) / ((m:ℝ) + 1) * m := by
        first | (field_simp; ring1) | field_simp
      rw [h1, mul_div_cancel_right₀ _ hm0, pow_succ]
      ring
    · rintro _ ⟨y, ⟨hy0, hy1⟩, rfl⟩
      show (1 - y) * regPoly K j (x + y) ≤ _
      rw [hreg]
      have hA : 0 ≤ 1 - y := by linarith
      have hB : 0 ≤ 1 - (1 - (x + y)) / m := by
        have : (1 - (x + y)) / m ≤ 1 := by
          rw [div_le_one (by positivity)]; linarith
        linarith
      have := amgm (1 - y) (1 - (1 - (x + y)) / m) hA hB m
      have heq : ((1 - y) + m * (1 - (1 - (x + y)) / m)) / (m + 1) =
          1 - (1 - x) / ((m:ℝ) + 1) := by
        first | (field_simp; ring1) | field_simp
      rw [heq] at this
      exact this
  · have hreg : ∀ z, regPoly K j z = if z = 1 then 1 else 0 := fun z => by
      unfold regPoly; rw [if_neg (show ¬ j < K by omega)]
    have hm : K - j = 0 := by omega
    have hv : (1 - (1 - x) / (((0 : ℕ) : ℝ) + 1)) ^ (0 + 1) = x := by simp
    rw [hm, hv]
    constructor
    · refine ⟨1 - x, ⟨by linarith, le_refl _⟩, ?_⟩
      show (1 - (1 - x)) * regPoly K j (x + (1 - x)) = x
      rw [hreg, if_pos (show x + (1 - x) = 1 by ring)]
      ring
    · rintro _ ⟨y, ⟨hy0, hy1⟩, rfl⟩
      show (1 - y) * regPoly K j (x + y) ≤ x
      rw [hreg]
      split_ifs with h
      · linarith
      · linarith

end Aux_MultiStageAlloc_proposition_1

open MultiStageAlloc Aux_MultiStageAlloc_proposition_1 in
theorem solution (K : ℕ) (hK : 1 ≤ K) :
    (∀ x ∈ Set.Icc (0 : ℝ) 1, regPoly K K x = if x = 1 then 1 else 0) ∧
    (∀ k, 1 ≤ k → k < K → ∀ x ∈ Set.Icc (0 : ℝ) 1,
      IsGreatest ((fun y => (1 - y) * regPoly K (k + 1) (x + y)) '' Set.Icc 0 (1 - x))
        (regPoly K k x)) ∧
    (∀ k, 1 ≤ k → k ≤ K → ∀ x ∈ Set.Icc (0 : ℝ) 1, regPoly K k x ∈ Set.Icc (0 : ℝ) 1) ∧
    (∀ f : ℕ → ℝ → ℝ,
      (∀ x ∈ Set.Icc (0 : ℝ) 1, f K x = if x = 1 then 1 else 0) →
      (∀ k, 1 ≤ k → k < K → ∀ x ∈ Set.Icc (0 : ℝ) 1,
        IsGreatest ((fun y => (1 - y) * f (k + 1) (x + y)) '' Set.Icc 0 (1 - x)) (f k x)) →
      ∀ k, 1 ≤ k → k ≤ K → ∀ x ∈ Set.Icc (0 : ℝ) 1, f k x = regPoly K k x) ∧
    (∀ k, 1 ≤ k → k < K →
      (∀ x, regPoly K k x = (1 - (1 - x) / ((K - k : ℕ) : ℝ)) ^ (K - k)) ∧
      ∃ p : Polynomial ℝ, p.natDegree = K - k ∧ ∀ x, p.eval x = regPoly K k x) ∧
    (∀ k, 1 ≤ k → k < K →
      StrictMonoOn (regPoly K k) (Set.Icc 0 1) ∧ ContinuousOn (regPoly K k) (Set.Icc 0 1) ∧
      DifferentiableOn ℝ (regF K k) (Set.Icc 0 1) ∧
      StrictConvexOn ℝ (Set.Icc 0 1) (regF K k)) ∧
    (∀ k, 1 ≤ k → k ≤ K → ∀ x ∈ Set.Icc (0 : ℝ) 1, regPoly K k x ≤ Real.exp (x - 1)) ∧
    (∀ x ∈ Set.Icc (0 : ℝ) 1,
      Tendsto (fun K' : ℕ => regPoly K' 1 x) atTop (𝓝 (Real.exp (x - 1)))) ∧
    (∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ K' : ℕ, 2 ≤ K' → regPoly K' 1 x ≤ regPoly (K' + 1) 1 x) ∧
    IsLeast ((fun y => 1 - (1 - y) * regPoly K 1 y) '' Set.Icc 0 1) (gammaK K) := by
  have P1 : ∀ x ∈ Set.Icc (0 : ℝ) 1, regPoly K K x = if x = 1 then 1 else 0 := by
    intro x _
    unfold regPoly
    rw [if_neg (lt_irrefl K)]
  have P2 : ∀ k, 1 ≤ k → k < K → ∀ x ∈ Set.Icc (0 : ℝ) 1,
      IsGreatest ((fun y => (1 - y) * regPoly K (k + 1) (x + y)) '' Set.Icc 0 (1 - x))
        (regPoly K k x) := by
    intro k _ hkK x hx
    have h := key_max K (k + 1) hkK x hx
    have hv : regPoly K k x = (1 - (1 - x) / (((K - (k + 1) : ℕ) : ℝ) + 1)) ^ (K - (k + 1) + 1) := by
      unfold regPoly
      rw [if_pos hkK]
      have : K - k = K - (k + 1) + 1 := by omega
      rw [this, Nat.cast_add, Nat.cast_one]
    rw [hv]
    exact h
  -- formula for k < K
  have hform : ∀ k, k < K → ∀ x, regPoly K k x = (1 - (1 - x) / ((K - k : ℕ) : ℝ)) ^ (K - k) := by
    intro k hkK x
    unfold regPoly
    rw [if_pos hkK]
  refine ⟨P1, P2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- P3
    intro k _ hkK x hx
    obtain ⟨hx0, hx1⟩ := hx
    rcases Nat.lt_or_ge k K with h | h
    · rw [hform k h]
      have hn : (1:ℝ) ≤ ((K - k : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ K - k)
      have hd0 : 0 ≤ (1 - x) / ((K - k : ℕ) : ℝ) := div_nonneg (by linarith) (by linarith)
      have hd1 : (1 - x) / ((K - k : ℕ) : ℝ) ≤ 1 := by
        rw [div_le_one (by linarith)]; linarith
      exact ⟨pow_nonneg (by linarith) _, pow_le_one₀ (by linarith) (by linarith)⟩
    · have hk : k = K := le_antisymm hkK h
      subst hk
      rw [P1 x ⟨hx0, hx1⟩]
      split_ifs
      · exact ⟨zero_le_one, le_refl _⟩
      · exact ⟨le_refl _, zero_le_one⟩
  · -- P4 uniqueness
    intro f hfK hfrec
    have main : ∀ d, ∀ k, K - k = d → 1 ≤ k → k ≤ K → ∀ x ∈ Set.Icc (0 : ℝ) 1,
        f k x = regPoly K k x := by
      intro d
      induction d with
      | zero =>
        intro k hd _ hkK x hx
        have hk : k = K := by omega
        subst hk
        rw [hfK x hx, P1 x hx]
      | succ d ih =>
        intro k hd hk1 hkK x hx
        have hkK' : k < K := by omega
        have h1 := hfrec k hk1 hkK' x hx
        have h2 := P2 k hk1 hkK' x hx
        have himg : ((fun y => (1 - y) * f (k + 1) (x + y)) '' Set.Icc 0 (1 - x)) =
            ((fun y => (1 - y) * regPoly K (k + 1) (x + y)) '' Set.Icc 0 (1 - x)) := by
          apply Set.image_congr
          intro y hy
          have hxy : x + y ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith [hx.1, hy.1], by linarith [hy.2]⟩
          rw [ih (k + 1) (by omega) (by omega) (by omega) (x + y) hxy]
        rw [himg] at h1
        exact h1.unique h2
    intro k hk1 hkK x hx
    exact main (K - k) k rfl hk1 hkK x hx
  · -- P5
    intro k _ hkK
    refine ⟨hform k hkK, ?_⟩
    have hn : (1:ℝ) ≤ ((K - k : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ K - k)
    have hn0 : (1 / ((K - k : ℕ) : ℝ)) ≠ 0 := by
      apply div_ne_zero one_ne_zero; linarith
    refine ⟨(Polynomial.C (1 / ((K - k : ℕ) : ℝ)) * Polynomial.X +
      Polynomial.C (1 - 1 / ((K - k : ℕ) : ℝ))) ^ (K - k), ?_, ?_⟩
    · rw [Polynomial.natDegree_pow, Polynomial.natDegree_linear hn0, mul_one]
    · intro x
      rw [hform k hkK x, Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_C]
      congr 1
      ring
  · -- P6
    intro k _ hkK
    have hn : (1:ℝ) ≤ ((K - k : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ K - k)
    have hfun : regPoly K k = fun x => (1 - (1 - x) / ((K - k : ℕ) : ℝ)) ^ (K - k) :=
      funext (hform k hkK)
    have hcont : Continuous (regPoly K k) := by rw [hfun]; fun_prop
    have hsm : StrictMonoOn (regPoly K k) (Set.Icc 0 1) := by
      intro a ha b hb hab
      rw [hfun]
      show (1 - (1 - a) / ((K - k : ℕ) : ℝ)) ^ (K - k) < (1 - (1 - b) / ((K - k : ℕ) : ℝ)) ^ (K - k)
      have hlt : (1 - b) / ((K - k : ℕ) : ℝ) < (1 - a) / ((K - k : ℕ) : ℝ) :=
        div_lt_div_of_pos_right (by linarith) (by linarith)
      have hd1 : (1 - a) / ((K - k : ℕ) : ℝ) ≤ 1 := by
        rw [div_le_one (by linarith)]; linarith [ha.1]
      exact pow_lt_pow_left₀ (by linarith) (by linarith) (by omega)
    have hd : ∀ x, HasDerivAt (regF K k) (regPoly K k x) x := fun x =>
      (hcont.integral_hasStrictDerivAt 0 x).hasDerivAt
    have hderiv : deriv (regF K k) = regPoly K k := funext fun x => (hd x).deriv
    refine ⟨hsm, hcont.continuousOn, fun x _ => (hd x).differentiableAt.differentiableWithinAt, ?_⟩
    apply StrictMonoOn.strictConvexOn_of_deriv (convex_Icc 0 1)
      (fun x _ => (hd x).continuousAt.continuousWithinAt)
    rw [hderiv]
    exact hsm.mono interior_subset
  · -- P7
    intro k _ hkK x hx
    rcases Nat.lt_or_ge k K with h | h
    · rw [hform k h]
      have hn : (1:ℝ) ≤ ((K - k : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ K - k)
      have hd1 : (1 - x) / ((K - k : ℕ) : ℝ) ≤ 1 := by
        rw [div_le_one (by linarith)]; linarith [hx.1]
      have hb := Real.add_one_le_exp (-((1 - x) / ((K - k : ℕ) : ℝ)))
      have hpow := pow_le_pow_left₀ (by linarith) hb (K - k)
      rw [← Real.exp_nat_mul] at hpow
      have hmul : ((K - k : ℕ) : ℝ) * -((1 - x) / ((K - k : ℕ) : ℝ)) = x - 1 := by
        rw [mul_neg, mul_div_cancel₀ _ (by linarith : ((K - k : ℕ) : ℝ) ≠ 0)]
        ring
      rw [hmul] at hpow
      have : 1 - (1 - x) / ((K - k : ℕ) : ℝ) = -((1 - x) / ((K - k : ℕ) : ℝ)) + 1 := by ring
      rw [this]
      exact hpow
    · have hk : k = K := le_antisymm hkK h
      subst hk
      rw [P1 x hx]
      split_ifs with h1
      · rw [h1, sub_self, Real.exp_zero]
      · exact (Real.exp_pos _).le
  · -- P8
    intro x _
    refine (tendsto_add_atTop_iff_nat 1).mp ?_
    have h := Real.tendsto_one_add_div_pow_exp (x - 1)
    apply h.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    show (1 + (x - 1) / (n:ℝ)) ^ n = regPoly (n + 1) 1 x
    unfold regPoly
    rw [if_pos (show 1 < n + 1 by omega)]
    have : n + 1 - 1 = n := by omega
    rw [this]
    congr 1
    ring
  · -- P9
    intro x hx K' hK'
    obtain ⟨N, rfl⟩ : ∃ N, K' = N + 1 := ⟨K' - 1, by omega⟩
    have hN : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast (by omega : 1 ≤ N)
    have e1 : regPoly (N + 1) 1 x = (1 - (1 - x) / (N:ℝ)) ^ N := by
      unfold regPoly
      rw [if_pos (show 1 < N + 1 by omega)]
      have : N + 1 - 1 = N := by omega
      rw [this]
    have e2 : regPoly (N + 1 + 1) 1 x = (1 - (1 - x) / ((N:ℝ) + 1)) ^ (N + 1) := by
      unfold regPoly
      rw [if_pos (show 1 < N + 1 + 1 by omega)]
      have : N + 1 + 1 - 1 = N + 1 := by omega
      rw [this, Nat.cast_add, Nat.cast_one]
    rw [e1, e2]
    have hB : 0 ≤ 1 - (1 - x) / (N:ℝ) := by
      have : (1 - x) / (N:ℝ) ≤ 1 := by
        rw [div_le_one (by linarith)]; linarith [hx.1]
      linarith
    have := amgm 1 (1 - (1 - x) / (N:ℝ)) zero_le_one hB N
    have heq : (1 + (N:ℝ) * (1 - (1 - x) / (N:ℝ))) / ((N:ℝ) + 1) = 1 - (1 - x) / ((N:ℝ) + 1) := by
      have hN0 : (N:ℝ) ≠ 0 := by linarith
      first | (field_simp; ring1) | field_simp
    rw [heq, one_mul] at this
    exact this
  · -- P10
    have h := key_max K 1 hK 0 ⟨le_refl _, zero_le_one⟩
    have hK1 : K - 1 + 1 = K := by omega
    have hc : ((K - 1 : ℕ) : ℝ) + 1 = (K:ℝ) := by exact_mod_cast hK1
    rw [hc, hK1, sub_zero] at h
    obtain ⟨⟨y0, hy0, hval⟩, hub⟩ := h
    constructor
    · refine ⟨y0, by simpa using hy0, ?_⟩
      show 1 - (1 - y0) * regPoly K 1 y0 = gammaK K
      have hval' : (1 - y0) * regPoly K 1 (0 + y0) = (1 - 1 / (K:ℝ)) ^ K := hval
      rw [zero_add] at hval'
      unfold gammaK
      rw [hval']
    · rintro _ ⟨y, hy, rfl⟩
      have := hub ⟨y, by simpa using hy, rfl⟩
      have this' : (1 - y) * regPoly K 1 (0 + y) ≤ (1 - 1 / (K:ℝ)) ^ K := this
      rw [zero_add] at this'
      show gammaK K ≤ 1 - (1 - y) * regPoly K 1 y
      unfold gammaK
      linarith
