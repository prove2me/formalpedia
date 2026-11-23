-- Prove2me | solution 1 for IntegerRootsFN.Main.lemma_A_1
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T02:47:08.995784+00:00
-- url     : https://prove2.me/submissions/6c2a9542-c423-4b2f-902d-76e619dbb021

import Mathlib
import Definitions.Def_IntegerRootsFN_Main_PolynomialData

set_option autoImplicit false

open scoped BigOperators

private lemma prod_one_sub_coeff_bound (s : Multiset ℂ) (c : ℝ) (hc : 0 ≤ c)
    (hs : ∀ a ∈ s, ‖a‖ ≤ c) (k : ℕ) :
    ‖(s.map (fun a => 1 - Polynomial.C a * Polynomial.X)).prod.coeff k‖
      ≤ (s.card.choose k : ℝ) * c ^ k := by
  induction s using Multiset.induction_on generalizing k with
  | empty =>
      by_cases hk : k = 0
      · subst k
        simp
      · have hchoose : (0 : ℕ).choose k = 0 :=
          Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hk)
        simp [Polynomial.coeff_one, hk, hchoose]
  | cons a s ih =>
      have ha : ‖a‖ ≤ c := hs a (Multiset.mem_cons_self a s)
      have hs' : ∀ b ∈ s, ‖b‖ ≤ c := by
        intro b hb
        exact hs b (Multiset.mem_cons_of_mem hb)
      simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons]
      cases k with
      | zero =>
          simpa [Polynomial.coeff_zero_eq_eval_zero] using ih hs' 0
      | succ k =>
          rw [show (1 - Polynomial.C a * Polynomial.X) *
              (Multiset.map (fun a => 1 - Polynomial.C a * Polynomial.X) s).prod =
              (Multiset.map (fun a => 1 - Polynomial.C a * Polynomial.X) s).prod -
              Polynomial.C a * (Polynomial.X *
                (Multiset.map (fun a => 1 - Polynomial.C a * Polynomial.X) s).prod) by ring]
          simp only [Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_X_mul]
          calc
            ‖((Multiset.map (fun a => 1 - Polynomial.C a * Polynomial.X) s).prod.coeff (k + 1)) -
                a * (Multiset.map (fun a => 1 - Polynomial.C a * Polynomial.X) s).prod.coeff k‖
                ≤ ‖(Multiset.map (fun a => 1 - Polynomial.C a * Polynomial.X) s).prod.coeff (k + 1)‖ +
                    ‖a‖ * ‖(Multiset.map (fun a => 1 - Polynomial.C a * Polynomial.X) s).prod.coeff k‖ := by
                  simpa only [norm_mul] using norm_sub_le
                    ((Multiset.map (fun a => 1 - Polynomial.C a * Polynomial.X) s).prod.coeff (k + 1))
                    (a * (Multiset.map (fun a => 1 - Polynomial.C a * Polynomial.X) s).prod.coeff k)
            _ ≤ (s.card.choose (k + 1) : ℝ) * c ^ (k + 1) + c * ((s.card.choose k : ℝ) * c ^ k) := by
                  exact add_le_add (ih hs' (k + 1))
                    (mul_le_mul ha (ih hs' k) (norm_nonneg _) hc)
            _ = ((s.card + 1).choose (k + 1) : ℝ) * c ^ (k + 1) := by
                  rw [Nat.choose_succ_succ]
                  push_cast
                  ring

private lemma exclusion (d : ℕ) (q : Polynomial ℂ) (hq : q.natDegree = d)
    (h : (∑ k ∈ Finset.range d, ‖q.coeff (k + 1)‖) < ‖q.coeff 0‖) :
    ∀ z : ℂ, ‖z‖ ≤ 1 → ¬q.IsRoot z := by
  intro z hz hroot
  have heval : Polynomial.eval z q = q.coeff 0 +
      ∑ k ∈ Finset.range d, q.coeff (k + 1) * z ^ (k + 1) := by
    rw [Polynomial.eval_eq_sum_range, hq, Finset.sum_range_succ']
    ring
  rw [hroot.eq_zero] at heval
  have htri : ‖∑ k ∈ Finset.range d, q.coeff (k + 1) * z ^ (k + 1)‖ ≤
      ∑ k ∈ Finset.range d, ‖q.coeff (k + 1)‖ := by
    calc
      _ ≤ ∑ k ∈ Finset.range d, ‖q.coeff (k + 1) * z ^ (k + 1)‖ := norm_sum_le _ _
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro k hk
        rw [norm_mul, norm_pow]
        have hp : ‖z‖ ^ (k + 1) ≤ 1 := pow_le_one₀ (norm_nonneg _) hz
        nlinarith [norm_nonneg (q.coeff (k + 1))]
  have hz0 : q.coeff 0 = -∑ k ∈ Finset.range d, q.coeff (k + 1) * z ^ (k + 1) := by
    linear_combination -heval
  rw [hz0, norm_neg] at h
  exact (not_lt_of_ge htri) h

private lemma normalized_factorization (s : Multiset ℂ) (c : ℂ) (q : Polynomial ℂ)
    (hs : ∀ a ∈ s, a ≠ 0)
    (hq : q = Polynomial.C c * (s.map (fun a => Polynomial.X - Polynomial.C a)).prod) :
    q = Polynomial.C (q.coeff 0) *
      (s.map (fun a => 1 - Polynomial.C a⁻¹ * Polynomial.X)).prod := by
  have hfactor : (s.map (fun a => Polynomial.X - Polynomial.C a)).prod =
      Polynomial.C (s.map (fun a => -a)).prod *
        (s.map (fun a => 1 - Polynomial.C a⁻¹ * Polynomial.X)).prod := by
    calc
      (s.map (fun a => Polynomial.X - Polynomial.C a)).prod =
          (s.map (fun a => Polynomial.C (-a) *
            (1 - Polynomial.C a⁻¹ * Polynomial.X))).prod := by
        congr 1
        apply Multiset.map_congr rfl
        intro a ha
        have haa : -a * a⁻¹ = -1 := by
          field_simp [hs a ha]
        calc
          Polynomial.X - Polynomial.C a = Polynomial.C (-a) - Polynomial.C (-1) * Polynomial.X := by
            simp
            ring
          _ = Polynomial.C (-a) - Polynomial.C ((-a) * a⁻¹) * Polynomial.X := by rw [haa]
          _ = Polynomial.C (-a) * (1 - Polynomial.C a⁻¹ * Polynomial.X) := by
            rw [Polynomial.C_mul]
            ring
      _ = (s.map (fun a => Polynomial.C (-a))).prod *
          (s.map (fun a => 1 - Polynomial.C a⁻¹ * Polynomial.X)).prod :=
        Multiset.prod_map_mul
      _ = _ := by
        congr 1
        simpa only [Multiset.map_map, Function.comp_apply] using
          (Multiset.prod_hom (s.map (fun a => -a)) Polynomial.C)
  have hq0 : q.coeff 0 = c * (s.map (fun a => -a)).prod := by
    rw [hq, Polynomial.coeff_C_mul]
    congr 1
    rw [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_multiset_prod]
    simp
  calc
    q = Polynomial.C c * (s.map (fun a => Polynomial.X - Polynomial.C a)).prod := hq
    _ = Polynomial.C c * (Polynomial.C (s.map (fun a => -a)).prod *
        (s.map (fun a => 1 - Polynomial.C a⁻¹ * Polynomial.X)).prod) := by rw [hfactor]
    _ = Polynomial.C (c * (s.map (fun a => -a)).prod) *
        (s.map (fun a => 1 - Polynomial.C a⁻¹ * Polynomial.X)).prod := by
      rw [Polynomial.C_mul]
      ring
    _ = _ := by rw [← hq0]

private lemma binomial_tail_le (d : ℕ) (c : ℝ) :
    ∑ k ∈ Finset.range d, (d.choose (k + 1) : ℝ) * c ^ (k + 1) ≤ (1 + c) ^ d - 1 := by
  have hid : (c + 1) ^ d =
      1 + ∑ k ∈ Finset.range d, (d.choose (k + 1) : ℝ) * c ^ (k + 1) := by
    rw [add_pow, Finset.sum_range_succ']
    simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, one_pow, mul_one]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [show (1 : ℝ) + c = c + 1 by ring, hid]
  linarith

private lemma exponential_bound (d : ℕ) (hd : 1 ≤ d) :
    (1 + 2 / (3 * (d : ℝ))) ^ d < 2 := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hd)
  have hdc : (d : ℝ) * (2 / (3 * (d : ℝ))) = 2 / 3 := by
    field_simp
  have he23 : Real.exp (2 / 3 : ℝ) < 2 := by
    by_contra! hx
    have hp : (2 : ℝ) ^ 3 ≤ Real.exp (2 / 3 : ℝ) ^ 3 :=
      pow_le_pow_left₀ (by norm_num) hx 3
    have hpow3 : Real.exp (2 / 3 : ℝ) ^ 3 = Real.exp 2 := by
      rw [← Real.exp_nat_mul]
      norm_num
    have hpow2 : Real.exp 2 = Real.exp 1 ^ 2 := by
      rw [← Real.exp_nat_mul]
      norm_num
    rw [hpow3, hpow2] at hp
    nlinarith [Real.exp_pos 1, Real.exp_one_lt_d9]
  have hbase : 1 + 2 / (3 * (d : ℝ)) ≤ Real.exp (2 / (3 * (d : ℝ))) := by
    linarith [Real.add_one_le_exp (2 / (3 * (d : ℝ)))]
  calc
    (1 + 2 / (3 * (d : ℝ))) ^ d ≤ Real.exp (2 / (3 * (d : ℝ))) ^ d :=
      pow_le_pow_left₀ (by positivity) hbase d
    _ = Real.exp ((d : ℝ) * (2 / (3 * (d : ℝ)))) := by rw [Real.exp_nat_mul]
    _ < 2 := by rw [hdc]; exact he23

theorem solution (d : ℕ) (hd : 1 ≤ d) (q : Polynomial ℂ) (hq : q.natDegree = d) :
    ((∑ k ∈ Finset.range d, ‖q.coeff (k + 1)‖) < ‖q.coeff 0‖ →
      ∀ z : ℂ, ‖z‖ ≤ 1 → ¬q.IsRoot z) ∧
    (‖q.coeff 0‖ ≤ (∑ k ∈ Finset.range d, ‖q.coeff (k + 1)‖) →
      ∃ z : ℂ, q.IsRoot z ∧ ‖z‖ ≤ (3 : ℝ) / 2 * d) := by
  refine ⟨exclusion d q hq, ?_⟩
  intro hbound
  by_contra! h
  have hqne : q ≠ 0 := by
    intro hq0
    subst q
    simp at hq
    omega
  have hcard : q.roots.card = d :=
    (Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits q)).trans hq
  have hfact : q = Polynomial.C q.leadingCoeff *
      (q.roots.map (fun a => Polynomial.X - Polynomial.C a)).prod :=
    (IsAlgClosed.splits q).eq_prod_roots
  have hroots : ∀ a ∈ q.roots, (3 : ℝ) / 2 * d < ‖a‖ := by
    intro a ha
    exact h a ((Polynomial.mem_roots hqne).mp ha)
  have hnorms : ∀ a ∈ q.roots, ‖a⁻¹‖ ≤ 2 / (3 * (d : ℝ)) := by
    intro a ha
    have hlt := hroots a ha
    have hdpos : (0 : ℝ) < d := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hd)
    have hRpos : (0 : ℝ) < (3 : ℝ) / 2 * d := by positivity
    have hapos : 0 < ‖a‖ := lt_trans hRpos hlt
    calc
      ‖a⁻¹‖ = ‖a‖⁻¹ := norm_inv a
      _ ≤ ((3 : ℝ) / 2 * d)⁻¹ := (inv_le_inv₀ hapos hRpos).mpr (le_of_lt hlt)
      _ = 2 / (3 * (d : ℝ)) := by field_simp
  have hrootne : ∀ a ∈ q.roots, a ≠ 0 := by
    intro a ha ha0
    subst a
    have hlt := hroots 0 ha
    simp only [norm_zero] at hlt
    have hdnonneg : (0 : ℝ) ≤ d := by positivity
    nlinarith
  have hnorm := normalized_factorization q.roots q.leadingCoeff q hrootne hfact
  let P : Polynomial ℂ := q.roots.map (fun a => 1 - Polynomial.C a⁻¹ * Polynomial.X) |>.prod
  have hcoeff (k : ℕ) : q.coeff (k + 1) =
      q.coeff 0 * P.coeff (k + 1) := by
    have hh := congrArg (fun r : Polynomial ℂ => r.coeff (k + 1)) hnorm
    simpa only [Polynomial.coeff_C_mul, P] using hh
  have hPbound (k : ℕ) : ‖P.coeff (k + 1)‖ ≤
      (d.choose (k + 1) : ℝ) * (2 / (3 * (d : ℝ))) ^ (k + 1) := by
    have hh := prod_one_sub_coeff_bound (q.roots.map (fun a => a⁻¹))
      (2 / (3 * (d : ℝ))) (by positivity) (by
        intro b hb
        obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hb
        exact hnorms a ha) (k + 1)
    simpa only [Multiset.map_map, Function.comp_apply, Multiset.card_map, hcard, P] using hh
  have hsumlt : (∑ k ∈ Finset.range d, ‖q.coeff (k + 1)‖) < ‖q.coeff 0‖ := by
    have hsumle : (∑ k ∈ Finset.range d, ‖q.coeff (k + 1)‖) ≤
        ‖q.coeff 0‖ * ∑ k ∈ Finset.range d,
          (d.choose (k + 1) : ℝ) * (2 / (3 * (d : ℝ))) ^ (k + 1) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro k hk
      rw [hcoeff, norm_mul]
      exact mul_le_mul_of_nonneg_left (hPbound k) (norm_nonneg _)
    have htail : (∑ k ∈ Finset.range d,
        (d.choose (k + 1) : ℝ) * (2 / (3 * (d : ℝ))) ^ (k + 1)) < 1 := by
      calc
        _ ≤ (1 + 2 / (3 * (d : ℝ))) ^ d - 1 := binomial_tail_le d _
        _ < 1 := by linarith [exponential_bound d hd]
    have hq0pos : 0 < ‖q.coeff 0‖ := by
      rw [norm_pos_iff]
      intro hq0
      have h0root : q.IsRoot 0 := by
        rw [Polynomial.IsRoot.def, ← Polynomial.coeff_zero_eq_eval_zero, hq0]
      have hh := h 0 h0root
      simp only [norm_zero] at hh
      have hdpos : (0 : ℝ) ≤ d := by positivity
      nlinarith
    calc
      _ ≤ ‖q.coeff 0‖ * ∑ k ∈ Finset.range d,
          (d.choose (k + 1) : ℝ) * (2 / (3 * (d : ℝ))) ^ (k + 1) := hsumle
      _ < ‖q.coeff 0‖ * 1 := (mul_lt_mul_of_pos_left htail hq0pos)
      _ = ‖q.coeff 0‖ := mul_one _
  exact (not_lt_of_ge hbound) hsumlt
