-- Prove2me | solution 1 for MultiSecretary.BR.sufficient_condition
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-20T01:13:39.26276+00:00
-- url     : https://prove2.me/submissions/3924a4da-e40c-47f4-a32b-a31a59aed098

import Mathlib
import Definitions.Def_MultiSecretary_BR_Model

set_option autoImplicit false

namespace MultiSecretary.BR

open Finset

variable {m : ℕ} (I : Instance m)

theorem ps_E_add {n : ℕ} (g h : (Fin n → Fin m) → ℝ) :
    I.E (fun x => g x + h x) = I.E g + I.E h := by
  unfold Instance.E; rw [← Finset.sum_add_distrib]; congr 1; ext x; ring

theorem ps_E_sub {n : ℕ} (g h : (Fin n → Fin m) → ℝ) :
    I.E (fun x => g x - h x) = I.E g - I.E h := by
  unfold Instance.E; rw [← Finset.sum_sub_distrib]; congr 1; ext x; ring

theorem ps_E_cmul {n : ℕ} (c : ℝ) (g : (Fin n → Fin m) → ℝ) :
    I.E (fun x => c * g x) = c * I.E g := by
  unfold Instance.E; rw [Finset.mul_sum]; congr 1; ext x; ring

theorem ps_E_sum {n : ℕ} {ι : Type} (s : Finset ι) (g : ι → (Fin n → Fin m) → ℝ) :
    I.E (fun x => ∑ i ∈ s, g i x) = ∑ i ∈ s, I.E (g i) := by
  unfold Instance.E; simp_rw [Finset.mul_sum]; exact Finset.sum_comm

theorem ps_weight_nonneg {n : ℕ} (x : Fin n → Fin m) : 0 ≤ I.weight x := by
  unfold Instance.weight; exact Finset.prod_nonneg (fun t _ => (I.f_pos _).le)

theorem ps_E_mono {n : ℕ} (g h : (Fin n → Fin m) → ℝ) (hgh : ∀ x, g x ≤ h x) :
    I.E g ≤ I.E h := by
  unfold Instance.E
  exact Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hgh x) (ps_weight_nonneg I x))

theorem ps_E_prod {n : ℕ} (G : Fin n → Fin m → ℝ) :
    I.E (fun x => ∏ s, G s (x s)) = ∏ s, ∑ j, I.f j * G s j := by
  unfold Instance.E Instance.weight
  rw [Fintype.prod_sum]
  congr 1; ext x; rw [← Finset.prod_mul_distrib]

theorem ps_E_const {n : ℕ} (c : ℝ) : I.E (fun _ : Fin n → Fin m => c) = c := by
  have h := ps_E_prod I (n := n) (fun _ _ => 1)
  simp only [Finset.prod_const_one, mul_one, I.f_sum] at h
  have h2 := ps_E_cmul I (n := n) c (fun _ => 1)
  simp only [mul_one] at h2
  rw [h2, h]; ring

theorem ps_E_one {n : ℕ} (t : Fin n) (g : Fin m → ℝ) :
    I.E (fun x => g (x t)) = ∑ j, I.f j * g j := by
  have h := ps_E_prod I (fun s j => if s = t then g j else 1)
  have e1 : (fun x : Fin n → Fin m => ∏ s, (if s = t then g (x s) else 1)) = fun x => g (x t) := by
    ext x; rw [Fintype.prod_ite_eq']
  rw [e1] at h
  rw [h]
  have e2 : ∀ s : Fin n, ∑ j, I.f j * (if s = t then g j else 1) =
      if s = t then ∑ j, I.f j * g j else 1 := by
    intro s; by_cases hs : s = t <;> simp [hs, I.f_sum]
  simp_rw [e2]; rw [Fintype.prod_ite_eq']

theorem ps_E_two {n : ℕ} (t t' : Fin n) (htt : t ≠ t') (g h : Fin m → ℝ) :
    I.E (fun x => g (x t) * h (x t')) = (∑ j, I.f j * g j) * (∑ j, I.f j * h j) := by
  have H := ps_E_prod I (fun s j => (if s = t then g j else 1) * (if s = t' then h j else 1))
  have e1 : (fun x : Fin n → Fin m =>
      ∏ s, ((if s = t then g (x s) else 1) * (if s = t' then h (x s) else 1))) =
      fun x => g (x t) * h (x t') := by
    ext x; rw [Finset.prod_mul_distrib, Fintype.prod_ite_eq', Fintype.prod_ite_eq']
  rw [e1] at H
  rw [H]
  have e2 : ∀ s : Fin n, ∑ j, I.f j * ((if s = t then g j else 1) * (if s = t' then h j else 1)) =
      (if s = t then ∑ j, I.f j * g j else 1) * (if s = t' then ∑ j, I.f j * h j else 1) := by
    intro s
    by_cases hs : s = t
    · subst hs; simp [htt]
    · by_cases hs' : s = t'
      · subst hs'; simp [hs]
      · simp [hs, hs', I.f_sum]
  simp_rw [e2]; rw [Finset.prod_mul_distrib, Fintype.prod_ite_eq', Fintype.prod_ite_eq']

theorem ps_cast_tsub (k b : ℕ) : ((k - b : ℕ) : ℝ) = max ((k : ℝ) - b) 0 := by
  rcases le_total b k with h | h
  · rw [Nat.cast_sub h, max_eq_left (by linarith [(Nat.cast_le (α := ℝ)).2 h])]
  · rw [Nat.sub_eq_zero_of_le h, max_eq_right (by linarith [(Nat.cast_le (α := ℝ)).2 h])]; simp

theorem ps_sum_lt (n r : ℕ) (hr : r ≤ n) :
    ∑ t : Fin n, (if t.val < r then (1 : ℝ) else 0) = r := by
  rw [Fin.sum_univ_eq_sum_range (fun i => if i < r then (1 : ℝ) else 0), ← Finset.sum_filter]
  have : (range n).filter (· < r) = range r := by
    ext i; simp only [mem_filter, mem_range]; omega
  rw [this]; simp

theorem ps_key (α β a1 ZA Z0 Z1 cA c0 v k : ℝ) (hβ : 0 ≤ β) (hαβ : β ≤ α) (ha1 : β ≤ a1)
    (hcA : cA ≤ ZA) (hc0 : c0 ≤ Z0) (hv : 0 ≤ v) (hs : cA + c0 + v ≤ k) (hZ1 : 0 ≤ Z1) :
    α * (cA - ZA) + α * c0 + β * v ≤
      α * min Z0 (max (k - ZA) 0) + β * min Z1 (max (k - ZA - Z0) 0) +
        a1 * max (k - ZA - Z0 - Z1) 0 := by
  have hα : 0 ≤ α := le_trans hβ hαβ
  have ha10 : 0 ≤ a1 := le_trans hβ ha1
  set u := cA + c0 - ZA with hu_def
  set m0 := min Z0 (max (k - ZA) 0) with hm0
  set w := max (k - ZA - Z0) 0 with hw
  have hu : u ≤ m0 := le_min (by linarith) (le_max_of_le_left (by linarith))
  have s2 : α * u + β * v ≤ α * m0 + β * max (u + v - m0) 0 := by
    rcases le_total (u + v - m0) 0 with h | h
    · rw [max_eq_right h]
      nlinarith [mul_le_mul_of_nonneg_left (show u + v ≤ m0 by linarith) hα,
        mul_le_mul_of_nonneg_right hαβ hv]
    · rw [max_eq_left h]
      nlinarith [mul_le_mul_of_nonneg_left hu (sub_nonneg.2 hαβ)]
  have s3 : max (u + v - m0) 0 ≤ w := by
    have hk : k - ZA - m0 ≤ w := by
      rcases le_total Z0 (max (k - ZA) 0) with h | h
      · rw [hm0, min_eq_left h]; exact le_max_left _ _
      · rw [hm0, min_eq_right h]
        have := le_max_left (k - ZA) 0
        linarith [le_max_right (k - ZA - Z0) 0]
    exact max_le (by linarith) (le_max_right _ _)
  have s4 : β * w ≤ β * min Z1 w + a1 * max (k - ZA - Z0 - Z1) 0 := by
    have hw0 : 0 ≤ w := le_max_right _ _
    have hmx : 0 ≤ max (k - ZA - Z0 - Z1) 0 := le_max_right _ _
    rcases le_total Z1 w with h | h
    · rw [min_eq_left h]
      have h2 : w - Z1 ≤ max (k - ZA - Z0 - Z1) 0 := by
        rcases le_total (k - ZA - Z0) 0 with h3 | h3
        · rw [hw, max_eq_right h3]; linarith
        · rw [hw, max_eq_left h3]; exact le_max_left _ _
      nlinarith [mul_le_mul_of_nonneg_right ha1 (sub_nonneg.2 h),
        mul_le_mul_of_nonneg_left h2 ha10]
    · rw [min_eq_right h]; nlinarith [mul_nonneg ha10 hmx]
  have e : α * (cA - ZA) + α * c0 + β * v = α * u + β * v := by rw [hu_def]; ring
  rw [e]
  nlinarith [mul_le_mul_of_nonneg_left s3 hβ]

theorem ps_minmono (a a' b b' k : ℝ) (ha : a ≤ a') (hb : b ≤ b') :
    min a' (max (k - b') 0) ≤ min a (max (k - b) 0) + (a' - a) := by
  have h1 : max (k - b') 0 ≤ max (k - b) 0 := max_le_max (by linarith) le_rfl
  rcases le_total a (max (k - b) 0) with h | h
  · rw [min_eq_left h]; linarith [min_le_left a' (max (k - b') 0)]
  · rw [min_eq_right h]; linarith [min_le_right a' (max (k - b') 0)]

theorem ps_fiber {n : ℕ} (P : Fin n → Prop) [DecidablePred P] (S : Finset (Fin m))
    (b : Fin m → ℝ) (x : Fin n → Fin m) :
    ∑ j ∈ S, b j * ∑ t, (if P t ∧ x t = j then (1 : ℝ) else 0) =
      ∑ t, if P t ∧ x t ∈ S then b (x t) else 0 := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  by_cases hP : P t
  · simp [hP]
  · simp [hP]

theorem ps_Z_cast {n : ℕ} (r : ℕ) (j : Fin m) (x : Fin n → Fin m) :
    (Z r j x : ℝ) = ∑ t, if t.val < r ∧ x t = j then (1 : ℝ) else 0 := by
  unfold Z; rw [Finset.natCast_card_filter]

theorem ps_on_cast {n : ℕ} (σ : (Fin n → Fin m) → Fin n → Bool) (r : ℕ) (j : Fin m)
    (x : Fin n → Fin m) :
    (onCount σ r j x : ℝ) =
      ∑ t, if (t.val < r ∧ σ x t = true) ∧ x t = j then (1 : ℝ) else 0 := by
  unfold onCount; rw [Finset.natCast_card_filter]; simp only [and_assoc]

theorem ps_off_cast {n : ℕ} (k r : ℕ) (j : Fin m) (x : Fin n → Fin m) :
    (offCount k r j x : ℝ) =
      min (Z r j x : ℝ) (max ((k : ℝ) - ∑ i ∈ univ.filter (fun i => i < j), (Z r i x : ℝ)) 0) := by
  unfold offCount; rw [Nat.cast_min, ps_cast_tsub, Nat.cast_sum]

theorem ps_binom_bound {n : ℕ} (L : Finset (Fin m)) (k e : ℝ) (he : 0 < e) (hn : 0 < n)
    (hc : (n : ℝ) * e ≤ n * (∑ j ∈ L, I.f j) - k) :
    I.E (fun x : Fin n → Fin m => max (k - ∑ t, (if x t ∈ L then (1 : ℝ) else 0)) 0)
      ≤ 1 / (4 * e) := by
  set p := ∑ j ∈ L, I.f j with hp
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hp0 : 0 ≤ p := Finset.sum_nonneg (fun j _ => (I.f_pos j).le)
  have hp1 : p ≤ 1 := by
    rw [hp, ← I.f_sum]
    exact Finset.sum_le_sum_of_subset_of_nonneg (subset_univ L) (fun j _ _ => (I.f_pos j).le)
  set c := (n : ℝ) * p - k with hc_def
  have hc0 : 0 < c := by nlinarith [mul_pos hnr he]
  set g : Fin m → ℝ := fun j => p - if j ∈ L then 1 else 0 with hg
  have hmean : ∑ j, I.f j * g j = 0 := by
    simp only [hg, mul_sub, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib, ← Finset.sum_mul,
      I.f_sum, Finset.sum_ite_mem, Finset.univ_inter]
    ring
  have hgg : ∀ j, g j * g j ≤ 1 := by
    intro j; simp only [hg]; split_ifs <;> nlinarith
  have hsq : ∑ j, I.f j * (g j * g j) ≤ 1 := by
    calc ∑ j, I.f j * (g j * g j) ≤ ∑ j, I.f j * 1 :=
          Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hgg j) (I.f_pos j).le)
      _ = 1 := by simp [I.f_sum]
  -- pointwise
  have hpt : ∀ x : Fin n → Fin m,
      max (k - ∑ t, (if x t ∈ L then (1 : ℝ) else 0)) 0 ≤
        (1 / (4 * c)) * ((∑ t, g (x t)) * (∑ t, g (x t))) := by
    intro x
    have hY : ∑ t, g (x t) = (n : ℝ) * p - ∑ t, (if x t ∈ L then (1 : ℝ) else 0) := by
      simp only [hg, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
    set Y := ∑ t, g (x t)
    have hkW : k - ∑ t, (if x t ∈ L then (1 : ℝ) else 0) = Y - c := by rw [hY, hc_def]; ring
    rw [hkW]
    have h4c : 0 < 4 * c := by linarith
    rcases le_total (Y - c) 0 with h | h
    · rw [max_eq_right h]
      exact mul_nonneg (div_nonneg zero_le_one h4c.le) (mul_self_nonneg Y)
    · rw [max_eq_left h, one_div_mul_eq_div, le_div_iff₀ h4c]
      nlinarith [sq_nonneg (Y - 2 * c)]
  have hEY : I.E (fun x : Fin n → Fin m => (∑ t, g (x t)) * (∑ t, g (x t))) ≤ n := by
    have e1 : (fun x : Fin n → Fin m => (∑ t, g (x t)) * (∑ t, g (x t))) =
        fun x => ∑ t, ∑ t', g (x t) * g (x t') := by
      ext x; rw [Finset.sum_mul_sum]
    rw [e1, ps_E_sum]
    simp_rw [ps_E_sum]
    calc ∑ t : Fin n, ∑ t' : Fin n, I.E (fun x => g (x t) * g (x t'))
        ≤ ∑ t : Fin n, ∑ t' : Fin n, (if t = t' then (1 : ℝ) else 0) := by
          refine Finset.sum_le_sum (fun t _ => Finset.sum_le_sum (fun t' _ => ?_))
          by_cases htt : t = t'
          · subst htt
            rw [if_pos rfl, ps_E_one I t (fun j => g j * g j)]; exact hsq
          · rw [if_neg htt, ps_E_two I t t' htt g g, hmean]; simp
      _ = n := by simp
  calc I.E (fun x : Fin n → Fin m => max (k - ∑ t, (if x t ∈ L then (1 : ℝ) else 0)) 0)
      ≤ I.E (fun x : Fin n → Fin m => (1 / (4 * c)) * ((∑ t, g (x t)) * (∑ t, g (x t)))) :=
        ps_E_mono I _ _ hpt
    _ = (1 / (4 * c)) * I.E (fun x : Fin n → Fin m => (∑ t, g (x t)) * (∑ t, g (x t))) :=
        ps_E_cmul I _ _
    _ ≤ (1 / (4 * c)) * n := mul_le_mul_of_nonneg_left hEY (div_nonneg zero_le_one (by linarith))
    _ ≤ 1 / (4 * e) := by
        rw [one_div_mul_eq_div, div_le_div_iff₀ (by linarith) (by linarith)]
        nlinarith

theorem ps_ZS {n : ℕ} (r : ℕ) (S : Finset (Fin m)) (b : Fin m → ℝ) (x : Fin n → Fin m) :
    ∑ j ∈ S, b j * (Z r j x : ℝ) = ∑ t, if t.val < r ∧ x t ∈ S then b (x t) else 0 := by
  simp_rw [ps_Z_cast]; exact ps_fiber (fun t : Fin n => t.val < r) S b x

theorem ps_OS {n : ℕ} (σ : (Fin n → Fin m) → Fin n → Bool) (r : ℕ) (S : Finset (Fin m))
    (b : Fin m → ℝ) (x : Fin n → Fin m) :
    ∑ j ∈ S, b j * (onCount σ r j x : ℝ) =
      ∑ t, if (t.val < r ∧ σ x t = true) ∧ x t ∈ S then b (x t) else 0 := by
  simp_rw [ps_on_cast]; exact ps_fiber (fun t : Fin n => t.val < r ∧ σ x t = true) S b x

end MultiSecretary.BR

open MultiSecretary.BR Finset in
theorem solution {m : ℕ} (I : Instance m) (n k : ℕ) (hk : k ≤ n)
    (σ : (Fin n → Fin m) → Fin n → Bool) (hσ : σ ∈ policies n m k)
    (τ : (Fin n → Fin m) → ℕ) (hτn : ∀ x, τ x ≤ n)
    (hτ : ∀ x y : Fin n → Fin m, (∀ s : Fin n, s.val < τ x → x s = y s) → τ y = τ x)
    (M : ℝ)
    (h1 : ∑ j ∈ univ.filter (fun j => j < I.actionIndex n k),
            I.E (fun x => (onCount σ (τ x) j x : ℝ)) =
          ∑ j ∈ univ.filter (fun j => j < I.actionIndex n k),
            I.E (fun x => (Z (τ x) j x : ℝ)))
    (h2 : I.E (fun x => (offCount k (τ x) (I.actionIndex n k) x : ℝ)) - M ≤
          I.E (fun x => (onCount σ (τ x) (I.actionIndex n k) x : ℝ)))
    (h3 : ∀ h : (I.actionIndex n k).val + 1 < m,
          I.E (fun x => (offCount k (τ x) ⟨(I.actionIndex n k).val + 1, h⟩ x : ℝ)) - M ≤
          I.E (fun x => (onCount σ (τ x) ⟨(I.actionIndex n k).val + 1, h⟩ x : ℝ)))
    (h4 : (n : ℝ) - M ≤ I.E (fun x => (τ x : ℝ))) :
    I.Voff n k - I.value σ ≤ 3 * I.a I.top * M + I.a I.top / (4 * I.eps) := by
  set j0 := I.actionIndex n k with hj0
  set A := univ.filter (fun j : Fin m => j < j0) with hA
  have htop : ∀ j : Fin m, I.top ≤ j := fun j => Fin.le_iff_val_le_val.2 (Nat.zero_le _)
  have ha1 : ∀ j, I.a j ≤ I.a I.top := fun j => I.a_anti.antitone (htop j)
  have hEτ : I.E (fun x => (τ x : ℝ)) ≤ n := by
    calc I.E (fun x => (τ x : ℝ)) ≤ I.E (fun _ => (n : ℝ)) :=
          ps_E_mono I _ _ (fun x => by exact_mod_cast hτn x)
      _ = n := ps_E_const I _
  have hM : 0 ≤ M := by linarith
  have hεpos : 0 < I.eps := by
    have : 0 < univ.inf' ⟨I.top, mem_univ _⟩ I.f := (Finset.lt_inf'_iff _).2 (fun j _ => I.f_pos j)
    unfold Instance.eps; linarith
  have hq0 : 0 ≤ 1 / (4 * I.eps) := div_nonneg zero_le_one (by linarith)
  have hSZ : ∀ (r : ℕ) (j : Fin m) (x : Fin n → Fin m), (onCount σ r j x : ℝ) ≤ Z r j x := by
    intro r j x
    unfold onCount Z
    exact_mod_cast card_le_card (fun t ht => by
      simp only [mem_filter, mem_univ, true_and] at ht ⊢; exact ⟨ht.1, ht.2.2⟩)
  have hEq : ∀ j ∈ A, I.E (fun x => (onCount σ (τ x) j x : ℝ)) = I.E (fun x => (Z (τ x) j x : ℝ)) :=
    (Finset.sum_eq_sum_iff_of_le (fun j _ => ps_E_mono I _ _ (fun x => hSZ _ _ _))).1 h1
  have hj0A : j0 ∉ A := by simp [hA]
  have hZle : ∀ x j, (Z (τ x) j x : ℝ) ≤ Z n j x := by
    intro x j; rw [ps_Z_cast, ps_Z_cast]; apply sum_le_sum; intro t _
    by_cases h : t.val < τ x ∧ x t = j
    · rw [if_pos h, if_pos ⟨t.isLt, h.2⟩]
    · rw [if_neg h]; split_ifs <;> norm_num
  obtain ⟨j1, β, hβ0, hβ1, hj1A, hj10, hβU, h3', hO1, hR⟩ : ∃ (j1 : Fin m) (β : ℝ),
      0 ≤ β ∧ β ≤ I.a j1 ∧ ¬ j1 < j0 ∧ (j1 = j0 → β = 0) ∧ (∀ j, j0 < j → I.a j ≤ β) ∧
      β * (I.E (fun x => (offCount k (τ x) j1 x : ℝ)) -
        I.E (fun x => (onCount σ (τ x) j1 x : ℝ))) ≤ β * M ∧
      (∀ x, β * min (Z n j1 x : ℝ) (max ((k : ℝ) - ∑ j ∈ A, (Z n j x : ℝ) - (Z n j0 x : ℝ)) 0) ≤
          β * ((offCount k (τ x) j1 x : ℝ) + ((Z n j1 x : ℝ) - (Z (τ x) j1 x : ℝ)))) ∧
      I.E (fun x => max ((k : ℝ) - ∑ j ∈ A, (Z n j x : ℝ) - (Z n j0 x : ℝ) - (Z n j1 x : ℝ)) 0)
        ≤ 1 / (4 * I.eps) := by
    by_cases hlast : j0.val + 1 < m
    · set j1 : Fin m := ⟨j0.val + 1, hlast⟩ with hj1
      have hj1v : j1.val = j0.val + 1 := rfl
      have hfil : univ.filter (fun i : Fin m => i < j1) = insert j0 A := by
        ext i
        simp only [mem_filter, mem_univ, true_and, mem_insert, hA, Fin.lt_def, Fin.ext_iff]
        omega
      have hj1n : j1 ∉ insert j0 A := by
        simp only [mem_insert, hA, mem_filter, mem_univ, true_and, Fin.ext_iff, Fin.lt_def]
        omega
      refine ⟨j1, I.a j1, (I.a_pos j1).le, le_rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [Fin.lt_def]; omega
      · intro h; have := congrArg Fin.val h; omega
      · intro j hj
        exact I.a_anti.antitone (Fin.le_def.2 (by rw [Fin.lt_def] at hj; omega))
      · have := h3 hlast
        exact mul_le_mul_of_nonneg_left (by linarith) (I.a_pos j1).le
      · intro x
        apply mul_le_mul_of_nonneg_left _ (I.a_pos j1).le
        rw [ps_off_cast, hfil, sum_insert hj0A]
        have hmm := ps_minmono (Z (τ x) j1 x) (Z n j1 x)
          ((Z (τ x) j0 x : ℝ) + ∑ j ∈ A, (Z (τ x) j x : ℝ)) ((Z n j0 x : ℝ) + ∑ j ∈ A, (Z n j x : ℝ))
          k (hZle x j1) (add_le_add (hZle x j0) (sum_le_sum fun j _ => hZle x j))
        have e : (k : ℝ) - ∑ j ∈ A, (Z n j x : ℝ) - Z n j0 x =
            k - ((Z n j0 x : ℝ) + ∑ j ∈ A, (Z n j x : ℝ)) := by ring
        rw [e]; linarith
      · rcases Nat.eq_zero_or_pos n with hn | hn
        · have hk0 : k = 0 := by omega
          have hpt : ∀ x : Fin n → Fin m,
              max ((k : ℝ) - ∑ j ∈ A, (Z n j x : ℝ) - (Z n j0 x : ℝ) - (Z n j1 x : ℝ)) 0 ≤ 0 := by
            intro x
            apply max_le _ le_rfl
            have := sum_nonneg (fun j (_ : j ∈ A) => (Nat.cast_nonneg (Z n j x) : (0 : ℝ) ≤ _))
            rw [hk0]; push_cast
            linarith [(Nat.cast_nonneg (Z n j0 x) : (0 : ℝ) ≤ _),
              (Nat.cast_nonneg (Z n j1 x) : (0 : ℝ) ≤ _)]
          calc _ ≤ I.E (fun _ : Fin n → Fin m => (0 : ℝ)) := ps_E_mono I _ _ hpt
            _ = 0 := ps_E_const I _
            _ ≤ 1 / (4 * I.eps) := hq0
        · have hW : ∀ x : Fin n → Fin m,
              (k : ℝ) - ∑ j ∈ A, (Z n j x : ℝ) - Z n j0 x - Z n j1 x =
                k - ∑ t, (if x t ∈ insert j1 (insert j0 A) then (1 : ℝ) else 0) := by
            intro x
            have h := ps_ZS n (insert j1 (insert j0 A)) (fun _ => (1 : ℝ)) x
            simp only [one_mul] at h
            rw [sum_insert hj1n, sum_insert hj0A] at h
            simp only [Fin.is_lt, true_and] at h
            linarith
          simp_rw [hW]
          apply ps_binom_bound I _ _ _ hεpos hn
          rw [sum_insert hj1n, sum_insert hj0A]
          have hnot : ¬ (I.survival j1 + I.f j1 / 2 ≤ (k : ℝ) / n) := by
            intro hle
            have hmem : j1 ∈ univ.filter
                (fun j : Fin m => I.survival j + I.f j / 2 ≤ (k : ℝ) / n) :=
              mem_filter.2 ⟨mem_univ _, hle⟩
            have hne : (univ.filter
                (fun j : Fin m => I.survival j + I.f j / 2 ≤ (k : ℝ) / n)).Nonempty := ⟨j1, hmem⟩
            have hle' : j1 ≤ j0 := by
              rw [hj0]; unfold Instance.actionIndex; rw [dif_pos hne]; exact le_max' _ _ hmem
            rw [Fin.le_def] at hle'; omega
          have hsurv : I.survival j1 = I.f j0 + ∑ j ∈ A, I.f j := by
            unfold Instance.survival; rw [hfil, sum_insert hj0A]
          have hnr : (0 : ℝ) < n := by exact_mod_cast hn
          have hlt2 : (k : ℝ) < (I.survival j1 + I.f j1 / 2) * n := by
            have := not_le.1 hnot; rwa [div_lt_iff₀ hnr] at this
          have heps : I.eps ≤ I.f j1 / 2 := by
            unfold Instance.eps
            have := Finset.inf'_le I.f (mem_univ j1)
            linarith
          rw [hsurv] at hlt2
          nlinarith [mul_le_mul_of_nonneg_left heps hnr.le]
    · have hall : ∀ j : Fin m, j ≤ j0 := fun j => Fin.le_def.2 (by have := j.isLt; omega)
      refine ⟨j0, 0, le_rfl, (I.a_pos j0).le, lt_irrefl _, fun _ => rfl, ?_, by simp,
        fun x => by simp, ?_⟩
      · intro j hj; exact absurd hj (not_lt.2 (hall j))
      · have hpt : ∀ x : Fin n → Fin m,
            max ((k : ℝ) - ∑ j ∈ A, (Z n j x : ℝ) - (Z n j0 x : ℝ) - (Z n j0 x : ℝ)) 0 ≤ 0 := by
          intro x
          apply max_le _ le_rfl
          have h := ps_ZS n (insert j0 A) (fun _ => (1 : ℝ)) x
          simp only [one_mul] at h
          rw [sum_insert hj0A] at h
          have hin : ∀ t : Fin n, x t ∈ insert j0 A := fun t => by
            rcases (hall (x t)).lt_or_eq with h' | h'
            · exact mem_insert_of_mem (by simp [hA, h'])
            · rw [h']; exact mem_insert_self _ _
          simp only [Fin.is_lt, true_and, hin, if_true, sum_const, card_univ, Fintype.card_fin,
            nsmul_eq_mul, mul_one] at h
          have : (k : ℝ) ≤ n := by exact_mod_cast hk
          linarith [(Nat.cast_nonneg (Z n j0 x) : (0 : ℝ) ≤ _)]
        calc _ ≤ I.E (fun _ : Fin n → Fin m => (0 : ℝ)) := ps_E_mono I _ _ hpt
          _ = 0 := ps_E_const I _
          _ ≤ 1 / (4 * I.eps) := hq0
  -- generic part
  have hα0 : 0 ≤ I.a j0 := (I.a_pos j0).le
  have hβα : β ≤ I.a j0 := hβ1.trans (I.a_anti.antitone (not_lt.1 hj1A))
  have hβa1 : β ≤ I.a I.top := hβ1.trans (ha1 j1)
  have hpw : ∀ x : Fin n → Fin m,
      (univ.filter (fun s : Fin n → Bool => (univ.filter (fun t => s t = true)).card ≤ k)).sup'
          ⟨fun _ => false, by simp⟩ (fun s => ∑ t, if s t = true then I.a (x t) else 0)
        - (∑ t, if σ x t = true then I.a (x t) else 0) ≤
      (∑ j ∈ A, I.a j * ((Z (τ x) j x : ℝ) - onCount σ (τ x) j x))
        + I.a j0 * ((offCount k (τ x) j0 x : ℝ) - onCount σ (τ x) j0 x)
        + β * ((offCount k (τ x) j1 x : ℝ) - onCount σ (τ x) j1 x)
        + I.a I.top * ((n : ℝ) - τ x)
        + I.a I.top * max ((k : ℝ) - ∑ j ∈ A, (Z n j x : ℝ) - (Z n j0 x : ℝ) - (Z n j1 x : ℝ)) 0 := by
    intro x
    have F1 : (univ.filter (fun s : Fin n → Bool => (univ.filter (fun t => s t = true)).card ≤ k)).sup'
          ⟨fun _ => false, by simp⟩ (fun s => ∑ t, if s t = true then I.a (x t) else 0) ≤
        ∑ j ∈ A, I.a j * (Z n j x : ℝ)
          + I.a j0 * min (Z n j0 x : ℝ) (max ((k : ℝ) - ∑ j ∈ A, (Z n j x : ℝ)) 0)
          + β * min (Z n j1 x : ℝ) (max ((k : ℝ) - ∑ j ∈ A, (Z n j x : ℝ) - Z n j0 x) 0)
          + I.a I.top * max ((k : ℝ) - ∑ j ∈ A, (Z n j x : ℝ) - Z n j0 x - Z n j1 x) 0 := by
      apply Finset.sup'_le
      intro s hs
      have hcard : (∑ t, if s t = true then (1 : ℝ) else 0) ≤ k := by
        rw [← Finset.natCast_card_filter]; exact_mod_cast (mem_filter.1 hs).2
      have eWA := ps_ZS n A I.a x
      have eZA := ps_ZS n A (fun _ => (1 : ℝ)) x
      have eZ0 := ps_Z_cast n j0 x
      simp only [one_mul] at eZA
      have hpt : ∀ t : Fin n, (if s t = true then I.a (x t) else 0) ≤
          (if t.val < n ∧ x t ∈ A then I.a (x t) else 0)
            - I.a j0 * (if t.val < n ∧ x t ∈ A then (1 : ℝ) else 0)
            + I.a j0 * (if s t = true ∧ x t ∈ A then (1 : ℝ) else 0)
            + I.a j0 * (if s t = true ∧ x t = j0 then (1 : ℝ) else 0)
            + β * (if s t = true ∧ j0 < x t then (1 : ℝ) else 0) := by
        intro t
        have ht := t.isLt
        rcases lt_trichotomy (x t) j0 with h | h | h
        · have hm : x t ∈ A := by simp [hA, h]
          have hne : x t ≠ j0 := h.ne
          have hng : ¬ j0 < x t := not_lt.2 h.le
          have hαa : I.a j0 ≤ I.a (x t) := I.a_anti.antitone h.le
          by_cases hs : s t = true <;> simp [hs, hm, hne, hng, ht] <;> linarith
        · have hm : x t ∉ A := by simp [hA, h]
          by_cases hs : s t = true <;> simp [hs, hm, h, ht, hj0A]
        · have hm : x t ∉ A := by simp [hA, not_lt.2 h.le]
          have hne : x t ≠ j0 := h.ne'
          have hβx : I.a (x t) ≤ β := hβU _ h
          by_cases hs : s t = true <;> simp [hs, hm, hne, h, ht] <;> linarith
      have hsum := Finset.sum_le_sum (fun t (_ : t ∈ univ) => hpt t)
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum
      rw [← eWA, ← eZA] at hsum
      have hcA : (∑ t, if s t = true ∧ x t ∈ A then (1 : ℝ) else 0) ≤ ∑ j ∈ A, (Z n j x : ℝ) := by
        rw [eZA]; apply sum_le_sum; intro t _
        by_cases h : s t = true ∧ x t ∈ A
        · rw [if_pos h, if_pos ⟨t.isLt, h.2⟩]
        · rw [if_neg h]; split_ifs <;> norm_num
      have hc0 : (∑ t, if s t = true ∧ x t = j0 then (1 : ℝ) else 0) ≤ Z n j0 x := by
        rw [eZ0]; apply sum_le_sum; intro t _
        by_cases h : s t = true ∧ x t = j0
        · rw [if_pos h, if_pos ⟨t.isLt, h.2⟩]
        · rw [if_neg h]; split_ifs <;> norm_num
      have hv : 0 ≤ ∑ t, if s t = true ∧ j0 < x t then (1 : ℝ) else 0 :=
        sum_nonneg (fun t _ => by split_ifs <;> norm_num)
      have hs3 : (∑ t, if s t = true ∧ x t ∈ A then (1 : ℝ) else 0)
          + (∑ t, if s t = true ∧ x t = j0 then (1 : ℝ) else 0)
          + (∑ t, if s t = true ∧ j0 < x t then (1 : ℝ) else 0) ≤ k := by
        rw [← sum_add_distrib, ← sum_add_distrib]
        refine le_trans (sum_le_sum (fun t _ => ?_)) hcard
        rcases lt_trichotomy (x t) j0 with h | h | h
        · by_cases hs : s t = true <;> simp [hs, hA, h, h.ne, not_lt.2 h.le]
        · by_cases hs : s t = true <;> simp [hs, hA, h]
        · by_cases hs : s t = true <;> simp [hs, hA, h.ne', not_lt.2 h.le, h]
      have hK := ps_key (I.a j0) β (I.a I.top) (∑ j ∈ A, (Z n j x : ℝ)) (Z n j0 x) (Z n j1 x) _ _ _ k
        hβ0 hβα hβa1 hcA hc0 hv hs3 (Nat.cast_nonneg _)
      linarith
    have F2 : ∑ j ∈ A, I.a j * (onCount σ (τ x) j x : ℝ) + I.a j0 * onCount σ (τ x) j0 x
        + β * onCount σ (τ x) j1 x ≤ ∑ t, if σ x t = true then I.a (x t) else 0 := by
      have e1 := ps_OS σ (τ x) A I.a x
      have e2 := ps_OS σ (τ x) {j0} (fun _ => I.a j0) x
      have e3 := ps_OS σ (τ x) {j1} (fun _ => β) x
      rw [sum_singleton] at e2 e3
      beta_reduce at e2 e3
      rw [e1, e2, e3, ← sum_add_distrib, ← sum_add_distrib]
      apply sum_le_sum; intro t _
      by_cases hq : t.val < τ x ∧ σ x t = true
      · have hσt := hq.2
        simp only [hq, true_and, hσt, if_true, mem_singleton]
        rcases lt_trichotomy (x t) j0 with h | h | h
        · have hm : x t ∈ A := by simp [hA, h]
          have hne : x t ≠ j0 := h.ne
          have hne1 : x t ≠ j1 := fun e => hj1A (e ▸ h)
          simp [hm, hne, hne1]
        · have hm : x t ∉ A := by simp [hA, h]
          by_cases e : x t = j1
          · have hb : β = 0 := hj10 (e.symm.trans h)
            simp [hm, h, hb, hj0A]
          · have hne1 : j0 ≠ j1 := fun e' => e (h.trans e')
            simp [hm, h, e, hj0A, hne1]
        · have hm : x t ∉ A := by simp [hA, not_lt.2 h.le]
          have hne : x t ≠ j0 := h.ne'
          by_cases e : x t = j1
          · have hj1A' : j1 ∉ A := by simp [hA, hj1A]
            have hj1ne : j1 ≠ j0 := fun e' => hne (e.trans e')
            simp [hm, hne, e, hβ1, hj1A', hj1ne]
          · simp [hm, hne, e]; exact (I.a_pos _).le
      · simp only [hq, false_and, if_false]
        split_ifs <;> linarith [I.a_pos (x t)]
    have F3 : (∑ j ∈ A, I.a j * (Z n j x : ℝ)) - (∑ j ∈ A, I.a j * (Z (τ x) j x : ℝ))
        + I.a j0 * ((Z n j0 x : ℝ) - Z (τ x) j0 x) + β * ((Z n j1 x : ℝ) - Z (τ x) j1 x)
        ≤ I.a I.top * ((n : ℝ) - τ x) := by
      have e1 := ps_ZS n A I.a x
      have e2 := ps_ZS (τ x) A I.a x
      have e3 := ps_ZS n {j0} (fun _ => I.a j0) x
      have e4 := ps_ZS (τ x) {j0} (fun _ => I.a j0) x
      have e5 := ps_ZS n {j1} (fun _ => β) x
      have e6 := ps_ZS (τ x) {j1} (fun _ => β) x
      rw [sum_singleton] at e3 e4 e5 e6
      beta_reduce at e3 e4 e5 e6
      have en := ps_sum_lt n n le_rfl
      have eτ := ps_sum_lt n (τ x) (hτn x)
      conv_rhs => rw [← en, ← eτ, ← sum_sub_distrib, Finset.mul_sum]
      conv_lhs => rw [mul_sub, mul_sub, e1, e2, e3, e4, e5, e6, ← sum_sub_distrib,
        ← sum_sub_distrib, ← sum_sub_distrib, ← sum_add_distrib, ← sum_add_distrib]
      apply sum_le_sum; intro t _
      have ht := t.isLt
      by_cases hτt : t.val < τ x
      · simp [hτt, ht]
      · simp only [hτt, ht, true_and, false_and, if_true, if_false, sub_zero, mul_one,
          mem_singleton]
        rcases lt_trichotomy (x t) j0 with h | h | h
        · have hm : x t ∈ A := by simp [hA, h]
          have hne : x t ≠ j0 := h.ne
          have hne1 : x t ≠ j1 := fun e => hj1A (e ▸ h)
          simp [hm, hne, hne1, ha1]
        · have hm : x t ∉ A := by simp [hA, h]
          by_cases e : x t = j1
          · have hb : β = 0 := hj10 (e.symm.trans h)
            simp [hm, h, hb, ha1, hj0A]
          · have hne1 : j0 ≠ j1 := fun e' => e (h.trans e')
            simp [hm, h, e, ha1, hj0A, hne1]
        · have hm : x t ∉ A := by simp [hA, not_lt.2 h.le]
          have hne : x t ≠ j0 := h.ne'
          by_cases e : x t = j1
          · have hj1A' : j1 ∉ A := by simp [hA, hj1A]
            have hj1ne : j1 ≠ j0 := fun e' => hne (e.trans e')
            simp [hm, hne, e, hβa1, hj1A', hj1ne]
          · simp [hm, hne, e] <;> linarith [I.a_pos I.top]
    have hmn0 : min (Z n j0 x : ℝ) (max ((k : ℝ) - ∑ j ∈ A, (Z n j x : ℝ)) 0) ≤
        (offCount k (τ x) j0 x : ℝ) + ((Z n j0 x : ℝ) - Z (τ x) j0 x) := by
      rw [ps_off_cast]
      exact ps_minmono _ _ _ _ _ (hZle x j0) (sum_le_sum fun j _ => hZle x j)
    have hO := hO1 x
    have hmul := mul_le_mul_of_nonneg_left hmn0 hα0
    have hsplit : ∑ j ∈ A, I.a j * ((Z (τ x) j x : ℝ) - onCount σ (τ x) j x) =
        ∑ j ∈ A, I.a j * (Z (τ x) j x : ℝ) - ∑ j ∈ A, I.a j * (onCount σ (τ x) j x : ℝ) := by
      rw [← sum_sub_distrib]; exact sum_congr rfl (fun j _ => by ring)
    rw [hsplit]
    linarith [F1, F2, F3, hmul, hO]
  have hV : I.Voff n k = I.E (fun x : Fin n → Fin m =>
      (univ.filter (fun s : Fin n → Bool => (univ.filter (fun t => s t = true)).card ≤ k)).sup'
          ⟨fun _ => false, by simp⟩ (fun s => ∑ t, if s t = true then I.a (x t) else 0)) := rfl
  have hval : I.value σ = I.E (fun x => ∑ t, if σ x t = true then I.a (x t) else 0) := rfl
  have hE := ps_E_mono I _ _ hpw
  rw [ps_E_sub, ← hV, ← hval] at hE
  simp only [ps_E_add, ps_E_sub, ps_E_cmul, ps_E_sum, ps_E_const] at hE
  have h0 : ∑ j ∈ A, I.a j * (I.E (fun x => (Z (τ x) j x : ℝ)) -
      I.E (fun x => (onCount σ (τ x) j x : ℝ))) = 0 :=
    sum_eq_zero (fun j hj => by rw [hEq j hj]; ring)
  have t2 := mul_le_mul_of_nonneg_left (show I.E (fun x => (offCount k (τ x) j0 x : ℝ)) -
      I.E (fun x => (onCount σ (τ x) j0 x : ℝ)) ≤ M by linarith) hα0
  have t4 := mul_le_mul_of_nonneg_left (show (n : ℝ) - I.E (fun x => (τ x : ℝ)) ≤ M by linarith)
    (I.a_pos I.top).le
  have t5 := mul_le_mul_of_nonneg_left hR (I.a_pos I.top).le
  have t6 := mul_le_mul_of_nonneg_right (ha1 j0) hM
  have t7 := mul_le_mul_of_nonneg_right hβa1 hM
  have e8 : I.a I.top / (4 * I.eps) = I.a I.top * (1 / (4 * I.eps)) := by ring
  rw [e8]
  linarith
