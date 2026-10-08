-- Prove2me | solution 1 for LogSobolevMC.Metropolis.example_1_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T15:23:34.695475+00:00
-- url     : https://prove2.me/submissions/571fd917-8c7c-44c6-b3fa-602e40594a92

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_LogSobolevMC_Metropolis_Chains



namespace LogSobolevMC.Metropolis

open MarkovMixing
open scoped BigOperators

/-! ### Generic facts about the Metropolis construction -/

lemma metropolis_stochastic {V : Type*} [Fintype V] [DecidableEq V]
    (Ψ : Matrix V V ℝ) (hΨ : IsStochastic Ψ) (π : V → ℝ) (hπ : ∀ x, 0 < π x) :
    IsStochastic (metropolis Ψ π) := by
  have hmin : ∀ x z, 0 ≤ min 1 (π z / π x) ∧ min 1 (π z / π x) ≤ 1 := fun x z =>
    ⟨le_min zero_le_one (div_nonneg (hπ z).le (hπ x).le), min_le_left _ _⟩
  constructor
  · intro x y; unfold metropolis; split_ifs with h
    · have h1 : ∑ z ∈ ({x}ᶜ : Finset V), Ψ x z * min 1 (π z / π x)
          ≤ ∑ z ∈ ({x}ᶜ : Finset V), Ψ x z :=
        Finset.sum_le_sum (fun z _ => by
          have := hmin x z; have := hΨ.1 x z; nlinarith)
      have h2 : ∑ z ∈ ({x}ᶜ : Finset V), Ψ x z ≤ 1 := by
        rw [← hΨ.2 x]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun z _ _ => hΨ.1 x z)
      linarith
    · exact mul_nonneg (hΨ.1 x y) (hmin x y).1
  · intro x
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ x)]
    have e1 : metropolis Ψ π x x = 1 - ∑ z ∈ ({x}ᶜ : Finset V), Ψ x z * min 1 (π z / π x) := by
      unfold metropolis; simp
    have e2 : ∑ y ∈ Finset.univ.erase x, metropolis Ψ π x y
        = ∑ y ∈ ({x}ᶜ : Finset V), Ψ x y * min 1 (π y / π x) := by
      rw [Finset.compl_eq_univ_sdiff, Finset.sdiff_singleton_eq_erase]
      apply Finset.sum_congr rfl; intro y hy
      unfold metropolis; rw [if_neg (Finset.ne_of_mem_erase hy)]
    rw [e1, e2]; ring

lemma metropolis_detailed {V : Type*} [Fintype V] [DecidableEq V]
    (Ψ : Matrix V V ℝ) (hsym : ∀ x y, Ψ x y = Ψ y x) (π : V → ℝ) (hπ : ∀ x, 0 < π x) :
    DetailedBalance (metropolis Ψ π) π := by
  intro x y
  by_cases h : y = x
  · subst h; rfl
  · unfold metropolis; rw [if_neg h, if_neg (Ne.symm h)]
    have e : ∀ a b : V, π a * (Ψ a b * min 1 (π b / π a)) = Ψ a b * min (π a) (π b) := by
      intro a b
      rw [← mul_assoc, mul_comm (π a), mul_assoc]; congr 1
      rw [mul_min_of_nonneg _ _ (hπ a).le, mul_one, mul_div_cancel₀ _ (hπ a).ne']
    rw [e, e, hsym, min_comm]

/-! ### The binomial distribution and the base walk -/

lemma binomPi_pos (n : ℕ) (x : Fin (n + 1)) : 0 < binomPi n x := by
  unfold binomPi
  have : 0 < n.choose x := Nat.choose_pos (by have := x.isLt; omega)
  positivity

lemma binomPi_div (n : ℕ) (x y : Fin (n + 1)) :
    binomPi n y / binomPi n x = ((n.choose y : ℕ) : ℝ) / ((n.choose x : ℕ) : ℝ) := by
  unfold binomPi
  have : (2:ℝ) ^ n ≠ 0 := by positivity
  field_simp

lemma ratio_up (n : ℕ) (x y : Fin (n + 1)) (h : (y : ℕ) = x + 1) :
    binomPi n y / binomPi n x = ((n : ℝ) - x) / ((x : ℝ) + 1) := by
  rw [binomPi_div]
  have hx : (x : ℕ) + 1 ≤ n := by have := y.isLt; omega
  have hc := Nat.choose_succ_right_eq n x
  have hpos : (0:ℝ) < n.choose x := by exact_mod_cast Nat.choose_pos (by omega)
  rw [h, div_eq_div_iff hpos.ne' (by positivity)]
  have := congrArg (fun m : ℕ => (m : ℝ)) hc
  push_cast [Nat.cast_sub (by omega : (x:ℕ) ≤ n)] at this
  linear_combination this

lemma ratio_down (n : ℕ) (x y : Fin (n + 1)) (h : (y : ℕ) + 1 = x) :
    binomPi n y / binomPi n x = (x : ℝ) / ((n : ℝ) - x + 1) := by
  rw [binomPi_div]
  have hx : (x : ℕ) ≤ n := by have := x.isLt; omega
  have hc := Nat.choose_succ_right_eq n y
  rw [h] at hc
  have hpos : (0:ℝ) < n.choose x := by exact_mod_cast Nat.choose_pos hx
  rw [div_eq_div_iff hpos.ne' (by
    have : (x:ℝ) ≤ n := by exact_mod_cast hx
    linarith)]
  have := congrArg (fun m : ℕ => (m : ℝ)) hc
  have hy : (y:ℕ) ≤ n := by omega
  push_cast [Nat.cast_sub hy] at this
  have hyx : ((y:ℕ):ℝ) = (x:ℝ) - 1 := by
    have : ((y:ℕ):ℝ) + 1 = (x:ℝ) := by exact_mod_cast h
    linarith
  rw [hyx] at this
  linear_combination -this

lemma base_up (n : ℕ) (x y : Fin (n + 1)) (h : (y : ℕ) = x + 1) : baseWalk n x y = 1 / 2 := by
  unfold baseWalk; rw [if_pos (Or.inl h)]

lemma base_down (n : ℕ) (x y : Fin (n + 1)) (h : (y : ℕ) + 1 = x) : baseWalk n x y = 1 / 2 := by
  unfold baseWalk; rw [if_pos (Or.inr h)]

lemma base_zero (n : ℕ) (x y : Fin (n + 1)) (h1 : x ≠ y) (h2 : (y : ℕ) ≠ x + 1)
    (h3 : (y : ℕ) + 1 ≠ x) : baseWalk n x y = 0 := by
  unfold baseWalk
  rw [if_neg (by omega), if_neg (by intro h; exact h1 h.1)]

lemma base_diag (n : ℕ) (x : Fin (n + 1)) :
    baseWalk n x x = if (x : ℕ) = 0 ∨ (x : ℕ) = n then 1 / 2 else 0 := by
  unfold baseWalk
  rw [if_neg (by omega)]
  by_cases h : (x : ℕ) = 0 ∨ (x : ℕ) = n
  · rw [if_pos ⟨rfl, h⟩, if_pos h]
  · rw [if_neg (by intro h'; exact h h'.2), if_neg h]

lemma base_symm (n : ℕ) (x y : Fin (n + 1)) : baseWalk n x y = baseWalk n y x := by
  unfold baseWalk
  by_cases h1 : (y : ℕ) = x + 1 ∨ (y : ℕ) + 1 = x
  · have h1' : (x : ℕ) = y + 1 ∨ (x : ℕ) + 1 = y := by omega
    rw [if_pos h1, if_pos h1']
  · have h1' : ¬ ((x : ℕ) = y + 1 ∨ (x : ℕ) + 1 = y) := by omega
    rw [if_neg h1, if_neg h1']
    by_cases h2 : x = y
    · subst h2; rfl
    · rw [if_neg (fun h => h2 h.1), if_neg (fun h => h2 h.1.symm)]

/-- Sum over the complement of `x` when `x` has two neighbours. -/
lemma sum_two (n : ℕ) (x : Fin (n + 1)) (h1 : 1 ≤ (x : ℕ)) (h2 : (x : ℕ) + 1 ≤ n)
    (g : Fin (n + 1) → ℝ) :
    ∑ z ∈ ({x}ᶜ : Finset (Fin (n + 1))), baseWalk n x z * g z
      = 1 / 2 * g ⟨x + 1, by omega⟩ + 1 / 2 * g ⟨x - 1, by omega⟩ := by
  rw [Finset.sum_eq_add_of_mem (⟨x + 1, by omega⟩ : Fin (n + 1)) (⟨x - 1, by omega⟩ : Fin (n + 1))]
  · rw [base_up n x _ rfl, base_down n x _ (by show (x:ℕ) - 1 + 1 = x; omega)]
  · rw [Finset.mem_compl, Finset.mem_singleton]; intro heq
    have := congrArg Fin.val heq; change (x:ℕ) + 1 = x at this; omega
  · rw [Finset.mem_compl, Finset.mem_singleton]; intro heq
    have := congrArg Fin.val heq; change (x:ℕ) - 1 = x at this; omega
  · intro heq
    have := congrArg Fin.val heq; change (x:ℕ) + 1 = x - 1 at this; omega
  · intro c hc hne
    rw [base_zero n x c, zero_mul]
    · simp only [Finset.mem_compl, Finset.mem_singleton] at hc; exact Ne.symm hc
    · intro heq; apply hne.1; exact Fin.ext heq
    · intro heq; apply hne.2; exact Fin.ext (by show (c:ℕ) = (x:ℕ) - 1; omega)

lemma sum_zero (n : ℕ) (hn : 1 ≤ n) (x : Fin (n + 1)) (h : (x : ℕ) = 0)
    (g : Fin (n + 1) → ℝ) :
    ∑ z ∈ ({x}ᶜ : Finset (Fin (n + 1))), baseWalk n x z * g z = 1 / 2 * g ⟨1, by omega⟩ := by
  rw [Finset.sum_eq_single_of_mem (⟨1, by omega⟩ : Fin (n + 1))]
  · rw [base_up n x _ (by show 1 = (x:ℕ) + 1; omega)]
  · rw [Finset.mem_compl, Finset.mem_singleton]; intro heq
    have := congrArg Fin.val heq; change 1 = (x:ℕ) at this; omega
  · intro c hc hne
    rw [base_zero n x c, zero_mul]
    · simp only [Finset.mem_compl, Finset.mem_singleton] at hc; exact Ne.symm hc
    · intro heq; apply hne; exact Fin.ext (by show (c:ℕ) = 1; omega)
    · intro heq; omega

lemma sum_top (n : ℕ) (hn : 1 ≤ n) (x : Fin (n + 1)) (h : (x : ℕ) = n)
    (g : Fin (n + 1) → ℝ) :
    ∑ z ∈ ({x}ᶜ : Finset (Fin (n + 1))), baseWalk n x z * g z = 1 / 2 * g ⟨n - 1, by omega⟩ := by
  rw [Finset.sum_eq_single_of_mem (⟨n - 1, by omega⟩ : Fin (n + 1))]
  · rw [base_down n x _ (by show n - 1 + 1 = (x:ℕ); omega)]
  · rw [Finset.mem_compl, Finset.mem_singleton]; intro heq
    have := congrArg Fin.val heq; change n - 1 = (x:ℕ) at this; omega
  · intro c hc hne
    rw [base_zero n x c, zero_mul]
    · simp only [Finset.mem_compl, Finset.mem_singleton] at hc; exact Ne.symm hc
    · intro heq; omega
    · intro heq; apply hne; exact Fin.ext (by show (c:ℕ) = n - 1; omega)

lemma base_stochastic (n : ℕ) (hn : 1 ≤ n) : IsStochastic (baseWalk n) := by
  constructor
  · intro x y; unfold baseWalk; split_ifs <;> norm_num
  · intro x
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ x), ← Finset.sdiff_singleton_eq_erase,
      ← Finset.compl_eq_univ_sdiff, base_diag]
    have e : ∑ z ∈ ({x}ᶜ : Finset (Fin (n + 1))), baseWalk n x z
        = ∑ z ∈ ({x}ᶜ : Finset (Fin (n + 1))), baseWalk n x z * (fun _ => (1:ℝ)) z := by
      simp
    rw [e]
    by_cases h0 : (x : ℕ) = 0
    · rw [sum_zero n hn x h0, if_pos (Or.inl h0)]; norm_num
    by_cases h1 : (x : ℕ) = n
    · rw [sum_top n hn x h1, if_pos (Or.inr h1)]; norm_num
    rw [sum_two n x (by omega) (by have := x.isLt; omega), if_neg (by omega)]; norm_num

/-! ### The Metropolis kernel -/

lemma metro_off (n : ℕ) (x y : Fin (n + 1)) (h : y ≠ x) :
    binomMetropolis n x y = baseWalk n x y * min 1 (binomPi n y / binomPi n x) := by
  unfold binomMetropolis metropolis; rw [if_neg h]

lemma metro_diag (n : ℕ) (x : Fin (n + 1)) :
    binomMetropolis n x x
      = 1 - ∑ z ∈ ({x}ᶜ : Finset (Fin (n + 1))), baseWalk n x z * min 1 (binomPi n z / binomPi n x) := by
  unfold binomMetropolis metropolis; rw [if_pos rfl]

lemma cast_le_of_real (a b : ℕ) (h : (a : ℝ) ≤ b) : a ≤ b := by exact_mod_cast h

theorem example_1_1_core (n : ℕ) (hn : 1 ≤ n) :
    MarkovMixing.IsStochastic (binomMetropolis n) ∧
    (∀ x y : Fin (n + 1),
      (((y : ℕ) = (x : ℕ) + 1 ∧ 2 * ((x : ℕ) : ℝ) ≤ (n : ℝ) - 1) ∨
        ((y : ℕ) + 1 = (x : ℕ) ∧ (n : ℝ) + 1 ≤ 2 * ((x : ℕ) : ℝ))) →
      binomMetropolis n x y = 1 / 2) ∧
    (∀ x y : Fin (n + 1),
      (y : ℕ) + 1 = (x : ℕ) → 1 ≤ ((x : ℕ) : ℝ) → 2 * ((x : ℕ) : ℝ) ≤ (n : ℝ) + 1 →
      binomMetropolis n x y = ((x : ℕ) : ℝ) / (2 * ((n : ℝ) - ((x : ℕ) : ℝ) + 1))) ∧
    (∀ x y : Fin (n + 1),
      (y : ℕ) = (x : ℕ) + 1 → (n : ℝ) - 1 ≤ 2 * ((x : ℕ) : ℝ) → ((x : ℕ) : ℝ) ≤ (n : ℝ) - 1 →
      binomMetropolis n x y = ((n : ℝ) - ((x : ℕ) : ℝ)) / (2 * (((x : ℕ) : ℝ) + 1))) ∧
    (∀ x : Fin (n + 1), 2 * ((x : ℕ) : ℝ) ≤ (n : ℝ) - 1 →
      binomMetropolis n x x =
        ((n : ℝ) - 2 * ((x : ℕ) : ℝ) + 1) / (2 * ((n : ℝ) - ((x : ℕ) : ℝ) + 1))) ∧
    (∀ x : Fin (n + 1), (n : ℝ) + 1 ≤ 2 * ((x : ℕ) : ℝ) →
      binomMetropolis n x x =
        (2 * ((x : ℕ) : ℝ) - (n : ℝ) + 1) / (2 * (((x : ℕ) : ℝ) + 1))) ∧
    (∀ x : Fin (n + 1), 2 * (x : ℕ) = n →
      binomMetropolis n x x = 2 / ((n : ℝ) + 2)) ∧
    (∀ x y : Fin (n + 1), x ≠ y → (y : ℕ) ≠ (x : ℕ) + 1 → (y : ℕ) + 1 ≠ (x : ℕ) →
      binomMetropolis n x y = 0) ∧
    MarkovMixing.DetailedBalance (binomMetropolis n) (binomPi n) := by
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact metropolis_stochastic _ (base_stochastic n hn) _ (binomPi_pos n)
  · rintro x y (⟨h, hx⟩ | ⟨h, hx⟩)
    · rw [metro_off n x y (by omega), base_up n x y h, ratio_up n x y h]
      have hx' : (x:ℝ) + 1 ≤ (n:ℝ) - x := by linarith
      rw [min_eq_left (by rw [le_div_iff₀ (by positivity)]; linarith), mul_one]
    · rw [metro_off n x y (by omega), base_down n x y h, ratio_down n x y h]
      have hxn : (x:ℝ) ≤ n := by exact_mod_cast (by have := x.isLt; omega : (x:ℕ) ≤ n)
      rw [min_eq_left (by rw [le_div_iff₀ (by linarith)]; linarith), mul_one]
  · intro x y h h1 hx
    rw [metro_off n x y (by omega), base_down n x y h, ratio_down n x y h]
    have hxn : (x:ℝ) ≤ n := by exact_mod_cast (by have := x.isLt; omega : (x:ℕ) ≤ n)
    rw [min_eq_right (by rw [div_le_one (by linarith)]; linarith)]
    field_simp
  · intro x y h h1 hx
    rw [metro_off n x y (by omega), base_up n x y h, ratio_up n x y h]
    rw [min_eq_right (by rw [div_le_one (by positivity)]; linarith)]
    field_simp
  · intro x hx
    rw [metro_diag]
    have hxn : 2 * (x:ℕ) + 1 ≤ n := by
      apply cast_le_of_real; push_cast; linarith
    by_cases h0 : (x : ℕ) = 0
    · rw [sum_zero n hn x h0]
      have hx0 : ((x:ℕ):ℝ) = 0 := by exact_mod_cast h0
      rw [ratio_up n x _ (by show 1 = (x:ℕ) + 1; omega), hx0]
      rw [min_eq_left (by rw [le_div_iff₀ (by norm_num)]; linarith)]
      field_simp; ring
    · rw [sum_two n x (by omega) (by omega)]
      have hx1 : (1:ℝ) ≤ x := by exact_mod_cast (by omega : 1 ≤ (x:ℕ))
      rw [ratio_up n x _ rfl, ratio_down n x _ (by show (x:ℕ) - 1 + 1 = x; omega)]
      rw [min_eq_left (by rw [le_div_iff₀ (by positivity)]; linarith)]
      rw [min_eq_right (by rw [div_le_one (by linarith)]; linarith)]
      have : (n:ℝ) - x + 1 ≠ 0 := by linarith
      field_simp; ring
  · intro x hx
    rw [metro_diag]
    have hxn : n + 1 ≤ 2 * (x:ℕ) := by
      apply cast_le_of_real; push_cast; linarith
    have hxle : (x:ℕ) ≤ n := by have := x.isLt; omega
    have hxle' : (x:ℝ) ≤ n := by exact_mod_cast hxle
    by_cases h0 : (x : ℕ) = n
    · rw [sum_top n hn x h0]
      have hx0 : ((x:ℕ):ℝ) = n := by exact_mod_cast h0
      rw [ratio_down n x _ (by show n - 1 + 1 = (x:ℕ); omega), hx0]
      rw [min_eq_left (by rw [le_div_iff₀ (by linarith)]; linarith)]
      field_simp; ring
    · rw [sum_two n x (by omega) (by omega)]
      rw [ratio_up n x _ rfl, ratio_down n x _ (by show (x:ℕ) - 1 + 1 = x; omega)]
      rw [min_eq_right (by rw [div_le_one (by positivity)]; linarith)]
      rw [min_eq_left (by rw [le_div_iff₀ (by linarith)]; linarith)]
      have : (x:ℝ) + 1 ≠ 0 := by positivity
      field_simp; ring
  · intro x hx
    rw [metro_diag]
    have hxr : (n:ℝ) = 2 * x := by exact_mod_cast hx.symm
    rw [sum_two n x (by omega) (by omega)]
    rw [ratio_up n x _ rfl, ratio_down n x _ (by show (x:ℕ) - 1 + 1 = x; omega)]
    have hx1 : (1:ℝ) ≤ x := by exact_mod_cast (by omega : 1 ≤ (x:ℕ))
    rw [min_eq_right (by rw [div_le_one (by positivity)]; linarith)]
    rw [min_eq_right (by rw [div_le_one (by linarith)]; linarith)]
    rw [hxr]
    have : (x:ℝ) + 1 ≠ 0 := by positivity
    have : 2 * (x:ℝ) + 2 ≠ 0 := by positivity
    field_simp; ring
  · intro x y h1 h2 h3
    rw [metro_off n x y (Ne.symm h1), base_zero n x y h1 h2 h3, zero_mul]
  · exact metropolis_detailed _ (base_symm n) _ (binomPi_pos n)

end LogSobolevMC.Metropolis

open LogSobolevMC.Metropolis
open MarkovMixing

theorem solution (n : ℕ) (hn : 1 ≤ n) :
    MarkovMixing.IsStochastic (binomMetropolis n) ∧
    (∀ x y : Fin (n + 1),
      (((y : ℕ) = (x : ℕ) + 1 ∧ 2 * ((x : ℕ) : ℝ) ≤ (n : ℝ) - 1) ∨
        ((y : ℕ) + 1 = (x : ℕ) ∧ (n : ℝ) + 1 ≤ 2 * ((x : ℕ) : ℝ))) →
      binomMetropolis n x y = 1 / 2) ∧
    (∀ x y : Fin (n + 1),
      (y : ℕ) + 1 = (x : ℕ) → 1 ≤ ((x : ℕ) : ℝ) → 2 * ((x : ℕ) : ℝ) ≤ (n : ℝ) + 1 →
      binomMetropolis n x y = ((x : ℕ) : ℝ) / (2 * ((n : ℝ) - ((x : ℕ) : ℝ) + 1))) ∧
    (∀ x y : Fin (n + 1),
      (y : ℕ) = (x : ℕ) + 1 → (n : ℝ) - 1 ≤ 2 * ((x : ℕ) : ℝ) → ((x : ℕ) : ℝ) ≤ (n : ℝ) - 1 →
      binomMetropolis n x y = ((n : ℝ) - ((x : ℕ) : ℝ)) / (2 * (((x : ℕ) : ℝ) + 1))) ∧
    (∀ x : Fin (n + 1), 2 * ((x : ℕ) : ℝ) ≤ (n : ℝ) - 1 →
      binomMetropolis n x x =
        ((n : ℝ) - 2 * ((x : ℕ) : ℝ) + 1) / (2 * ((n : ℝ) - ((x : ℕ) : ℝ) + 1))) ∧
    (∀ x : Fin (n + 1), (n : ℝ) + 1 ≤ 2 * ((x : ℕ) : ℝ) →
      binomMetropolis n x x =
        (2 * ((x : ℕ) : ℝ) - (n : ℝ) + 1) / (2 * (((x : ℕ) : ℝ) + 1))) ∧
    (∀ x : Fin (n + 1), 2 * (x : ℕ) = n →
      binomMetropolis n x x = 2 / ((n : ℝ) + 2)) ∧
    (∀ x y : Fin (n + 1), x ≠ y → (y : ℕ) ≠ (x : ℕ) + 1 → (y : ℕ) + 1 ≠ (x : ℕ) →
      binomMetropolis n x y = 0) ∧
    MarkovMixing.DetailedBalance (binomMetropolis n) (binomPi n) := by
  exact example_1_1_core n hn
