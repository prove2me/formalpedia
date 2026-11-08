-- Prove2me | solution 1 for LineVsPoint.lemma_2_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T17:54:39.293212+00:00
-- url     : https://prove2.me/submissions/01508e82-8faa-4c66-a995-60d151a8b3e7

import Mathlib
import Definitions.Def_LineVsPoint_VD

set_option autoImplicit false

universe u

namespace Aux_LVP22

theorem gauss1 (M : ℕ) : ∑ j ∈ Finset.range (M + 1), ((j : ℝ) + 1) = (M + 1) * (M + 2) / 2 := by
  induction M with
  | zero => norm_num
  | succ M ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

theorem gauss (M : ℕ) :
    ∑ a ∈ Finset.range (M + 1), ((M - a + 1 : ℕ) : ℝ) = (M + 1) * (M + 2) / 2 := by
  rw [← gauss1 M, ← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  have : M - (M + 1 - 1 - j) + 1 = j + 1 := by omega
  rw [this]
  push_cast
  ring

theorem sq_sum (K : ℕ) : ∀ x : ℝ, (K : ℝ) ≤ x → x < K + 1 →
    x ^ 3 / 3 ≤ ∑ c ∈ Finset.range (K + 1), (x - c) ^ 2 := by
  induction K with
  | zero =>
    intro x h0 h1
    simp only [Nat.cast_zero, zero_add] at h0 h1
    simp
    nlinarith [mul_nonneg h0 h0]
  | succ K ih =>
    intro x h0 h1
    push_cast at h0 h1
    rw [Finset.sum_range_succ']
    have hih := ih (x - 1) (by linarith) (by linarith)
    have hre : ∑ c ∈ Finset.range (K + 1), (x - ((c + 1 : ℕ) : ℝ)) ^ 2 =
        ∑ c ∈ Finset.range (K + 1), (x - 1 - (c : ℝ)) ^ 2 := by
      apply Finset.sum_congr rfl
      intro c _
      push_cast
      ring
    rw [hre]
    have hx1 : (1 : ℝ) ≤ x := by
      have : (0 : ℝ) ≤ K := Nat.cast_nonneg K
      linarith
    simp only [Nat.cast_zero, sub_zero]
    nlinarith [hih]

end Aux_LVP22

open Aux_LVP22 in
theorem solution :
    ∀ (F : Type u) [Field F] (d : ℕ), 1 ≤ d → ∀ D : ℝ, 0 ≤ D →
      D ^ 3 / (6 * (d : ℝ)) < (Module.finrank F (LineVsPoint.VD F d D) : ℝ) := by
  intro F _ d hd D hD
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith
  set S : Set (Fin 3 →₀ ℕ) := {e | ((e 0 + e 1 + d * e 2 : ℕ) : ℝ) ≤ D} with hS
  have hrank : Module.finrank F (LineVsPoint.VD F d D) = Nat.card S := by
    unfold LineVsPoint.VD
    exact Module.finrank_eq_nat_card_basis (MvPolynomial.basisRestrictSupport F S)
  have hSfin : S.Finite := by
    apply (Set.finite_Iic (Finsupp.equivFunOnFinite.symm (fun _ : Fin 3 => ⌊D⌋₊))).subset
    intro e he
    simp only [hS, Set.mem_setOf_eq] at he
    simp only [Set.mem_Iic]
    rw [Finsupp.le_def]
    intro i
    simp only [Finsupp.coe_equivFunOnFinite_symm]
    apply Nat.le_floor
    have h2 : (e 2 : ℝ) ≤ d * e 2 := by
      have : (0 : ℝ) ≤ e 2 := Nat.cast_nonneg _
      nlinarith
    push_cast at he
    have h0 : (0 : ℝ) ≤ e 0 := Nat.cast_nonneg _
    have h1 : (0 : ℝ) ≤ e 1 := Nat.cast_nonneg _
    have h2' : (0 : ℝ) ≤ e 2 := Nat.cast_nonneg _
    fin_cases i <;> simp <;> nlinarith
  set K := ⌊D / d⌋₊ with hK
  let M : ℕ → ℕ := fun c => ⌊D - d * c⌋₊
  let T := (Finset.range (K + 1)).sigma
    (fun c => (Finset.range (M c + 1)).sigma (fun a => Finset.range (M c - a + 1)))
  let f : (Σ _ : ℕ, Σ _ : ℕ, ℕ) → (Fin 3 →₀ ℕ) := fun x =>
    Finsupp.equivFunOnFinite.symm ![x.2.1, x.2.2, x.1]
  have hcK : ∀ c, c ≤ K → (d : ℝ) * c ≤ D := by
    intro c hc
    have h1 : (c : ℝ) ≤ D / d := by
      have := Nat.floor_le (div_nonneg hD hdpos.le)
      have hc' : (c : ℝ) ≤ K := by exact_mod_cast hc
      linarith
    rw [le_div_iff₀ hdpos] at h1
    linarith
  have hmaps : ∀ x ∈ (T : Set (Σ _ : ℕ, Σ _ : ℕ, ℕ)), f x ∈ S := by
    rintro ⟨c, a, b⟩ hx
    simp only [T, Finset.coe_sigma, Set.mem_sigma_iff, Finset.mem_coe, Finset.mem_range] at hx
    obtain ⟨hc, ha, hb⟩ := hx
    simp only [hS, Set.mem_setOf_eq, f, Finsupp.coe_equivFunOnFinite_symm]
    show ((a + b + d * c : ℕ) : ℝ) ≤ D
    have hab : a + b ≤ M c := by omega
    have hM : ((M c : ℕ) : ℝ) ≤ D - d * c := Nat.floor_le (by linarith [hcK c (by omega)])
    have hab' : ((a + b : ℕ) : ℝ) ≤ M c := by exact_mod_cast hab
    push_cast at hab' ⊢
    linarith
  have hinj : Set.InjOn f (T : Set (Σ _ : ℕ, Σ _ : ℕ, ℕ)) := by
    rintro ⟨c, a, b⟩ _ ⟨c', a', b'⟩ _ h
    have h0 := congrArg (fun e : Fin 3 →₀ ℕ => e 0) h
    have h1 := congrArg (fun e : Fin 3 →₀ ℕ => e 1) h
    have h2 := congrArg (fun e : Fin 3 →₀ ℕ => e 2) h
    simp [f] at h0 h1 h2
    subst h0 h1 h2
    rfl
  have hcardT : T.card ≤ Nat.card S := by
    rw [Nat.card_coe_set_eq, ← Set.ncard_coe_finset]
    exact Set.ncard_le_ncard_of_injOn f hmaps hinj hSfin
  have hTval : (T.card : ℝ) = ∑ c ∈ Finset.range (K + 1), ((M c : ℝ) + 1) * ((M c : ℝ) + 2) / 2 := by
    simp only [T, Finset.card_sigma, Finset.card_range]
    push_cast
    apply Finset.sum_congr rfl
    intro c _
    rw [← gauss (M c)]
    apply Finset.sum_congr rfl
    intro a ha
    rw [Finset.mem_range] at ha
    push_cast [Nat.cast_sub (show a ≤ M c by omega)]
    ring
  have hstrict : ∑ c ∈ Finset.range (K + 1), (D - d * c) ^ 2 / 2 <
      ∑ c ∈ Finset.range (K + 1), ((M c : ℝ) + 1) * ((M c : ℝ) + 2) / 2 := by
    apply Finset.sum_lt_sum_of_nonempty ⟨0, by simp⟩
    intro c hc
    rw [Finset.mem_range] at hc
    have hr : 0 ≤ D - d * c := by linarith [hcK c (by omega)]
    have hlt : D - d * c < (M c : ℝ) + 1 := Nat.lt_floor_add_one _
    have hM0 : (0 : ℝ) ≤ M c := Nat.cast_nonneg _
    nlinarith
  have hlow : D ^ 3 / (6 * d) ≤ ∑ c ∈ Finset.range (K + 1), (D - d * c) ^ 2 / 2 := by
    have hx := sq_sum K (D / d) (Nat.floor_le (div_nonneg hD hdpos.le))
      (Nat.lt_floor_add_one _)
    have heq : ∑ c ∈ Finset.range (K + 1), (D - d * c) ^ 2 / 2 =
        (d : ℝ) ^ 2 / 2 * ∑ c ∈ Finset.range (K + 1), (D / d - c) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c _
      field_simp <;> ring
    rw [heq]
    have h3 : D ^ 3 / (6 * d) = (d : ℝ) ^ 2 / 2 * ((D / d) ^ 3 / 3) := by
      field_simp <;> ring
    rw [h3]
    apply mul_le_mul_of_nonneg_left hx (by positivity)
  rw [hrank]
  have : (T.card : ℝ) ≤ (Nat.card S : ℝ) := by exact_mod_cast hcardT
  linarith
