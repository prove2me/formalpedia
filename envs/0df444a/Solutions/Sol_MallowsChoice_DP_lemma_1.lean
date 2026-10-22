-- Prove2me | solution 1 for MallowsChoice.DP.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T02:27:15.41612+00:00
-- url     : https://prove2.me/submissions/ca159bcc-0684-4a64-91b3-a0ce0eec673c

import Mathlib
import Definitions.Def_MallowsChoice_DP_Setting

open Finset MallowsChoice.DP

namespace MallowsAux

lemma insertRank_injective {m : ℕ} (σ : Equiv.Perm (Fin m)) (s : Fin (m + 1)) :
    Function.Injective (insertRank σ s) := by
  intro x y h
  induction x using Fin.lastCases with
  | last =>
    induction y using Fin.lastCases with
    | last => rfl
    | cast j =>
      simp only [insertRank, Fin.lastCases_last, Fin.lastCases_castSucc] at h
      exact absurd h.symm (Fin.succAbove_ne _ _)
  | cast i =>
    induction y using Fin.lastCases with
    | last =>
      simp only [insertRank, Fin.lastCases_last, Fin.lastCases_castSucc] at h
      exact absurd h (Fin.succAbove_ne _ _)
    | cast j =>
      simp only [insertRank, Fin.lastCases_castSucc] at h
      have := σ.injective (Fin.succAbove_right_injective h)
      rw [this]

noncomputable def insPerm {m : ℕ} (σ : Equiv.Perm (Fin m)) (s : Fin (m + 1)) :
    Equiv.Perm (Fin (m + 1)) :=
  Equiv.ofBijective _ (Finite.injective_iff_bijective.mp (insertRank_injective σ s))

lemma insPerm_last {m : ℕ} (σ : Equiv.Perm (Fin m)) (s : Fin (m + 1)) :
    insPerm σ s (Fin.last m) = s := by
  simp [insPerm, insertRank]

lemma insPerm_castSucc {m : ℕ} (σ : Equiv.Perm (Fin m)) (s : Fin (m + 1)) (j : Fin m) :
    insPerm σ s j.castSucc = s.succAbove (σ j) := by
  simp [insPerm, insertRank]

lemma rim_sum (θ : ℝ) (m : ℕ) (f : Equiv.Perm (Fin (m + 1)) → ℝ) :
    ∑ τ, rimProb θ (m + 1) τ * f τ =
      ∑ σ : Equiv.Perm (Fin m), ∑ s : Fin (m + 1),
        rimProb θ m σ * alpha θ (s.val + 1) (m + 1) * f (insPerm σ s) := by
  simp only [rimProb]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun σ _ => ?_
  rw [Finset.sum_comm]
  refine sum_congr rfl fun s _ => ?_
  have key : ∀ τ : Equiv.Perm (Fin (m + 1)),
      (∀ j, τ j = insertRank σ s j) ↔ τ = insPerm σ s :=
    fun τ => ⟨fun h => Equiv.ext h, fun h j => by rw [h]; rfl⟩
  simp_rw [key, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq']
  simp

lemma gamma_eq (θ : ℝ) (r M : ℕ) :
    gamma θ r M = ∑ k ∈ range M, if k < r then alpha θ (k + 1) M else 0 := by
  induction r with
  | zero => simp [gamma]
  | succ r ih =>
    have h1 : gamma θ (r + 1) M = gamma θ r M + alpha θ (r + 1) M := by
      simp only [gamma]
      rw [Finset.sum_Icc_succ_top (by omega)]
    rw [h1, ih]
    have h2 : ∀ k, (if k < r + 1 then alpha θ (k + 1) M else 0) =
        (if k < r then alpha θ (k + 1) M else 0) +
          (if k = r then alpha θ (k + 1) M else 0) := by
      intro k
      by_cases hk : k < r
      · rw [if_pos hk, if_pos (by omega), if_neg (by omega)]; ring
      · by_cases hk2 : k = r
        · subst hk2; simp
        · rw [if_neg (by omega), if_neg hk, if_neg hk2]; ring
    simp_rw [h2]
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq']
    congr 1
    split_ifs with hr
    · rfl
    · simp only [mem_range] at hr
      simp only [alpha]
      rw [if_neg (by omega)]

lemma alpha_sum (θ : ℝ) (M : ℕ) (hM : 1 ≤ M) :
    ∑ k ∈ range M, alpha θ (k + 1) M = 1 := by
  have hZ : 0 < ∑ k ∈ range M, Real.exp (-θ * (k : ℝ)) :=
    Finset.sum_pos (fun k _ => Real.exp_pos _) (by simp; omega)
  have h1 : ∀ k ∈ range M, alpha θ (k + 1) M =
      Real.exp (-θ * (((M - 1 - k : ℕ)) : ℝ)) / ∑ k ∈ range M, Real.exp (-θ * (k : ℝ)) := by
    intro k hk
    simp only [mem_range] at hk
    simp only [alpha]
    rw [if_pos (by omega)]
    congr 3
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast; ring
  rw [Finset.sum_congr rfl h1, ← Finset.sum_div,
    Finset.sum_range_reflect (fun k => Real.exp (-θ * (k : ℝ))) M]
  exact div_self hZ.ne'

lemma one_sub_gamma (θ : ℝ) (M : ℕ) (hM : 1 ≤ M) (r : ℕ) :
    1 - gamma θ r M = ∑ k ∈ range M, if k < r then 0 else alpha θ (k + 1) M := by
  rw [← alpha_sum θ M hM, gamma_eq, ← Finset.sum_sub_distrib]
  refine sum_congr rfl fun k _ => ?_
  split_ifs <;> ring

lemma piProb_fin {n m : ℕ} (θ : ℝ) (S : Finset (Fin n)) (hm : m ≤ n) (a : Fin m) (r : ℕ) :
    piProb θ S (a.val + 1) r m = ∑ σ : Equiv.Perm (Fin m), rimProb θ m σ *
      (if Fin.castLE hm a ∈ S ∧ (σ a).val + 1 = r ∧
          ∀ b : Fin m, Fin.castLE hm b ∈ S → b ≠ a → σ a < σ b then (1 : ℝ) else 0) := by
  unfold piProb
  rw [dif_pos hm, dif_pos ⟨by omega, a.isLt⟩]
  have ha : (⟨a.val + 1 - 1, by omega⟩ : Fin m) = a := Fin.ext (by simp)
  split_ifs with hr
  · simp only [ha]
  · symm
    refine Finset.sum_eq_zero fun σ _ => ?_
    rw [if_neg]
    · simp
    · rintro ⟨-, h, -⟩
      have := (σ a).isLt
      omega

end MallowsAux

open MallowsAux

namespace MallowsAux

lemma insPair_injective (m : ℕ) :
    Function.Injective (fun p : Equiv.Perm (Fin m) × Fin (m + 1) => insPerm p.1 p.2) := by
  rintro ⟨σ, s⟩ ⟨σ', s'⟩ h
  simp only at h
  have hs : s = s' := by
    have := congrArg (fun τ : Equiv.Perm (Fin (m + 1)) => τ (Fin.last m)) h
    simpa [insPerm_last] using this
  subst hs
  have hσ : σ = σ' := by
    ext j
    have := congrArg (fun τ : Equiv.Perm (Fin (m + 1)) => τ j.castSucc) h
    simp only [insPerm_castSucc] at this
    rw [Fin.succAbove_right_injective this]
  rw [hσ]

lemma insPair_bijective (m : ℕ) :
    Function.Bijective (fun p : Equiv.Perm (Fin m) × Fin (m + 1) => insPerm p.1 p.2) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨insPair_injective m, ?_⟩
  simp only [Fintype.card_prod, Fintype.card_perm, Fintype.card_fin]
  rw [Nat.factorial_succ]
  ring

lemma kendall_eq_sum {m : ℕ} (τ : Equiv.Perm (Fin m)) :
    kendall τ = ∑ p : Fin m, ∑ q : Fin m, if p < q ∧ τ q < τ p then 1 else 0 := by
  unfold kendall
  rw [Finset.card_filter, Fintype.sum_prod_type]

lemma count_ge (m t : ℕ) (σ : Equiv.Perm (Fin m)) :
    (∑ i : Fin m, if t ≤ (σ i).val then 1 else 0) = m - t := by
  rw [Equiv.sum_comp σ (fun k : Fin m => if t ≤ k.val then 1 else 0),
    Fin.sum_univ_eq_sum_range (fun k => if t ≤ k then 1 else 0), ← Finset.card_filter]
  have : (range m).filter (fun k => t ≤ k) = Ico t m := by
    ext k; simp; omega
  rw [this, Nat.card_Ico]

lemma kendall_ins {m : ℕ} (σ : Equiv.Perm (Fin m)) (s : Fin (m + 1)) :
    kendall (insPerm σ s) = kendall σ + (m - s.val) := by
  rw [kendall_eq_sum, kendall_eq_sum]
  rw [Fin.sum_univ_castSucc]
  simp_rw [Fin.sum_univ_castSucc (n := m)]
  simp only [insPerm_castSucc, insPerm_last, Fin.castSucc_lt_castSucc_iff,
    Fin.succAbove_lt_succAbove_iff, Fin.castSucc_lt_last, true_and,
    Fin.lt_succAbove_iff_le_castSucc]
  have h0 : ∀ q : Fin m, ¬ (Fin.last m < q.castSucc) := fun q => not_lt.mpr (Fin.le_last _)
  simp only [h0, false_and, if_false, Finset.sum_const_zero, lt_irrefl, add_zero]
  rw [Finset.sum_add_distrib]
  congr 1
  rw [← count_ge m s.val σ]
  refine sum_congr rfl fun i _ => ?_
  congr 1

lemma rim_form (θ : ℝ) : ∀ m : ℕ, ∃ c : ℝ, ∀ τ : Equiv.Perm (Fin m),
    rimProb θ m τ = c * Real.exp (-θ * (kendall τ : ℝ)) := by
  intro m
  induction m with
  | zero =>
    refine ⟨1, fun τ => ?_⟩
    have : kendall τ = 0 := by
      unfold kendall
      simp
    simp [rimProb, this]
  | succ m ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨c / ∑ k ∈ range (m + 1), Real.exp (-θ * (k : ℝ)), fun τ => ?_⟩
    obtain ⟨⟨σ0, s0⟩, hτ⟩ := (insPair_bijective m).2 τ
    simp only at hτ
    have key : ∀ (σ : Equiv.Perm (Fin m)) (s : Fin (m + 1)),
        (∀ j, τ j = insertRank σ s j) ↔ (σ, s) = (σ0, s0) := by
      intro σ s
      constructor
      · intro h
        apply insPair_injective m
        simp only
        rw [hτ]
        exact (Equiv.ext h).symm
      · intro h j
        rw [← hτ]
        simp only [Prod.mk.injEq] at h
        rw [h.1, h.2]
        rfl
    simp only [rimProb]
    simp_rw [if_congr (key _ _) rfl rfl]
    rw [← Fintype.sum_prod_type' (fun σ s =>
        if (σ, s) = (σ0, s0) then rimProb θ m σ * alpha θ (s.val + 1) (m + 1) else 0)]
    rw [Fintype.sum_ite_eq']
    rw [← hτ, kendall_ins, hc]
    simp only [alpha]
    rw [if_pos ⟨by omega, by omega⟩]
    have hs := s0.isLt
    rw [show ((m + 1 : ℕ) : ℝ) - ((s0.val + 1 : ℕ) : ℝ) = ((m - s0.val : ℕ) : ℝ) by
      rw [Nat.cast_sub (by omega)]; push_cast; ring]
    push_cast
    rw [mul_add, Real.exp_add]
    ring

lemma rim_total (θ : ℝ) : ∀ m : ℕ, ∑ τ : Equiv.Perm (Fin m), rimProb θ m τ = 1 := by
  intro m
  induction m with
  | zero => simp [rimProb]
  | succ m ih =>
    have := rim_sum θ m (fun _ => 1)
    simp only [mul_one] at this
    rw [this]
    simp_rw [← Finset.mul_sum]
    rw [Fin.sum_univ_eq_sum_range (fun k => alpha θ (k + 1) (m + 1)), alpha_sum θ (m + 1) (by omega)]
    simpa using ih

end MallowsAux

theorem lemma_1_sol (θ : ℝ) (hθ : 0 ≤ θ) :
    ∀ (m : ℕ) (τ : Equiv.Perm (Fin m)), rimProb θ m τ = mallows θ τ := by
  intro m τ
  obtain ⟨c, hc⟩ := rim_form θ m
  have htot := rim_total θ m
  simp_rw [hc, ← Finset.mul_sum] at htot
  have hpsi : psi m θ = ∑ σ : Equiv.Perm (Fin m), Real.exp (-θ * (kendall σ : ℝ)) := rfl
  have h1 : c * psi m θ = 1 := by rw [hpsi]; exact htot
  have hpos : psi m θ ≠ 0 := by
    intro h; rw [h, mul_zero] at h1; exact zero_ne_one h1
  rw [hc, mallows, eq_div_iff hpos]
  linear_combination (Real.exp (-θ * (kendall τ : ℝ))) * h1

theorem pi_sum_sol (n : ℕ) (θ : ℝ) (hθ : 0 ≤ θ)
    (S : Finset (Fin n)) (a : Fin n) (ha : a ∈ S) :
    choiceProb θ S a =
      ∑ s ∈ Icc 1 n, piProb θ S (a.val + 1) s n := by
  have hcl : ∀ b : Fin n, Fin.castLE (le_refl n) b = b := fun b => Fin.ext rfl
  simp_rw [piProb_fin θ S (le_refl n) a, hcl]
  rw [Finset.sum_comm, choiceProb]
  refine sum_congr rfl fun σ _ => ?_
  rw [← Finset.mul_sum, lemma_1_sol θ hθ n σ]
  congr 1
  have : ∀ ℓ, (if a ∈ S ∧ (σ a).val + 1 = ℓ ∧
        ∀ b : Fin n, b ∈ S → b ≠ a → σ a < σ b then (1 : ℝ) else 0) =
      if (σ a).val + 1 = ℓ then (if ∀ b ∈ S, b ≠ a → σ a < σ b then (1 : ℝ) else 0)
        else 0 := by
    intro ℓ
    by_cases hl : (σ a).val + 1 = ℓ
    · simp only [hl, eq_true ha, true_and, if_true]
    · simp only [hl, false_and, and_false, if_false]
  simp_rw [this]
  have := (σ a).isLt
  rw [Finset.sum_ite_eq, if_pos (show (σ a).val + 1 ∈ Icc 1 n by simp only [mem_Icc]; omega)]

theorem solution (θ : ℝ) (hθ : 0 ≤ θ) :
    ∀ (m : ℕ) (τ : Equiv.Perm (Fin m)), rimProb θ m τ = mallows θ τ :=
  lemma_1_sol θ hθ
