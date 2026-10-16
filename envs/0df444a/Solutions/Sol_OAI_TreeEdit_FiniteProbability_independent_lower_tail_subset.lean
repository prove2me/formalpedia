-- Prove2me | solution 1 for OAI.TreeEdit.FiniteProbability.independent_lower_tail_subset
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:30:54.209239+00:00
-- url     : https://prove2.me/submissions/96a45650-ef19-4aec-8977-7a00a461dd39

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TreeEdit/FiniteProbability.lean:L251-L295
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.FiniteProbability.independent_lower_tail_subset. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TreeEdit
import Definitions.Def_OAI_Combinatorics_TreeEdit_Model
import Definitions.Def_OAI_Combinatorics_TreeEdit_FiniteProbability

-- ---- from OAI.Combinatorics.TreeEdit.FiniteProbability ----
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement); as in oai-math-oct-2026.
private abbrev Finset.prod_le_prod₀ := @Finset.prod_le_prod

namespace OAI

namespace TreeEdit.FiniteProbability
open scoped BigOperators
open Classical

lemma mean_nonneg {A : Type*} [Fintype A] {f : A → ℝ} (hf : ∀ a, 0 ≤ f a) :
    0 ≤ mean f := mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (Finset.sum_nonneg (fun a _ => hf a))

lemma mean_le {A : Type*} [Fintype A] {f g : A → ℝ} (h : ∀ a, f a ≤ g a) :
    mean f ≤ mean g := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun a _ => h a)) (by positivity)

lemma mean_const {A : Type*} [Fintype A] [Nonempty A] (c : ℝ) : mean (fun _ : A => c) = c := by
  simp only [mean, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero), one_mul]

lemma mean_add {A : Type*} [Fintype A] (f g : A → ℝ) :
    mean (fun a => f a + g a) = mean f + mean g := by simp [mean, Finset.sum_add_distrib, mul_add]

lemma mean_mul_const {A : Type*} [Fintype A] (f : A → ℝ) (c : ℝ) :
    mean (fun a => f a * c) = mean f * c := by simp [mean, Finset.sum_mul, mul_assoc]

lemma mean_prod {I : Type*} [Fintype I] {A : I → Type*} [∀ i, Fintype (A i)]
    (f : ∀ i, A i → ℝ) :
    mean (fun a : ∀ i, A i => ∏ i, f i (a i)) = ∏ i, mean (f i) := by
  classical
  simp only [mean, Fintype.card_pi, Nat.cast_prod, Finset.prod_inv_distrib, Finset.prod_mul_distrib]
  congr 1
  exact (Fintype.prod_sum f).symm

lemma markov {A : Type*} [Fintype A] {E : A → Prop} {f : A → ℝ} {c : ℝ}
    (hc : 0 < c) (hf : ∀ a, 0 ≤ f a) (hE : ∀ a, E a → c ≤ f a) :
    probability E ≤ mean f / c := by
  apply (le_div_iff₀ hc).mpr
  rw [probability, ← mean_mul_const]
  apply mean_le
  intro a
  by_cases h : E a
  · simpa [h] using hE a h
  · simpa [h] using hf a

lemma independent_lower_tail_subset {I : Type*} [Fintype I] {A : I → Type*}
    [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] (E : ∀ i, A i → Prop)
    (s : Finset I) {n : ℕ} (hn : n ≤ s.card)
    (hE : ∀ i ∈ s, (4 : ℝ) / 5 ≤ probability (E i)) :
    probability (fun a : ∀ i, A i =>
      4 * (Finset.univ.filter (fun i => E i (a i))).card < n) ≤ (4 / 5 : ℝ) ^ n := by
  let f : ∀ i, A i → ℝ := fun i a => if i ∈ s then (if E i a then 1 else 4) else 1
  have hf (i : I) : mean (f i) ≤ if i ∈ s then 8 / 5 else 1 := by
    by_cases hi : i ∈ s
    · simp only [hi, ↓reduceIte]
      have hh : mean (f i) + 3 * probability (E i) = 4 := by
        rw [probability]
        rw [mul_comm 3, ← mean_mul_const, ← mean_add]
        calc
          _ = mean (fun _ : A i => (4 : ℝ)) := by
            apply congrArg mean
            funext a
            dsimp [f]
            by_cases h : E i a <;> norm_num [h, hi]
          _ = _ := mean_const 4
      linarith [hE i hi]
    · simp only [f, hi, ↓reduceIte, mean_const, le_refl]
  have hprod (a : ∀ i, A i) :
      ∏ i, f i (a i) = (4 : ℝ) ^ (s.filter (fun i => ¬ E i (a i))).card := by
    simp only [f, Finset.prod_ite, Finset.prod_const_one, mul_one, one_mul,
      Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.prod_const]
  have hd (a : ∀ i, A i) (ha : 4 * (Finset.univ.filter (fun i => E i (a i))).card < n) :
      (2 : ℝ) ^ s.card ≤ ∏ i, f i (a i) := by
    have hh := Finset.card_filter_add_card_filter_not (s := s) (p := fun i => E i (a i))
    have hsub : (s.filter (fun i => E i (a i))).card ≤
        (Finset.univ.filter (fun i => E i (a i))).card := Finset.card_le_card (by intro j hj; simpa using (Finset.mem_filter.mp hj).2)
    rw [hprod, show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hh := markov (f := fun a : ∀ i, A i => ∏ i, f i (a i)) (by positivity : 0 < (2 : ℝ) ^ s.card)
    (fun a => Finset.prod_nonneg (fun i _ => by dsimp [f]; split_ifs <;> norm_num)) hd
  calc
    _ ≤ mean (fun a : ∀ i, A i => ∏ i, f i (a i)) / (2 : ℝ) ^ s.card := hh
    _ = (∏ i, mean (f i)) / (2 : ℝ) ^ s.card := by rw [mean_prod]
    _ ≤ (8 / 5 : ℝ) ^ s.card / (2 : ℝ) ^ s.card := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      calc
        _ ≤ ∏ i : I, (if i ∈ s then (8 / 5 : ℝ) else 1) := Finset.prod_le_prod₀ (fun i _ => mean_nonneg (fun a => by dsimp [f]; split_ifs <;> norm_num)) (fun i _ => hf i)
        _ = _ := by simp [div_pow]
    _ = (4 / 5 : ℝ) ^ s.card := by rw [← div_pow]; norm_num
    _ ≤ _ := pow_le_pow_of_le_one (by norm_num) (by norm_num) hn

end TreeEdit.FiniteProbability

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.FiniteProbability
open scoped BigOperators
open Classical


theorem solution : type_of% @_root_.OAI.TreeEdit.FiniteProbability.independent_lower_tail_subset := @_root_.OAI.TreeEdit.FiniteProbability.independent_lower_tail_subset
