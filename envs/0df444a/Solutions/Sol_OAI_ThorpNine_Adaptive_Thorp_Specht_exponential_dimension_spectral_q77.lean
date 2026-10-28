-- Prove2me | solution 1 for OAI.ThorpNine.Adaptive.Thorp.Specht.exponential_dimension_spectral_q77
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:02:25.529995+00:00
-- url     : https://prove2.me/submissions/a08f4705-1a02-4963-be71-ba11c3dbd6ab

import Mathlib
import Definitions.Def_ThorpRouting
import Definitions.Def_OAIQ077T000
import Theorems.Thm_OAI_ThorpNine_Adaptive_Thorp_UnitaryFinite_medium_exception_decay_q77

section
-- module Solutions.OAIQ077_TR.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    dite p a b = b h := dif_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Adaptive_Coins
attribute [-instance] _root_.OAI.ThorpNine.Adaptive.Thorp.instFintypeSelectedCycle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Adaptive

namespace Thorp

open scoped BigOperators
open Filter

lemma card_positions (d : ℕ) : Fintype.card (Card d) = 2 ^ d := by
  simp [Card]

lemma log_factorial_lower {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) * Real.log n - n ≤ Real.log (Nat.factorial n) := by
  have h := Stirling.le_log_factorial_stirling (show n ≠ 0 by omega)
  have hln : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have hlp : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by
    have := Real.pi_gt_three
    linarith)
  linarith

lemma prod_split_at {α : Type*} [DecidableEq α] (s : Finset α) (f : α → ℝ) (a : α) :
    ∏ i ∈ s, f i = (if a ∈ s then f a else 1) * ∏ i ∈ s.erase a, f i := by
  by_cases ha : a ∈ s
  · rw [ite_eq_left ha]
    exact (Finset.mul_prod_erase s f ha).symm
  · simp [ha]

lemma prod_split_two {α : Type*} [DecidableEq α] (s : Finset α) (f : α → ℝ)
    (a b : α) (hab : a ≠ b) :
    ∏ i ∈ s, f i = (if a ∈ s then f a else 1) * (if b ∈ s then f b else 1) *
      ∏ i ∈ (s.erase a).erase b, f i := by
  calc
    ∏ i ∈ s, f i = (if a ∈ s then f a else 1) * ∏ i ∈ s.erase a, f i :=
      prod_split_at s f a
    _ = _ := by
      rw [prod_split_at (s.erase a) f b]
      have hm : (b ∈ s.erase a) ↔ b ∈ s :=
        ⟨fun h => (Finset.mem_erase.mp h).2, fun h => Finset.mem_erase.mpr ⟨Ne.symm hab, h⟩⟩
      simp only [hm, mul_assoc]

lemma swap_average_product {α : Type*} [DecidableEq α] (s : Finset α) (p : α → ℝ)
    (hp : ∀ i, 0 ≤ p i) (a b : α) :
    ((∏ i ∈ s, p i) + ∏ i ∈ s, p (Equiv.swap a b i)) / 2 ≤
      ∏ i ∈ s, (p i + p (Equiv.swap a b i)) / 2 := by
  by_cases hab : a = b
  · subst b
    simp only [Equiv.swap_self, Equiv.refl_apply]
    have h : (fun i => (p i + p i) / 2) = p := by funext i; ring
    rw [h]
    linarith
  let t := (s.erase a).erase b
  have hfix : ∀ i ∈ t, Equiv.swap a b i = i := by
    intro i hi
    exact Equiv.swap_apply_of_ne_of_ne (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
      (Finset.mem_erase.mp hi).1
  have hprod : (∏ i ∈ t, p (Equiv.swap a b i)) = ∏ i ∈ t, p i :=
    Finset.prod_congr rfl (fun i hi => by rw [hfix i hi])
  have havg : (∏ i ∈ t, (p i + p (Equiv.swap a b i)) / 2) = ∏ i ∈ t, p i :=
    Finset.prod_congr rfl (fun i hi => by rw [hfix i hi]; ring)
  rw [prod_split_two s p a b hab,
    prod_split_two s (fun i => p (Equiv.swap a b i)) a b hab,
    prod_split_two s (fun i => (p i + p (Equiv.swap a b i)) / 2) a b hab]
  change ((if a ∈ s then p a else 1) * (if b ∈ s then p b else 1) * (∏ i ∈ t, p i) +
    (if a ∈ s then p (Equiv.swap a b a) else 1) *
      (if b ∈ s then p (Equiv.swap a b b) else 1) * (∏ i ∈ t, p (Equiv.swap a b i))) / 2 ≤ _
  rw [hprod]
  change _ ≤ (if a ∈ s then (p a + p (Equiv.swap a b a)) / 2 else 1) *
    (if b ∈ s then (p b + p (Equiv.swap a b b)) / 2 else 1) *
      (∏ i ∈ t, (p i + p (Equiv.swap a b i)) / 2)
  rw [havg, Equiv.swap_apply_left, Equiv.swap_apply_right]
  have ht : 0 ≤ ∏ i ∈ t, p i := Finset.prod_nonneg (fun i _ => hp i)
  by_cases ha : a ∈ s <;> by_cases hb : b ∈ s <;> simp only [ha, hb, ↓reduceIte]
  · have hsq := mul_nonneg (sq_nonneg (p a - p b)) ht
    nlinarith
  all_goals ring_nf; rfl

lemma indicator_subset_prod {α : Type*} [DecidableEq α] (A s : Finset α) :
    (if s ⊆ A then (1 : ℝ) else 0) = ∏ i ∈ s, (if i ∈ A then 1 else 0) := by
  by_cases h : s ⊆ A
  · rw [ite_eq_left h]
    exact (Finset.prod_eq_one (fun i hi => ite_eq_left (h hi))).symm
  · rw [ite_eq_right h]
    obtain ⟨i, hi, hiA⟩ := Finset.not_subset.mp h
    exact (Finset.prod_eq_zero hi (ite_eq_right hiA)).symm

namespace QueryTree

variable {ι : Type*} [DecidableEq ι]

lemma weighted_congr (T : QueryTree ι) {ω η : ι → Bool}
    (h : ∀ i ∈ T.queries, ω i = η i) : T.weighted ω = T.weighted η := by
  induction T with
  | reject => rfl
  | accept => rfl
  | branch i zero one ih₀ ih₁ =>
    have hi := h i (Finset.mem_insert_self _ _)
    simp only [weighted, hi]
    rw [ih₀ (fun j hj => h j (Finset.mem_insert_of_mem (Finset.mem_union_left _ hj))),
      ih₁ (fun j hj => h j (Finset.mem_insert_of_mem (Finset.mem_union_right _ hj)))]
  | force i b next ih =>
    have hi := h i (Finset.mem_insert_self _ _)
    simp only [weighted, hi]
    rw [ih (fun j hj => h j (Finset.mem_insert_of_mem hj))]

lemma flipCoin_apply_eq (i : ι) (ω : ι → Bool) : flipCoin i ω i = !(ω i) := by
  change Function.update ω i (!(ω i)) i = _
  exact Function.update_self _ _ _

lemma flipCoin_apply_ne (i j : ι) (h : j ≠ i) (ω : ι → Bool) :
    flipCoin i ω j = ω j := by
  change Function.update ω i (!(ω i)) j = _
  exact Function.update_of_ne h _ _

lemma weighted_flip_of_not_mem (T : QueryTree ι) (i : ι) (hi : i ∉ T.queries)
    (ω : ι → Bool) : T.weighted (flipCoin i ω) = T.weighted ω := by
  apply weighted_congr
  intro j hj
  exact flipCoin_apply_ne i j (fun h => hi (h ▸ hj)) ω

lemma mean_indicator_bit [Fintype ι] (f : (ι → Bool) → ℝ) (i : ι) (b : Bool)
    (hf : ∀ ω, f (flipCoin i ω) = f ω) :
    finiteMean (fun ω => if ω i = b then f ω else 0) = finiteMean f / 2 := by
  let g := fun ω : ι → Bool => if ω i = b then f ω else 0
  have hp (ω : ι → Bool) : g ω + g (flipCoin i ω) = f ω := by
    dsimp [g]
    rw [flipCoin_apply_eq, hf]
    cases hω : ω i <;> cases b <;> simp
  have hs := Equiv.sum_comp (flipCoin i) g
  have hadd : (∑ ω, g ω) + (∑ ω, g (flipCoin i ω)) = ∑ ω, f ω := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun ω _ => hp ω)
  unfold finiteMean
  change (∑ ω, g ω) / _ = _
  rw [hs] at hadd
  have hh : (∑ ω, g ω) = (∑ ω, f ω) / 2 := by linarith
  rw [hh]
  ring

lemma mean_weighted_le_one [Fintype ι] (T : QueryTree ι) (hT : T.Fresh) :
    finiteMean T.weighted ≤ 1 := by
  induction T with
  | reject => simp [weighted, finiteMean]
  | accept => simp [weighted, finiteMean]
  | branch i zero one ih₀ ih₁ =>
    obtain ⟨hz, ho, hfz, hfo⟩ := hT
    have h₀ := mean_indicator_bit zero.weighted i false (zero.weighted_flip_of_not_mem i hz)
    have h₁ := mean_indicator_bit one.weighted i true (one.weighted_flip_of_not_mem i ho)
    have he : finiteMean (branch i zero one).weighted =
        finiteMean (fun ω => if ω i = false then zero.weighted ω else 0) +
        finiteMean (fun ω => if ω i = true then one.weighted ω else 0) := by
      unfold finiteMean
      rw [← add_div, ← Finset.sum_add_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro ω _
      cases hω : ω i <;> simp [weighted, hω]
    rw [he, h₀, h₁]
    linarith [ih₀ hfz, ih₁ hfo]
  | force i b next ih =>
    obtain ⟨hi, hn⟩ := hT
    have hm := mean_indicator_bit next.weighted i b (next.weighted_flip_of_not_mem i hi)
    have he : finiteMean (force i b next).weighted =
        2 * finiteMean (fun ω => if ω i = b then next.weighted ω else 0) := by
      unfold finiteMean
      rw [← mul_div_assoc, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro ω _
      by_cases h : ω i = b <;> simp [weighted, h]
    rw [he, hm]
    linarith [ih hn]

omit [DecidableEq ι] in
lemma weighted_eq (T : QueryTree ι) (ω : ι → Bool) :
    T.weighted ω = if T.succeeds ω then (2 : ℝ) ^ T.charge ω else 0 := by
  induction T with
  | reject => rfl
  | accept => norm_num [weighted, succeeds, charge]
  | branch i zero one ih₀ ih₁ =>
    cases h : ω i <;> simp [weighted, succeeds, charge, h, ih₀, ih₁]
  | force i b next ih =>
    by_cases h : ω i = b
    · simp only [weighted, succeeds, charge, h, ↓reduceIte, ih]
      cases hs : next.succeeds ω <;> simp [pow_succ, mul_comm]
    · simp [weighted, succeeds, h]

end QueryTree

end Thorp

end ThorpNine.Adaptive

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Adaptive_ExposedCoins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Adaptive

namespace Thorp
open scoped BigOperators
open Filter

lemma finiteMean_congr {Ω : Type*} [Fintype Ω] {f g : Ω → ℝ}
    (h : ∀ ω, f ω = g ω) : finiteMean f = finiteMean g := by
  unfold finiteMean
  congr 1
  exact Finset.sum_congr rfl (fun ω _ => h ω)

lemma mean_coinCylinder {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (v : ι → Bool) :
    finiteMean (fun ω : ι → Bool => if ∀ i ∈ s, ω i = v i then (1 : ℝ) else 0) =
      1 / (2 : ℝ) ^ s.card := by
  induction s using Finset.induction_on with
  | empty => simp [finiteMean]
  | @insert i s hi ih =>
    let f := fun ω : ι → Bool => if ∀ j ∈ s, ω j = v j then (1 : ℝ) else 0
    have hf : ∀ ω, f (QueryTree.flipCoin i ω) = f ω := by
      intro ω
      have he : (∀ j ∈ s, QueryTree.flipCoin i ω j = v j) ↔ ∀ j ∈ s, ω j = v j := by
        apply forall₂_congr
        intro j hj
        rw [QueryTree.flipCoin_apply_ne i j (fun h => hi (h ▸ hj))]
      dsimp [f]
      simp only [he]
    have hm := QueryTree.mean_indicator_bit f i (v i) hf
    have he : (fun ω : ι → Bool => if ∀ j ∈ insert i s, ω j = v j then (1 : ℝ) else 0) =
        (fun ω => if ω i = v i then f ω else 0) := by
      funext ω
      by_cases h : ω i = v i <;> simp [f, h]
    rw [he, hm]
    change finiteMean (fun ω : ι → Bool => if ∀ j ∈ s, ω j = v j then (1 : ℝ) else 0) / 2 = _
    rw [ih, Finset.card_insert_of_notMem hi, pow_succ]
    ring

namespace QueryTree
variable {ι : Type*} [DecidableEq ι]

lemma memo_queries_disjoint (T : QueryTree ι) (R : Finset ι) (η : ι → Bool) :
    Disjoint (memo T R η).queries R := by
  induction T generalizing R η with
  | reject => simp [memo,queries]
  | accept => simp [memo,queries]
  | branch i zero one ih₀ ih₁ =>
    by_cases hi : i ∈ R
    · simp only [memo,hi,↓reduceIte]
      cases η i <;> simp only [Bool.false_eq_true,↓reduceIte]
      · exact ih₀ R η
      · exact ih₁ R η
    · simp only [memo,hi,↓reduceIte,queries,Finset.disjoint_insert_left,Finset.disjoint_union_left]
      exact ⟨by simp, (ih₀ (insert i R) _).mono_right (Finset.subset_insert _ _),
        (ih₁ (insert i R) _).mono_right (Finset.subset_insert _ _)⟩
  | force i b next ih =>
    by_cases hi : i ∈ R
    · simp only [memo,hi,↓reduceIte]
      by_cases hb : η i = b
      · simpa only [hb,↓reduceIte] using ih R η
      · simp [hb,queries]
    · simp only [memo,hi,↓reduceIte,queries,Finset.disjoint_insert_left]
      exact ⟨by simp,(ih (insert i R) _).mono_right (Finset.subset_insert _ _)⟩

lemma memo_fresh (T : QueryTree ι) (R : Finset ι) (η : ι → Bool) :
    (memo T R η).Fresh := by
  induction T generalizing R η with
  | reject => trivial
  | accept => trivial
  | branch i zero one ih₀ ih₁ =>
    by_cases hi : i ∈ R
    · simp only [memo,hi,↓reduceIte]
      cases η i <;> simp only [Bool.false_eq_true,↓reduceIte]
      · exact ih₀ R η
      · exact ih₁ R η
    · simp only [memo,hi,↓reduceIte,Fresh]
      exact ⟨fun hm => Finset.disjoint_left.mp (memo_queries_disjoint zero (insert i R) _) hm
          (Finset.mem_insert_self _ _),
        fun hm => Finset.disjoint_left.mp (memo_queries_disjoint one (insert i R) _) hm
          (Finset.mem_insert_self _ _), ih₀ _ _,ih₁ _ _⟩
  | force i b next ih =>
    by_cases hi : i ∈ R
    · simp only [memo,hi,↓reduceIte]
      by_cases hb : η i = b
      · simpa only [hb,↓reduceIte] using ih R η
      · simp [hb,Fresh]
    · simp only [memo,hi,↓reduceIte,Fresh]
      exact ⟨fun hm => Finset.disjoint_left.mp (memo_queries_disjoint next (insert i R) _) hm
        (Finset.mem_insert_self _ _),ih _ _⟩

lemma update_agrees {R : Finset ι} {η ω : ι → Bool}
    (h : ∀ i ∈ R, η i = ω i) (i : ι) :
    ∀ j ∈ insert i R, Function.update η i (ω i) j = ω j := by
  intro j hj
  rcases Finset.mem_insert.mp hj with rfl | hj
  · simp
  · by_cases hji : j = i
    · subst j; simp
    · rw [Function.update_of_ne hji]
      exact h j hj

lemma memo_succeeds (T : QueryTree ι) (R : Finset ι) (η ω : ι → Bool)
    (h : ∀ i ∈ R, η i = ω i) : (memo T R η).succeeds ω = T.succeeds ω := by
  induction T generalizing R η with
  | reject => rfl
  | accept => rfl
  | branch i zero one ih₀ ih₁ =>
    by_cases hi : i ∈ R
    · simp only [memo,hi,↓reduceIte,succeeds,h i hi]
      cases ω i <;> simp only [Bool.false_eq_true,↓reduceIte]
      · exact ih₀ R η h
      · exact ih₁ R η h
    · simp only [memo,hi,↓reduceIte,succeeds]
      cases hb : ω i <;> simp only [Bool.false_eq_true,↓reduceIte]
      · exact ih₀ _ _ (by simpa only [hb] using update_agrees h i)
      · exact ih₁ _ _ (by simpa only [hb] using update_agrees h i)
  | force i b next ih =>
    by_cases hi : i ∈ R
    · simp only [memo,hi,↓reduceIte,h i hi]
      by_cases hb : ω i = b
      · simp only [hb,↓reduceIte,succeeds]
        exact ih R η h
      · simp [hb,succeeds]
    · simp only [memo,hi,↓reduceIte,succeeds]
      by_cases hb : ω i = b
      · simp only [hb,↓reduceIte]
        exact ih _ _ (by simpa only [hb] using update_agrees h i)
      · simp [hb]

lemma memo_charge (T : QueryTree ι) (R : Finset ι) (η ω : ι → Bool)
    (h : ∀ i ∈ R, η i = ω i) : (memo T R η).charge ω = freshCharge T R ω := by
  induction T generalizing R η with
  | reject => rfl
  | accept => rfl
  | branch i zero one ih₀ ih₁ =>
    by_cases hi : i ∈ R
    · simp only [memo,hi,↓reduceIte,freshCharge,h i hi,Finset.insert_eq_of_mem hi]
      cases ω i <;> simp only [Bool.false_eq_true,↓reduceIte]
      · exact ih₀ R η h
      · exact ih₁ R η h
    · simp only [memo,hi,↓reduceIte,charge,freshCharge]
      cases hb : ω i <;> simp only [Bool.false_eq_true,↓reduceIte]
      · exact ih₀ _ _ (by simpa only [hb] using update_agrees h i)
      · exact ih₁ _ _ (by simpa only [hb] using update_agrees h i)
  | force i b next ih =>
    by_cases hi : i ∈ R
    · simp only [memo,hi,↓reduceIte,h i hi,freshCharge,Finset.insert_eq_of_mem hi,Nat.add_zero]
      by_cases hb : ω i = b
      · simp only [hb,↓reduceIte]
        exact ih R η h
      · simp [hb,charge]
    · simp only [memo,hi,↓reduceIte,charge,freshCharge]
      by_cases hb : ω i = b
      · simp only [hb,↓reduceIte]
        rw [ih _ _ (by simpa only [hb] using update_agrees h i)]
      · simp [hb]

lemma mean_freshCharge_le_one [Fintype ι] (T : QueryTree ι) :
    finiteMean (fun ω : ι → Bool =>
      if T.succeeds ω then (2:ℝ) ^ T.freshCharge ∅ ω else 0) ≤ 1 := by
  let η : ι → Bool := fun _ => false
  have hm := mean_weighted_le_one (memo T ∅ η) (memo_fresh T ∅ η)
  have he : finiteMean (memo T ∅ η).weighted =
      finiteMean (fun ω : ι → Bool =>
        if T.succeeds ω then (2:ℝ) ^ T.freshCharge ∅ ω else 0) := by
    apply finiteMean_congr
    intro ω
    rw [weighted_eq, memo_succeeds _ _ _ _ (by simp), memo_charge _ _ _ _ (by simp)]
  rw [he] at hm
  exact hm


end QueryTree

lemma finiteMean_add {Ω : Type*} [Fintype Ω] (f g : Ω → ℝ) :
    finiteMean (fun ω => f ω + g ω) = finiteMean f + finiteMean g := by
  simp only [finiteMean,Finset.sum_add_distrib,add_div]

lemma finiteMean_mul_const {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) (c : ℝ) :
    finiteMean (fun ω => f ω * c) = finiteMean f * c := by
  unfold finiteMean
  rw [← Finset.sum_mul]
  ring

lemma finiteMean_mono {Ω : Type*} [Fintype Ω] {f g : Ω → ℝ}
    (h : ∀ ω, f ω ≤ g ω) : finiteMean f ≤ finiteMean g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun ω _ => h ω)) (Nat.cast_nonneg _)

lemma finiteMean_equiv {Ω Ω' : Type*} [Fintype Ω] [Fintype Ω']
    (e : Ω ≃ Ω') (f : Ω → ℝ) :
    finiteMean f = finiteMean (fun ω => f (e.symm ω)) := by
  unfold finiteMean
  rw [Fintype.card_congr e]
  congr 1
  exact Fintype.sum_equiv e _ _ (fun ω => by simp)

lemma finiteMean_prod_left {Ω Ω' : Type*} [Fintype Ω] [Fintype Ω'] [Nonempty Ω']
    (f : Ω → ℝ) : finiteMean (fun ω : Ω × Ω' => f ω.1) = finiteMean f := by
  simp only [finiteMean,Fintype.sum_prod_type,Finset.sum_const,nsmul_eq_mul,
    ← Finset.mul_sum,Fintype.card_prod,Nat.cast_mul,Finset.card_univ]
  have hn : (Fintype.card Ω' : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp

lemma finiteMean_pi_eval {C : Type*} [Fintype C] [DecidableEq C]
    {A : C → Type*} [∀ c, Fintype (A c)] [∀ c, Nonempty (A c)]
    (c : C) (g : A c → ℝ) :
    finiteMean (fun z : ∀ c, A c => g (z c)) = finiteMean g := by
  rw [finiteMean_equiv (Equiv.piSplitAt c A)]
  have he : (fun z : A c × ((j : {j // j ≠ c}) → A j) =>
      g ((Equiv.piSplitAt c A).symm z c)) = (fun z => g z.1) := by
    funext z
    simp [Equiv.piSplitAt]
  rw [he,finiteMean_prod_left]

lemma finiteMean_eq_indicator {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (a : Ω) :
    finiteMean (fun ω : Ω => if ω = a then (1:ℝ) else 0) = 1 / Fintype.card Ω := by
  simp [finiteMean]

lemma exp_finiteMean_le {Ω : Type*} [Fintype Ω] [Nonempty Ω] (f : Ω → ℝ) :
    Real.exp (finiteMean f) ≤ finiteMean (fun ω => Real.exp (f ω)) := by
  have hn : (Fintype.card Ω : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hw : ∑ ω : Ω, (1 / (Fintype.card Ω : ℝ)) = 1 := by simp [hn]
  have hj := convexOn_exp.map_sum_le (t := Finset.univ)
    (w := fun _ : Ω => 1 / (Fintype.card Ω : ℝ)) (p := f)
    (fun _ _ => by positivity) hw (fun _ _ => Set.mem_univ _)
  simp only [smul_eq_mul, ← Finset.mul_sum] at hj
  simpa only [finiteMean, div_eq_mul_inv, one_div, mul_comm, mul_one, one_mul] using hj

end Thorp

end ThorpNine.Adaptive

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Adaptive_RotationMeeting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Adaptive

namespace Thorp
open scoped BigOperators
open Filter

section OrbitCore
variable {α : Type*} [Fintype α] [DecidableEq α]

omit [DecidableEq α] in
lemma perm_minimalPeriod_pos (p : Equiv.Perm α) (x : α) :
    0 < Function.minimalPeriod p x :=
  Function.minimalPeriod_pos_of_mem_periodicPts (p.injective.mem_periodicPts x)

lemma orbitSet_card (p : Equiv.Perm α) (x : α) :
    (orbitSet p x).card = Function.minimalPeriod p x := by
  classical
  let f : Fin (Function.minimalPeriod p x) → {y // p.SameCycle x y} := fun n =>
    ⟨p^[n.val] x,by rw [Equiv.Perm.iterate_eq_pow]; exact ⟨(n.val:ℤ),by simp⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j hij
      apply Fin.ext
      exact Function.iterate_injOn_Iio_minimalPeriod i.isLt j.isLt (congrArg Subtype.val hij)
    · intro y
      obtain ⟨n,hn⟩ := y.property.exists_nat_pow_eq
      refine ⟨⟨n % Function.minimalPeriod p x, Nat.mod_lt _ (perm_minimalPeriod_pos p x)⟩,?_⟩
      apply Subtype.ext
      change p^[n % Function.minimalPeriod p x] x = y.val
      rw [Function.iterate_mod_minimalPeriod_eq,Equiv.Perm.iterate_eq_pow,hn]
  have hc := Fintype.card_congr (Equiv.ofBijective f hf)
  simpa [orbitSet,Fintype.card_subtype] using hc.symm

omit [Fintype α] in
lemma walkSet_succ_first (p : Equiv.Perm α) (r : ℕ) (x : α) :
    walkSet p (r+1) x = insert x (walkSet p r (p x)) := by
  ext y
  simp only [mem_walkSet,Finset.mem_insert]
  constructor
  · rintro ⟨n,hn,hny⟩
    cases n with
    | zero => exact Or.inl (by simpa using hny.symm)
    | succ n => exact Or.inr ⟨n,by omega,by simpa only [Function.iterate_succ_apply] using hny⟩
  · rintro (rfl | ⟨n,hn,hny⟩)
    · exact ⟨0,by omega,rfl⟩
    · exact ⟨n+1,by omega,by simpa only [Function.iterate_succ_apply] using hny⟩

omit [Fintype α] in
lemma not_mem_short_walk (p : Equiv.Perm α) (x : α) {r : ℕ}
    (hr : r < Function.minimalPeriod p x) : x ∉ walkSet p r (p x) := by
  rintro hx
  obtain ⟨n,hn,hnx⟩ := (mem_walkSet _ _ _ _).mp hx
  have hperiod : Function.IsPeriodicPt p (n+1) x := by
    simpa only [Function.IsPeriodicPt,Function.IsFixedPt,Function.iterate_succ_apply] using hnx
  have hp := hperiod.minimalPeriod_le (by omega : 0 < n+1)
  omega

lemma walkSet_period (p : Equiv.Perm α) (x : α) :
    walkSet p (Function.minimalPeriod p x) x = orbitSet p x := by
  ext y
  simp only [mem_walkSet,mem_orbitSet]
  constructor
  · rintro ⟨n,_,rfl⟩
    rw [Equiv.Perm.iterate_eq_pow]
    exact ⟨(n:ℤ),by simp⟩
  · intro h
    obtain ⟨n,hn⟩ := h.exists_nat_pow_eq
    refine ⟨n % Function.minimalPeriod p x,Nat.mod_lt _ (perm_minimalPeriod_pos p x),?_⟩
    rw [Function.iterate_mod_minimalPeriod_eq,Equiv.Perm.iterate_eq_pow,hn]

lemma cycleTrace_walk (p : Equiv.Perm α) (S : Finset α) (r : ℕ) (x : α) (V : Finset α)
    (hr : r < Function.minimalPeriod p x) (hS : walkSet p (r+1) x ⊆ S)
    (hV : Disjoint V (walkSet p (r+1) x)) :
    cycleTrace p S (p^[r+1] x) r x V = some (V ∪ walkSet p (r+1) x,p^[r] x) := by
  induction r generalizing x V with
  | zero =>
    have hxS : x ∈ S := hS (by simp [walkSet_succ_first])
    have hxV : x ∉ V := fun h => Finset.disjoint_left.mp hV h (by simp [walkSet_succ_first])
    simp [cycleTrace,hxS,hxV,walkSet_succ_first]
  | succ r ih =>
    have hxS : x ∈ S := hS (by rw [walkSet_succ_first]; exact Finset.mem_insert_self _ _)
    have hxV : x ∉ V := fun h => Finset.disjoint_left.mp hV h
      (by rw [walkSet_succ_first]; exact Finset.mem_insert_self _ _)
    have hr' : r < Function.minimalPeriod p (p x) := by
      rw [Function.minimalPeriod_apply (p.injective.mem_periodicPts x)]
      omega
    have hS' : walkSet p (r+1) (p x) ⊆ S := by
      intro y hy
      apply hS
      rw [walkSet_succ_first]
      exact Finset.mem_insert_of_mem hy
    have hV' : Disjoint (insert x V) (walkSet p (r+1) (p x)) := by
      apply Finset.disjoint_left.mpr
      intro y hy hy'
      rcases Finset.mem_insert.mp hy with hy | hy
      · subst y
        exact not_mem_short_walk p x hr hy'
      · apply Finset.disjoint_left.mp hV hy
        rw [walkSet_succ_first]
        exact Finset.mem_insert_of_mem hy'
    rw [cycleTrace,ite_eq_left ⟨hxS,hxV⟩,Function.iterate_succ_apply p (r+1) x,
      ih _ _ hr' hS' hV',walkSet_succ_first p (r+1) x,Function.iterate_succ_apply]
    simp only [Finset.insert_union,Finset.union_insert]

lemma cycleTrace_orbit (p : Equiv.Perm α) (S V : Finset α) (z : α)
    (hS : orbitSet p z ⊆ S) (hV : Disjoint V (orbitSet p z)) :
    cycleTrace p S (p z) (Function.minimalPeriod p z - 1) (p z) V =
      some (V ∪ orbitSet p z,z) := by
  have hpos := perm_minimalPeriod_pos p z
  have he : Function.minimalPeriod p (p z) = Function.minimalPeriod p z :=
    Function.minimalPeriod_apply (p.injective.mem_periodicPts z)
  have hp : Function.minimalPeriod p z - 1 + 1 = Function.minimalPeriod p z := by omega
  have hw : walkSet p (Function.minimalPeriod p z - 1 + 1) (p z) = orbitSet p z := by
    rw [hp,←he,walkSet_period,orbitSet_apply]
  have hr : Function.minimalPeriod p z - 1 < Function.minimalPeriod p (p z) := by rw [he]; omega
  have h := cycleTrace_walk p S (Function.minimalPeriod p z-1) (p z) V hr
    (by simpa only [hw] using hS) (by simpa only [hw] using hV)
  have ht : p^[Function.minimalPeriod p z-1] (p z) = z := by
    rw [← Function.iterate_succ_apply,show (Function.minimalPeriod p z-1).succ =
      Function.minimalPeriod p z by omega,Function.iterate_minimalPeriod]
  have ha : p^[Function.minimalPeriod p z-1+1] (p z) = p z := by
    rw [hp,←he,Function.iterate_minimalPeriod]
  simpa only [ha,ht,hw] using h

end OrbitCore

section Collections
variable {d A : ℕ}

lemma sum_comp_injective_le {α β : Type*} [Fintype α] [Fintype β]
    (e : α → β) (he : Function.Injective e) (f : β → ℝ) (hf : ∀ b, 0 ≤ f b) :
    ∑ a, f (e a) ≤ ∑ b, f b := by
  classical
  calc
    _ = ∑ b ∈ Finset.univ.image e, f b := (Finset.sum_image (fun _ _ _ _ h => he h)).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun b _ _ => hf b)

lemma collectionWeight_pos (d : ℕ) {A : ℕ} (r : Fin A → ℕ) : 0 < collectionWeight d r := by
  unfold collectionWeight rotationLower
  positivity

lemma collectionWeight_eq_sqrt (d : ℕ) {A : ℕ} (r : Fin A → ℕ) :
    collectionWeight d r = (Real.sqrt ((2:ℝ)^d))^A * ∏ i : Fin A, Real.sqrt (r i+1) := by
  have hn : ((2:ℝ)^d)^A = Real.exp ((A:ℝ)*d*Real.log 2) := by
    rw [mul_assoc,Real.exp_nat_mul,Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<2)]
  have hp : (∏ i : Fin A, (r i+1 : ℝ)) = Real.exp (∑ i : Fin A, Real.log (r i+1)) := by
    rw [Real.exp_sum]
    apply Finset.prod_congr rfl
    intro i _
    exact (Real.exp_log (by positivity)).symm
  have hs : Real.sqrt ((2:ℝ)^d) = Real.exp ((d:ℝ)*Real.log 2/2) := by
    rw [Real.sqrt_eq_rpow,Real.rpow_def_of_pos (by positivity),Real.log_pow]
    congr 1
    ring
  have hj (i : Fin A) : Real.sqrt (r i+1) = Real.exp (Real.log (r i+1)/2) := by
    rw [Real.sqrt_eq_rpow,Real.rpow_def_of_pos (by positivity)]
    congr 1
    ring
  simp_rw [collectionWeight,hn,hp,rotationLower,hs,hj]
  rw [←Real.exp_add,←Real.exp_add,←Real.exp_nat_mul,←Real.exp_sum,←Real.exp_add]
  congr 1
  rw [←Finset.sum_div,←Finset.sum_div]
  have hl : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  field_simp
  ring

end Collections

end Thorp

end ThorpNine.Adaptive

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Adaptive_AssignmentSlots
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Adaptive

namespace Thorp
open scoped BigOperators
open Filter

lemma factorial_mgf {Ω : Type*} [Fintype Ω] (F : Ω → ℕ) (k : ℕ) (Λ q : ℝ)
    (hF : ∀ ω, F ω ≤ k) (hΛ : 0 ≤ Λ) (hq : 1 ≤ q)
    (hm : ∀ a, finiteMean (fun ω => ((F ω).descFactorial a : ℝ)) ≤ Λ^a) :
    finiteMean (fun ω => q^(F ω)) ≤ Real.exp ((q-1)*Λ) := by
  have hc (n a : ℕ) : (n.choose a : ℝ) = (n.descFactorial a : ℝ) / (a.factorial : ℝ) := by
    rw [Nat.descFactorial_eq_factorial_mul_choose,Nat.cast_mul]
    exact (mul_div_cancel_left₀ _ (by exact_mod_cast Nat.factorial_ne_zero a)).symm
  have hex (ω : Ω) : q^(F ω) = ∑ a ∈ Finset.range (k+1),
      ((F ω).descFactorial a : ℝ) * ((q-1)^a / (a.factorial : ℝ)) := by
    calc
      _ = ((q-1)+1)^(F ω) := by congr 1; ring
      _ = ∑ a ∈ Finset.range (F ω+1), (q-1)^a * (F ω).choose a := by
        rw [add_pow]
        simp only [one_pow,mul_one]
      _ = ∑ a ∈ Finset.range (k+1), (q-1)^a * (F ω).choose a := by
        apply Finset.sum_subset (Finset.range_mono (Nat.add_le_add_right (hF ω) _))
        intro a _ ha
        have hn : F ω < a := by have := (Finset.mem_range.not.mp ha); omega
        rw [Nat.choose_eq_zero_of_lt hn,Nat.cast_zero,mul_zero]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro a _
        rw [hc]
        ring
  simp_rw [hex,finiteMean_sum,finiteMean_mul_const]
  calc
    _ ≤ ∑ a ∈ Finset.range (k+1), Λ^a * ((q-1)^a / (a.factorial : ℝ)) := by
      apply Finset.sum_le_sum
      intro a _
      exact mul_le_mul_of_nonneg_right (hm a) (by positivity)
    _ = ∑ a ∈ Finset.range (k+1), ((q-1)*Λ)^a / (a.factorial : ℝ) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [mul_pow]
      ring
    _ ≤ _ := Real.sum_le_exp_of_nonneg (mul_nonneg (sub_nonneg.mpr hq) hΛ) _

lemma inv_sqrt_step (j : ℕ) :
    1 / Real.sqrt (j+1) ≤ 2*(Real.sqrt (j+1)-Real.sqrt j) := by
  have hp : 0 < Real.sqrt (j+1) := Real.sqrt_pos.mpr (by positivity)
  apply (div_le_iff₀ hp).mpr
  have h1 := Real.sq_sqrt (show (0:ℝ) ≤ j+1 by positivity)
  have h0 := Real.sq_sqrt (show (0:ℝ) ≤ j by positivity)
  nlinarith [sq_nonneg (Real.sqrt (j+1)-Real.sqrt j)]

lemma sum_inv_sqrt (J : ℕ) :
    (∑ j : Fin J, 1 / Real.sqrt ((j:ℕ)+1)) ≤ 2*Real.sqrt J := by
  have h (n : ℕ) : (∑ j ∈ Finset.range n, 1 / Real.sqrt (j+1)) ≤ 2*Real.sqrt n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      have hs := inv_sqrt_step n
      push_cast
      linarith
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => (1 / Real.sqrt (j+1) : ℝ)) J]
  exact h J

section FullCycleMGF
variable {d : ℕ}

lemma finiteMean_pos {Ω : Type*} [Fintype Ω] [Nonempty Ω] {f : Ω → ℝ}
    (h : ∀ ω, 0 < f ω) : 0 < finiteMean f := by
  apply div_pos
  · exact Finset.sum_pos (fun ω _ => h ω) Finset.univ_nonempty
  · exact Nat.cast_pos.mpr Fintype.card_pos

end FullCycleMGF

namespace RoutingNetwork
variable {α ι : Type*} [Fintype α] [DecidableEq α] [Fintype ι] [DecidableEq ι]
  {d : ℕ} (R : RoutingNetwork α ι d)

lemma card_switches_using (ω : ι → Bool) (x : α) :
    (Finset.univ.filter (fun i : ι =>
      (R.users ω i).1 = x ∨ (R.users ω i).2 = x)).card = d := by
  classical
  have he : Finset.univ.filter (fun i : ι =>
      (R.users ω i).1 = x ∨ (R.users ω i).2 = x) = R.path ω x := by
    ext i
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,R.mem_path]
  rw [he,R.card_path]
lemma switch_incidence_sum (b : ι → Bool) (w : α → ℝ) :
    ∑ i : ι, (w (R.users b i).1 + w (R.users b i).2) =
      (d : ℝ) * ∑ x : α, w x := by
  classical
  calc
    _ = ∑ i : ι, ∑ x : α,
        if (R.users b i).1 = x ∨ (R.users b i).2 = x then w x else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_ite]
      simp only [Finset.sum_const_zero, add_zero]
      have he : Finset.univ.filter (fun x : α =>
          (R.users b i).1 = x ∨ (R.users b i).2 = x) =
          {(R.users b i).1, (R.users b i).2} := by
        ext x; simp [eq_comm]
      rw [he, Finset.sum_pair (R.users_ne b i)]
    _ = ∑ x : α, ∑ i : ι,
        if (R.users b i).1 = x ∨ (R.users b i).2 = x then w x else 0 :=
      Finset.sum_comm
    _ = ∑ x : α, (d : ℝ) * w x := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_ite]
      simp only [Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
        card_switches_using]
    _ = _ := by rw [Finset.mul_sum]

lemma weighted_switch_min_bound (b : ι → Bool) (w : α → ℝ) :
    ∑ i : ι, min (w (R.users b i).1) (w (R.users b i).2) ≤
      (d : ℝ) / 2 * ∑ x : α, w x := by
  have h : 2 * (∑ i : ι,
      min (w (R.users b i).1) (w (R.users b i).2)) ≤
      ∑ i : ι, (w (R.users b i).1 + w (R.users b i).2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    linarith [min_le_left (w (R.users b i).1) (w (R.users b i).2),
      min_le_right (w (R.users b i).1) (w (R.users b i).2)]
  rw [switch_incidence_sum] at h
  linarith
section Rotation
variable {A : ℕ}

omit [DecidableEq α] in
lemma card_cycleFiber (o : α → Option (Fin A)) (i : Fin A) :
    Fintype.card {x : α // o x = some i} = (cycleFiber o i).card := by
  classical
  simp [cycleFiber,Fintype.card_subtype]

lemma terminal_mean {o : α → Option (Fin A)}
    [∀ i : Fin A, Nonempty {x : α // o x = some i}]
    (i : Fin A) (x : α) (hx : o x = some i) :
    finiteMean (fun z : Terminal o => if (z i).val = x then (1:ℝ) else 0) = slotWeight o i := by
  classical
  have hev := finiteMean_pi_eval (A := fun i : Fin A => {x : α // o x = some i})
    i (fun z => if z.val = x then (1:ℝ) else 0)
  rw [hev]
  have he : (fun z : {x : α // o x = some i} => if z.val = x then (1:ℝ) else 0) =
      (fun z => if z = ⟨x,hx⟩ then 1 else 0) := by
    funext z
    simp only [Subtype.ext_iff]
  rw [he,finiteMean_eq_indicator,card_cycleFiber,slotWeight]

omit [DecidableEq α] in
lemma slotWeight_antitone (o : α → Option (Fin A))
    (hn : ∀ i, (cycleFiber o i).Nonempty)
    (hm : Monotone (fun i => (cycleFiber o i).card)) : Antitone (slotWeight o) := by
  intro i j hij
  unfold slotWeight
  apply one_div_le_one_div_of_le
  · exact_mod_cast Finset.card_pos.mpr (hn i)
  · exact_mod_cast hm hij

lemma rotationMeeting_mean {o : α → Option (Fin A)}
    [∀ i : Fin A, Nonempty {x : α // o x = some i}]
    (hm : Monotone (fun i => (cycleFiber o i).card)) (u v : α) :
    finiteMean (fun z : Terminal o => rotationMeeting o z u v) =
      min (pathWeight o u) (pathWeight o v) + withinWeight o u v := by
  classical
  have hn : ∀ i, (cycleFiber o i).Nonempty := by
    intro i
    obtain ⟨x,hx⟩ := (inferInstance : Nonempty {x : α // o x = some i})
    exact ⟨x,mem_cycleFiber _ _ _ |>.mpr hx⟩
  have hw := slotWeight_antitone o hn hm
  cases hu : o u with
  | none =>
    cases hv : o v with
    | none => simp [rotationMeeting,pathWeight,withinWeight,hu,hv,finiteMean]
    | some j =>
      have hj : 0 ≤ slotWeight o j := by unfold slotWeight; positivity
      simp [rotationMeeting,pathWeight,withinWeight,hu,hv,finiteMean,min_eq_left hj]
  | some i =>
    cases hv : o v with
    | none =>
      have hi : 0 ≤ slotWeight o i := by unfold slotWeight; positivity
      simp [rotationMeeting,pathWeight,withinWeight,hu,hv,finiteMean,min_eq_right hi]
    | some j =>
      simp only [rotationMeeting,pathWeight,withinWeight,hu,hv]
      rcases lt_trichotomy i j with hij | rfl | hji
      · simp only [hij,↓reduceIte,ne_of_lt hij]
        rw [terminal_mean j v hv,min_eq_right (hw (le_of_lt hij)),add_zero]
      · simp only [lt_self_iff_false,↓reduceIte,min_self]
        rw [finiteMean_add,terminal_mean i u hu,terminal_mean i v hv]
      · simp only [not_lt_of_ge (le_of_lt hji),hji,↓reduceIte,ne_of_gt hji]
        rw [terminal_mean i u hu,min_eq_left (hw (le_of_lt hji)),add_zero]

omit [DecidableEq α] in
lemma pathWeight_sum (o : α → Option (Fin A)) (hn : ∀ i, (cycleFiber o i).Nonempty) :
    ∑ x : α, pathWeight o x = (A : ℝ) := by
  classical
  have he (x : α) : pathWeight o x =
      ∑ i : Fin A, if o x = some i then slotWeight o i else 0 := by
    cases hx : o x with
    | none => simp [pathWeight,hx]
    | some j => simp [pathWeight,hx]
  simp only [he]
  rw [Finset.sum_comm]
  have hf (i : Fin A) : (∑ x : α, if o x = some i then slotWeight o i else 0) = 1 := by
    rw [← Finset.sum_filter]
    change (∑ _x ∈ cycleFiber o i, slotWeight o i) = 1
    simp only [Finset.sum_const,nsmul_eq_mul,slotWeight]
    exact mul_one_div_cancel (by exact_mod_cast (Finset.card_pos.mpr (hn i)).ne')
  simp only [hf,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]

lemma withinWeight_sum_bound (o : α → Option (Fin A))
    (hn : ∀ i, (cycleFiber o i).Nonempty) (b : ι → Bool) :
    (∑ s : ι, withinWeight o (R.users b s).1 (R.users b s).2) ≤
      ∑ i : Fin A, Real.log (cycleFiber o i).card / (2 * Real.log 2) := by
  classical
  have he (u v : α) : withinWeight o u v =
      ∑ i : Fin A, (if u ∈ cycleFiber o i ∧ v ∈ cycleFiber o i then (1:ℝ) else 0) * slotWeight o i := by
    simp only [mem_cycleFiber]
    cases hu : o u <;> cases hv : o v <;> simp [withinWeight,hu,hv,ite_and,eq_comm]
  simp only [he]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro i _
  rw [← Finset.sum_mul]
  have hi := R.entropy b (cycleFiber o i)
  have hpos : (0:ℝ) < (cycleFiber o i).card := by exact_mod_cast Finset.card_pos.mpr (hn i)
  have hmul := mul_le_mul_of_nonneg_right hi (show 0 ≤ slotWeight o i by unfold slotWeight; positivity)
  calc
    _ ≤ ((cycleFiber o i).card : ℝ) * Real.log (cycleFiber o i).card /
        (2 * Real.log 2) * slotWeight o i := hmul
    _ = _ := by unfold slotWeight; field_simp

lemma rotationCharge_mean_bound {o : α → Option (Fin A)}
    [∀ i : Fin A, Nonempty {x : α // o x = some i}]
    (hm : Monotone (fun i => (cycleFiber o i).card)) (b : ι → Bool) :
    finiteMean (rotationCharge R o b) ≤ (A:ℝ) * d / 2 +
      ∑ i : Fin A, Real.log (cycleFiber o i).card / (2 * Real.log 2) := by
  classical
  have hn : ∀ i, (cycleFiber o i).Nonempty := by
    intro i
    obtain ⟨x,hx⟩ := (inferInstance : Nonempty {x : α // o x = some i})
    exact ⟨x,mem_cycleFiber _ _ _ |>.mpr hx⟩
  unfold rotationCharge
  rw [finiteMean_sum]
  simp only [rotationMeeting_mean hm,Finset.sum_add_distrib]
  have h₁ := weighted_switch_min_bound R b (pathWeight o)
  rw [pathWeight_sum o hn] at h₁
  have h₂ := withinWeight_sum_bound R o hn b
  linarith

lemma rotation_exp_bound {o : α → Option (Fin A)}
    [∀ i : Fin A, Nonempty {x : α // o x = some i}]
    (hm : Monotone (fun i => (cycleFiber o i).card)) (b : ι → Bool) :
    Real.exp (-Real.log 2 * ((A:ℝ)*d/2 +
      ∑ i : Fin A, Real.log (cycleFiber o i).card / (2 * Real.log 2))) ≤
      finiteMean (fun z : Terminal o => Real.exp (-Real.log 2 * rotationCharge R o b z)) := by
  have hb := rotationCharge_mean_bound R hm b
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hm' : -Real.log 2 * ((A:ℝ)*d/2 +
      ∑ i : Fin A, Real.log (cycleFiber o i).card / (2 * Real.log 2)) ≤
      finiteMean (fun z : Terminal o => -Real.log 2 * rotationCharge R o b z) := by
    have he := finiteMean_mul_const (rotationCharge R o b) (-Real.log 2)
    simp only [mul_comm] at he
    rw [he]
    exact mul_le_mul_of_nonpos_left hb (neg_nonpos.mpr hlog)
  exact (Real.exp_le_exp.mpr hm').trans (exp_finiteMean_le _)

end Rotation

namespace QueryTree
open Thorp.QueryTree

lemma seekCycle_raw_charge (S : Finset (α)) (a : α) (r : ℕ)
    (x : α) (V : Finset (α)) (k : Finset (α) → QueryTree (ι))
    (ω : ι → Bool) (K : ℕ)
    (hK : ∀ V, (k V).succeeds ω = true → (k V).charge ω = K)
    (hs : (seekCycle R S a r x V k).succeeds ω = true) :
    (seekCycle R S a r x V k).charge ω = K + d := by
  induction r generalizing x V with
  | zero =>
    by_cases hv : x ∈ S ∧ x ∉ V
    · rw [seekCycle,ite_eq_left hv,R.close_succeeds] at hs
      split_ifs at hs with he
      · rw [seekCycle,ite_eq_left hv,R.close_raw_charge _ _ _ _ he,hK _ hs]
    · simp [seekCycle,hv,Thorp.QueryTree.succeeds] at hs
  | succ r ih =>
    by_cases hv : x ∈ S ∧ x ∉ V
    · rw [seekCycle,ite_eq_left hv,R.follow_succeeds] at hs
      rw [seekCycle,ite_eq_left hv,R.follow_raw_charge]
      exact ih _ _ hs
    · simp [seekCycle,hv,Thorp.QueryTree.succeeds] at hs

lemma seekCycles_raw_charge (S : Finset (α)) (L : List (α × ℕ))
    (V : Finset (α)) (ω : ι → Bool)
    (hs : (seekCycles R S L V).succeeds ω = true) :
    (seekCycles R S L V).charge ω = L.length * d := by
  induction L generalizing V with
  | nil => simp [seekCycles,charge]
  | cons ar L ih =>
    obtain ⟨a,r⟩ := ar
    rw [seekCycles]
    rw [seekCycle_raw_charge R S a r a V (fun V => seekCycles R S L V) ω (L.length*d)
      (fun V hs => ih V hs) hs]
    simp [Nat.add_mul]

lemma cycles_weighted_success (S : Finset (α)) (L : List (α × ℕ)) :
    finiteMean (fun ω : ι → Bool =>
      if (seekCycles R S L ∅).succeeds ω then
        ((2:ℝ)^d)^L.length / (2:ℝ)^(seekCycles R S L ∅).staleCharge ∅ ω else 0) ≤ 1 := by
  let T := seekCycles R S L ∅
  have hh := mean_freshCharge_le_one T
  have he : finiteMean (fun ω : ι → Bool =>
      if T.succeeds ω then (2:ℝ)^T.freshCharge ∅ ω else 0) =
      finiteMean (fun ω : ι → Bool =>
        if T.succeeds ω then ((2:ℝ)^d)^L.length / (2:ℝ)^T.staleCharge ∅ ω else 0) := by
    apply finiteMean_congr
    intro ω
    cases hs : T.succeeds ω
    · simp
    · simp only [↓reduceIte]
      have hc := fresh_add_stale T ∅ ω
      rw [seekCycles_raw_charge R S L ∅ ω hs] at hc
      have hp : ((2:ℝ)^d)^L.length = (2:ℝ)^T.freshCharge ∅ ω * (2:ℝ)^T.staleCharge ∅ ω := by
        rw [←pow_add,hc,←pow_mul,Nat.mul_comm]
      rw [hp,mul_div_cancel_right₀ _ (pow_ne_zero _ (by norm_num))]
  rw [← he]
  exact hh

end QueryTree

lemma exposedPaths_insert (b : ι → Bool) (V : Finset (α)) (x : α) :
    exposedPaths R b (insert x V) = exposedPaths R b V ∪ R.path b x := by
  classical
  simp [exposedPaths,Finset.union_comm]

namespace QueryTree
open Thorp.QueryTree

lemma seekCycle_semantics (S : Finset (α)) (a : α) (r : ℕ)
    (x : α) (V W : Finset (α)) (z : α)
    (k : Finset (α) → QueryTree (ι)) (ω : ι → Bool)
    (h : cycleTrace (R.perm ω) S a r x V = some (W,z)) :
    (seekCycle R S a r x V k).succeeds ω = (k W).succeeds ω ∧
      (seekCycle R S a r x V k).staleCharge (exposedPaths R (ω) V) ω =
        (k W).staleCharge (exposedPaths R (ω) W) ω +
          terminalCharge R (ω) z (W.erase z) := by
  classical
  induction r generalizing x V with
  | zero =>
    simp only [cycleTrace] at h
    split_ifs at h with hv
    obtain ⟨hxS,hxV,hxa⟩ := hv
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj h)
    simp only [seekCycle,ite_eq_left (show x ∈ S ∧ x ∉ V from ⟨hxS,hxV⟩),R.close_succeeds,ite_eq_left hxa]
    constructor
    · trivial
    · rw [R.close_stale_charge _ _ _ _ _ hxa,exposedPaths_insert,
        Finset.erase_insert hxV]
      simp only [terminalCharge]
  | succ r ih =>
    simp only [cycleTrace] at h
    split_ifs at h with hv
    obtain ⟨hxS,hxV⟩ := hv
    rw [seekCycle,ite_eq_left ⟨hxS,hxV⟩,R.follow_succeeds,R.follow_stale_charge]
    rw [← exposedPaths_insert]
    exact ih _ _ h

lemma seekCycle_orbit (S V : Finset (α)) (z : α)
    (k : Finset (α) → QueryTree (ι)) (ω : ι → Bool)
    (hS : orbitSet (R.perm ω) z ⊆ S)
    (hV : Disjoint V (orbitSet (R.perm ω) z)) :
    let p := R.perm ω
    let W := V ∪ orbitSet p z
    (seekCycle R S (p z) (Function.minimalPeriod p z-1) (p z) V k).succeeds ω = (k W).succeeds ω ∧
      (seekCycle R S (p z) (Function.minimalPeriod p z-1) (p z) V k).staleCharge
          (exposedPaths R (ω) V) ω =
        (k W).staleCharge (exposedPaths R (ω) W) ω +
          terminalCharge R (ω) z (W.erase z) := by
  exact seekCycle_semantics _ _ _ _ _ _ _ _ _ _ (cycleTrace_orbit _ _ _ _ hS hV)

end QueryTree

end RoutingNetwork
end Thorp

end ThorpNine.Adaptive

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Adaptive_PriorPaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Adaptive

namespace Thorp
open scoped BigOperators
open Filter
namespace RoutingNetwork
variable {α ι : Type*} [Fintype α] [DecidableEq α] [Fintype ι] [DecidableEq ι]
  {d : ℕ} (R : RoutingNetwork α ι d)
lemma mem_exposedPaths (b : ι → Bool) (V : Finset (α)) (s : ι) :
    s ∈ exposedPaths R b V ↔ (R.users b s).1 ∈ V ∨ (R.users b s).2 ∈ V := by
  classical
  simp only [exposedPaths,Finset.mem_biUnion,R.mem_path]
  constructor
  · rintro ⟨x,hx,h | h⟩
    · exact Or.inl (h ▸ hx)
    · exact Or.inr (h ▸ hx)
  · rintro (h | h)
    · exact ⟨_,h,Or.inl rfl⟩
    · exact ⟨_,h,Or.inr rfl⟩

lemma terminalCharge_sum (b : ι → Bool) (z : α) (V : Finset (α))
    (hz : z ∉ V) :
    (terminalCharge R b z V : ℝ) = ∑ s : ι,
      ((if (R.users b s).1 = z ∧ (R.users b s).2 ∈ V then (1:ℝ) else 0) +
      (if (R.users b s).2 = z ∧ (R.users b s).1 ∈ V then (1:ℝ) else 0)) := by
  classical
  have he : R.path b z ∩ exposedPaths R b V =
      Finset.univ.filter (fun s =>
        ((R.users b s).1 = z ∧ (R.users b s).2 ∈ V) ∨
        ((R.users b s).2 = z ∧ (R.users b s).1 ∈ V)) := by
    ext s
    simp only [Finset.mem_inter,R.mem_path,mem_exposedPaths,
      Finset.mem_filter,Finset.mem_univ,true_and]
    by_cases h₁ : (R.users b s).1 = z <;>
      by_cases h₂ : (R.users b s).2 = z <;> simp [h₁,h₂,hz]
  rw [terminalCharge,he]
  simp only [← Finset.sum_boole]
  apply Finset.sum_congr rfl
  intro s _
  by_cases h₁ : (R.users b s).1 = z <;>
    by_cases h₂ : (R.users b s).2 = z <;> simp [h₁,h₂,hz]

lemma terminalCharge_prior_sum {A : ℕ} (o : α → Option (Fin A))
    (b : ι → Bool) (z : Terminal o) (i : Fin A) :
    (terminalCharge R b (z i).val ((priorPaths o (i.val+1)).erase (z i).val) : ℝ) =
      ∑ s : ι,
        ((if (z i).val = (R.users b s).1 ∧ (R.users b s).2 ∈ priorPaths o (i.val+1)
          then (1:ℝ) else 0) +
        (if (z i).val = (R.users b s).2 ∧ (R.users b s).1 ∈ priorPaths o (i.val+1)
          then (1:ℝ) else 0)) := by
  classical
  rw [terminalCharge_sum _ _ _ _ (Finset.notMem_erase _ _)]
  apply Finset.sum_congr rfl
  intro s _
  have hn := R.users_ne b s
  simp only [Finset.mem_erase]
  by_cases h₁ : (z i).val = (R.users b s).1 <;>
    by_cases h₂ : (z i).val = (R.users b s).2 <;> simp_all [eq_comm]

lemma rotationMeeting_eq_slot_sum {A : ℕ} (o : α → Option (Fin A))
    (z : Terminal o) (u v : α) :
    rotationMeeting o z u v = ∑ i : Fin A,
      ((if (z i).val = u ∧ v ∈ priorPaths o (i.val+1) then (1:ℝ) else 0) +
      (if (z i).val = v ∧ u ∈ priorPaths o (i.val+1) then (1:ℝ) else 0)) := by
  classical
  have only_owner (u : α) (a : Fin A) (hou : o u = some a)
      (i : Fin A) (hia : i ≠ a) : (z i).val ≠ u := by
    intro h
    have hi := (z i).property
    rw [h,hou] at hi
    exact hia (Option.some.inj hi).symm
  have sum_one (u v : α) (a : Fin A) (hou : o u = some a) :
      (∑ i : Fin A, if (z i).val = u ∧ v ∈ priorPaths o (i.val+1) then (1:ℝ) else 0) =
      if (z a).val = u ∧ v ∈ priorPaths o (a.val+1) then 1 else 0 := by
    apply Finset.sum_eq_single a
    · intro i _ hia
      simp [only_owner u a hou i hia]
    · simp
  have sum_none (u v : α) (hou : o u = none) :
      (∑ i : Fin A, if (z i).val = u ∧ v ∈ priorPaths o (i.val+1) then (1:ℝ) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have hn : (z i).val ≠ u := by
      intro h
      have hi := (z i).property
      rw [h,hou] at hi
      contradiction
    simp [hn]
  rw [Finset.sum_add_distrib]
  cases hou : o u with
  | none =>
    rw [sum_none u v hou]
    simp [rotationMeeting,hou,mem_priorPaths]
  | some a =>
    rw [sum_one u v a hou]
    cases hov : o v with
    | none =>
      rw [sum_none v u hov]
      simp [rotationMeeting,hou,hov,mem_priorPaths]
    | some b =>
      rw [sum_one v u b hov]
      simp only [rotationMeeting,hou,hov,mem_priorPaths,Option.some.injEq]
      rcases lt_trichotomy a b with hab | rfl | hba
      · have hn : ¬ b.val < a.val+1 := by omega
        have hy : a.val < b.val+1 := by omega
        simp [hab,hn,hy]
      · simp
      · have hn : ¬ a.val < b.val+1 := by omega
        have hy : b.val < a.val+1 := by omega
        simp [hba,not_lt_of_ge (le_of_lt hba),hn,hy]

lemma rotationCharge_eq_terminal_sum {A : ℕ} (o : α → Option (Fin A))
    (b : ι → Bool) (z : Terminal o) :
    rotationCharge R o b z = ∑ i : Fin A,
      (terminalCharge R b (z i).val ((priorPaths o (i.val+1)).erase (z i).val) : ℝ) := by
  simp only [rotationCharge,rotationMeeting_eq_slot_sum,terminalCharge_prior_sum]
  exact Finset.sum_comm

lemma priorPaths_succ {A : ℕ} (o : α → Option (Fin A)) (t : ℕ) (ht : t < A) :
    priorPaths o (t+1) = priorPaths o t ∪ cycleFiber o ⟨t,ht⟩ := by
  classical
  ext x
  simp only [mem_priorPaths,Finset.mem_union,mem_cycleFiber]
  constructor
  · rintro ⟨i,hi,hit⟩
    by_cases h : i.val < t
    · exact Or.inl ⟨i,hi,h⟩
    · have he : i = ⟨t,ht⟩ := Fin.ext (by change i.val = t; omega)
      exact Or.inr (he ▸ hi)
  · rintro (⟨i,hi,hit⟩ | hi)
    · exact ⟨i,hi,by omega⟩
    · exact ⟨⟨t,ht⟩,hi,by change t < t+1; omega⟩

omit [DecidableEq α] in
lemma priorPaths_disjoint {A : ℕ} (o : α → Option (Fin A)) (i : Fin A) :
    Disjoint (priorPaths o i.val) (cycleFiber o i) := by
  classical
  apply Finset.disjoint_left.mpr
  intro x hx hx'
  obtain ⟨j,hj,hji⟩ := (mem_priorPaths _ _ _).mp hx
  have he : j = i := Option.some.inj (hj.symm.trans ((mem_cycleFiber _ _ _).mp hx'))
  subst j
  exact (lt_irrefl _ hji)

namespace QueryTree
open Thorp.QueryTree

lemma seekCycles_owned {A : ℕ} (S : Finset (α)) (r : Fin A → ℕ)
    (o : α → Option (Fin A)) (z : Terminal o) (ω : ι → Bool)
    (hS : ∀ i, cycleFiber o i ⊆ S)
    (hO : ∀ i, orbitSet (R.perm ω) (z i).val = cycleFiber o i)
    (hC : ∀ i, (cycleFiber o i).card = r i+1) :
    let p := R.perm ω
    let L := List.ofFn (fun i : Fin A => (p (z i).val,r i))
    (seekCycles R S L ∅).succeeds ω = true ∧
      ((seekCycles R S L ∅).staleCharge ∅ ω : ℝ) = rotationCharge R o (ω) z := by
  classical
  let b := ω
  let p := R.perm b
  let f (i : Fin A) := (p (z i).val,r i)
  let c (i : Fin A) : ℝ := terminalCharge R b (z i).val ((priorPaths o (i.val+1)).erase (z i).val)
  have hc (i : Fin A) : Function.minimalPeriod p (z i).val - 1 = r i := by
    have he := orbitSet_card p (z i).val
    rw [hO,hC] at he
    omega
  have hs (t : ℕ) (ht : t ≤ A) :
      (seekCycles R S ((List.ofFn f).drop t) (priorPaths o t)).succeeds ω = true ∧
        ((seekCycles R S ((List.ofFn f).drop t) (priorPaths o t)).staleCharge (exposedPaths R b (priorPaths o t)) ω : ℝ) =
          ((List.ofFn c).drop t).sum := by
    induction ht using Nat.decreasingInduction with
    | self => simp only [List.length_ofFn,le_refl,List.drop_eq_nil_of_le,List.sum_nil,seekCycles,Thorp.QueryTree.succeeds,staleCharge,Nat.cast_zero,and_self]
    | of_succ t ht ih =>
      have htf : t < (List.ofFn f).length := by simpa using ht
      have htc : t < (List.ofFn c).length := by simpa using ht
      rw [List.drop_eq_getElem_cons htf,List.drop_eq_getElem_cons htc]
      simp only [List.getElem_ofFn,List.sum_cons,seekCycles]
      have h := seekCycle_orbit R S (priorPaths o t) (z ⟨t,ht⟩).val
        (fun V => seekCycles R S ((List.ofFn f).drop (t+1)) V) ω
        (by rw [hO]; exact hS _) (by rw [hO]; exact priorPaths_disjoint o ⟨t,ht⟩)
      dsimp only at h
      rw [hc,hO,←priorPaths_succ o t ht] at h
      dsimp only [f]
      constructor
      · exact h.1.trans ih.1
      · rw [h.2,Nat.cast_add,ih.2]
        exact add_comm _ _
  have h := hs 0 (Nat.zero_le _)
  simp only [List.drop_zero,priorPaths_zero,exposedPaths_empty,List.sum_ofFn] at h
  dsimp only
  exact ⟨h.1,h.2.trans (rotationCharge_eq_terminal_sum R o b z).symm⟩

end QueryTree
section Collections
variable {A : ℕ}

lemma rootedStart_injective {p : Equiv.Perm (α)} {S : Finset (α)} {r : Fin A → ℕ} :
    Function.Injective (rootedStart (p:=p) (S:=S) (r:=r)) := by
  rintro ⟨c,z⟩ ⟨c',z'⟩ h
  have hz (i : Fin A) : (z i).val = (z' i).val :=
    p.injective (congrArg Subtype.val (congrFun h i))
  have hc : c = c' := Subtype.ext (owner_ext (fun i => by
    rw [←c.property.2.2 i (z i).val (z i).property,
      ←c'.property.2.2 i (z' i).val (z' i).property,hz]))
  subst c'
  have hzz : z = z' := funext (fun i => Subtype.ext (hz i))
  subst z'
  rfl

lemma rooted_weight_sum_le (S : Finset (α)) (r : Fin A → ℕ) (ω : ι → Bool) :
    (∑ c : RootedSlots (R.perm ω) S r,
      ((2:ℝ)^d)^A * Real.exp (-Real.log 2 * rotationCharge R c.1.val (ω) c.2)) ≤
    ∑ a : Fin A → S,
      if (QueryTree.seekCycles R S (List.ofFn (fun i => ((a i).val,r i))) ∅).succeeds ω then
        ((2:ℝ)^d)^A / (2:ℝ)^(QueryTree.seekCycles R S (List.ofFn (fun i => ((a i).val,r i))) ∅).staleCharge ∅ ω
      else 0 := by
  classical
  let p := R.perm ω
  let g (a : Fin A → S) : ℝ :=
    if (QueryTree.seekCycles R S (List.ofFn (fun i => ((a i).val,r i))) ∅).succeeds ω then
      ((2:ℝ)^d)^A / (2:ℝ)^(QueryTree.seekCycles R S (List.ofFn (fun i => ((a i).val,r i))) ∅).staleCharge ∅ ω
    else 0
  have he (c : RootedSlots p S r) :
      ((2:ℝ)^d)^A * Real.exp (-Real.log 2 * rotationCharge R c.1.val (ω) c.2) =
      g (rootedStart c) := by
    have hs := QueryTree.seekCycles_owned R S r c.1.val c.2 ω c.1.property.2.1
      (fun i => c.1.property.2.2 i (c.2 i).val (c.2 i).property) c.1.property.1
    dsimp only at hs
    unfold g
    rw [ite_eq_left (show (QueryTree.seekCycles R S (List.ofFn (fun i => ((rootedStart c i).val,r i))) ∅).succeeds ω = true from hs.1)]
    rw [← hs.2,neg_mul,Real.exp_neg,mul_comm (Real.log 2),Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<2)]
    rfl
  simp_rw [he]
  exact sum_comp_injective_le rootedStart rootedStart_injective g (fun a => by dsimp [g]; split_ifs <;> positivity)

lemma collection_rotation_lower (S : Finset (α)) (r : Fin A → ℕ) (hr : Monotone r)
    (ω : ι → Bool) (c : CycleSlots (R.perm ω) S r) :
    collectionWeight d r ≤ ∑ z : Terminal c.val,
      ((2:ℝ)^d)^A * Real.exp (-Real.log 2 * rotationCharge R c.val (ω) z) := by
  classical
  let (i : Fin A) : Nonempty {x : α // c.val x = some i} := c.terminal_nonempty i
  have hm : Monotone (fun i => (cycleFiber c.val i).card) := by
    intro i j hij
    dsimp only
    rw [c.property.1,c.property.1]
    exact Nat.add_le_add_right (hr hij) 1
  have hb := rotation_exp_bound R hm (ω)
  have hcard : (Fintype.card (Terminal c.val) : ℝ) = ∏ i : Fin A, (r i+1 : ℝ) := by
    rw [Fintype.card_pi,Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro i _
    rw [card_cycleFiber,c.property.1,Nat.cast_add,Nat.cast_one]
  have hp : (0:ℝ) < Fintype.card (Terminal c.val) := Nat.cast_pos.mpr Fintype.card_pos
  have hl : rotationLower d r ≤ finiteMean (fun z : Terminal c.val => Real.exp (-Real.log 2 * rotationCharge R c.val (ω) z)) := by
    simpa only [rotationLower,c.property.1,Nat.cast_add,Nat.cast_one] using hb
  have hh := (le_div_iff₀ hp).mp hl
  rw [hcard] at hh
  unfold collectionWeight
  rw [← Finset.mul_sum]
  calc
    _ = ((2:ℝ)^d)^A * (rotationLower d r * ∏ i : Fin A, (r i+1 : ℝ)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hh (by positivity)

lemma cycleSlots_weighted_moment (S : Finset (α)) (r : Fin A → ℕ) (hr : Monotone r) :
    finiteMean (fun ω : ι → Bool =>
      (Fintype.card (CycleSlots (R.perm ω) S r) : ℝ)) *
      collectionWeight d r ≤ (S.card : ℝ)^A := by
  classical
  let g (a : Fin A → S) (ω : ι → Bool) : ℝ :=
    if (QueryTree.seekCycles R S (List.ofFn (fun i => ((a i).val,r i))) ∅).succeeds ω then
      ((2:ℝ)^d)^A / (2:ℝ)^(QueryTree.seekCycles R S (List.ofFn (fun i => ((a i).val,r i))) ∅).staleCharge ∅ ω
    else 0
  have hω (ω : ι → Bool) :
      (Fintype.card (CycleSlots (R.perm ω) S r) : ℝ) * collectionWeight d r ≤
        ∑ a : Fin A → S, g a ω := by
    calc
      _ = ∑ _c : CycleSlots (R.perm ω) S r, collectionWeight d r := by simp
      _ ≤ ∑ c : CycleSlots (R.perm ω) S r,
          ∑ z : Terminal c.val, ((2:ℝ)^d)^A * Real.exp (-Real.log 2 * rotationCharge R c.val (ω) z) :=
        Finset.sum_le_sum (fun c _ => collection_rotation_lower R S r hr ω c)
      _ = ∑ c : RootedSlots (R.perm ω) S r,
          ((2:ℝ)^d)^A * Real.exp (-Real.log 2 * rotationCharge R c.1.val (ω) c.2) :=
        (Fintype.sum_sigma (fun c : RootedSlots (R.perm ω) S r =>
          ((2:ℝ)^d)^A * Real.exp (-Real.log 2 * rotationCharge R c.1.val (ω) c.2))).symm
      _ ≤ _ := rooted_weight_sum_le R S r ω
  have hb := finiteMean_mono hω
  rw [finiteMean_mul_const,finiteMean_sum] at hb
  calc
    _ ≤ ∑ a : Fin A → S, finiteMean (g a) := hb
    _ ≤ ∑ _a : Fin A → S, (1:ℝ) := by
      apply Finset.sum_le_sum
      intro a _
      have hh := QueryTree.cycles_weighted_success R S (List.ofFn (fun i : Fin A => ((a i).val,r i)))
      simpa only [List.length_ofFn] using hh
    _ = _ := by simp

lemma cycleSlots_moment (S : Finset (α)) (r : Fin A → ℕ) (hr : Monotone r) :
    finiteMean (fun ω : ι → Bool =>
      (Fintype.card (CycleSlots (R.perm ω) S r) : ℝ)) ≤
        (S.card : ℝ)^A / collectionWeight d r := by
  exact (le_div_iff₀ (collectionWeight_pos d r)).mpr (cycleSlots_weighted_moment R S r hr)

lemma butterfly_cycleSlots_moment (S : Finset (α)) (r : Fin A → ℕ) (hr : Monotone r) :
    finiteMean (fun ω : ι → Bool =>
      (Fintype.card (CycleSlots (R.perm ω) S r) : ℝ)) ≤
        ((S.card : ℝ) / Real.sqrt ((2:ℝ)^d))^A *
          ∏ i : Fin A, (1 / Real.sqrt (r i+1)) := by
  have h := cycleSlots_moment R S r hr
  rw [collectionWeight_eq_sqrt,div_mul_eq_div_mul_one_div] at h
  rw [div_pow]
  simpa only [one_div,Finset.prod_inv_distrib] using h

end Collections

section AllLengths
variable {A : ℕ}

lemma card_cycleSlots_relabel (p : Equiv.Perm (α)) (S : Finset (α))
    (r : Fin A → ℕ) (e : Equiv.Perm (Fin A)) :
    Fintype.card (CycleSlots p S r) = Fintype.card (CycleSlots p S (r ∘ e)) := by
  exact Fintype.card_congr ((cycleSlotsEquivAssignments p S r).trans
    ((assignmentRelabel p S r e).trans (cycleSlotsEquivAssignments p S (r ∘ e)).symm))

lemma butterfly_cycleSlots_moment_all (S : Finset (α)) (r : Fin A → ℕ) :
    finiteMean (fun ω : ι → Bool =>
      (Fintype.card (CycleSlots (R.perm ω) S r) : ℝ)) ≤
        ((S.card : ℝ) / Real.sqrt ((2:ℝ)^d))^A *
          ∏ i : Fin A, (1 / Real.sqrt (r i+1)) := by
  have h := butterfly_cycleSlots_moment R S (r ∘ Tuple.sort r) (Tuple.monotone_sort r)
  simp_rw [←card_cycleSlots_relabel] at h
  have hp := Equiv.prod_comp (Tuple.sort r) (fun i : Fin A => (1 / Real.sqrt (r i+1) : ℝ))
  simpa only [Function.comp_apply,hp] using h

lemma shortCycle_factorial_eq (p : Equiv.Perm (α)) (S : Finset (α)) (J : ℕ) :
    (Fintype.card (ShortCycle p S J)).descFactorial A =
      ∑ r : Fin A → Fin J, Fintype.card (CycleSlots p S (fun i => (r i : ℕ))) := by
  classical
  have hc := Fintype.card_embedding_eq (α := Fin A) (β := ShortCycle p S J)
  simp only [Fintype.card_fin] at hc
  rw [←hc, Fintype.card_congr (shortEmbeddingEquiv p S J),Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro r _
  exact (Fintype.card_congr (cycleSlotsEquivAssignments p S (fun i => (r i : ℕ)))).symm

end AllLengths

section CycleMGF

lemma butterfly_shortCycle_moment (S : Finset (α)) (J A : ℕ) :
    finiteMean (fun ω : ι → Bool =>
      ((Fintype.card (ShortCycle (R.perm ω) S J)).descFactorial A : ℝ)) ≤
      ((S.card : ℝ) / Real.sqrt ((2:ℝ)^d) * ∑ j : Fin J, 1 / Real.sqrt ((j:ℕ)+1))^A := by
  classical
  simp_rw [shortCycle_factorial_eq,Nat.cast_sum,finiteMean_sum]
  calc
    _ ≤ ∑ r : Fin A → Fin J,
        ((S.card : ℝ) / Real.sqrt ((2:ℝ)^d))^A *
          ∏ i : Fin A, (1 / Real.sqrt ((r i : ℕ)+1)) := by
      apply Finset.sum_le_sum
      intro r _
      exact butterfly_cycleSlots_moment_all R S (fun i => (r i : ℕ))
    _ = _ := by
      rw [←Finset.mul_sum,mul_pow]
      congr 1
      rw [←Fintype.prod_sum (fun (_ : Fin A) (j : Fin J) => (1 / Real.sqrt ((j:ℕ)+1) : ℝ))]
      simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]

lemma cycleMass_le (p : Equiv.Perm (α)) (S : Finset (α)) : cycleMass p S ≤ S.card := by
  classical
  let f : (Σ C : SelectedCycle p S, {x : α // x ∈ C.val}) → S :=
    fun c => ⟨c.2.val,c.1.property.2 c.2.property⟩
  have hi : Function.Injective f := by
    intro c e h
    have hx : c.2.val = e.2.val := congrArg Subtype.val h
    have hC : c.1 = e.1 := c.1.eq_of_mem e.1 c.2.property (hx ▸ e.2.property)
    rcases c with ⟨c,x⟩
    rcases e with ⟨e,y⟩
    dsimp only at hC
    subst e
    have he : x=y := Subtype.ext hx
    cases he
    rfl
  have hh := Fintype.card_le_of_injective f hi
  simpa only [Fintype.card_sigma,Fintype.card_coe,cycleMass] using hh

lemma shortCycle_card_le (p : Equiv.Perm (α)) (S : Finset (α)) (J : ℕ) :
    Fintype.card (ShortCycle p S J) ≤ S.card := by
  classical
  calc
    _ ≤ Fintype.card (SelectedCycle p S) := Fintype.card_subtype_le _
    _ = ∑ _ : SelectedCycle p S, 1 := by simp
    _ ≤ cycleMass p S := Finset.sum_le_sum (fun C _ => C.nonempty.card_pos)
    _ ≤ _ := cycleMass_le p S

lemma butterfly_shortCycle_mgf (S : Finset (α)) (J : ℕ) (q : ℝ) (hq : 1 ≤ q) :
    finiteMean (fun ω : ι → Bool =>
      q^(Fintype.card (ShortCycle (R.perm ω) S J))) ≤
      Real.exp ((q-1)*((S.card : ℝ) / Real.sqrt ((2:ℝ)^d) * ∑ j : Fin J, 1 / Real.sqrt ((j:ℕ)+1))) := by
  apply factorial_mgf _ S.card _ q (fun ω => shortCycle_card_le _ _ _)
  · positivity
  · exact hq
  · exact butterfly_shortCycle_moment R S J

end CycleMGF


lemma selectedCycle_card_split (p : Equiv.Perm (α)) (S : Finset (α)) (J : ℕ) :
    Fintype.card (SelectedCycle p S) =
      Fintype.card (ShortCycle p S J) + Fintype.card (LongCycle p S J) := by
  classical
  rw [←Fintype.card_congr (Equiv.sumCompl (fun C : SelectedCycle p S => C.val.card ≤ J)),Fintype.card_sum]

lemma longCycle_card_bound (p : Equiv.Perm (α)) (S : Finset (α)) (J : ℕ) :
    J * Fintype.card (LongCycle p S J) ≤ S.card := by
  classical
  have hs := Equiv.sum_comp (Equiv.sumCompl (fun C : SelectedCycle p S => C.val.card ≤ J))
    (fun C : SelectedCycle p S => C.val.card)
  rw [Fintype.sum_sum_type] at hs
  have h0 : J * Fintype.card (LongCycle p S J) ≤
      ∑ C : LongCycle p S J, C.val.val.card := by
    calc
      _ = ∑ _C : LongCycle p S J, J := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum (fun C _ => Nat.le_of_lt (Nat.lt_of_not_ge C.property))
  have hh := cycleMass_le p S
  unfold cycleMass at hh
  rw [←hs] at hh
  exact h0.trans ((Nat.le_add_left _ _).trans hh)

lemma longCycle_pow_bound (p : Equiv.Perm (α)) (S : Finset (α))
    (J : ℕ) (hJ : 0 < J) (q : ℝ) (hq : 1 ≤ q) :
    q^(Fintype.card (LongCycle p S J)) ≤ Real.exp ((S.card : ℝ)/J * Real.log q) := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hc : (Fintype.card (LongCycle p S J) : ℝ) ≤ (S.card : ℝ)/J := by
    apply (le_div_iff₀ (by exact_mod_cast hJ)).mpr
    have hh := longCycle_card_bound p S J
    exact_mod_cast (by simpa only [mul_comm] using hh)
  calc
    _ = Real.exp ((Fintype.card (LongCycle p S J) : ℝ)*Real.log q) := by
      rw [Real.exp_nat_mul,Real.exp_log hq0]
    _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hc (Real.log_nonneg hq))

lemma butterfly_cycle_log_mgf (S : Finset (α)) (J : ℕ) (hJ : 0 < J)
    (q : ℝ) (hq : 1 ≤ q) :
    Real.log (finiteMean (fun ω : ι → Bool =>
      q^(Fintype.card (SelectedCycle (R.perm ω) S)))) ≤
      (S.card : ℝ)/J * Real.log q + 2*q*S.card*Real.sqrt J / Real.sqrt ((2:ℝ)^d) := by
  let lam : ℝ := (S.card : ℝ)/Real.sqrt ((2:ℝ)^d) * ∑ j : Fin J, 1 / Real.sqrt ((j:ℕ)+1)
  let c : ℝ := (S.card : ℝ)/J * Real.log q
  have hnum : (q-1)*lam ≤ 2*q*S.card*Real.sqrt J / Real.sqrt ((2:ℝ)^d) := by
    have hsum := sum_inv_sqrt J
    have hp : 0 ≤ (S.card : ℝ)/Real.sqrt ((2:ℝ)^d) := by positivity
    have h0 : 0 ≤ 2*Real.sqrt J := by positivity
    have hh := mul_le_mul_of_nonneg_left hsum hp
    have hq1 : 0 ≤ q-1 := sub_nonneg.mpr hq
    calc
      _ ≤ (q-1)*((S.card : ℝ)/Real.sqrt ((2:ℝ)^d)*(2*Real.sqrt J)) :=
        mul_le_mul_of_nonneg_left hh hq1
      _ ≤ q*((S.card : ℝ)/Real.sqrt ((2:ℝ)^d)*(2*Real.sqrt J)) :=
        mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hp h0)
      _ = _ := by ring
  have hm : finiteMean (fun ω : ι → Bool =>
      q^(Fintype.card (SelectedCycle (R.perm ω) S))) ≤
      Real.exp (c+(q-1)*lam) := by
    calc
      _ ≤ finiteMean (fun ω : ι → Bool =>
          q^(Fintype.card (ShortCycle (R.perm ω) S J))*Real.exp c) := by
        apply finiteMean_mono
        intro ω
        rw [selectedCycle_card_split _ _ J,pow_add]
        exact mul_le_mul_of_nonneg_left (longCycle_pow_bound _ S J hJ q hq) (by positivity)
      _ = finiteMean (fun ω : ι → Bool =>
          q^(Fintype.card (ShortCycle (R.perm ω) S J))) * Real.exp c :=
        finiteMean_mul_const _ _
      _ ≤ Real.exp ((q-1)*lam) * Real.exp c :=
        mul_le_mul_of_nonneg_right (butterfly_shortCycle_mgf R S J q hq) (Real.exp_nonneg _)
      _ = _ := by rw [←Real.exp_add,add_comm]
  have hpos : 0 < finiteMean (fun ω : ι → Bool =>
      q^(Fintype.card (SelectedCycle (R.perm ω) S))) := by
    apply finiteMean_pos
    intro ω
    positivity
  have hlog := Real.log_le_log hpos hm
  rw [Real.log_exp] at hlog
  dsimp [c] at hlog
  linarith


end RoutingNetwork

end Thorp

end ThorpNine.Adaptive

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Adaptive_ParallelFollow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Adaptive

namespace Thorp
open scoped BigOperators
open Filter
section ParallelButterfly
variable {α B : Type*} [Fintype α] [DecidableEq α] [Fintype B] [DecidableEq B] {d : ℕ}

lemma parallel_cycle_log_mgf (pre : α ≃ B × Card d) (post : B × Card d ≃ α)
    (S : Finset α) (J : ℕ) (hJ : 0 < J) (q : ℝ) (hq : 1 ≤ q) :
    Real.log (finiteMean (fun ω : B × SwitchIndex d → Bool =>
      q^(Fintype.card (RoutingNetwork.SelectedCycle (relabeledPerm pre post ω) S)))) ≤
      (S.card : ℝ)/J * Real.log q + 2*q*S.card*Real.sqrt J / Real.sqrt ((2:ℝ)^d) := by
  exact (parallelNetwork pre post).butterfly_cycle_log_mgf S J hJ q hq

end ParallelButterfly

lemma butterfly_split (r s : ℕ) (lo : Card r × SwitchIndex s → Bool)
    (hi : Card s × SwitchIndex r → Bool) (x : Card (s+r)) :
    cardSplit r s (butterflyPerm (s+r) (decodeButterfly (s+r) (assembleBits r s lo hi)) x) =
      let y := cardSplit r s x
      let z := butterflyPerm s (decodeButterfly s (fun i => lo (y.1,i))) y.2
      (butterflyPerm r (decodeButterfly r (fun i => hi (z,i))) y.1,z) := by
  induction r with
  | zero =>
    apply Prod.ext
    · funext i
      exact Fin.elim0 i
    · rfl
  | succ r ih =>
    let lo' : Card r × SwitchIndex s → Bool := fun j => lo (Fin.cons (x 0) j.1,j.2)
    let hi' : Card s × SwitchIndex r → Bool := fun j => hi (j.1,Sum.inr (x 0,j.2))
    have hh := ih lo' hi' (Fin.tail x)
    let u := butterflyPerm (s+r) (decodeButterfly (s+r) (assembleBits r s lo' hi')) (Fin.tail x)
    let y := cardSplit r s (Fin.tail x)
    let z := butterflyPerm s (decodeButterfly s (fun i => lo' (y.1,i))) y.2
    let w := butterflyPerm r (decodeButterfly r (fun i => hi' (z,i))) y.1
    change cardSplit r s u = (w,z) at hh
    change ((Fin.cons (Bool.xor (x 0) (hi ((cardSplit r s u).2,Sum.inl (cardSplit r s u).1)))
        ((cardSplit r s u).1) : Card (r+1)), (cardSplit r s u).2) =
      ((Fin.cons (Bool.xor (x 0) (hi (z,Sum.inl w))) w : Card (r+1)),z)
    rw [hh]

lemma assembleBits_eq (r s : ℕ) (lo : Card r × SwitchIndex s → Bool)
    (hi : Card s × SwitchIndex r → Bool) (i : SwitchIndex (s+r)) :
    assembleBits r s lo hi i = Sum.elim lo hi (splitSwitch r s i) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rcases i with y | ⟨b,j⟩
    · rfl
    · simp only [assembleBits,splitSwitch,Equiv.coe_fn_mk]
      rw [ih]
      cases splitSwitch r s j <;> rfl

lemma splitCoinEquiv_apply (r s : ℕ) (lo : Card r × SwitchIndex s → Bool)
    (hi : Card s × SwitchIndex r → Bool) :
    splitCoinEquiv r s (lo,hi) = assembleBits r s lo hi := by
  funext i
  exact (assembleBits_eq r s lo hi i).symm

lemma finiteMean_prod {Ω Ω' : Type*} [Fintype Ω] [Fintype Ω'] (f : Ω × Ω' → ℝ) :
    finiteMean f = finiteMean (fun x => finiteMean (fun y => f (x,y))) := by
  simp only [finiteMean, Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul,
    ←Finset.sum_div, div_div, mul_comm]

lemma finiteMean_split (r s : ℕ) (f : (SwitchIndex (s+r) → Bool) → ℝ) :
    finiteMean f = finiteMean (fun lo : Card r × SwitchIndex s → Bool =>
      finiteMean (fun hi : Card s × SwitchIndex r → Bool => f (assembleBits r s lo hi))) := by
  rw [finiteMean_equiv (splitCoinEquiv r s).symm]
  simp only [Equiv.symm_symm]
  rw [finiteMean_prod]
  apply finiteMean_congr
  intro lo
  apply finiteMean_congr
  intro hi
  rw [splitCoinEquiv_apply]

section PartiallyExposed
variable {α : Type*} {r s : ℕ}

lemma exposed_perm_eq (pre : α ≃ Card (s+r)) (post : Card (s+r) ≃ α)
    (lo : Card r × SwitchIndex s → Bool) (hi : Card s × SwitchIndex r → Bool) :
    (pre.trans (butterflyPerm (s+r) (decodeButterfly (s+r) (assembleBits r s lo hi)))).trans post =
      relabeledPerm (freshPre pre lo) (freshPost post) hi := by
  ext x
  simpa only [relabeledPerm, freshPre, freshPost, parallelPerm, Equiv.trans_apply,
    Equiv.coe_fn_mk, Equiv.prodComm_apply, Prod.swap, Equiv.symm_apply_apply] using
    congrArg (fun y => post ((cardSplit r s).symm y)) (butterfly_split r s lo hi (pre x))

lemma partially_exposed_cycle_log_mgf [Fintype α] [DecidableEq α]
    (pre : α ≃ Card (s+r)) (post : Card (s+r) ≃ α)
    (lo : Card r × SwitchIndex s → Bool) (S : Finset α)
    (J : ℕ) (hJ : 0 < J) (q : ℝ) (hq : 1 ≤ q) :
    Real.log (finiteMean (fun hi : Card s × SwitchIndex r → Bool =>
      q^(Fintype.card (RoutingNetwork.SelectedCycle
        ((pre.trans (butterflyPerm (s+r)
          (decodeButterfly (s+r) (assembleBits r s lo hi)))).trans post) S)))) ≤
      (S.card : ℝ)/J * Real.log q + 2*q*S.card*Real.sqrt J / Real.sqrt ((2:ℝ)^r) := by
  simp only [exposed_perm_eq]
  exact parallel_cycle_log_mgf (freshPre pre lo) (freshPost post) S J hJ q hq

end PartiallyExposed

lemma inclusionMoment_eq {α Ω : Type*} [DecidableEq α] [Fintype Ω]
    (F : Ω → Finset α) (S : Finset α) :
    inclusionMoment F S = finiteMean (fun ω => if S ⊆ F ω then (1:ℝ) else 0) := by
  unfold inclusionMoment
  apply finiteMean_congr
  intro ω
  split_ifs <;> rfl

lemma finiteMean_bool (f : Bool → ℝ) : finiteMean f = (f false+f true)/2 := by
  simp only [finiteMean, Fintype.sum_bool, Fintype.card_bool, Nat.cast_ofNat]
  ring

lemma finiteMean_pi_prod {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : ι → Type*}
    [∀ i, Fintype (Ω i)] (f : (i : ι) → Ω i → ℝ) :
    finiteMean (fun ω : (i : ι) → Ω i => ∏ i, f i (ω i)) = ∏ i, finiteMean (f i) := by
  simp only [finiteMean,←Fintype.prod_sum,Fintype.card_pi,Nat.cast_prod,Finset.prod_div_distrib]

section ParallelFairLayer
variable {β : Type*} [Fintype β] [DecidableEq β]

lemma prod_pairFiber (S : Finset (Bool × β)) (f : Bool × β → ℝ) :
    (∏ x ∈ S, f x) = ∏ b : β, ∏ ε ∈ pairFiber S b, f (ε,b) := by
  classical
  simp only [pairFiber,Finset.prod_filter]
  rw [Finset.prod_comm,←Fintype.prod_prod_type (fun x : Bool × β => if x ∈ S then f x else 1)]
  rw [←Finset.prod_filter]
  congr 1
  ext x
  simp

lemma fiber_average_bound (S : Finset Bool) (p : Bool → ℝ) (hp : ∀ b, 0 ≤ p b) :
    finiteMean (fun c : Bool => ∏ ε ∈ S, p (Bool.xor ε c)) ≤
      ∏ ε ∈ S, (p ε + p (!ε))/2 := by
  rw [finiteMean_bool]
  have hxor : ∀ ε : Bool, Bool.xor ε true = Equiv.swap false true ε := by decide
  simp only [Bool.xor_false,hxor]
  calc
    _ ≤ ∏ ε ∈ S, (p ε+p (Equiv.swap false true ε))/2 :=
      swap_average_product S p hp false true
    _ = _ := Finset.prod_congr rfl (fun ε _ => by cases ε <;> rfl)

lemma CylinderBound.fair_parallel {m : Finset (Bool × β) → ℝ} {p : Bool × β → ℝ}
    (h : CylinderBound m p) (hp : ∀ x, 0 ≤ p x) :
    CylinderBound (fun S => finiteMean (fun ξ : β → Bool => m (S.image (pairLayer ξ))))
      (fun x => (p x+p (!x.1,x.2))/2) := by
  intro S
  calc
    _ ≤ finiteMean (fun ξ : β → Bool => ∏ x ∈ S, p (pairLayer ξ x)) := by
      apply finiteMean_mono
      intro ξ
      simpa only [Finset.prod_image (pairLayer ξ).injective.injOn] using h (S.image (pairLayer ξ))
    _ = ∏ b : β, finiteMean (fun c : Bool => ∏ ε ∈ pairFiber S b, p (Bool.xor ε c,b)) := by
      calc
        _ = finiteMean (fun ξ : β → Bool => ∏ b : β,
            ∏ ε ∈ pairFiber S b, p (Bool.xor ε (ξ b),b)) :=
          finiteMean_congr (fun ξ => prod_pairFiber S (fun x => p (pairLayer ξ x)))
        _ = _ := finiteMean_pi_prod (fun b c => ∏ ε ∈ pairFiber S b, p (Bool.xor ε c,b))
    _ ≤ ∏ b : β, ∏ ε ∈ pairFiber S b, (p (ε,b)+p (!ε,b))/2 := by
      apply Finset.prod_le_prod
      · intro b _
        exact div_nonneg (Finset.sum_nonneg (fun c _ =>
          Finset.prod_nonneg (fun ε _ => hp (Bool.xor ε c,b)))) (Nat.cast_nonneg _)
      · intro b _
        exact fiber_average_bound (pairFiber S b) (fun ε => p (ε,b)) (fun ε => hp (ε,b))
    _ = _ := (prod_pairFiber S (fun x => (p x+p (!x.1,x.2))/2)).symm

lemma finiteMean_comm {Ω Ω' : Type*} [Fintype Ω] [Fintype Ω'] (f : Ω → Ω' → ℝ) :
    finiteMean (fun x => finiteMean (f x)) = finiteMean (fun y => finiteMean (fun x => f x y)) := by
  simp only [finiteMean,←Finset.sum_div,div_div]
  rw [Finset.sum_comm,mul_comm]

end ParallelFairLayer

section RelabelMarks
variable {α β Ω Ω' : Type*} [DecidableEq α] [DecidableEq β] [Fintype Ω] [Fintype Ω']

omit [Fintype Ω] [Fintype Ω'] in
lemma subset_image_equiv_iff (e : α ≃ β) (A : Finset α) (S : Finset β) :
    S ⊆ A.image e ↔ S.image e.symm ⊆ A := by
  constructor
  · intro h x hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨x,hx,hxy⟩ := Finset.mem_image.mp (h hy)
    simpa only [←hxy,Equiv.symm_apply_apply] using hx
  · intro h y hy
    exact Finset.mem_image.mpr ⟨e.symm y,h (Finset.mem_image_of_mem _ hy),e.apply_symm_apply y⟩

end RelabelMarks

lemma finiteMean_prod_mul {Ω Ω' : Type*} [Fintype Ω] [Fintype Ω']
    (f : Ω → ℝ) (g : Ω' → ℝ) :
    finiteMean (fun ω : Ω × Ω' => f ω.1*g ω.2) = finiteMean f * finiteMean g := by
  simp only [finiteMean,Fintype.sum_prod_type,Fintype.card_prod,Nat.cast_mul,
    ←Finset.mul_sum,←Finset.sum_mul]
  ring

section JoinChildren
variable {β : Type*} [DecidableEq β]

lemma childJoin_boolFiber (S : Finset (Bool × β)) :
    childJoin (boolFiber S false) (boolFiber S true) = S := by
  ext ⟨b,x⟩
  rw [mem_childJoin]
  cases b <;> simp only [Bool.false_eq_true,↓reduceIte,mem_boolFiber]

lemma prod_childJoin (A B : Finset β) (f : Bool × β → ℝ) :
    (∏ x ∈ childJoin A B, f x) = (∏ x ∈ A, f (false,x)) * ∏ x ∈ B, f (true,x) := by
  classical
  have hd : Disjoint (A.image (fun x => (false,x))) (B.image (fun x => (true,x))) := by
    apply Finset.disjoint_left.mpr
    rintro x hx hy
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b,hb,hba⟩ := Finset.mem_image.mp hy
    exact Bool.false_ne_true (congrArg Prod.fst hba).symm
  rw [childJoin,Finset.prod_union hd,
    Finset.prod_image (fun _ _ _ _ h => congrArg Prod.snd h),
    Finset.prod_image (fun _ _ _ _ h => congrArg Prod.snd h)]

lemma prod_boolFibers (S : Finset (Bool × β)) (f : Bool × β → ℝ) :
    (∏ x ∈ S, f x) = (∏ x ∈ boolFiber S false, f (false,x)) *
      ∏ x ∈ boolFiber S true, f (true,x) := by
  rw [←prod_childJoin,childJoin_boolFiber]

end JoinChildren

namespace CycleColoring
variable {α : Type*} [Fintype α] [DecidableEq α]

lemma root_mem {p : Equiv.Perm α} {S : Finset α} (C : RoutingNetwork.SelectedCycle p S) :
    root C ∈ C.val := C.nonempty.choose_spec

lemma orbit_subset_of_predecessor_closed (p : Equiv.Perm α) (D : Finset α)
    (hD : ∀ x ∈ D, p.symm x ∈ D) {x : α} (hx : x ∈ D) : orbitSet p x ⊆ D := by
  intro y hy
  have hh := ((mem_orbitSet p x y).mp hy).inv
  obtain ⟨n,hn⟩ := hh.exists_nat_pow_eq
  have hp (k : ℕ) : (p⁻¹ ^ k) x ∈ D := by
    induction k with
    | zero => simpa using hx
    | succ k ih => simpa only [pow_succ',Equiv.Perm.mul_apply,Equiv.Perm.coe_inv] using hD _ ih
  exact hn ▸ hp n

lemma record_injective (p : Equiv.Perm α) (S : Finset α) :
    Function.Injective (record (p := p) (S := S)) := by
  classical
  intro f g hfg
  apply Subtype.ext
  funext x
  by_contra hne
  have hx : x ∈ S := by
    by_contra h
    exact hne ((f.property.1 x h).trans (g.property.1 x h).symm)
  let D := S.filter (fun y => f.val y ≠ g.val y)
  have hxD : x ∈ D := Finset.mem_filter.mpr ⟨hx,hne⟩
  have hprev (y : α) (hy : y ∈ D) : p.symm y ∈ D := by
    obtain ⟨hyS,hyne⟩ := Finset.mem_filter.mp hy
    have hpS : p.symm y ∈ S := by
      by_contra hn
      have hseed : y ∈ boundary p S := Finset.mem_filter.mpr ⟨hyS,hn⟩
      exact hyne (congrFun hfg (Sum.inl ⟨y,hseed⟩))
    refine Finset.mem_filter.mpr ⟨hpS,?_⟩
    have hf := f.property.2 (p.symm y) hpS (by simpa only [Equiv.apply_symm_apply] using hyS)
    have hg := g.property.2 (p.symm y) hpS (by simpa only [Equiv.apply_symm_apply] using hyS)
    simp only [Equiv.apply_symm_apply] at hf hg
    intro he
    exact hyne (hf.trans (he.trans hg.symm))
  have horb := orbit_subset_of_predecessor_closed p D hprev hxD
  let C : RoutingNetwork.SelectedCycle p S :=
    ⟨orbitSet p x,⟨x,rfl⟩,fun y hy => (Finset.mem_filter.mp (horb hy)).1⟩
  have hrD : root C ∈ D := horb (root_mem C)
  have hrne := (Finset.mem_filter.mp hrD).2
  exact hrne (congrFun hfg (Sum.inr C))

lemma card_coloring_le (p : Equiv.Perm α) (S : Finset α) :
    Fintype.card (Coloring p S) ≤
      2 ^ ((boundary p S).card + Fintype.card (RoutingNetwork.SelectedCycle p S)) := by
  have h := Fintype.card_le_of_injective (record (p := p) (S := S)) (record_injective p S)
  simpa only [Fintype.card_fun,Fintype.card_sum,Fintype.card_coe,Fintype.card_bool] using h

omit [Fintype α] in
lemma boundary_card (p : Equiv.Perm α) (S : Finset α) :
    (boundary p S).card = S.card - (S.filter (fun x => p.symm x ∈ S)).card := by
  classical
  have h := Finset.card_filter_add_card_filter_not (s := S) (fun x => p.symm x ∈ S)
  unfold boundary
  omega

end CycleColoring
end Thorp

end ThorpNine.Adaptive

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Adaptive_AlternatingPerm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Adaptive

namespace Thorp
open scoped BigOperators
open Filter
namespace CycleColoring
variable {α : Type*} [Fintype α] [DecidableEq α]
omit [Fintype α] in
lemma bipartitionFlip_injective (p : Equiv.Perm α) (S : Finset α)
    (χ : α → Bool) (hχ : ∀ x, χ (p x) = !(χ x)) :
    Function.Injective (bipartitionFlip p S χ hχ) := by
  classical
  intro f g he
  apply Subtype.ext
  funext x
  by_cases hx : x ∈ S
  · have hh := congrFun (congrArg Subtype.val he) x
    change (if x ∈ S then Bool.xor (f.val x) (χ x) else false) =
      (if x ∈ S then Bool.xor (g.val x) (χ x) else false) at hh
    simp only [ite_eq_left hx] at hh
    cases hfx : f.val x <;> cases hgx : g.val x <;> cases hcx : χ x <;> simp_all
  · exact (f.property.1 x hx).trans (g.property.1 x hx).symm

lemma card_opposite_le (p : Equiv.Perm α) (S : Finset α)
    (χ : α → Bool) (hχ : ∀ x, χ (p x) = !(χ x)) :
    Fintype.card (OppositeColoring p S) ≤
      2 ^ ((boundary p S).card + Fintype.card (RoutingNetwork.SelectedCycle p S)) := by
  exact (Fintype.card_le_of_injective _ (bipartitionFlip_injective p S χ hχ)).trans
    (card_coloring_le p S)

omit [Fintype α] [DecidableEq α] in
lemma alternatingPerm_flip (p : Equiv.Perm α) (x : Bool × α) :
    (alternatingPerm p x).1 = !x.1 := by
  rcases x with ⟨b,x⟩
  cases b <;> rfl

lemma selected_alternating_eq (p : Equiv.Perm α) (A B : Finset α)
    (C : RoutingNetwork.SelectedCycle (alternatingPerm p) (childJoin A B)) :
    C.val = childJoin (projectCycle p A B C).val (projectCycle p A B C).val := by
  change C.val = childJoin (boolFiber C.val false) (boolFiber C.val false)
  obtain ⟨x,hx⟩ := C.property.1
  rw [hx,orbit_alternating,boolFiber_childJoin]
  rfl

lemma projectCycle_injective (p : Equiv.Perm α) (A B : Finset α) :
    Function.Injective (projectCycle p A B) := by
  intro C D he
  apply Subtype.ext
  rw [selected_alternating_eq p A B C,selected_alternating_eq p A B D,he]

lemma card_alternating_cycles_le (p : Equiv.Perm α) (A B : Finset α) :
    Fintype.card (RoutingNetwork.SelectedCycle (alternatingPerm p) (childJoin A B)) ≤
      Fintype.card (RoutingNetwork.SelectedCycle p A) :=
  Fintype.card_le_of_injective _ (projectCycle_injective p A B)

end CycleColoring

section PairAssignmentCount
variable {α : Type*} [Fintype α] [DecidableEq α]

omit [Fintype α] in
lemma mem_image_perm_iff (p : Equiv.Perm α) (A : Finset α) (y : α) :
    y ∈ A.image p ↔ p.symm y ∈ A := by
  constructor
  · intro h
    obtain ⟨x,hx,hxy⟩ := Finset.mem_image.mp h
    simpa only [←hxy,Equiv.symm_apply_apply] using hx
  · intro h
    exact Finset.mem_image.mpr ⟨p.symm y,h,p.apply_symm_apply y⟩

omit [Fintype α] in
lemma card_childJoin (A B : Finset α) : (childJoin A B).card = A.card+B.card := by
  have hd : Disjoint (A.image (fun x => (false,x))) (B.image (fun x => (true,x))) := by
    apply Finset.disjoint_left.mpr
    rintro x hx hy
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b,hb,hba⟩ := Finset.mem_image.mp hy
    exact Bool.false_ne_true (congrArg Prod.fst hba).symm
  have hi (b : Bool) : Function.Injective (fun x : α => (b,x)) :=
    fun _ _ h => congrArg Prod.snd h
  rw [childJoin,Finset.card_union_of_disjoint hd,
    Finset.card_image_of_injective A (hi false),Finset.card_image_of_injective B (hi true)]

omit [Fintype α] in
lemma alternating_internal (p : Equiv.Perm α) (A B : Finset α) :
    ((childJoin A B).filter (fun x => (CycleColoring.alternatingPerm p).symm x ∈ childJoin A B)) =
      childJoin (A ∩ B.image p) (B ∩ A) := by
  ext ⟨b,x⟩
  rw [Finset.mem_filter]
  cases b <;> simp only [mem_childJoin,CycleColoring.alternatingPerm,
    Equiv.symm_mk,Equiv.coe_fn_mk,Bool.false_eq_true,↓reduceIte,Finset.mem_inter,mem_image_perm_iff]

omit [Fintype α] in
lemma alternating_boundary_card (p : Equiv.Perm α) (A B : Finset α) :
    (CycleColoring.boundary (CycleColoring.alternatingPerm p) (childJoin A B)).card =
      (A ∪ B).card + (A ∪ B.image p).card - (A.card+B.card) := by
  rw [CycleColoring.boundary_card,alternating_internal,card_childJoin,card_childJoin]
  have h₀ := Finset.card_union_add_card_inter A B
  have h₁ := Finset.card_union_add_card_inter A (B.image p)
  rw [Finset.card_image_of_injective _ p.injective] at h₁
  have h₂ := Finset.inter_comm B A
  rw [h₂]
  omega

end PairAssignmentCount

lemma boolFiber_headTail (d : ℕ) (S : Finset (Card (d+1))) (b : Bool) :
    boolFiber (S.image (headTailEquiv d)) b = childMarks S b := by
  classical
  ext x
  rw [mem_boolFiber,mem_childMarks]
  constructor
  · intro h
    obtain ⟨y,hy,he⟩ := Finset.mem_image.mp h
    have hh := congrArg (headTailEquiv d).symm he
    rw [Equiv.symm_apply_apply] at hh
    change y = Fin.cons b x at hh
    exact hh ▸ hy
  · intro h
    exact Finset.mem_image.mpr ⟨Fin.cons b x,h,by rfl⟩

lemma prod_childMarks (d : ℕ) (S : Finset (Card (d+1))) (f : Card (d+1) → ℝ) :
    (∏ x ∈ S, f x) =
      (∏ x ∈ childMarks S false, f (Fin.cons false x)) *
      ∏ x ∈ childMarks S true, f (Fin.cons true x) := by
  classical
  have h := prod_boolFibers (S.image (headTailEquiv d)) (fun x => f ((headTailEquiv d).symm x))
  rw [Finset.prod_image (headTailEquiv d).injective.injOn,
    boolFiber_headTail,boolFiber_headTail] at h
  simp only [Equiv.symm_apply_apply] at h
  exact h

lemma finiteMean_headAverage (d : ℕ) (p : Card (d+1) → ℝ) :
    finiteMean (headAverage p) = finiteMean p := by
  rw [finiteMean_equiv (headTailEquiv d),finiteMean_prod,finiteMean_comm]
  apply finiteMean_congr
  intro y
  rw [finiteMean_bool]
  rfl

lemma pairSwitch_product_bound (d : ℕ) (S : Finset (Card (d+1)))
    (p : Card (d+1) → ℝ) (hp : ∀ x, 0 ≤ p x) :
    finiteMean (fun ξ : Card d → Bool => ∏ x ∈ S, p (pairSwitch ξ x)) ≤
      ∏ x ∈ S, headAverage p (Fin.tail x) := by
  classical
  have h : CylinderBound (fun T => ∏ x ∈ T, p ((headTailEquiv d).symm x))
      (fun x => p ((headTailEquiv d).symm x)) := fun _ => le_rfl
  have hh := h.fair_parallel (fun x => hp _) (S.image (headTailEquiv d))
  simp only [Finset.prod_image (pairLayer _).injective.injOn,
    Finset.prod_image (headTailEquiv d).injective.injOn] at hh
  convert hh using 1
  · apply finiteMean_congr
    intro ξ
    apply Finset.prod_congr rfl
    intro x _
    rfl
  · apply Finset.prod_congr rfl
    intro x _
    change (p (Fin.cons false (Fin.tail x))+p (Fin.cons true (Fin.tail x)))/2 =
      (p (Fin.cons (x 0) (Fin.tail x))+p (Fin.cons (!(x 0)) (Fin.tail x)))/2
    cases x 0
    · rfl
    · simp only [Bool.not_true]
      ring

lemma butterflyPerm_step (d : ℕ)
    (c : (SwitchIndex d → Bool) × (SwitchIndex d → Bool)) (ξ : Card d → Bool) :
    butterflyPerm (d+1) (decodeButterfly (d+1) ((coinStepEquiv d).symm (c,ξ))) =
    pairSwitch ξ * childLift (fun b => butterflyPerm d (decodeButterfly d (if b then c.2 else c.1))) := by
  change pairSwitch (fun y => (coinStepEquiv d).symm (c,ξ) (Sum.inl y)) *
    childLift (fun b => butterflyPerm d (decodeButterfly d
      (fun i => (coinStepEquiv d).symm (c,ξ) (Sum.inr (b,i))))) = _
  apply congrArg₂ (· * ·)
  · rfl
  · apply congrArg childLift
    funext b
    apply congrArg (fun ω => butterflyPerm d (decodeButterfly d ω))
    funext i
    cases b <;> rfl

lemma butterfly_product_bound (d : ℕ) (S : Finset (Card d))
    (p : Card d → ℝ) (hp : ∀ x, 0 ≤ p x) :
    finiteMean (fun ω : SwitchIndex d → Bool =>
      ∏ x ∈ S, p (butterflyPerm d (decodeButterfly d ω) x)) ≤ (finiteMean p)^S.card := by
  classical
  induction d with
  | zero =>
    have he : p = fun _ => p (fun i => Fin.elim0 i) := by
      funext x
      exact congrArg p (Subsingleton.elim _ _)
    rw [he]
    simp only [Finset.prod_const,finiteMean_const,le_refl]
  | succ d ih =>
    let g : Card d → ℝ := headAverage p
    have hg : ∀ x, 0 ≤ g x := fun x => div_nonneg (add_nonneg (hp _) (hp _)) (by norm_num)
    rw [finiteMean_equiv (coinStepEquiv d),finiteMean_prod]
    calc
      _ ≤ finiteMean (fun c : (SwitchIndex d → Bool) × (SwitchIndex d → Bool) =>
        (∏ x ∈ childMarks S false, g (butterflyPerm d (decodeButterfly d c.1) x)) *
        ∏ x ∈ childMarks S true, g (butterflyPerm d (decodeButterfly d c.2) x)) := by
        apply finiteMean_mono
        intro c
        let f : Equiv.Perm (Card (d+1)) := childLift (fun b =>
          butterflyPerm d (decodeButterfly d (if b then c.2 else c.1)))
        have hh := pairSwitch_product_bound d (S.image f) p hp
        simp only [Finset.prod_image f.injective.injOn] at hh
        convert hh using 1
        · apply finiteMean_congr
          intro ξ
          apply Finset.prod_congr rfl
          intro x _
          rw [butterflyPerm_step]
          rfl
        · rw [prod_childMarks]
          simp only [f,childLift,Equiv.coe_fn_mk,Fin.cons_zero,Fin.tail_cons,
            Bool.false_eq_true,↓reduceIte]
          rfl
      _ = (finiteMean (fun c : SwitchIndex d → Bool =>
        ∏ x ∈ childMarks S false, g (butterflyPerm d (decodeButterfly d c) x))) *
        finiteMean (fun c : SwitchIndex d → Bool =>
        ∏ x ∈ childMarks S true, g (butterflyPerm d (decodeButterfly d c) x)) :=
          finiteMean_prod_mul
            (fun c : SwitchIndex d → Bool => ∏ x ∈ childMarks S false,
              g (butterflyPerm d (decodeButterfly d c) x))
            (fun c : SwitchIndex d → Bool => ∏ x ∈ childMarks S true,
              g (butterflyPerm d (decodeButterfly d c) x))
      _ ≤ (finiteMean g)^(childMarks S false).card * (finiteMean g)^(childMarks S true).card :=
        mul_le_mul (ih (childMarks S false) g hg) (ih (childMarks S true) g hg)
          (finiteMean_nonneg fun c => Finset.prod_nonneg (fun x _ => hg _))
          (pow_nonneg (finiteMean_nonneg hg) _)
      _ = (finiteMean p)^S.card := by
        rw [←pow_add,card_childMarks_add,finiteMean_headAverage]

lemma inverseButterflyMarks_inclusion (d : ℕ) (A S : Finset (Card d)) :
    inclusionMoment (inverseButterflyMarks d A) S ≤
      ((A.card : ℝ)/(2:ℝ)^d)^S.card := by
  classical
  let p : Card d → ℝ := fun x => if x ∈ A then 1 else 0
  have hm : finiteMean p = (A.card : ℝ)/(2:ℝ)^d := by
    simp only [finiteMean,p,card_positions,Nat.cast_pow,Nat.cast_ofNat]
    congr 1
    simp
  have he : inclusionMoment (inverseButterflyMarks d A) S =
      finiteMean (fun ω : SwitchIndex d → Bool =>
        ∏ x ∈ S, p (butterflyPerm d (decodeButterfly d ω) x)) := by
    rw [inclusionMoment_eq]
    apply finiteMean_congr
    intro ω
    simp only [inverseButterflyMarks,subset_image_equiv_iff,Equiv.symm_symm,indicator_subset_prod,
      Finset.prod_image (butterflyPerm d (decodeButterfly d ω)).injective.injOn,p]
  rw [he]
  simpa only [hm] using butterfly_product_bound d S p (fun x => by dsimp [p]; split_ifs <;> norm_num)

namespace PairRouting

section
variable {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α]

omit [Fintype α] in
lemma mem_occupied (x : ι → Bool × α) (y : α) : y ∈ occupied x ↔ ∃ i, (x i).2 = y := by
  simp [occupied]

omit [Fintype α] in
lemma chosenCoin_apply (x : ι → Bool × α) (c : ι → Bool) (hc : Compatible x c) (i : ι) :
    chosenCoin x c (x i).2 = required x c i := by
  classical
  simp only [chosenCoin,dite_eq_left (show ∃ j, (x j).2 = (x i).2 from ⟨i,rfl⟩)]
  exact hc _ i (Classical.choose_spec (show ∃ j, (x j).2 = (x i).2 from ⟨i,rfl⟩))

omit [Fintype α] in
lemma colors_eq_iff (x : ι → Bool × α) (c : ι → Bool) (hc : Compatible x c) (ξ : α → Bool) :
    colors x ξ = c ↔ ∀ y ∈ occupied x, ξ y = chosenCoin x c y := by
  constructor
  · intro he y hy
    obtain ⟨i,rfl⟩ := (mem_occupied x y).mp hy
    rw [chosenCoin_apply x c hc i]
    rw [←he,required_colors]
  · intro he
    funext i
    apply (xor_eq_iff _ _ _).mpr
    exact (he _ ((mem_occupied x _).mpr ⟨i,rfl⟩)).trans (chosenCoin_apply x c hc i)

lemma colors_probability (x : ι → Bool × α) (c : ι → Bool) :
    finiteMean (fun ξ : α → Bool => if colors x ξ = c then (1 : ℝ) else 0) =
      if Compatible x c then 1/(2:ℝ)^(occupied x).card else 0 := by
  classical
  by_cases hc : Compatible x c
  · rw [ite_eq_left hc]
    have he := fun ξ => colors_eq_iff x c hc ξ
    simp only [he]
    exact mean_coinCylinder (occupied x) (chosenCoin x c)
  · rw [ite_eq_right hc]
    have he : ∀ ξ, colors x ξ ≠ c := fun ξ hh => hc (hh ▸ colors_compatible x ξ)
    simp only [he,ite_false,finiteMean_const]

omit [Fintype ι] [Fintype α] [DecidableEq α] in
lemma sandwich_matches_iff (ξ η : α → Bool) (p : Bool → Equiv.Perm α) (x y : ι → Bool × α) :
    (∀ i, sandwich ξ η p (x i) = y i) ↔
      colors x ξ = colors y η ∧ ChildMatches p x y (colors x ξ) := by
  have he (i : ι) : sandwich ξ η p (x i) = y i ↔
      colors x ξ i = colors y η i ∧ p (colors x ξ i) (x i).2 = (y i).2 := by
    change pairLayer η (lift p (pairLayer ξ (x i))) = y i ↔ _
    rw [←Equiv.eq_symm_apply]
    change (colors x ξ i,p (colors x ξ i) (x i).2) = (colors y η i,(y i).2) ↔ _
    exact ⟨Prod.mk.inj,fun h => Prod.ext h.1 h.2⟩
  simp only [he,forall_and,←funext_iff,ChildMatches]

lemma sandwich_probability [DecidableEq ι] (p : Bool → Equiv.Perm α) (x y : ι → Bool × α) :
    finiteMean (fun coins : (α → Bool) × (α → Bool) =>
      if ∀ i, sandwich coins.1 coins.2 p (x i) = y i then (1:ℝ) else 0) =
    ∑ c : ι → Bool,
      (if Compatible x c then 1/(2:ℝ)^(occupied x).card else 0) *
      (if Compatible y c then 1/(2:ℝ)^(occupied y).card else 0) *
      (if ChildMatches p x y c then 1 else 0) := by
  classical
  have he (coins : (α → Bool) × (α → Bool)) :
      (if ∀ i, sandwich coins.1 coins.2 p (x i) = y i then (1:ℝ) else 0) =
      ∑ c : ι → Bool, (if colors x coins.1 = c then (1:ℝ) else 0) *
        (if colors y coins.2 = c then 1 else 0) * (if ChildMatches p x y c then 1 else 0) := by
    rw [Finset.sum_eq_single (colors x coins.1)]
    · by_cases hc : colors x coins.1 = colors y coins.2
      · simp only [sandwich_matches_iff,hc,true_and,↓reduceIte,one_mul]
      · simp only [sandwich_matches_iff,hc,false_and,↓reduceIte,one_mul,Ne.symm hc,zero_mul]
    · intro c _ hc
      simp only [Ne.symm hc,ite_false,zero_mul]
    · simp
  simp_rw [he]
  rw [finiteMean_sum]
  apply Finset.sum_congr rfl
  intro c _
  rw [finiteMean_mul_const]
  rw [finiteMean_prod_mul
    (fun ξ : α → Bool => if colors x ξ = c then (1:ℝ) else 0)
    (fun η : α → Bool => if colors y η = c then (1:ℝ) else 0),
    colors_probability,colors_probability]

omit [Fintype ι] [Fintype α] [DecidableEq α] in
lemma childMatches_split (p₀ p₁ : Equiv.Perm α) (x y : ι → Bool × α) (c : ι → Bool) :
    ChildMatches (fun b => if b then p₁ else p₀) x y c ↔
      (∀ i : {i // c i = false}, p₀ (x i.val).2 = (y i.val).2) ∧
      (∀ i : {i // c i = true}, p₁ (x i.val).2 = (y i.val).2) := by
  constructor
  · intro h
    constructor
    · intro i
      simpa only [i.property,Bool.false_eq_true,↓reduceIte] using h i.val
    · intro i
      simpa only [i.property,↓reduceIte] using h i.val
  · rintro ⟨h₀,h₁⟩ i
    cases hi : c i
    · simpa only [hi,Bool.false_eq_true,↓reduceIte] using h₀ ⟨i,hi⟩
    · simpa only [hi,↓reduceIte] using h₁ ⟨i,hi⟩

omit [Fintype α] in
lemma childMatches_mean {Ω Ω' : Type*} [Fintype Ω] [Fintype Ω']
    (P : Ω → Equiv.Perm α) (Q : Ω' → Equiv.Perm α) (x y : ι → Bool × α) (c : ι → Bool) :
    finiteMean (fun ω : Ω × Ω' =>
      if ChildMatches (fun b => if b then Q ω.2 else P ω.1) x y c then (1:ℝ) else 0) =
      tupleProbability P (fun i : {i // c i = false} => (x i.val).2)
        (fun i : {i // c i = false} => (y i.val).2) *
      tupleProbability Q (fun i : {i // c i = true} => (x i.val).2)
        (fun i : {i // c i = true} => (y i.val).2) := by
  classical
  let f : Ω → ℝ := fun ω => if ∀ i : {i // c i = false}, P ω (x i.val).2 = (y i.val).2 then 1 else 0
  let g : Ω' → ℝ := fun ω => if ∀ i : {i // c i = true}, Q ω (x i.val).2 = (y i.val).2 then 1 else 0
  have he (ω : Ω × Ω') :
      (if ChildMatches (fun b => if b then Q ω.2 else P ω.1) x y c then (1:ℝ) else 0) = f ω.1*g ω.2 := by
    simp only [childMatches_split,f,g]
    split_ifs <;> simp_all
  simp_rw [he]
  exact finiteMean_prod_mul f g

lemma sandwich_mean [DecidableEq ι] {Ω Ω' : Type*} [Fintype Ω] [Fintype Ω']
    (P : Ω → Equiv.Perm α) (Q : Ω' → Equiv.Perm α) (x y : ι → Bool × α) :
    finiteMean (fun ω : Ω × Ω' => finiteMean (fun coins : (α → Bool) × (α → Bool) =>
      if ∀ i, sandwich coins.1 coins.2 (fun b => if b then Q ω.2 else P ω.1) (x i) = y i
      then (1:ℝ) else 0)) =
    ∑ c : ι → Bool,
      (if Compatible x c then 1/(2:ℝ)^(occupied x).card else 0) *
      (if Compatible y c then 1/(2:ℝ)^(occupied y).card else 0) *
      (tupleProbability P (fun i : {i // c i = false} => (x i.val).2)
        (fun i : {i // c i = false} => (y i.val).2) *
      tupleProbability Q (fun i : {i // c i = true} => (x i.val).2)
        (fun i : {i // c i = true} => (y i.val).2)) := by
  classical
  simp_rw [sandwich_probability]
  rw [finiteMean_sum]
  apply Finset.sum_congr rfl
  intro c _
  simp only [mul_comm ((if Compatible x c then _ else _) * _),finiteMean_mul_const,
    childMatches_mean]


omit [Fintype α] in
lemma assignmentColoring_injective (e : ι ↪ Bool × α) (p : Bool → Equiv.Perm α) :
    Function.Injective (assignmentColoring e p) := by
  intro c c' he
  apply Subtype.ext
  funext i
  have hh := congrFun (congrArg Subtype.val he) (e i)
  change Function.extend e c.val (fun _ => false) (e i) =
    Function.extend e c'.val (fun _ => false) (e i) at hh
  simpa only [e.injective.extend_apply] using hh

omit [Fintype α] in
lemma occupied_labelSet (e : ι ↪ Bool × α) : occupied e = (labelSet e).image Prod.snd := by
  classical
  simp only [occupied,labelSet,Finset.image_image,Function.comp_def]

omit [Fintype ι] [Fintype α] in
lemma image_snd_childJoin (A B : Finset α) : (childJoin A B).image Prod.snd = A ∪ B := by
  classical
  simp only [childJoin,Finset.image_union,Finset.image_image,Function.comp_def,Finset.image_id']

omit [Fintype ι] [Fintype α] in
lemma image_lift_childJoin (p : Bool → Equiv.Perm α) (A B : Finset α) :
    (childJoin A B).image (fun x => (lift p x).2) = A.image (p false) ∪ B.image (p true) := by
  classical
  simp only [childJoin,Finset.image_union,Finset.image_image,Function.comp_def,lift,Equiv.coe_fn_mk]

omit [Fintype α] in
lemma occupied_lift_card (e : ι ↪ Bool × α) (p : Bool → Equiv.Perm α) :
    (occupied (fun i => lift p (e i))).card =
      (boolFiber (labelSet e) false ∪ (boolFiber (labelSet e) true).image (alternatingProjection p)).card := by
  classical
  have he : occupied (fun i => lift p (e i)) = (labelSet e).image (fun x => (lift p x).2) := by
    simp only [occupied,labelSet,Finset.image_image,Function.comp_def]
  rw [he,←childJoin_boolFiber (labelSet e),image_lift_childJoin]
  simp only [CycleColoring.boolFiber_childJoin,Bool.false_eq_true,↓reduceIte]
  let A := boolFiber (labelSet e) false
  let B := boolFiber (labelSet e) true
  change (A.image (p false) ∪ B.image (p true)).card = (A ∪ B.image (alternatingProjection p)).card
  have hh : A.image (p false) ∪ B.image (p true) =
      (A ∪ B.image (alternatingProjection p)).image (p false) := by
    simp only [Finset.image_union,Finset.image_image,Function.comp_def,
      alternatingProjection,Equiv.Perm.coe_mul,Equiv.apply_symm_apply]
  rw [hh,Finset.card_image_of_injective _ (p false).injective]

omit [Fintype α] in
lemma occupied_eq_fibers (e : ι ↪ Bool × α) :
    occupied e = boolFiber (labelSet e) false ∪ boolFiber (labelSet e) true := by
  rw [occupied_labelSet,←childJoin_boolFiber (labelSet e),image_snd_childJoin]
  simp only [CycleColoring.boolFiber_childJoin,Bool.false_eq_true,↓reduceIte]

omit [Fintype α] in
lemma card_labelSet (e : ι ↪ Bool × α) : (labelSet e).card = Fintype.card ι := by
  classical
  exact (Finset.card_image_of_injective _ e.injective).trans (Finset.card_univ)

omit [Fintype α] in
lemma occupied_card_double (e : ι ↪ Bool × α) : Fintype.card ι ≤ 2*(occupied e).card := by
  have h₀ : (boolFiber (labelSet e) false).card ≤ (occupied e).card := by
    rw [occupied_eq_fibers]
    exact Finset.card_le_card Finset.subset_union_left
  have h₁ : (boolFiber (labelSet e) true).card ≤ (occupied e).card := by
    rw [occupied_eq_fibers]
    exact Finset.card_le_card Finset.subset_union_right
  have he : (boolFiber (labelSet e) false).card+(boolFiber (labelSet e) true).card = Fintype.card ι := by
    rw [←card_childJoin,childJoin_boolFiber,card_labelSet]
  omega

lemma bothAssignments_exact_bound (e : ι ↪ Bool × α) (p : Bool → Equiv.Perm α) :
    Fintype.card (BothAssignments e p) ≤
      2 ^ ((occupied e).card + (occupied (fun i => lift p (e i))).card - Fintype.card ι +
        alternatingCycles e p) := by
  have h := CycleColoring.card_opposite_le
    (CycleColoring.alternatingPerm (alternatingProjection p)) (labelSet e)
    Prod.fst (CycleColoring.alternatingPerm_flip (alternatingProjection p))
  have hb : (CycleColoring.boundary (CycleColoring.alternatingPerm (alternatingProjection p))
      (labelSet e)).card =
      (occupied e).card + (occupied (fun i => lift p (e i))).card - Fintype.card ι := by
    have hh := alternating_boundary_card (alternatingProjection p)
      (boolFiber (labelSet e) false) (boolFiber (labelSet e) true)
    rw [childJoin_boolFiber] at hh
    rw [occupied_eq_fibers,occupied_lift_card]
    have he := card_childJoin (boolFiber (labelSet e) false) (boolFiber (labelSet e) true)
    rw [childJoin_boolFiber,card_labelSet] at he
    simpa only [he] using hh
  rw [hb] at h
  exact (Fintype.card_le_of_injective _ (assignmentColoring_injective e p)).trans h

lemma assignments_actual_bound (e : ι ↪ Bool × α) (ξ η : α → Bool) (p : Bool → Equiv.Perm α) :
    Fintype.card (Assignments e (routedEmbedding e ξ η p)) ≤
      2 ^ ((occupied e).card + (occupied (routedEmbedding e ξ η p)).card - Fintype.card ι +
        alternatingCycles (switchedEmbedding e ξ) p) := by
  rw [Fintype.card_congr (assignmentsEquiv e ξ η p)]
  exact bothAssignments_exact_bound (switchedEmbedding e ξ) p

end
variable {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α] [DecidableEq ι]

omit [Fintype α] [DecidableEq α] in
lemma card_compatibleSet (x y : ι → Bool × α) :
    (compatibleSet x y).card = Fintype.card (Assignments x y) := by
  classical
  exact (Fintype.card_subtype _).symm

omit [Fintype α] [DecidableEq ι] in
lemma outerWeight_pos (x y : ι → Bool × α) : 0 < outerWeight x y := by
  unfold outerWeight
  positivity

omit [Fintype α] in
lemma sum_colors_factor (x y : ι → Bool × α) (f : (ι → Bool) → ℝ) :
    (∑ c : ι → Bool,
      (if Compatible x c then 1/(2:ℝ)^(occupied x).card else 0) *
      (if Compatible y c then 1/(2:ℝ)^(occupied y).card else 0) * f c) =
      outerWeight x y * ∑ c ∈ compatibleSet x y, f c := by
  classical
  rw [compatibleSet,Finset.sum_filter,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  by_cases hx : Compatible x c <;> by_cases hy : Compatible y c
  · simp only [hx,hy,true_and,↓reduceIte,outerWeight,pow_add,one_div_mul_one_div]
  · simp only [hx,hy,and_false,↓reduceIte,mul_zero,zero_mul]
  · simp only [hx,hy,false_and,↓reduceIte,mul_zero,zero_mul]
  · simp only [hx,hy,false_and,↓reduceIte,mul_zero,zero_mul]

lemma sandwich_weighted_probability (p : Bool → Equiv.Perm α) (x y : ι → Bool × α)
    (W : (ι → Bool) → ℝ) :
    finiteMean (fun coins : (α → Bool) × (α → Bool) =>
      if ∀ i, sandwich coins.1 coins.2 p (x i) = y i then W (colors x coins.1) else 0) =
    outerWeight x y * ∑ c ∈ compatibleSet x y, if ChildMatches p x y c then W c else 0 := by
  classical
  have he (coins : (α → Bool) × (α → Bool)) :
      (if ∀ i, sandwich coins.1 coins.2 p (x i) = y i then W (colors x coins.1) else 0) =
      ∑ c : ι → Bool, (if colors x coins.1 = c then (1:ℝ) else 0) *
        (if colors y coins.2 = c then 1 else 0) * (if ChildMatches p x y c then W c else 0) := by
    rw [Finset.sum_eq_single (colors x coins.1)]
    · by_cases hc : colors x coins.1 = colors y coins.2
      · simp only [sandwich_matches_iff,hc,true_and,↓reduceIte,one_mul]
      · simp only [sandwich_matches_iff,hc,false_and,↓reduceIte,one_mul,Ne.symm hc,zero_mul]
    · intro c _ hc
      simp only [Ne.symm hc,ite_false,zero_mul]
    · simp
  simp_rw [he]
  rw [finiteMean_sum,←sum_colors_factor]
  apply Finset.sum_congr rfl
  intro c _
  rw [finiteMean_mul_const,finiteMean_prod_mul
    (fun ξ : α → Bool => if colors x ξ = c then (1:ℝ) else 0)
    (fun η : α → Bool => if colors y η = c then (1:ℝ) else 0),
    colors_probability,colors_probability]

omit [Fintype α] [DecidableEq ι] in
lemma tupleProbability_nonneg {Ω β : Type*} [Fintype Ω] [DecidableEq β]
    (P : Ω → Equiv.Perm β) (x y : ι → β) : 0 ≤ tupleProbability P x y := by
  classical
  exact finiteMean_nonneg (fun ω => by split_ifs <;> norm_num)

lemma sandwich_power_bound {Ω Ω' : Type*} [Fintype Ω] [Fintype Ω']
    (P : Ω → Equiv.Perm α) (Q : Ω' → Equiv.Perm α) (x y : ι → Bool × α)
    (a : ℝ) (ha : 0 ≤ a) :
    (finiteMean (fun ω : Ω × Ω' => finiteMean (fun coins : (α → Bool) × (α → Bool) =>
      if ∀ i, sandwich coins.1 coins.2 (fun b => if b then Q ω.2 else P ω.1) (x i) = y i
      then (1:ℝ) else 0)))^(1+a) ≤
    (outerWeight x y)^(1+a) * ((compatibleSet x y).card:ℝ)^a *
      ∑ c ∈ compatibleSet x y,
      (tupleProbability P (fun i : {i // c i = false} => (x i.val).2)
        (fun i : {i // c i = false} => (y i.val).2))^(1+a) *
      (tupleProbability Q (fun i : {i // c i = true} => (x i.val).2)
        (fun i : {i // c i = true} => (y i.val).2))^(1+a) := by
  classical
  rw [sandwich_mean,sum_colors_factor]
  let f (c : ι → Bool) : ℝ :=
      tupleProbability P (fun i : {i // c i = false} => (x i.val).2)
        (fun i : {i // c i = false} => (y i.val).2) *
      tupleProbability Q (fun i : {i // c i = true} => (x i.val).2)
        (fun i : {i // c i = true} => (y i.val).2)
  have hf (c : ι → Bool) : 0 ≤ f c := mul_nonneg (tupleProbability_nonneg _ _ _)
    (tupleProbability_nonneg _ _ _)
  rw [Real.mul_rpow (le_of_lt (outerWeight_pos _ _)) (Finset.sum_nonneg (fun c _ => hf c))]
  have hh := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg (compatibleSet x y)
    (show 1 ≤ 1+a by linarith) (fun c _ => hf c)
  have he : 1+a-1=a := by ring
  rw [he] at hh
  calc
    _ ≤ (outerWeight x y)^(1+a) *
        (((compatibleSet x y).card:ℝ)^a * ∑ c ∈ compatibleSet x y, (f c)^(1+a)) :=
      mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg (le_of_lt (outerWeight_pos _ _)) _)
    _ = _ := by
      rw [←mul_assoc]
      congr 1
      apply Finset.sum_congr rfl
      intro c _
      exact Real.mul_rpow (tupleProbability_nonneg _ _ _) (tupleProbability_nonneg _ _ _)

end PairRouting

end Thorp

end ThorpNine.Adaptive

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Adaptive_BenesCoins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Adaptive

namespace Thorp
open scoped BigOperators
open Filter

lemma childLift_inv (d : ℕ) (p : Bool → Equiv.Perm (Card d)) :
    (childLift p)⁻¹ = childLift (fun b => (p b)⁻¹) := rfl

lemma pairSwitch_inv (d : ℕ) (ξ : Card d → Bool) : (pairSwitch ξ)⁻¹ = pairSwitch ξ := rfl

lemma palindromePerm_step (d : ℕ) (c : BenesCoins d × BenesCoins d)
    (coins : (Card d → Bool) × (Card d → Bool)) :
    palindromePerm (d+1) ((benesStepEquiv d).symm (c,coins)) =
      pairSwitch coins.2 * childLift (fun b => palindromePerm d (if b then c.2 else c.1)) *
        pairSwitch coins.1 := by
  change (butterflyPerm (d+1) (decodeButterfly (d+1)
      ((coinStepEquiv d).symm ((c.1.1,c.2.1),coins.2)))) *
    (butterflyPerm (d+1) (decodeButterfly (d+1)
      ((coinStepEquiv d).symm ((c.1.2,c.2.2),coins.1))))⁻¹ = _
  rw [butterflyPerm_step,butterflyPerm_step,mul_inv_rev,childLift_inv,pairSwitch_inv]
  rw [mul_assoc (pairSwitch coins.2),←mul_assoc (childLift _),childLift_mul,←mul_assoc]
  congr 2
  apply congrArg childLift
  funext b
  cases b <;> rfl

lemma headTail_switch (d : ℕ) (ξ : Card d → Bool) (x : Card (d+1)) :
    headTailEquiv d (pairSwitch ξ x) = pairLayer ξ (headTailEquiv d x) := rfl

lemma headTail_child (d : ℕ) (p : Bool → Equiv.Perm (Card d)) (x : Card (d+1)) :
    headTailEquiv d (childLift p x) = PairRouting.lift p (headTailEquiv d x) := rfl

lemma palindromePerm_coordinates (d : ℕ) (c : BenesCoins d × BenesCoins d)
    (coins : (Card d → Bool) × (Card d → Bool)) (x : Card (d+1)) :
    headTailEquiv d (palindromePerm (d+1) ((benesStepEquiv d).symm (c,coins)) x) =
      PairRouting.sandwich coins.1 coins.2 (fun b => palindromePerm d (if b then c.2 else c.1))
        (headTailEquiv d x) := by
  rw [palindromePerm_step]
  simp only [Equiv.Perm.mul_apply,headTail_switch,headTail_child]
  rfl

namespace CycleColoring
variable {α : Type*} [Fintype α] [DecidableEq α]

lemma alternating_cycle_two (p : Equiv.Perm α) (S : Finset (Bool × α))
    (C : RoutingNetwork.SelectedCycle (alternatingPerm p) S) : 2 ≤ C.val.card := by
  obtain ⟨x,hx⟩ := C.nonempty
  have hpx : alternatingPerm p x ∈ C.val := by
    rw [←C.orbit_eq hx,mem_orbitSet]
    exact (Equiv.Perm.SameCycle.refl _ _).apply_right
  have hne : x ≠ alternatingPerm p x := by
    intro he
    have hh := congrArg Prod.fst he
    rw [alternatingPerm_flip] at hh
    cases hb : x.1 <;> simp only [hb, Bool.not_false, Bool.not_true] at hh <;> cases hh
  have hs : {x,alternatingPerm p x} ⊆ C.val := by
    intro y hy
    simp only [Finset.mem_insert,Finset.mem_singleton] at hy
    rcases hy with rfl | rfl <;> assumption
  have hh := Finset.card_le_card hs
  simpa only [Finset.card_pair hne] using hh

lemma alternating_cycle_count_double (p : Equiv.Perm α) (S : Finset (Bool × α)) :
    2 * Fintype.card (RoutingNetwork.SelectedCycle (alternatingPerm p) S) ≤ S.card := by
  classical
  calc
    _ = ∑ _C : RoutingNetwork.SelectedCycle (alternatingPerm p) S, 2 := by simp [Nat.mul_comm]
    _ ≤ RoutingNetwork.cycleMass (alternatingPerm p) S :=
      Finset.sum_le_sum (fun C _ => alternating_cycle_two p S C)
    _ ≤ _ := RoutingNetwork.cycleMass_le _ _

end CycleColoring

namespace PairRouting

section
variable {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α]

lemma alternatingCycles_double (e : ι ↪ Bool × α) (p : Bool → Equiv.Perm α) :
    2 * alternatingCycles e p ≤ Fintype.card ι := by
  have hh := CycleColoring.alternating_cycle_count_double (alternatingProjection p) (labelSet e)
  simpa only [alternatingCycles, card_labelSet] using hh

lemma alternatingCycles_zero (e : ι ↪ Bool × α) (p : Bool → Equiv.Perm α)
    (hι : Fintype.card ι ≤ 1) : alternatingCycles e p = 0 := by
  have hh := alternatingCycles_double e p
  omega

end
variable {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α] [DecidableEq ι]

omit [Fintype α] [DecidableEq ι] in
lemma colors_chosenCoin (x : ι → Bool × α) (c : ι → Bool) (hc : Compatible x c) :
    colors x (chosenCoin x c) = c := by
  funext i
  simp only [colors,chosenCoin_apply x c hc i,required]
  cases (x i).1 <;> cases c i <;> rfl

omit [Fintype α] [DecidableEq ι] in
lemma coloredEmbedding_apply (x : ι ↪ Bool × α) (c : ι → Bool) (hc : Compatible x c) (i : ι) :
    coloredEmbedding x c hc i = (c i,(x i).2) := by
  apply Prod.ext
  · exact congrFun (colors_chosenCoin x c hc) i
  · rfl

omit [Fintype α] [DecidableEq ι] in
lemma switchedEmbedding_eq_colored (x : ι ↪ Bool × α) (c : ι → Bool) (hc : Compatible x c)
    (ξ : α → Bool) (he : colors x ξ = c) :
    switchedEmbedding x ξ = coloredEmbedding x c hc := by
  ext i : 1
  rw [coloredEmbedding_apply]
  apply Prod.ext
  · exact congrFun he i
  · rfl

lemma assignments_match_bound (x y : ι ↪ Bool × α) (c : ι → Bool)
    (hc : c ∈ compatibleSet x y) (p : Bool → Equiv.Perm α) (hm : ChildMatches p x y c) :
    (compatibleSet x y).card ≤
      2 ^ ((occupied x).card + (occupied y).card - Fintype.card ι +
        alternatingCycles (coloredEmbedding x c (mem_compatibleSet x y c |>.mp hc).1) p) := by
  obtain ⟨hcx,hcy⟩ := (mem_compatibleSet x y c).mp hc
  let ξ := chosenCoin x c
  let η := chosenCoin y c
  have he : routedEmbedding x ξ η p = y := by
    ext i : 1
    have h := (sandwich_matches_iff ξ η p x y).mpr
      ⟨(colors_chosenCoin x c hcx).trans (colors_chosenCoin y c hcy).symm,by
        simpa only [ξ,colors_chosenCoin x c hcx] using hm⟩
    exact h i
  have hh := assignments_actual_bound x ξ η p
  rw [he] at hh
  rw [card_compatibleSet]
  exact hh

omit [Fintype α] [DecidableEq ι] in
lemma occupied_sum_ge (x y : ι ↪ Bool × α) :
    Fintype.card ι ≤ (occupied x).card + (occupied y).card := by
  have h₀ := occupied_card_double x
  have h₁ := occupied_card_double y
  omega

lemma assignment_weight_bound (x y : ι ↪ Bool × α) (c : ι → Bool)
    (hc : c ∈ compatibleSet x y) (p : Bool → Equiv.Perm α) (hm : ChildMatches p x y c) :
    ((compatibleSet x y).card:ℝ) * outerWeight x y ≤
      (2:ℝ)^((alternatingCycles
        (coloredEmbedding x c (mem_compatibleSet x y c |>.mp hc).1) p : ℝ) - Fintype.card ι) := by
  let z := alternatingCycles (coloredEmbedding x c (mem_compatibleSet x y c |>.mp hc).1) p
  let b := (occupied x).card+(occupied y).card
  let h := Fintype.card ι
  have hb : h ≤ b := occupied_sum_ge x y
  have hn : ((compatibleSet x y).card:ℝ) ≤ (2:ℝ)^(b-h+z) := by
    exact_mod_cast assignments_match_bound x y c hc p hm
  change ((compatibleSet x y).card:ℝ) * (1/(2:ℝ)^b) ≤ (2:ℝ)^((z:ℝ)-h)
  rw [mul_one_div]
  calc
    _ ≤ (2:ℝ)^(b-h+z)/(2:ℝ)^b := div_le_div_of_nonneg_right hn (by positivity)
    _ = _ := by
      rw [←Real.rpow_natCast,←Real.rpow_natCast,←Real.rpow_sub (by norm_num : (0:ℝ)<2)]
      congr 1
      rw [Nat.cast_add,Nat.cast_sub hb]
      ring

lemma assignment_factor_bound (x y : ι ↪ Bool × α) (c : ι → Bool)
    (hc : c ∈ compatibleSet x y) (p : Bool → Equiv.Perm α) (hm : ChildMatches p x y c)
    (a : ℝ) (ha : 0 ≤ a) :
    (outerWeight x y)^a * ((compatibleSet x y).card:ℝ)^a ≤
      (2:ℝ)^(((alternatingCycles
        (coloredEmbedding x c (mem_compatibleSet x y c |>.mp hc).1) p : ℝ) - Fintype.card ι)*a) := by
  have h := Real.rpow_le_rpow (mul_nonneg (Nat.cast_nonneg _) (le_of_lt (outerWeight_pos x y)))
    (assignment_weight_bound x y c hc p hm) ha
  rw [Real.mul_rpow (Nat.cast_nonneg _) (le_of_lt (outerWeight_pos x y)),
    ←Real.rpow_mul (by norm_num : (0:ℝ)≤2)] at h
  simpa only [mul_comm] using h


lemma sandwich_weighted_probability_subtype (p : Bool → Equiv.Perm α) (x y : ι → Bool × α)
    (W : (ι → Bool) → ℝ) :
    finiteMean (fun coins : (α → Bool) × (α → Bool) =>
      if ∀ i, sandwich coins.1 coins.2 p (x i) = y i then W (colors x coins.1) else 0) =
    outerWeight x y * ∑ c : {c // c ∈ compatibleSet x y},
      if ChildMatches p x y c.val then W c.val else 0 := by
  rw [sandwich_weighted_probability]
  congr 1
  rw [Finset.sum_subtype (compatibleSet x y) (fun _ => Iff.rfl)]

omit [Fintype α] [DecidableEq α] [DecidableEq ι] in
lemma color_card_add (c : ι → Bool) :
    Fintype.card {i // c i = false} + Fintype.card {i // c i = true} = Fintype.card ι := by
  have he : {i // c i = true} ≃ {i // ¬c i = false} := Equiv.subtypeEquivRight fun i => by
    cases c i <;> simp
  rw [Fintype.card_congr he]
  rw [Fintype.card_subtype_compl]
  exact Nat.add_sub_of_le (Fintype.card_subtype_le _)

end PairRouting

lemma palindromeCost_eq (d : ℕ) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card (d+1)) (σ : BenesCoins (d+1)) :
    palindromeCost (d+1) e σ =
      assignmentCost d (e.trans (headTailEquiv d).toEmbedding)
        (PairRouting.colors (e.trans (headTailEquiv d).toEmbedding) (benesStepEquiv d σ).2.1)
        (PairRouting.colors_compatible _ _) (benesStepEquiv d σ).1 := by
  unfold palindromeCost assignmentCost
  dsimp only
  rw [PairRouting.switchedEmbedding_eq_colored _ _ (PairRouting.colors_compatible _ _) _ rfl]

lemma palindromeCost_step (d : ℕ) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card (d+1)) (ω : BenesCoins d × BenesCoins d)
    (coins : (Card d → Bool) × (Card d → Bool)) :
    palindromeCost (d+1) e ((benesStepEquiv d).symm (ω,coins)) =
      assignmentCost d (e.trans (headTailEquiv d).toEmbedding)
        (PairRouting.colors (e.trans (headTailEquiv d).toEmbedding) coins.1)
        (PairRouting.colors_compatible _ _) ω := by
  rw [palindromeCost_eq]
  simp only [Equiv.apply_symm_apply]

lemma routingMoment_nonneg (d : ℕ) {ι : Type*} [Fintype ι]
    (e f : ι ↪ Card d) (a : ℝ) : 0 ≤ routingMoment d e f a := by
  classical
  exact finiteMean_nonneg (fun _ => by split_ifs <;> positivity)

lemma palindrome_matches_step (d : ℕ) {ι : Type*}
    (e f : ι ↪ Card (d+1)) (ω : BenesCoins d × BenesCoins d)
    (coins : (Card d → Bool) × (Card d → Bool)) :
    (∀ i, palindromePerm (d+1) ((benesStepEquiv d).symm (ω,coins)) (e i) = f i) ↔
    (∀ i, PairRouting.sandwich coins.1 coins.2 (fun b => palindromePerm d (if b then ω.2 else ω.1))
      ((e.trans (headTailEquiv d).toEmbedding) i) = ((f.trans (headTailEquiv d).toEmbedding) i)) := by
  apply forall_congr'
  intro i
  rw [←(headTailEquiv d).injective.eq_iff,palindromePerm_coordinates]
  rfl

lemma routingMoment_step (d : ℕ) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e f : ι ↪ Card (d+1)) (a : ℝ) :
    let x := e.trans (headTailEquiv d).toEmbedding
    let y := f.trans (headTailEquiv d).toEmbedding
    routingMoment (d+1) e f a = PairRouting.outerWeight x y *
      ∑ c : {c // c ∈ PairRouting.compatibleSet x y},
        finiteMean (fun ω : BenesCoins d × BenesCoins d =>
          if PairRouting.ChildMatches (fun b => palindromePerm d (if b then ω.2 else ω.1)) x y c.val
          then (2:ℝ)^((assignmentCost d x c.val
            ((PairRouting.mem_compatibleSet x y c.val).mp c.property).1 ω:ℝ)*a) else 0) := by
  classical
  intro x y
  rw [routingMoment,finiteMean_equiv (benesStepEquiv d),finiteMean_prod]
  have he (ω : BenesCoins d × BenesCoins d) :
      finiteMean (fun coins : (Card d → Bool) × (Card d → Bool) =>
        if ∀ i, palindromePerm (d+1) ((benesStepEquiv d).symm (ω,coins)) (e i) = f i
        then (2:ℝ)^((palindromeCost (d+1) e ((benesStepEquiv d).symm (ω,coins)):ℝ)*a) else 0) =
      PairRouting.outerWeight x y *
        ∑ c : {c // c ∈ PairRouting.compatibleSet x y},
          if PairRouting.ChildMatches (fun b => palindromePerm d (if b then ω.2 else ω.1)) x y c.val
          then (2:ℝ)^((assignmentCost d x c.val
            ((PairRouting.mem_compatibleSet x y c.val).mp c.property).1 ω:ℝ)*a) else 0 := by
    let W : (ι → Bool) → ℝ := fun c =>
      if hc : PairRouting.Compatible x c then (2:ℝ)^((assignmentCost d x c hc ω:ℝ)*a) else 0
    calc
      _ = finiteMean (fun coins : (Card d → Bool) × (Card d → Bool) =>
        if ∀ i, PairRouting.sandwich coins.1 coins.2 (fun b => palindromePerm d (if b then ω.2 else ω.1))
          (x i) = y i then W (PairRouting.colors x coins.1) else 0) := by
        apply finiteMean_congr
        intro coins
        simp only [palindrome_matches_step,palindromeCost_step]
        simp only [W,PairRouting.colors_compatible,↓reduceDIte]
        rfl
      _ = _ := by
        rw [PairRouting.sandwich_weighted_probability_subtype]
        congr 1
        apply Finset.sum_congr rfl
        intro c _
        simp only [W,((PairRouting.mem_compatibleSet x y c.val).mp c.property).1,↓reduceDIte]
  simp_rw [he]
  simp_rw [mul_comm (PairRouting.outerWeight x y)]
  rw [finiteMean_mul_const,finiteMean_sum,mul_comm]

lemma child_moment_product (d : ℕ) {ι : Type*} [Fintype ι]
    (x y : ι ↪ Bool × Card d) (c : ι → Bool)
    (hcx : PairRouting.Compatible x c) (hcy : PairRouting.Compatible y c) (a : ℝ) :
    routingMoment d (PairRouting.childEmbedding x c hcx false) (PairRouting.childEmbedding y c hcy false) a *
      routingMoment d (PairRouting.childEmbedding x c hcx true) (PairRouting.childEmbedding y c hcy true) a =
    finiteMean (fun ω : BenesCoins d × BenesCoins d =>
      if PairRouting.ChildMatches (fun b => palindromePerm d (if b then ω.2 else ω.1)) x y c
      then (2:ℝ)^(((palindromeCost d (PairRouting.childEmbedding x c hcx false) ω.1 : ℝ) +
        palindromeCost d (PairRouting.childEmbedding x c hcx true) ω.2)*a) else 0) := by
  classical
  unfold routingMoment
  rw [←finiteMean_prod_mul]
  apply finiteMean_congr
  intro ω
  let M₀ := ∀ i : {i // c i = false}, palindromePerm d ω.1 (x i.val).2 = (y i.val).2
  let M₁ := ∀ i : {i // c i = true}, palindromePerm d ω.2 (x i.val).2 = (y i.val).2
  have hp : (fun b : Bool => palindromePerm d (if b then ω.2 else ω.1)) =
      (fun b => if b then palindromePerm d ω.2 else palindromePerm d ω.1) := by
    funext b
    cases b <;> rfl
  have hs : PairRouting.ChildMatches (fun b => palindromePerm d (if b then ω.2 else ω.1)) x y c ↔
      M₀ ∧ M₁ := by rw [hp]; exact PairRouting.childMatches_split _ _ _ _ _
  change (if M₀ then _ else 0) * (if M₁ then _ else 0) = _
  by_cases h₀ : M₀ <;> by_cases h₁ : M₁
  · simp only [hs,h₀,h₁,true_and,↓reduceIte]
    rw [←Real.rpow_add (by norm_num : (0:ℝ)<2)]
    congr 1
    ring
  · simp only [hs,h₀,h₁,and_false,↓reduceIte,mul_zero]
  · simp only [hs,h₀,h₁,false_and,↓reduceIte,zero_mul]
  · simp only [hs,h₀,h₁,false_and,↓reduceIte,mul_zero]

lemma palindrome_probability_step (d : ℕ) {ι : Type*} [Fintype ι]
    (e f : ι ↪ Card (d+1)) :
    PairRouting.tupleProbability (palindromePerm (d+1)) e f =
    finiteMean (fun ω : BenesCoins d × BenesCoins d =>
      finiteMean (fun coins : (Card d → Bool) × (Card d → Bool) =>
        if ∀ i, PairRouting.sandwich coins.1 coins.2 (fun b => if b then palindromePerm d ω.2 else palindromePerm d ω.1)
          ((e.trans (headTailEquiv d).toEmbedding) i) = ((f.trans (headTailEquiv d).toEmbedding) i)
        then (1:ℝ) else 0)) := by
  classical
  rw [PairRouting.tupleProbability,finiteMean_equiv (benesStepEquiv d),finiteMean_prod]
  have hp (b : Bool) (p q : BenesCoins d) :
      palindromePerm d (if b then p else q) = (if b then palindromePerm d p else palindromePerm d q) := by
    cases b <;> rfl
  simp only [palindrome_matches_step,hp]

lemma child_power_product_bound (d : ℕ) {ι : Type*} [Fintype ι]
    (x y : ι ↪ Bool × Card d) (c : ι → Bool)
    (hcx : PairRouting.Compatible x c) (hcy : PairRouting.Compatible y c) (a : ℝ)
    (hfalse : (PairRouting.tupleProbability (palindromePerm d)
        (PairRouting.childEmbedding x c hcx false) (PairRouting.childEmbedding y c hcy false))^(1+a) ≤
      (2:ℝ)^(-(d:ℝ)*Fintype.card {i // c i = false}*a) *
        routingMoment d (PairRouting.childEmbedding x c hcx false) (PairRouting.childEmbedding y c hcy false) a)
    (htrue : (PairRouting.tupleProbability (palindromePerm d)
        (PairRouting.childEmbedding x c hcx true) (PairRouting.childEmbedding y c hcy true))^(1+a) ≤
      (2:ℝ)^(-(d:ℝ)*Fintype.card {i // c i = true}*a) *
        routingMoment d (PairRouting.childEmbedding x c hcx true) (PairRouting.childEmbedding y c hcy true) a) :
    (PairRouting.tupleProbability (palindromePerm d)
      (PairRouting.childEmbedding x c hcx false) (PairRouting.childEmbedding y c hcy false))^(1+a) *
      (PairRouting.tupleProbability (palindromePerm d)
        (PairRouting.childEmbedding x c hcx true) (PairRouting.childEmbedding y c hcy true))^(1+a) ≤
    (2:ℝ)^(-(d:ℝ)*Fintype.card ι*a) *
      finiteMean (fun ω : BenesCoins d × BenesCoins d =>
        if PairRouting.ChildMatches (fun b => palindromePerm d (if b then ω.2 else ω.1)) x y c
        then (2:ℝ)^(((palindromeCost d (PairRouting.childEmbedding x c hcx false) ω.1 : ℝ) +
          palindromeCost d (PairRouting.childEmbedding x c hcx true) ω.2)*a) else 0) := by
  have hh := mul_le_mul hfalse htrue
    (Real.rpow_nonneg (PairRouting.tupleProbability_nonneg _ _ _) _)
    (mul_nonneg (by positivity) (routingMoment_nonneg _ _ _ _))
  rw [mul_mul_mul_comm,child_moment_product,←Real.rpow_add (by norm_num : (0:ℝ)<2)] at hh
  have he : -(d:ℝ)*Fintype.card {i // c i = false}*a + -(d:ℝ)*Fintype.card {i // c i = true}*a =
      -(d:ℝ)*Fintype.card ι*a := by
    rw [←add_mul,←mul_add,←Nat.cast_add,PairRouting.color_card_add]
  rwa [he] at hh

lemma assignment_moment_bound (d : ℕ) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x y : ι ↪ Bool × Card d) (c : ι → Bool) (hc : c ∈ PairRouting.compatibleSet x y)
    (a : ℝ) (ha : 0 ≤ a) :
    let hcx := ((PairRouting.mem_compatibleSet x y c).mp hc).1
    PairRouting.outerWeight x y ^ a * ((PairRouting.compatibleSet x y).card:ℝ)^a *
      ((2:ℝ)^(-(d:ℝ)*Fintype.card ι*a) *
        finiteMean (fun ω : BenesCoins d × BenesCoins d =>
          if PairRouting.ChildMatches (fun b => palindromePerm d (if b then ω.2 else ω.1)) x y c
          then (2:ℝ)^(((palindromeCost d (PairRouting.childEmbedding x c hcx false) ω.1 : ℝ) +
            palindromeCost d (PairRouting.childEmbedding x c hcx true) ω.2)*a) else 0)) ≤
    (2:ℝ)^(-((d:ℝ)+1)*Fintype.card ι*a) *
      finiteMean (fun ω : BenesCoins d × BenesCoins d =>
        if PairRouting.ChildMatches (fun b => palindromePerm d (if b then ω.2 else ω.1)) x y c
        then (2:ℝ)^((assignmentCost d x c hcx ω:ℝ)*a) else 0) := by
  classical
  intro hcx
  have hscale (q : ℝ) (F : BenesCoins d × BenesCoins d → ℝ) :
      q * finiteMean F = finiteMean (fun ω => q * F ω) := by
    simp_rw [mul_comm q,finiteMean_mul_const]
  rw [←mul_assoc,hscale,hscale]
  apply finiteMean_mono
  intro ω
  split_ifs with hm
  · have hh := PairRouting.assignment_factor_bound x y c hc
      (fun b => palindromePerm d (if b then ω.2 else ω.1)) hm a ha
    calc
      _ ≤ ((2:ℝ)^(((PairRouting.alternatingCycles (PairRouting.coloredEmbedding x c hcx)
          (fun b => palindromePerm d (if b then ω.2 else ω.1)):ℝ)-Fintype.card ι)*a) *
          (2:ℝ)^(-(d:ℝ)*Fintype.card ι*a)) *
          (2:ℝ)^(((palindromeCost d (PairRouting.childEmbedding x c hcx false) ω.1 : ℝ) +
            palindromeCost d (PairRouting.childEmbedding x c hcx true) ω.2)*a) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hh (by positivity)) (by positivity)
      _ = _ := by
        simp only [←Real.rpow_add (by norm_num : (0:ℝ)<2),assignmentCost,Nat.cast_add]
        congr 1
        ring
  · simp only [mul_zero]
    exact le_rfl

theorem palindrome_pointwise_moment (d : ℕ) {ι : Type*} [Fintype ι]
    (e f : ι ↪ Card d) (a : ℝ) (ha : 0 ≤ a) :
    (PairRouting.tupleProbability (palindromePerm d) e f)^(1+a) ≤
      (2:ℝ)^(-(d:ℝ)*Fintype.card ι*a) * routingMoment d e f a := by
  classical
  induction d generalizing ι with
  | zero =>
      have he : ∀ (ω : BenesCoins 0) (i : ι), palindromePerm 0 ω (e i) = f i :=
        fun _ _ => Subsingleton.elim _ _
      simp [PairRouting.tupleProbability,routingMoment,he,palindromeCost,finiteMean_const]
  | succ d ih =>
      let x := e.trans (headTailEquiv d).toEmbedding
      let y := f.trans (headTailEquiv d).toEmbedding
      let W := PairRouting.outerWeight x y
      let C := PairRouting.compatibleSet x y
      let p : (ι → Bool) → ℝ := fun c =>
        (PairRouting.tupleProbability (palindromePerm d)
          (fun i : {i // c i = false} => (x i.val).2)
          (fun i : {i // c i = false} => (y i.val).2))^(1+a) *
        (PairRouting.tupleProbability (palindromePerm d)
          (fun i : {i // c i = true} => (x i.val).2)
          (fun i : {i // c i = true} => (y i.val).2))^(1+a)
      let m : {c // c ∈ C} → ℝ := fun c =>
        finiteMean (fun ω : BenesCoins d × BenesCoins d =>
          if PairRouting.ChildMatches (fun b => palindromePerm d (if b then ω.2 else ω.1)) x y c.val
          then (2:ℝ)^((assignmentCost d x c.val
            ((PairRouting.mem_compatibleSet x y c.val).mp c.property).1 ω:ℝ)*a) else 0)
      have hp (c : {c // c ∈ C}) : W^a * (C.card:ℝ)^a * p c.val ≤
          (2:ℝ)^(-((d:ℝ)+1)*Fintype.card ι*a) * m c := by
        obtain ⟨hcx,hcy⟩ := (PairRouting.mem_compatibleSet x y c.val).mp c.property
        have h₀ := ih (PairRouting.childEmbedding x c.val hcx false)
          (PairRouting.childEmbedding y c.val hcy false)
        have h₁ := ih (PairRouting.childEmbedding x c.val hcx true)
          (PairRouting.childEmbedding y c.val hcy true)
        have hh := child_power_product_bound d x y c.val hcx hcy a h₀ h₁
        have hh' := mul_le_mul_of_nonneg_left hh
          (mul_nonneg (Real.rpow_nonneg (le_of_lt (PairRouting.outerWeight_pos x y)) a)
            (Real.rpow_nonneg (Nat.cast_nonneg C.card) a))
        exact hh'.trans (assignment_moment_bound d x y c.val c.property a ha)
      have hnode := PairRouting.sandwich_power_bound (palindromePerm d) (palindromePerm d) x y a ha
      rw [←palindrome_probability_step d e f] at hnode
      change (PairRouting.tupleProbability (palindromePerm (d+1)) e f)^(1+a) ≤
        W^(1+a) * (C.card:ℝ)^a * ∑ c ∈ C, p c at hnode
      have hsum : ∑ c ∈ C, p c = ∑ c : {c // c ∈ C}, p c.val := by
        rw [Finset.sum_subtype C (fun _ => Iff.rfl)]
      have hW : 0 < W := PairRouting.outerWeight_pos x y
      calc
        _ ≤ W^(1+a) * (C.card:ℝ)^a * ∑ c ∈ C, p c := hnode
        _ = W * ∑ c : {c // c ∈ C}, W^a * (C.card:ℝ)^a * p c.val := by
          rw [Real.rpow_add hW,Real.rpow_one,hsum,←Finset.mul_sum]
          ring
        _ ≤ W * ∑ c : {c // c ∈ C}, (2:ℝ)^(-((d:ℝ)+1)*Fintype.card ι*a) * m c :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun c _ => hp c)) (le_of_lt hW)
        _ = _ := by
          rw [←Finset.mul_sum,routingMoment_step]
          simp only [Nat.cast_add,Nat.cast_one]
          change W * ((2:ℝ)^(-((d:ℝ)+1)*Fintype.card ι*a) * ∑ c, m c) =
            (2:ℝ)^(-((d:ℝ)+1)*Fintype.card ι*a) * (W * ∑ c, m c)
          ring

lemma routingMoment_sum (d : ℕ) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (a : ℝ) :
    (∑ f : ι ↪ Card d, routingMoment d e f a) =
      finiteMean (fun ω : BenesCoins d => (2:ℝ)^((palindromeCost d e ω:ℝ)*a)) := by
  classical
  unfold routingMoment
  rw [←finiteMean_sum]
  apply finiteMean_congr
  intro ω
  let f₀ : ι ↪ Card d := e.trans (palindromePerm d ω).toEmbedding
  rw [Finset.sum_eq_single f₀]
  · have hm : ∀ i, palindromePerm d ω (e i) = f₀ i := fun _ => rfl
    simp only [hm,implies_true,↓reduceIte]
  · intro f _ hf
    have hm : ¬ ∀ i, palindromePerm d ω (e i) = f i := by
      intro hh
      apply hf
      ext i : 1
      exact (hh i).symm
    exact ite_eq_right hm
  · simp

lemma finite_row_power {X : Type*} [Fintype X] [Nonempty X]
    (p : X → ℝ) (hp : ∀ x, 0 ≤ p x) (a : ℝ) :
    finiteMean (fun x => ((Fintype.card X:ℝ)*p x)^(1+a)) =
      (Fintype.card X:ℝ)^a * ∑ x, (p x)^(1+a) := by
  have hn : (0:ℝ) < Fintype.card X := Nat.cast_pos.mpr Fintype.card_pos
  simp only [finiteMean,Real.mul_rpow (le_of_lt hn) (hp _),←Finset.mul_sum]
  rw [Real.rpow_add hn,Real.rpow_one]
  field_simp

lemma density_normalization (d h n : ℕ) (a : ℝ) :
    (n:ℝ)^a * (2:ℝ)^(-(d:ℝ)*h*a) = ((n:ℝ)/((2:ℝ)^d)^h)^a := by
  rw [Real.div_rpow (Nat.cast_nonneg _) (by positivity),←pow_mul,
    ←Real.rpow_natCast,←Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2),Nat.cast_mul]
  rw [show -(d:ℝ)*h*a = -((d:ℝ)*h*a) by ring,
    Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),div_eq_mul_inv]

theorem palindrome_row_density_moment (d : ℕ) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (a : ℝ) (ha : 0 ≤ a) :
    palindromeRowMoment d e a ≤
      (((2^d).descFactorial (Fintype.card ι):ℝ)/((2^d:ℕ):ℝ)^(Fintype.card ι))^a *
        finiteMean (fun ω : BenesCoins d => (2:ℝ)^((palindromeCost d e ω:ℝ)*a)) := by
  classical
  have : Nonempty (ι ↪ Card d) := ⟨e⟩
  rw [palindromeRowMoment,finite_row_power _ (fun f => PairRouting.tupleProbability_nonneg _ _ _)]
  calc
    _ ≤ (Fintype.card (ι ↪ Card d):ℝ)^a *
      ∑ f : ι ↪ Card d, (2:ℝ)^(-(d:ℝ)*Fintype.card ι*a) * routingMoment d e f a :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun f _ => palindrome_pointwise_moment d e f a ha))
        (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    _ = _ := by
      rw [←Finset.mul_sum,routingMoment_sum,←mul_assoc,density_normalization,
        Fintype.card_embedding_eq,card_positions]
      norm_cast

end Thorp
namespace Thorp

lemma subset_biUnion_indicator {α β : Type*} [DecidableEq α] [Fintype β]
    (A : Finset α) (T : β → Finset α) :
    (if Finset.univ.biUnion T ⊆ A then (1:ℝ) else 0) =
      ∏ b, if T b ⊆ A then (1:ℝ) else 0 := by
  classical
  by_cases h : Finset.univ.biUnion T ⊆ A
  · rw [ite_eq_left h]
    symm
    apply Finset.prod_eq_one
    intro b _
    rw [ite_eq_left]
    exact (Finset.subset_biUnion_of_mem T (Finset.mem_univ b)).trans h
  · rw [ite_eq_right h]
    obtain ⟨x,hx,hxA⟩ := Finset.not_subset.mp h
    obtain ⟨b,_,hxb⟩ := Finset.mem_biUnion.mp hx
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ b)
    rw [ite_eq_right]
    exact fun hb => hxA (hb hxb)

lemma cylinder_block_polynomial {α β Ω : Type*} [DecidableEq α] [Fintype β]
    [Fintype Ω] (τ : β → Type*) [∀ b, Fintype (τ b)]
    (F : Ω → Finset α) (p : α → ℝ)
    (hF : CylinderBound (inclusionMoment F) p)
    (T : ∀ b, τ b → Finset α) (c : ∀ b, τ b → ℝ)
    (hc : ∀ b s, 0 ≤ c b s)
    (hd : ∀ b b', b ≠ b' → ∀ s s', Disjoint (T b s) (T b' s')) :
    finiteMean (fun ω => ∏ b, ∑ s, c b s * if T b s ⊆ F ω then 1 else 0) ≤
      ∏ b, ∑ s, c b s * ∏ x ∈ T b s, p x := by
  classical
  simp_rw [Fintype.prod_sum]
  rw [finiteMean_sum]
  apply Finset.sum_le_sum
  intro s _
  let U := Finset.univ.biUnion (fun b => T b (s b))
  have he : (fun ω => ∏ b, c b (s b) * if T b (s b) ⊆ F ω then 1 else 0) =
      fun ω => (if U ⊆ F ω then 1 else 0) * ∏ b, c b (s b) := by
    funext ω
    rw [Finset.prod_mul_distrib,←subset_biUnion_indicator]
    exact mul_comm _ _
  rw [he,finiteMean_mul_const]
  have hdis : ((Finset.univ : Finset β) : Set β).PairwiseDisjoint (fun b => T b (s b)) := by
    intro b _ b' _ hbb
    exact hd b b' hbb (s b) (s b')
  have hmean : finiteMean (fun ω => if U ⊆ F ω then 1 else 0) = inclusionMoment F U := by
    unfold inclusionMoment
    apply finiteMean_congr
    intro ω
    by_cases hh : U ⊆ F ω <;> simp [hh]
  calc
    _ ≤ (∏ x ∈ U, p x) * ∏ b, c b (s b) :=
      mul_le_mul_of_nonneg_right (hmean.le.trans (hF U)) (Finset.prod_nonneg (fun b _ => hc b (s b)))
    _ = _ := by
      dsimp only [U]
      rw [Finset.prod_biUnion hdis,←Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro b _
      exact mul_comm _ _


lemma sparseCoefficient_nonneg {α : Type*} (w : ℝ) (hw : 0 ≤ w) (T : Finset α) :
    0 ≤ sparseCoefficient w T := by
  unfold sparseCoefficient
  split_ifs <;> positivity

lemma sparse_block_pointwise {α : Type*} [DecidableEq α] (A D : Finset α)
    (w : ℝ) (hw : 0 ≤ w) :
    w^(if 2 ≤ (D ∩ A).card then (D ∩ A).card else 0) ≤
      ∑ T : ↑D.powerset, sparseCoefficient w T.val * if T.val ⊆ A then 1 else 0 := by
  classical
  let V := D ∩ A
  let T : ↑D.powerset := if 2 ≤ V.card then
    ⟨V,Finset.mem_powerset.mpr Finset.inter_subset_left⟩ else
    ⟨∅,Finset.mem_powerset.mpr (Finset.empty_subset D)⟩
  calc
    _ = sparseCoefficient w T.val * (if T.val ⊆ A then 1 else 0) := by
      by_cases h : 2 ≤ V.card
      · have hn : V.card ≠ 1 := by omega
        simp [T,ite_eq_left h,sparseCoefficient,hn,show V ⊆ A from Finset.inter_subset_right,V]
      · simp [T,ite_eq_right h,sparseCoefficient,V] at *
    _ ≤ _ := Finset.single_le_sum (f := fun S : ↑D.powerset =>
      sparseCoefficient w S.val * (if S.val ⊆ A then 1 else 0))
      (fun S _ => mul_nonneg (sparseCoefficient_nonneg w hw S.val)
        (by split_ifs <;> norm_num)) (Finset.mem_univ T)

lemma geometric_sum_half (n : ℕ) {x : ℝ} (hx : 0 ≤ x) (hhalf : x ≤ 1/2) :
    ∑ i ∈ Finset.range n, x^i ≤ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ',pow_zero]
    simp only [pow_succ',←Finset.mul_sum]
    nlinarith

lemma sparse_binomial_bound (R : ℕ) (z : ℝ) (hz : 0 ≤ z) (hr : (R:ℝ)*z ≤ 1/2) :
    ∑ i ∈ Finset.range (R+1), (R.choose i:ℝ) * (if i = 1 then 0 else z^i) ≤
      1 + 2*((R:ℝ)*z)^2 := by
  classical
  let x := (R:ℝ)*z
  have hx : 0 ≤ x := mul_nonneg (Nat.cast_nonneg _) hz
  have hbound (i : ℕ) : (R.choose i:ℝ)*(if i=1 then 0 else z^i) ≤
      if i=1 then 0 else x^i := by
    by_cases h : i=1
    · simp [h]
    · simp only [ite_eq_right h]
      dsimp [x]
      rw [mul_pow]
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hz i)
      exact_mod_cast Nat.choose_le_pow R i
  calc
    _ ≤ ∑ i ∈ Finset.range (R+1), if i=1 then 0 else x^i :=
      Finset.sum_le_sum (fun i _ => hbound i)
    _ ≤ 1+2*x^2 := by
      rcases R with _ | R
      · simp [x]
      rcases R with _ | R
      · norm_num [Finset.sum_range_succ]
        positivity
      have he : ∑ i ∈ Finset.range (R+2+1), (if i=1 then 0 else x^i) =
          1 + x^2*∑ i ∈ Finset.range (R+1), x^i := by
        rw [show R+2+1=2+(R+1) by omega,Finset.sum_range_add]
        have hn (i : ℕ) : 2+i ≠ 1 := by omega
        simp only [hn,ite_false,pow_add,←Finset.mul_sum]
        norm_num [Finset.sum_range_succ]
      rw [he]
      have hg := geometric_sum_half (R+1) hx hr
      nlinarith [sq_nonneg x]

lemma sparse_block_product_bound {α : Type*} [DecidableEq α]
    (D : Finset α) (p w : ℝ) (hp : 0 ≤ p) (hw : 0 ≤ w)
    (hr : (D.card:ℝ)*(p*w) ≤ 1/2) :
    ∑ T : ↑D.powerset, sparseCoefficient w T.val * p^T.val.card ≤
      Real.exp (2*((D.card:ℝ)*(p*w))^2) := by
  classical
  have he : ∑ T : ↑D.powerset, sparseCoefficient w T.val * p^T.val.card =
      ∑ i ∈ Finset.range (D.card+1), (D.card.choose i:ℝ)*(if i=1 then 0 else (p*w)^i) := by
    rw [Finset.sum_coe_sort D.powerset (fun T => sparseCoefficient w T*p^T.card)]
    have hh : (fun T : Finset α => sparseCoefficient w T*p^T.card) =
        fun T => if T.card=1 then 0 else (p*w)^T.card := by
      funext T
      unfold sparseCoefficient
      split_ifs <;> simp [mul_pow,mul_comm]
    change (∑ T ∈ D.powerset, (fun T : Finset α => sparseCoefficient w T*p^T.card) T) = _
    rw [hh,Finset.sum_powerset_apply_card (fun i => if i=1 then (0:ℝ) else (p*w)^i)]
    simp only [nsmul_eq_mul]
  rw [he]
  exact (sparse_binomial_bound D.card (p*w) (mul_nonneg hp hw) hr).trans
    (by simpa only [add_comm] using Real.add_one_le_exp (2*((D.card:ℝ)*(p*w))^2))


theorem sparse_block_mgf {α β Ω : Type*} [DecidableEq α] [Fintype β] [Fintype Ω]
    (D : β → Finset α) (hd : Pairwise (fun b b' => Disjoint (D b) (D b')))
    (F : Ω → Finset α) (p w : ℝ) (hp : 0 ≤ p) (hw : 0 ≤ w)
    (hF : ∀ T, inclusionMoment F T ≤ p^T.card)
    (hr : ∀ b, ((D b).card:ℝ)*(p*w) ≤ 1/2) :
    finiteMean (fun ω => w^(sparseMass D (F ω))) ≤
      Real.exp (∑ b, 2*(((D b).card:ℝ)*(p*w))^2) := by
  classical
  have hc : CylinderBound (inclusionMoment F) (fun _ => p) := by
    intro T
    simpa only [Finset.prod_const] using hF T
  have hb := cylinder_block_polynomial (fun b => ↑(D b).powerset) F (fun _ => p) hc
    (fun _ S => S.val) (fun _ S => sparseCoefficient w S.val)
    (fun _ S => sparseCoefficient_nonneg w hw S.val)
    (fun b b' h S S' => (hd h).mono
      (Finset.mem_powerset.mp S.property) (Finset.mem_powerset.mp S'.property))
  calc
    _ ≤ finiteMean (fun ω => ∏ b, ∑ S : ↑(D b).powerset,
        sparseCoefficient w S.val * if S.val ⊆ F ω then 1 else 0) := by
      apply finiteMean_mono
      intro ω
      rw [sparseMass,←Finset.prod_pow_eq_pow_sum]
      apply Finset.prod_le_prod (fun _ _ => pow_nonneg hw _)
      intro b _
      exact sparse_block_pointwise (F ω) (D b) w hw
    _ ≤ ∏ b, ∑ S : ↑(D b).powerset, sparseCoefficient w S.val * p^S.val.card := by
      simpa only [Finset.prod_const] using hb
    _ ≤ _ := by
      rw [Real.exp_sum]
      apply Finset.prod_le_prod
      · intro b _
        exact Finset.sum_nonneg (fun S _ => mul_nonneg
          (sparseCoefficient_nonneg w hw S.val) (pow_nonneg hp _))
      · intro b _
        exact sparse_block_product_bound (D b) p w hp hw (hr b)

theorem inverseButterfly_sparse_mgf (d : ℕ) {β : Type*} [Fintype β]
    (D : β → Finset (Card d)) (hd : Pairwise (fun b b' => Disjoint (D b) (D b')))
    (A : Finset (Card d)) (w : ℝ) (hw : 0 ≤ w)
    (hr : ∀ b, ((D b).card:ℝ)*((A.card/(2:ℝ)^d)*w) ≤ 1/2) :
    finiteMean (fun ω : SwitchIndex d → Bool =>
      w^(sparseMass D (inverseButterflyMarks d A ω))) ≤
      Real.exp (∑ b, 2*(((D b).card:ℝ)*((A.card/(2:ℝ)^d)*w))^2) := by
  apply sparse_block_mgf D hd (inverseButterflyMarks d A) (A.card/(2:ℝ)^d) w
    (by positivity) hw
  · exact inverseButterflyMarks_inclusion d A
  · exact hr


lemma crowdedMass_le (h : ℕ) : crowdedMass h ≤ h := by
  unfold crowdedMass
  split_ifs <;> omega

lemma crowdedMass_add (u v : ℕ) : crowdedMass u + crowdedMass v ≤ crowdedMass (u+v) := by
  unfold crowdedMass
  split_ifs <;> omega

lemma alternatingCycles_le_crowded {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α]
    (e : ι ↪ Bool × α) (p : Bool → Equiv.Perm α) :
    PairRouting.alternatingCycles e p ≤ crowdedMass (Fintype.card ι) := by
  unfold crowdedMass
  split_ifs with h
  · have hh := PairRouting.alternatingCycles_double e p
    omega
  · rw [PairRouting.alternatingCycles_zero e p (by omega)]

lemma palindromeCost_le_crowded (d : ℕ) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (ω : BenesCoins d) :
    palindromeCost d e ω ≤ d*crowdedMass (Fintype.card ι) := by
  classical
  induction d generalizing ι with
  | zero => simp [palindromeCost]
  | succ d ih =>
    let σ := benesStepEquiv d ω
    let x := e.trans (headTailEquiv d).toEmbedding
    let c := PairRouting.colors x σ.2.1
    let hc := PairRouting.colors_compatible x σ.2.1
    have h₀ := ih (PairRouting.childEmbedding x c hc false) σ.1.1
    have h₁ := ih (PairRouting.childEmbedding x c hc true) σ.1.2
    have hz := alternatingCycles_le_crowded (PairRouting.switchedEmbedding x σ.2.1)
      (fun b => palindromePerm d (if b then σ.1.2 else σ.1.1))
    have hs := crowdedMass_add (Fintype.card {i // c i = false})
      (Fintype.card {i // c i = true})
    rw [PairRouting.color_card_add] at hs
    change PairRouting.alternatingCycles (PairRouting.switchedEmbedding x σ.2.1)
        (fun b => palindromePerm d (if b then σ.1.2 else σ.1.1)) +
        palindromeCost d (PairRouting.childEmbedding x c hc false) σ.1.1 +
        palindromeCost d (PairRouting.childEmbedding x c hc true) σ.1.2 ≤ _
    nlinarith

lemma palindromeLowCost_eq (H d : ℕ) (h : d ≤ H) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (ω : BenesCoins d) :
    palindromeLowCost H d e ω = palindromeCost d e ω := by
  classical
  induction d generalizing ι with
  | zero => rfl
  | succ d ih =>
    rw [palindromeLowCost,palindromeCost,ite_eq_left h]
    congr 2 <;> exact ih (by omega) _ _

lemma palindromeLowCost_le_cutoff (H d : ℕ) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (ω : BenesCoins d) :
    palindromeLowCost H d e ω ≤ H*cutoffMass H d e ω := by
  classical
  induction d generalizing ι with
  | zero => simp [palindromeLowCost,cutoffMass]
  | succ d ih =>
    by_cases h : d+1 ≤ H
    · rw [palindromeLowCost_eq H (d+1) h,cutoffMass,ite_eq_left h]
      exact (palindromeCost_le_crowded (d+1) e ω).trans (Nat.mul_le_mul_right _ h)
    · rw [palindromeLowCost,cutoffMass,ite_eq_right h,ite_eq_right h,zero_add,Nat.mul_add]
      exact Nat.add_le_add (ih _ _) (ih _ _)


end Thorp

end ThorpNine.Adaptive

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Adaptive_ParallelFreshPre
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Adaptive

namespace Thorp

lemma mem_centralBlock (r H : ℕ) (b : Card r) (x : Card (H+r)) :
    x ∈ centralBlock r H b ↔ (cardSplit r H x).1 = b := by
  classical
  constructor
  · intro h
    obtain ⟨z,_,rfl⟩ := Finset.mem_image.mp h
    simp only [Equiv.apply_symm_apply]
  · intro h
    apply Finset.mem_image.mpr
    refine ⟨(cardSplit r H x).2,Finset.mem_univ _,?_⟩
    rw [←h,Prod.mk.eta,Equiv.symm_apply_apply]

lemma centralBlock_card (r H : ℕ) (b : Card r) : (centralBlock r H b).card = 2^H := by
  classical
  rw [centralBlock,Finset.card_image_of_injective]
  · exact card_positions H
  · intro x y h
    exact congrArg Prod.snd ((cardSplit r H).symm.injective h)

lemma centralBlock_disjoint (r H : ℕ) :
    Pairwise (fun b b' => Disjoint (centralBlock r H b) (centralBlock r H b')) := by
  classical
  intro b b' h
  apply Finset.disjoint_left.mpr
  intro x hx hy
  exact h (((mem_centralBlock r H b x).mp hx).symm.trans
    ((mem_centralBlock r H b' x).mp hy))

lemma centralBlock_zero (H : ℕ) (b : Card 0) : centralBlock 0 H b = Finset.univ := by
  classical
  ext x
  simp only [mem_centralBlock,Finset.mem_univ,iff_true]
  exact Subsingleton.elim _ _

lemma centralBlock_step (r H : ℕ) (b : Bool) (c : Card r) :
    centralBlock (r+1) H (Fin.cons b c) = (centralBlock r H c).image (Fin.cons b) := by
  classical
  simp only [centralBlock,Finset.image_image,cardSplit,Equiv.coe_fn_symm_mk,
    Fin.cons_zero,Fin.tail_cons,Function.comp_def]

lemma block_inter_step (r H : ℕ) (b : Bool) (c : Card r) (A : Finset (Card (H+(r+1)))) :
    centralBlock (r+1) H (Fin.cons b c) ∩ A =
      (centralBlock r H c ∩ childMarks A b).image (Fin.cons b) := by
  classical
  rw [centralBlock_step]
  ext x
  constructor
  · intro hx
    obtain ⟨hxB,hxA⟩ := Finset.mem_inter.mp hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hxB
    exact Finset.mem_image.mpr ⟨y,Finset.mem_inter.mpr ⟨hy,(mem_childMarks A b y).mpr hxA⟩,rfl⟩
  · intro hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_inter.mpr ⟨Finset.mem_image.mpr ⟨y,(Finset.mem_inter.mp hy).1,rfl⟩,
      (mem_childMarks A b y).mp (Finset.mem_inter.mp hy).2⟩

lemma sparseMass_central_zero (H : ℕ) (A : Finset (Card H)) :
    sparseMass (centralBlock 0 H) A = crowdedMass A.card := by
  classical
  simp only [sparseMass,centralBlock_zero,Finset.univ_inter,crowdedMass,
    Finset.sum_const,Finset.card_univ,card_positions,pow_zero,one_nsmul]

lemma sparseMass_central_step (r H : ℕ) (A : Finset (Card (H+(r+1)))) :
    sparseMass (centralBlock (r+1) H) A =
      sparseMass (centralBlock r H) (childMarks A false) +
        sparseMass (centralBlock r H) (childMarks A true) := by
  classical
  unfold sparseMass
  rw [←Equiv.sum_comp (headTailEquiv r).symm,Fintype.sum_prod_type]
  have ht (b : Bool) (c : Card r) : (headTailEquiv r).symm (b,c) = Fin.cons b c := rfl
  simp only [Fintype.sum_bool,ht]
  have hc (b : Bool) (c : Card r) :
      (centralBlock (r+1) H (Fin.cons b c) ∩ A).card =
      (centralBlock r H c ∩ childMarks A b).card := by
    rw [block_inter_step]
    apply Finset.card_image_of_injective
    intro x y h
    simpa only [Fin.tail_cons] using congrArg Fin.tail h
  simp only [hc]
  exact add_comm _ _


lemma inverseButterfly_coordinates_step (d : ℕ)
    (c : (SwitchIndex d → Bool) × (SwitchIndex d → Bool)) (ξ : Card d → Bool)
    (x : Card (d+1)) :
    headTailEquiv d ((butterflyPerm (d+1)
      (decodeButterfly (d+1) ((coinStepEquiv d).symm (c,ξ)))).symm x) =
      (Bool.xor (x 0) (ξ (Fin.tail x)),
        (butterflyPerm d (decodeButterfly d
          (if Bool.xor (x 0) (ξ (Fin.tail x)) then c.2 else c.1))).symm (Fin.tail x)) := by
  rw [butterflyPerm_step]
  rfl

lemma inverseButterflyMarks_child (d : ℕ) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card (d+1))
    (c : (SwitchIndex d → Bool) × (SwitchIndex d → Bool)) (ξ : Card d → Bool) (b : Bool) :
    childMarks (inverseButterflyMarks (d+1) (Finset.univ.image e)
      ((coinStepEquiv d).symm (c,ξ))) b =
      inverseButterflyMarks d
        (Finset.univ.image (PairRouting.childEmbedding (e.trans (headTailEquiv d).toEmbedding)
          (PairRouting.colors (e.trans (headTailEquiv d).toEmbedding) ξ)
            (PairRouting.colors_compatible _ _) b)) (if b then c.2 else c.1) := by
  classical
  let x := e.trans (headTailEquiv d).toEmbedding
  let col := PairRouting.colors x ξ
  let child := PairRouting.childEmbedding x col (PairRouting.colors_compatible x ξ) b
  have hp (i : ι) : headTailEquiv d ((butterflyPerm (d+1)
      (decodeButterfly (d+1) ((coinStepEquiv d).symm (c,ξ)))).symm (e i)) =
      (col i,(butterflyPerm d (decodeButterfly d (if col i then c.2 else c.1))).symm (x i).2) :=
    inverseButterfly_coordinates_step d c ξ (e i)
  ext y
  simp only [mem_childMarks,inverseButterflyMarks,Finset.image_image,
    Finset.mem_image,Finset.mem_univ,true_and,Function.comp_def]
  constructor
  · rintro ⟨i,hi⟩
    have he := congrArg (headTailEquiv d) hi
    rw [hp i] at he
    change (col i,_) = (b,y) at he
    have hb := congrArg Prod.fst he
    have hy := congrArg Prod.snd he
    dsimp only at hb hy
    refine ⟨⟨i,hb⟩,?_⟩
    change (butterflyPerm d (decodeButterfly d (if b then c.2 else c.1))).symm (x i).2 = y
    simpa only [hb] using hy
  · rintro ⟨i,hi⟩
    refine ⟨i.val,?_⟩
    apply (headTailEquiv d).injective
    rw [hp]
    change (col i.val,_) = (b,y)
    have hb : col i.val = b := i.property
    rw [hb]
    exact Prod.ext rfl hi

lemma inverseButterflyMarks_card (d : ℕ) (A : Finset (Card d)) (ω : SwitchIndex d → Bool) :
    (inverseButterflyMarks d A ω).card = A.card := by
  classical
  exact Finset.card_image_of_injective _ (butterflyPerm d (decodeButterfly d ω)).symm.injective

lemma benes_input_coordinates (d : ℕ) (ω : BenesCoins (d+1)) :
    ω.2 = (coinStepEquiv d).symm
      (((benesStepEquiv d ω).1.1.2,(benesStepEquiv d ω).1.2.2),(benesStepEquiv d ω).2.1) := by
  change ω.2 = (coinStepEquiv d).symm (coinStepEquiv d ω.2)
  exact ((coinStepEquiv d).symm_apply_apply ω.2).symm

lemma cutoffMass_central (r H : ℕ) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card (H+r)) (ω : BenesCoins (H+r)) :
    cutoffMass H (H+r) e ω =
      sparseMass (centralBlock r H) (inverseButterflyMarks (H+r) (Finset.univ.image e) ω.2) := by
  classical
  induction r generalizing ι with
  | zero =>
    rw [sparseMass_central_zero,inverseButterflyMarks_card,
      Finset.card_image_of_injective _ e.injective,Finset.card_univ]
    cases H with
    | zero =>
      have hcard : Fintype.card ι ≤ 1 := by
        have hh := Fintype.card_le_of_injective e e.injective
        simpa only [Nat.add_zero,card_positions,pow_zero] using hh
      simp [cutoffMass,crowdedMass,show ¬2≤Fintype.card ι by omega]
    | succ H => simp only [cutoffMass,le_refl,ite_true]
  | succ r ih =>
    simp only [Nat.add_succ] at *
    rw [cutoffMass,ite_eq_right (by omega : ¬H+r+1≤H)]
    let σ := benesStepEquiv (H+r) ω
    let x := e.trans (headTailEquiv (H+r)).toEmbedding
    let col := PairRouting.colors x σ.2.1
    let hc := PairRouting.colors_compatible x σ.2.1
    change cutoffMass H (H+r) (PairRouting.childEmbedding x col hc false) σ.1.1 +
      cutoffMass H (H+r) (PairRouting.childEmbedding x col hc true) σ.1.2 = _
    rw [ih,ih,sparseMass_central_step,benes_input_coordinates (H+r) ω]
    rw [inverseButterflyMarks_child,inverseButterflyMarks_child]
    rfl


theorem palindrome_low_mgf (r H : ℕ) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card (H+r)) (q : ℝ) (hq : 1 ≤ q)
    (hr : (2:ℝ)^H*((Fintype.card ι/(2:ℝ)^(H+r))*q^H) ≤ 1/2) :
    finiteMean (fun ω : BenesCoins (H+r) => q^(palindromeLowCost H (H+r) e ω)) ≤
      Real.exp ((2:ℝ)^r * (2 * ((2:ℝ)^H*((Fintype.card ι/(2:ℝ)^(H+r))*q^H))^2)) := by
  classical
  have hec : (Finset.univ.image e).card = Fintype.card ι := by
    rw [Finset.card_image_of_injective _ e.injective,Finset.card_univ]
  have hm := inverseButterfly_sparse_mgf (H+r) (centralBlock r H)
    (centralBlock_disjoint r H) (Finset.univ.image e) (q^H)
    (pow_nonneg (by linarith) _) (fun b => by
      simpa only [centralBlock_card,hec,Nat.cast_pow,Nat.cast_ofNat] using hr)
  calc
    _ ≤ finiteMean (fun ω : BenesCoins (H+r) => (q^H)^(cutoffMass H (H+r) e ω)) := by
      apply finiteMean_mono
      intro ω
      rw [←pow_mul]
      exact pow_le_pow_right₀ hq (palindromeLowCost_le_cutoff H (H+r) e ω)
    _ = finiteMean (fun ω : SwitchIndex (H+r) → Bool =>
        (q^H)^(sparseMass (centralBlock r H)
          (inverseButterflyMarks (H+r) (Finset.univ.image e) ω))) := by
      simp_rw [cutoffMass_central]
      simp only [finiteMean_prod,finiteMean_const]
    _ ≤ _ := by
      simpa only [centralBlock_card,hec,Nat.cast_pow,Nat.cast_ofNat,Finset.sum_const,
        Finset.card_univ,card_positions,nsmul_eq_mul] using hm

end Thorp
namespace Thorp
variable {α : Type*} [Fintype α] [DecidableEq α]

lemma orbitSet_inverse (p : Equiv.Perm α) (x : α) : orbitSet p⁻¹ x = orbitSet p x := by
  ext y
  simp only [mem_orbitSet,Equiv.Perm.sameCycle_inv]

lemma selectedCycle_inverse (p : Equiv.Perm α) (S : Finset α) :
    Fintype.card (RoutingNetwork.SelectedCycle p⁻¹ S) =
      Fintype.card (RoutingNetwork.SelectedCycle p S) := by
  apply Fintype.card_congr
  refine { toFun := fun C => ⟨C.val,?_,C.property.2⟩
           invFun := fun C => ⟨C.val,?_,C.property.2⟩
           left_inv := fun _ => rfl
           right_inv := fun _ => rfl }
  · obtain ⟨x,hx⟩ := C.property.1
    exact ⟨x,hx.trans (orbitSet_inverse p x)⟩
  · obtain ⟨x,hx⟩ := C.property.1
    exact ⟨x,hx.trans (orbitSet_inverse p x).symm⟩

lemma conjugateCycle_injective (p g : Equiv.Perm α) (S : Finset α) :
    Function.Injective (conjugateCycle p g S) := by
  intro C D he
  apply Subtype.ext
  exact (Finset.image_injective g.injective) (congrArg Subtype.val he)

lemma selectedCycle_conjugate (p g : Equiv.Perm α) (S : Finset α) :
    Fintype.card (RoutingNetwork.SelectedCycle (g*p*g⁻¹) (S.image g)) =
      Fintype.card (RoutingNetwork.SelectedCycle p S) := by
  apply Nat.le_antisymm
  · have h := Fintype.card_le_of_injective _
      (conjugateCycle_injective (g*p*g⁻¹) g⁻¹ (S.image g))
    have hp : g⁻¹*(g*p*g⁻¹)*g = p := by group
    rw [inv_inv,hp] at h
    have hs : (S.image g).image g.symm = S := by
      ext x
      simp only [Finset.mem_image]
      constructor
      · rintro ⟨y,⟨z,hz,rfl⟩,he⟩
        have hz' : z = x := by simpa only [Equiv.symm_apply_apply] using he
        exact hz' ▸ hz
      · intro hx
        exact ⟨g x,⟨x,hx,rfl⟩,g.symm_apply_apply x⟩
    change _ ≤ Fintype.card (RoutingNetwork.SelectedCycle p ((S.image g).image g.symm)) at h
    rw [hs] at h
    exact h
  · exact Fintype.card_le_of_injective _ (conjugateCycle_injective p g S)

lemma alternatingCycles_le_projection {ι : Type*} [Fintype ι]
    (e : ι ↪ Bool × α) (p : Bool → Equiv.Perm α) :
    PairRouting.alternatingCycles e p ≤
      Fintype.card (RoutingNetwork.SelectedCycle (PairRouting.alternatingProjection p)
        (boolFiber (PairRouting.labelSet e) false)) := by
  have h := CycleColoring.card_alternating_cycles_le (PairRouting.alternatingProjection p)
    (boolFiber (PairRouting.labelSet e) false) (boolFiber (PairRouting.labelSet e) true)
  simpa only [PairRouting.alternatingCycles,childJoin_boolFiber] using h

lemma projectionCycles_forward (X₀ X₁ Y₀ Y₁ : Equiv.Perm α) (S : Finset α) :
    Fintype.card (RoutingNetwork.SelectedCycle
      ((Y₀*X₀⁻¹)⁻¹*(Y₁*X₁⁻¹)) S) =
    Fintype.card (RoutingNetwork.SelectedCycle
      (X₀⁻¹*X₁*Y₁⁻¹*Y₀) (S.image X₀.symm)) := by
  let p := (Y₀*X₀⁻¹)⁻¹*(Y₁*X₁⁻¹)
  calc
    _ = Fintype.card (RoutingNetwork.SelectedCycle (X₀⁻¹*p*X₀)
        (S.image X₀.symm)) := by
      change Fintype.card (RoutingNetwork.SelectedCycle p S) = _
      have h := (selectedCycle_conjugate p X₀⁻¹ S).symm
      rw [inv_inv] at h
      exact h
    _ = Fintype.card (RoutingNetwork.SelectedCycle (X₀⁻¹*p*X₀)⁻¹
        (S.image X₀.symm)) := (selectedCycle_inverse _ _).symm
    _ = _ := by
      have he : (X₀⁻¹*p*X₀)⁻¹ = X₀⁻¹*X₁*Y₁⁻¹*Y₀ := by dsimp only [p]; group
      rw [he]

end Thorp
namespace Thorp

lemma cycleCoefficient_nonneg (r J : ℕ) (q : ℝ) (hq : 1 ≤ q) :
    0 ≤ cycleCoefficient r J q := by
  unfold cycleCoefficient
  exact add_nonneg (div_nonneg (Real.log_nonneg hq) (Nat.cast_nonneg _))
    (div_nonneg (mul_nonneg (by linarith) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))

lemma projectionSide_card_le {α ι : Type*} [Fintype α] [DecidableEq α] [Fintype ι]
    (e : ι ↪ Bool × α) : (boolFiber (PairRouting.labelSet e) false).card ≤ Fintype.card ι := by
  have h := card_childJoin (boolFiber (PairRouting.labelSet e) false)
    (boolFiber (PairRouting.labelSet e) true)
  rw [childJoin_boolFiber,PairRouting.card_labelSet] at h
  omega

theorem node_partial_mgf (r s : ℕ) {ι : Type*} [Fintype ι]
    (e : ι ↪ Bool × Card (s+r)) (X₀ X₁ Y₁ : Equiv.Perm (Card (s+r)))
    (lo : Card r × SwitchIndex s → Bool) (J : ℕ) (hJ : 0 < J) (q : ℝ) (hq : 1 ≤ q) :
    finiteMean (fun hi : Card s × SwitchIndex r → Bool =>
      q^(PairRouting.alternatingCycles e (fun b => if b then Y₁*X₁⁻¹ else
        butterflyPerm (s+r) (decodeButterfly (s+r) (assembleBits r s lo hi))*X₀⁻¹))) ≤
      Real.exp (Fintype.card ι * cycleCoefficient r J q) := by
  classical
  let S := boolFiber (PairRouting.labelSet e) false
  let S' := S.image X₀.symm
  let post := X₀⁻¹*X₁*Y₁⁻¹
  let count := fun hi : Card s × SwitchIndex r → Bool =>
    Fintype.card (RoutingNetwork.SelectedCycle
      ((Equiv.refl _).trans (butterflyPerm (s+r)
        (decodeButterfly (s+r) (assembleBits r s lo hi))) |>.trans post) S')
  have hpoint (hi : Card s × SwitchIndex r → Bool) :
      PairRouting.alternatingCycles e (fun b => if b then Y₁*X₁⁻¹ else
        butterflyPerm (s+r) (decodeButterfly (s+r) (assembleBits r s lo hi))*X₀⁻¹) ≤ count hi := by
    refine (alternatingCycles_le_projection e _).trans_eq ?_
    simp only [PairRouting.alternatingProjection,Bool.false_eq_true,↓reduceIte]
    change Fintype.card (RoutingNetwork.SelectedCycle
      ((butterflyPerm (s+r) (decodeButterfly (s+r) (assembleBits r s lo hi))*X₀⁻¹)⁻¹ * (Y₁*X₁⁻¹)) S) = count hi
    exact projectionCycles_forward X₀ X₁ _ Y₁ S
  have hm := partially_exposed_cycle_log_mgf (Equiv.refl (Card (s+r))) post lo S' J hJ q hq
  have hp : 0 < finiteMean (fun hi : Card s × SwitchIndex r → Bool => q^(count hi)) :=
    finiteMean_pos (fun _ => pow_pos (by linarith) _)
  have hb : finiteMean (fun hi : Card s × SwitchIndex r → Bool => q^(count hi)) ≤
      Real.exp (S'.card * cycleCoefficient r J q) := by
    rw [←Real.exp_log hp]
    apply Real.exp_le_exp.mpr
    calc
      _ ≤ _ := hm
      _ = _ := by unfold cycleCoefficient; ring
  have hcard : S'.card ≤ Fintype.card ι := by
    rw [show S'.card = S.card from Finset.card_image_of_injective _ X₀.symm.injective]
    exact projectionSide_card_le e
  calc
    _ ≤ finiteMean (fun hi : Card s × SwitchIndex r → Bool => q^(count hi)) :=
      finiteMean_mono (fun hi => pow_le_pow_right₀ hq (hpoint hi))
    _ ≤ Real.exp (S'.card * cycleCoefficient r J q) := hb
    _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
      (by exact_mod_cast hcard) (cycleCoefficient_nonneg r J q hq))


lemma assembleBits_step (r s : ℕ) (lo : Card (r+1) × SwitchIndex s → Bool)
    (c : ((Card s × SwitchIndex r → Bool) × (Card s × SwitchIndex r → Bool)) ×
      (Card s × Card r → Bool)) :
    assembleBits (r+1) s lo ((highStepEquiv r s).symm c) =
      (coinStepEquiv (s+r)).symm
        ((assembleBits r s (fun j => lo (Fin.cons false j.1,j.2)) c.1.1,
          assembleBits r s (fun j => lo (Fin.cons true j.1,j.2)) c.1.2),
        fun y => c.2 ((cardSplit r s y).2,(cardSplit r s y).1)) := by
  funext i
  rcases i with y | ⟨b,i⟩
  · rfl
  · cases b <;> rfl

lemma palindromeLevelCost_step (t d : ℕ) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card (d+1)) (X Y : (SwitchIndex d → Bool) × (SwitchIndex d → Bool))
    (ξ η : Card d → Bool) :
    palindromeLevelCost t (d+1) e
      ((coinStepEquiv d).symm (Y,η),(coinStepEquiv d).symm (X,ξ)) =
      let x := e.trans (headTailEquiv d).toEmbedding
      let c := PairRouting.colors x ξ
      let hc := PairRouting.colors_compatible x ξ
      if t = d+1 then PairRouting.alternatingCycles (PairRouting.switchedEmbedding x ξ)
        (fun b => palindromePerm d (if b then (Y.2,X.2) else (Y.1,X.1))) else
        palindromeLevelCost t d (PairRouting.childEmbedding x c hc false) (Y.1,X.1) +
        palindromeLevelCost t d (PairRouting.childEmbedding x c hc true) (Y.2,X.2) := by
  rw [palindromeLevelCost]
  rfl

lemma palindromeLevelCost_gt (t d : ℕ) (h : d < t) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (ω : BenesCoins d) : palindromeLevelCost t d e ω = 0 := by
  classical
  induction d generalizing ι with
  | zero => rfl
  | succ d ih =>
    rw [palindromeLevelCost,ite_eq_right (by omega : t ≠ d+1),ih (by omega),ih (by omega),Nat.zero_add]


theorem palindrome_level_partial_mgf (r s u : ℕ) (hu : u < r)
    {ι : Type*} [Fintype ι] (e : ι ↪ Card (s+r)) (X : SwitchIndex (s+r) → Bool)
    (lo : Card r × SwitchIndex s → Bool) (J : ℕ) (hJ : 0 < J) (q : ℝ) (hq : 1 ≤ q) :
    finiteMean (fun hi : Card s × SwitchIndex r → Bool =>
      q^(palindromeLevelCost (s+u+1) (s+r) e (assembleBits r s lo hi,X))) ≤
      Real.exp (Fintype.card ι * cycleCoefficient u J q) := by
  classical
  induction r generalizing u ι with
  | zero => omega
  | succ r ih =>
    simp only [Nat.add_succ] at *
    let χ := coinStepEquiv (s+r) X
    let x := e.trans (headTailEquiv (s+r)).toEmbedding
    let c := PairRouting.colors x χ.2
    let hc := PairRouting.colors_compatible x χ.2
    let e₀ := PairRouting.childEmbedding x c hc false
    let e₁ := PairRouting.childEmbedding x c hc true
    let e' := PairRouting.switchedEmbedding x χ.2
    let lo₀ : Card r × SwitchIndex s → Bool := fun j => lo (Fin.cons false j.1,j.2)
    let lo₁ : Card r × SwitchIndex s → Bool := fun j => lo (Fin.cons true j.1,j.2)
    let Y₀ := fun hi : Card s × SwitchIndex r → Bool => assembleBits r s lo₀ hi
    let Y₁ := fun hi : Card s × SwitchIndex r → Bool => assembleBits r s lo₁ hi
    let N := fun hi : (Card s × SwitchIndex r → Bool) × (Card s × SwitchIndex r → Bool) =>
      PairRouting.alternatingCycles e' (fun b => if b then palindromePerm (s+r) (Y₁ hi.2,χ.1.2)
        else palindromePerm (s+r) (Y₀ hi.1,χ.1.1))
    let L₀ := fun hi : Card s × SwitchIndex r → Bool =>
      palindromeLevelCost (s+u+1) (s+r) e₀ (Y₀ hi,χ.1.1)
    let L₁ := fun hi : Card s × SwitchIndex r → Bool =>
      palindromeLevelCost (s+u+1) (s+r) e₁ (Y₁ hi,χ.1.2)
    have hs (hi : (Card s × SwitchIndex r → Bool) × (Card s × SwitchIndex r → Bool))
        (η : Card s × Card r → Bool) :
        palindromeLevelCost (s+u+1) (s+r+1) e
          (assembleBits (r+1) s lo ((highStepEquiv r s).symm (hi,η)),X) =
          if u = r then N hi else L₀ hi.1 + L₁ hi.2 := by
      rw [assembleBits_step]
      conv_lhs => rw [←(coinStepEquiv (s+r)).symm_apply_apply X]
      rw [palindromeLevelCost_step]
      simp only [Nat.add_right_cancel_iff,Nat.add_left_cancel_iff]
      dsimp only [χ,x,c,hc,e₀,e₁,e',lo₀,lo₁,Y₀,Y₁,N,L₀,L₁]
      congr 2
      funext b
      cases b <;> rfl
    rw [finiteMean_equiv (highStepEquiv r s),finiteMean_prod]
    simp_rw [hs,finiteMean_const]
    by_cases hur : u = r
    · subst u
      simp only [ite_true]
      rw [finiteMean_prod,finiteMean_comm]
      calc
        _ ≤ finiteMean (fun _hi : Card s × SwitchIndex r → Bool =>
          Real.exp (Fintype.card ι * cycleCoefficient r J q)) := by
          apply finiteMean_mono
          intro hi
          have hn := node_partial_mgf r s e'
            (butterflyPerm (s+r) (decodeButterfly (s+r) χ.1.1))
            (butterflyPerm (s+r) (decodeButterfly (s+r) χ.1.2))
            (butterflyPerm (s+r) (decodeButterfly (s+r) (Y₁ hi))) lo₀ J hJ q hq
          exact hn
        _ = _ := finiteMean_const _
    · simp only [ite_eq_right hur,pow_add]
      rw [finiteMean_prod_mul (fun hi => q ^ L₀ hi) (fun hi => q ^ L₁ hi)]
      have hu' : u < r := by omega
      have h₀ := ih u hu' e₀ χ.1.1 lo₀
      have h₁ := ih u hu' e₁ χ.1.2 lo₁
      have hp := mul_le_mul h₀ h₁ (finiteMean_nonneg (fun _ => pow_nonneg (by linarith) _))
        (Real.exp_nonneg _)
      refine hp.trans_eq ?_
      rw [←Real.exp_add]
      congr 1
      have hcount := PairRouting.color_card_add c
      have hcount' : (Fintype.card {i : ι // c i = false} : ℝ) +
          Fintype.card {i : ι // c i = true} = Fintype.card ι := by exact_mod_cast hcount
      change (Fintype.card {i : ι // c i = false} : ℝ) * cycleCoefficient u J q +
          Fintype.card {i : ι // c i = true} * cycleCoefficient u J q = _
      rw [←add_mul,hcount']


lemma switchHeight_le (d : ℕ) (i : SwitchIndex d) : switchHeight d i ≤ d := by
  induction d with
  | zero => exact Empty.elim i
  | succ d ih =>
    rcases i with y | ⟨b,i⟩
    · exact le_refl _
    · exact (ih i).trans (Nat.le_succ d)

lemma agreeThrough_mono {d s t : ℕ} (h : s ≤ t) {Y Y' : SwitchIndex d → Bool}
    (hh : AgreeThrough d t Y Y') : AgreeThrough d s Y Y' :=
  fun i hi => hh i (hi.trans h)

lemma layerAdapted_mono {d s t : ℕ} {β : Type*} {f : (SwitchIndex d → Bool) → β}
    (hf : LayerAdapted d s f) (h : s ≤ t) : LayerAdapted d t f :=
  fun Y Y' hh => hf Y Y' (agreeThrough_mono h hh)

lemma layerAdapted_comp {d s : ℕ} {α β : Type*} {f : (SwitchIndex d → Bool) → α}
    (hf : LayerAdapted d s f) (g : α → β) : LayerAdapted d s (g ∘ f) :=
  fun Y Y' h => congrArg g (hf Y Y' h)

lemma layerAdapted_sum {d s : ℕ} {ι : Type*} (A : Finset ι)
    (f : ι → (SwitchIndex d → Bool) → ℕ)
    (hf : ∀ i ∈ A, LayerAdapted d s (f i)) :
    LayerAdapted d s (fun Y => ∑ i ∈ A, f i Y) := by
  intro Y Y' h
  exact Finset.sum_congr rfl (fun i hi => hf i hi Y Y' h)

lemma assembleBits_agree (r s : ℕ) (lo : Card r × SwitchIndex s → Bool)
    (hi hi' : Card s × SwitchIndex r → Bool) :
    AgreeThrough (s+r) s (assembleBits r s lo hi) (assembleBits r s lo hi') := by
  induction r with
  | zero => intro i _; rfl
  | succ r ih =>
    intro i h
    rcases i with y | ⟨b,i⟩
    · have : s+r+1 ≤ s := h
      omega
    · exact ih (fun j => lo (Fin.cons b j.1,j.2))
        (fun j => hi (j.1,Sum.inr (b,j.2))) (fun j => hi' (j.1,Sum.inr (b,j.2))) i h

lemma palindromeLevelCost_adapted (t d : ℕ) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (X : SwitchIndex d → Bool) :
    LayerAdapted d (t-1) (fun Y => palindromeLevelCost t d e (Y,X)) := by
  classical
  induction d generalizing ι with
  | zero => intro Y Y' _; rfl
  | succ d ih =>
    intro Y Y' h
    change palindromeLevelCost t (d+1) e (Y,X) = palindromeLevelCost t (d+1) e (Y',X)
    conv_lhs => rw [←(coinStepEquiv d).symm_apply_apply Y,←(coinStepEquiv d).symm_apply_apply X]
    conv_rhs => rw [←(coinStepEquiv d).symm_apply_apply Y',←(coinStepEquiv d).symm_apply_apply X]
    rw [palindromeLevelCost_step,palindromeLevelCost_step]
    by_cases ht : t = d+1
    · subst t
      rw [ite_eq_left rfl,ite_eq_left rfl]
      have he₀ : (coinStepEquiv d Y).1.1 = (coinStepEquiv d Y').1.1 := by
        funext i
        exact h (Sum.inr (false,i)) (by simpa only [switchHeight,Nat.add_sub_cancel] using switchHeight_le d i)
      have he₁ : (coinStepEquiv d Y).1.2 = (coinStepEquiv d Y').1.2 := by
        funext i
        exact h (Sum.inr (true,i)) (by simpa only [switchHeight,Nat.add_sub_cancel] using switchHeight_le d i)
      rw [he₀,he₁]
    · rw [ite_eq_right ht,ite_eq_right ht]
      congr 1
      · apply ih
        intro i hi
        exact h (Sum.inr (false,i)) hi
      · apply ih
        intro i hi
        exact h (Sum.inr (true,i)) hi

lemma adapted_mul_mean_le (r s : ℕ) (F G : (SwitchIndex (s+r) → Bool) → ℝ)
    (hF : ∀ Y, 0 ≤ F Y) (hA : LayerAdapted (s+r) s F) (B : ℝ)
    (hG : ∀ lo : Card r × SwitchIndex s → Bool,
      finiteMean (fun hi : Card s × SwitchIndex r → Bool => G (assembleBits r s lo hi)) ≤ B) :
    finiteMean (fun Y => F Y*G Y) ≤ finiteMean F * B := by
  rw [finiteMean_split r s,finiteMean_split r s F,←finiteMean_mul_const]
  apply finiteMean_mono
  intro lo
  let H : Card s × SwitchIndex r → Bool := fun _ => false
  have hh (hi : Card s × SwitchIndex r → Bool) :
      F (assembleBits r s lo hi) = F (assembleBits r s lo H) :=
    hA _ _ (assembleBits_agree r s lo hi H)
  simp_rw [hh,finiteMean_const]
  rw [show (fun hi => F (assembleBits r s lo H) * G (assembleBits r s lo hi)) =
      (fun hi => G (assembleBits r s lo hi) * F (assembleBits r s lo H)) by
        funext hi; exact mul_comm _ _,finiteMean_mul_const]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hG lo) (hF _)


theorem cycleCoefficient_decay (l r : ℕ) (hr : (l:ℝ)/2 ≤ r)
    (q : ℝ) (hq : 1 ≤ q) (hlog : Real.log q ≤ (l:ℝ)/250) :
    cycleCoefficient r ⌈Real.exp ((l:ℝ)/32)⌉₊ q ≤
      68 * Real.exp (-(l:ℝ)/64) := by
  let E := Real.exp ((l:ℝ)/32)
  let J := ⌈E⌉₊
  have hl : (0:ℝ) ≤ l := Nat.cast_nonneg _
  have hE : 1 ≤ E := Real.one_le_exp_iff.mpr (by positivity)
  have hEpos : 0 < E := Real.exp_pos _
  have hEJ : E ≤ (J:ℝ) := Nat.le_ceil E
  have hJ : (1:ℝ) ≤ J := hE.trans hEJ
  have hJpos : (0:ℝ) < J := lt_of_lt_of_le (by norm_num) hJ
  have hJE : (J:ℝ) ≤ 2*E := by
    have h := Nat.ceil_lt_add_one (le_of_lt hEpos)
    change (J:ℝ) < E+1 at h
    linarith
  have hsqJ : Real.sqrt J ≤ (J:ℝ) := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith
  have hqp : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have hqE : q ≤ Real.exp ((l:ℝ)/250) := by
    rw [←Real.exp_log hqp]
    exact Real.exp_le_exp.mpr hlog
  have hln : (1/2:ℝ) ≤ Real.log 2 := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at hh ⊢
    exact hh
  have hden : Real.exp ((l:ℝ)/8) ≤ Real.sqrt ((2:ℝ)^r) := by
    have he : (2:ℝ)^r = Real.exp ((r:ℝ)*Real.log 2) := by
      rw [Real.exp_nat_mul,Real.exp_log (by norm_num)]
    rw [he,Real.sqrt_eq_rpow,Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp]
    apply Real.exp_le_exp.mpr
    have hrn : (0:ℝ) ≤ r := Nat.cast_nonneg _
    nlinarith
  have hlog' : Real.log q ≤ (l:ℝ) := by linarith
  have h₁ : Real.log q / (J:ℝ) ≤ 64*Real.exp (-(l:ℝ)/64) := by
    calc
      _ ≤ (l:ℝ)/E := div_le_div₀ (by positivity) hlog' hEpos hEJ
      _ ≤ (64*Real.exp ((l:ℝ)/64))/E := by
        apply div_le_div_of_nonneg_right _ (le_of_lt hEpos)
        have hh := Real.add_one_le_exp ((l:ℝ)/64)
        linarith
      _ = _ := by
        dsimp [E]
        rw [mul_div_assoc,←Real.exp_sub]
        congr 2
        ring
  have h₂ : 2*q*Real.sqrt J / Real.sqrt ((2:ℝ)^r) ≤
      4*Real.exp (-(l:ℝ)/64) := by
    calc
      _ ≤ (4*Real.exp ((l:ℝ)/250)*E)/Real.exp ((l:ℝ)/8) := by
        apply div_le_div₀ (by positivity) _ (Real.exp_pos _) hden
        have hs := hsqJ.trans hJE
        have hm := mul_le_mul hqE hs (Real.sqrt_nonneg _) (Real.exp_nonneg _)
        nlinarith
      _ = 4*Real.exp ((l:ℝ)/250+(l:ℝ)/32-(l:ℝ)/8) := by
        dsimp [E]
        rw [mul_assoc,←Real.exp_add,mul_div_assoc,←Real.exp_sub]
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _) (by norm_num)
        linarith
  change Real.log q / (J:ℝ) + 2*q*Real.sqrt J / Real.sqrt ((2:ℝ)^r) ≤ _
  linarith

lemma cycleCutoff_pos (l : ℕ) : 0 < ⌈Real.exp ((l:ℝ)/32)⌉₊ := by
  have h := Nat.le_ceil (Real.exp ((l:ℝ)/32))
  have he := Real.exp_pos ((l:ℝ)/32)
  have : (0:ℝ) < ⌈Real.exp ((l:ℝ)/32)⌉₊ := lt_of_lt_of_le he h
  exact_mod_cast this


lemma pow_sum_le_mean_powers {ι : Type*} [Fintype ι] [Nonempty ι]
    (z : ι → ℕ) (q : ℝ) (hq : 0 < q) :
    q^(∑ i, z i) ≤ finiteMean (fun i => q^(Fintype.card ι*z i)) := by
  have hn : (Fintype.card ι:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hm : finiteMean (fun i => (Fintype.card ι*z i:ℕ)*Real.log q) =
      (∑ i, z i:ℕ)*Real.log q := by
    simp only [finiteMean,Nat.cast_mul,Nat.cast_sum,←Finset.mul_sum,←Finset.sum_mul]
    field_simp
  have he := exp_finiteMean_le (fun i => (Fintype.card ι*z i:ℕ)*Real.log q)
  rw [hm,Real.exp_nat_mul,Real.exp_log hq] at he
  simpa only [Real.exp_nat_mul,Real.exp_log hq] using he

lemma palindromeSlabCost_adapted (l d : ℕ) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (X : SwitchIndex d → Bool) :
    LayerAdapted d (2*l) (fun Y => palindromeSlabCost l d e (Y,X)) := by
  apply layerAdapted_sum
  intro i _
  exact layerAdapted_mono (palindromeLevelCost_adapted (l+i.1+1) d e X) (by omega)

theorem palindrome_slab_partial_mgf (r s l : ℕ) (hl : 0 < l) (hs : 2*s ≤ l)
    {ι : Type*} [Fintype ι] (e : ι ↪ Card (s+r)) (X : SwitchIndex (s+r) → Bool)
    (lo : Card r × SwitchIndex s → Bool) (q : ℝ) (hq : 1 ≤ q)
    (hlog : Real.log q ≤ 1/250) :
    finiteMean (fun hi : Card s × SwitchIndex r → Bool =>
      q^(palindromeSlabCost l (s+r) e (assembleBits r s lo hi,X))) ≤
      Real.exp (Fintype.card ι * (68*Real.exp (-(l:ℝ)/64))) := by
  classical
  let : NeZero l := ⟨ne_of_gt hl⟩
  have hqp : 0 < q := lt_of_lt_of_le (by norm_num) hq
  calc
    _ ≤ finiteMean (fun hi : Card s × SwitchIndex r → Bool =>
      finiteMean (fun i : Fin l => q^(l*palindromeLevelCost (l+i.1+1) (s+r) e
        (assembleBits r s lo hi,X)))) := by
      apply finiteMean_mono
      intro hi
      simpa only [palindromeSlabCost,Fintype.card_fin] using
        pow_sum_le_mean_powers (fun i : Fin l => palindromeLevelCost (l+i.1+1) (s+r) e
          (assembleBits r s lo hi,X)) q hqp
    _ = finiteMean (fun i : Fin l => finiteMean (fun hi : Card s × SwitchIndex r → Bool =>
      q^(l*palindromeLevelCost (l+i.1+1) (s+r) e (assembleBits r s lo hi,X)))) := finiteMean_comm _
    _ ≤ finiteMean (fun _i : Fin l =>
      Real.exp (Fintype.card ι * (68*Real.exp (-(l:ℝ)/64)))) := by
      apply finiteMean_mono
      intro i
      by_cases ht : l+i.1+1 ≤ s+r
      · have hs' : s ≤ l+i.1 := by omega
        have he : l+i.1+1 = s+(l+i.1-s)+1 := by omega
        have hu : l+i.1-s < r := by omega
        have hm := palindrome_level_partial_mgf r s (l+i.1-s) hu e X lo
          ⌈Real.exp ((l:ℝ)/32)⌉₊ (cycleCutoff_pos l) (q^l) (one_le_pow₀ hq)
        have hc := cycleCoefficient_decay l (l+i.1-s) (by
          rw [Nat.cast_sub hs',Nat.cast_add]
          have hsr : (2:ℝ)*s ≤ l := by exact_mod_cast hs
          have hi : (0:ℝ) ≤ i.1 := Nat.cast_nonneg _
          linarith) (q^l) (one_le_pow₀ hq) (by
            rw [Real.log_pow]
            nlinarith [mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg l)])
        simp_rw [he,pow_mul]
        exact hm.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg _)))
      · have hz := palindromeLevelCost_gt (l+i.1+1) (s+r) (by omega) e
        simp only [hz,Nat.mul_zero,pow_zero,finiteMean_const]
        exact Real.one_le_exp_iff.mpr (by positivity)
    _ = _ := finiteMean_const _


lemma palindromeSlabCost_gt (l d : ℕ) (h : d ≤ l) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (ω : BenesCoins d) : palindromeSlabCost l d e ω = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  exact palindromeLevelCost_gt _ _ (by omega) _ _

lemma palindrome_slab_adapted_mul_le (d s l : ℕ) (hsd : s ≤ d) (hl : 0 < l)
    (hs : 2*s ≤ l) {ι : Type*} [Fintype ι] (e : ι ↪ Card d)
    (X : SwitchIndex d → Bool) (F : (SwitchIndex d → Bool) → ℝ)
    (hF : ∀ Y, 0 ≤ F Y) (hA : LayerAdapted d s F) (q : ℝ) (hq : 1 ≤ q)
    (hlog : Real.log q ≤ 1/250) :
    finiteMean (fun Y => F Y*q^(palindromeSlabCost l d e (Y,X))) ≤
      finiteMean F * Real.exp (Fintype.card ι * (68*Real.exp (-(l:ℝ)/64))) := by
  obtain ⟨r,rfl⟩ := Nat.exists_eq_add_of_le hsd
  exact adapted_mul_mean_le r s F _ hF hA _
    (fun lo => palindrome_slab_partial_mgf r s l hl hs e X lo q hq hlog)

lemma familyEnd_two (L n : ℕ) : 2*familyEnd L n ≤ L*4^n := by
  cases n with
  | zero => simp [familyEnd]
  | succ n => simp only [familyEnd,Nat.succ_ne_zero,ite_false,Nat.add_one_sub_one,pow_succ]; nlinarith

lemma familyEnd_ge (L n j : ℕ) (hj : j < n) : 2*(L*4^j) ≤ familyEnd L n := by
  cases n with
  | zero => omega
  | succ n =>
    simp only [familyEnd,Nat.succ_ne_zero,ite_false,Nat.add_one_sub_one]
    apply Nat.mul_le_mul_left
    exact Nat.mul_le_mul_left L (Nat.pow_le_pow_right (by decide) (by omega : j ≤ n))

lemma palindromeFamilyCost_adapted (L n d : ℕ) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (X : SwitchIndex d → Bool) :
    LayerAdapted d (familyEnd L n) (fun Y => palindromeFamilyCost L n d e (Y,X)) := by
  apply layerAdapted_sum
  intro j hj
  exact layerAdapted_mono (palindromeSlabCost_adapted (L*4^j) d e X)
    (familyEnd_ge L n j (Finset.mem_range.mp hj))

end Thorp

end ThorpNine.Adaptive

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Adaptive_HeightDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Adaptive

namespace Thorp

theorem palindrome_family_mgf (L n d : ℕ) (hL : 0 < L) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (X : SwitchIndex d → Bool) (q : ℝ) (hq : 1 ≤ q)
    (hlog : Real.log q ≤ 1/250) :
    finiteMean (fun Y => q^(palindromeFamilyCost L n d e (Y,X))) ≤
      Real.exp (Fintype.card ι * (68*∑ j ∈ Finset.range n,
        Real.exp (-((L*4^j:ℕ):ℝ)/64))) := by
  induction n with
  | zero => simp only [palindromeFamilyCost,Finset.range_zero,Finset.sum_empty,pow_zero,
      finiteMean_const,mul_zero,Real.exp_zero,le_refl]
  | succ n ih =>
    let l := L*4^n
    have hl : 0 < l := Nat.mul_pos hL (pow_pos (by decide) _)
    have hs : 2*familyEnd L n ≤ l := familyEnd_two L n
    have hc : ∀ Y, palindromeFamilyCost L (n+1) d e (Y,X) =
        palindromeFamilyCost L n d e (Y,X)+palindromeSlabCost l d e (Y,X) := by
      intro Y
      exact Finset.sum_range_succ _ _
    have hm : finiteMean (fun Y => q^(palindromeFamilyCost L (n+1) d e (Y,X))) ≤
        finiteMean (fun Y => q^(palindromeFamilyCost L n d e (Y,X))) *
          Real.exp (Fintype.card ι*(68*Real.exp (-(l:ℝ)/64))) := by
      by_cases hld : l ≤ d
      · simp_rw [hc,pow_add]
        exact palindrome_slab_adapted_mul_le d (familyEnd L n) l (by omega) hl hs e X _
          (fun _ => pow_nonneg (by linarith) _)
          (layerAdapted_comp (palindromeFamilyCost_adapted L n d e X) (fun c => q^c))
          q hq hlog
      · simp_rw [hc,palindromeSlabCost_gt l d (by omega) e,Nat.add_zero]
        exact le_mul_of_one_le_right
          (finiteMean_nonneg (fun _ => pow_nonneg (by linarith) _))
          (Real.one_le_exp_iff.mpr (by positivity))
    refine (hm.trans (mul_le_mul_of_nonneg_right ih (Real.exp_nonneg _))).trans_eq ?_
    rw [←Real.exp_add,Finset.sum_range_succ]
    congr 1
    dsimp [l]
    ring

lemma pow_four_ge (j : ℕ) : j+1 ≤ 4^j := by
  induction j with
  | zero => norm_num
  | succ j ih => rw [pow_succ]; omega

lemma sum_family_decay (L n : ℕ) (hL : 0 < L) :
    (∑ j ∈ Finset.range n, Real.exp (-((L*4^j:ℕ):ℝ)/64)) ≤
      Real.exp (-(L:ℝ)/64)/(1-Real.exp (-(1:ℝ)/64)) := by
  let r := Real.exp (-(1:ℝ)/64)
  have hr : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have hg : (∑ j ∈ Finset.range n, r^j) ≤ 1/(1-r) := by
    apply (le_div_iff₀ (by linarith : (0:ℝ)<1-r)).mpr
    have hh := geom_sum_mul r n
    nlinarith [pow_nonneg (le_of_lt hr) n]
  calc
    _ ≤ ∑ j ∈ Finset.range n, Real.exp (-(L:ℝ)/64)*r^j := by
      apply Finset.sum_le_sum
      intro j _
      have hj := pow_four_ge j
      have hlj : L+j ≤ L*4^j := by nlinarith
      have hlj' : (L:ℝ)+j ≤ (L*4^j:ℕ) := by exact_mod_cast hlj
      rw [←Real.exp_nat_mul,←Real.exp_add]
      exact Real.exp_le_exp.mpr (by linarith)
    _ = Real.exp (-(L:ℝ)/64)*(∑ j ∈ Finset.range n, r^j) := by rw [Finset.mul_sum]
    _ ≤ Real.exp (-(L:ℝ)/64)*(1/(1-r)) :=
      mul_le_mul_of_nonneg_left hg (Real.exp_nonneg _)
    _ = _ := by ring


lemma palindromeLevelCost_step_add (t d : ℕ) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card (d+1)) (ω : BenesCoins (d+1)) :
    palindromeLevelCost t (d+1) e ω =
      let σ := benesStepEquiv d ω
      let x := e.trans (headTailEquiv d).toEmbedding
      let c := PairRouting.colors x σ.2.1
      let hc := PairRouting.colors_compatible x σ.2.1
      (if t = d+1 then PairRouting.alternatingCycles (PairRouting.switchedEmbedding x σ.2.1)
          (fun b => palindromePerm d (if b then σ.1.2 else σ.1.1)) else 0) +
        palindromeLevelCost t d (PairRouting.childEmbedding x c hc false) σ.1.1 +
        palindromeLevelCost t d (PairRouting.childEmbedding x c hc true) σ.1.2 := by
  classical
  rw [palindromeLevelCost]
  dsimp only
  split_ifs with h
  · simp only [palindromeLevelCost_gt t d (by omega),Nat.add_zero]
  · simp only [Nat.zero_add]

lemma palindromeLowCost_sum (H d : ℕ) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (ω : BenesCoins d) :
    palindromeLowCost H d e ω = ∑ i ∈ Finset.range H, palindromeLevelCost (i+1) d e ω := by
  classical
  induction d generalizing ι with
  | zero => simp only [palindromeLowCost,palindromeLevelCost,Finset.sum_const_zero]
  | succ d ih =>
    rw [palindromeLowCost]
    simp only [palindromeLevelCost_step_add,Finset.sum_add_distrib]
    rw [←ih,←ih]
    congr 2
    simp only [Nat.add_right_cancel_iff,Finset.sum_ite_eq',Finset.mem_range,Nat.succ_le_iff]

lemma palindromeLowCost_slab (L d : ℕ) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (ω : BenesCoins d) :
    palindromeLowCost L d e ω + palindromeSlabCost L d e ω = palindromeLowCost (2*L) d e ω := by
  rw [palindromeLowCost_sum,palindromeLowCost_sum,show 2*L=L+L by omega,Finset.sum_range_add]
  congr 1
  exact Fin.sum_univ_eq_sum_range (fun i => palindromeLevelCost (L+i+1) d e ω) L

lemma palindromeCost_family (L n d : ℕ) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (ω : BenesCoins d) :
    palindromeLowCost L d e ω + palindromeFamilyCost L n d e ω +
      palindromeFamilyCost (2*L) n d e ω = palindromeLowCost (L*4^n) d e ω := by
  induction n with
  | zero => simp only [palindromeFamilyCost,Finset.range_zero,Finset.sum_empty,Nat.add_zero,
      pow_zero,mul_one]
  | succ n ih =>
    have he : (2*L)*4^n = 2*(L*4^n) := by ring
    have he' : L*4^(n+1) = 2*(2*(L*4^n)) := by rw [pow_succ]; ring
    simp only [palindromeFamilyCost,Finset.sum_range_succ] at ih ⊢
    rw [he,he',←palindromeLowCost_slab,←palindromeLowCost_slab,←ih]
    omega


lemma finiteMean_mul_sq_le {Ω : Type*} [Fintype Ω] (f g : Ω → ℝ) :
    (finiteMean (fun ω => f ω*g ω))^2 ≤ finiteMean (fun ω => (f ω)^2)*finiteMean (fun ω => (g ω)^2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ f g
  simp only [finiteMean,div_pow,div_mul_div_comm,←pow_two]
  exact div_le_div_of_nonneg_right h (sq_nonneg _)

lemma finiteMean_mul_exp_le {Ω : Type*} [Fintype Ω] (f g : Ω → ℝ) (A B : ℝ)
    (hf : finiteMean (fun ω => (f ω)^2) ≤ Real.exp A)
    (hg : finiteMean (fun ω => (g ω)^2) ≤ Real.exp B) :
    finiteMean (fun ω => f ω*g ω) ≤ Real.exp ((A+B)/2) := by
  have hc := finiteMean_mul_sq_le f g
  have hn : 0 ≤ finiteMean (fun ω => (g ω)^2) := finiteMean_nonneg (fun _ => sq_nonneg _)
  have hu := mul_le_mul hf hg hn (Real.exp_nonneg _)
  have he : Real.exp A*Real.exp B = (Real.exp ((A+B)/2))^2 := by
    rw [←Real.exp_add,←Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [he] at hu
  have hh := hc.trans hu
  have hep := Real.exp_pos ((A+B)/2)
  nlinarith


lemma heightDecay_nonneg (H : ℕ) : 0 ≤ heightDecay H := by
  have h : Real.exp (-(1:ℝ)/64) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  apply div_nonneg (by positivity) (by linarith)

lemma heightDecay_antitone : Antitone heightDecay := by
  intro L H h
  have hden : 0 ≤ 1-Real.exp (-(1:ℝ)/64) := by
    have h := Real.exp_lt_one_iff.mpr (by norm_num : -(1:ℝ)/64 < 0)
    linarith
  apply div_le_div_of_nonneg_right _ hden
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.exp_le_exp.mpr
  have h' : (L:ℝ) ≤ H := by exact_mod_cast h
  linarith

lemma palindrome_family_mgf_decay (L n d : ℕ) (hL : 0 < L) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (X : SwitchIndex d → Bool) (q : ℝ) (hq : 1 ≤ q)
    (hlog : Real.log q ≤ 1/250) :
    finiteMean (fun Y => q^(palindromeFamilyCost L n d e (Y,X))) ≤
      Real.exp (Fintype.card ι*heightDecay L) := by
  apply (palindrome_family_mgf L n d hL e X q hq hlog).trans
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  have h := mul_le_mul_of_nonneg_left (sum_family_decay L n hL) (by norm_num : (0:ℝ)≤68)
  simpa only [heightDecay,mul_div_assoc] using h

theorem palindrome_high_mgf (H n d : ℕ) (hH : 0 < H) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (X : SwitchIndex d → Bool) (q : ℝ) (hq : 1 ≤ q)
    (hlog : Real.log q ≤ 1/500) :
    finiteMean (fun Y => q^(palindromeFamilyCost H n d e (Y,X)+
      palindromeFamilyCost (2*H) n d e (Y,X))) ≤ Real.exp (Fintype.card ι*heightDecay H) := by
  have hq2 := one_le_pow₀ (n:=2) hq
  have hlog2 : Real.log (q^2) ≤ 1/250 := by rw [Real.log_pow]; norm_num; linarith
  have h₀ := palindrome_family_mgf_decay H n d hH e X (q^2) hq2 hlog2
  have h₁ := palindrome_family_mgf_decay (2*H) n d (by omega) e X (q^2) hq2 hlog2
  have h₁' := h₁.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
    (heightDecay_antitone (show H ≤ 2*H by omega)) (Nat.cast_nonneg _)))
  have hh := finiteMean_mul_exp_le (fun Y => q^(palindromeFamilyCost H n d e (Y,X)))
    (fun Y => q^(palindromeFamilyCost (2*H) n d e (Y,X)))
    (Fintype.card ι*heightDecay H) (Fintype.card ι*heightDecay H)
    (by simpa only [pow_right_comm] using h₀) (by simpa only [pow_right_comm] using h₁')
  simpa only [←pow_add,add_self_div_two] using hh

lemma palindrome_high_full_mgf (H n d : ℕ) (hH : 0 < H) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (q : ℝ) (hq : 1 ≤ q) (hlog : Real.log q ≤ 1/500) :
    finiteMean (fun ω : BenesCoins d => q^(palindromeFamilyCost H n d e ω+
      palindromeFamilyCost (2*H) n d e ω)) ≤ Real.exp (Fintype.card ι*heightDecay H) := by
  rw [finiteMean_prod,finiteMean_comm]
  calc
    _ ≤ finiteMean (fun _X : SwitchIndex d → Bool => Real.exp (Fintype.card ι*heightDecay H)) := by
      apply finiteMean_mono
      intro X
      exact palindrome_high_mgf H n d hH e X q hq hlog
    _ = _ := finiteMean_const _

theorem palindrome_cost_mgf_cutoff (r H : ℕ) (hH : 0 < H) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card (H+r)) (q : ℝ) (hq : 1 ≤ q) (hlog : Real.log q ≤ 1/1000)
    (hr : (2:ℝ)^H*((Fintype.card ι/(2:ℝ)^(H+r))*(q^2)^H) ≤ 1/2) :
    finiteMean (fun ω : BenesCoins (H+r) => q^(palindromeCost (H+r) e ω)) ≤
      Real.exp (((2:ℝ)^r*(2*((2:ℝ)^H*((Fintype.card ι/(2:ℝ)^(H+r))*(q^2)^H))^2)+
        Fintype.card ι*heightDecay H)/2) := by
  let d := H+r
  have hd : d ≤ H*4^d := by
    have hh := pow_four_ge d
    nlinarith
  have hcost (ω : BenesCoins d) : palindromeCost d e ω = palindromeLowCost H d e ω+
      (palindromeFamilyCost H d d e ω+palindromeFamilyCost (2*H) d d e ω) := by
    have hh := palindromeCost_family H d d e ω
    rw [palindromeLowCost_eq _ _ hd] at hh
    simpa only [Nat.add_assoc] using hh.symm
  have hq2 := one_le_pow₀ (n:=2) hq
  have hlog2 : Real.log (q^2) ≤ 1/500 := by rw [Real.log_pow]; norm_num; linarith
  have hlow := palindrome_low_mgf r H e (q^2) hq2 hr
  have hhigh := palindrome_high_full_mgf H d d hH e (q^2) hq2 hlog2
  have hh := finiteMean_mul_exp_le (fun ω : BenesCoins d => q^(palindromeLowCost H d e ω))
    (fun ω : BenesCoins d => q^(palindromeFamilyCost H d d e ω+palindromeFamilyCost (2*H) d d e ω))
    _ _ (by simpa only [pow_right_comm] using hlow) (by simpa only [pow_right_comm] using hhigh)
  change finiteMean (fun ω : BenesCoins d => q^(palindromeCost d e ω)) ≤ _
  simpa only [hcost,pow_add,pow_right_comm] using hh


lemma cutoffMass_le (H d : ℕ) {ι : Type*} [Fintype ι] (e : ι ↪ Card d) (ω : BenesCoins d) :
    cutoffMass H d e ω ≤ Fintype.card ι := by
  classical
  induction d generalizing ι with
  | zero => exact Nat.zero_le _
  | succ d ih =>
    rw [cutoffMass]
    split_ifs
    · exact crowdedMass_le _
    · exact (Nat.add_le_add (ih _ _) (ih _ _)).trans_eq (PairRouting.color_card_add _)

lemma palindromeLowCost_le (H d : ℕ) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (ω : BenesCoins d) : palindromeLowCost H d e ω ≤ H*Fintype.card ι :=
  (palindromeLowCost_le_cutoff H d e ω).trans (Nat.mul_le_mul_left H (cutoffMass_le H d e ω))

theorem palindrome_cost_mgf_coarse (d : ℕ) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (q : ℝ) (hq : 1 ≤ q) (hlog : Real.log q ≤ 1/1000) :
    finiteMean (fun ω : BenesCoins d => q^(palindromeCost d e ω)) ≤
      Real.exp (Fintype.card ι*(1+heightDecay 1)) := by
  have hd : d ≤ 1*4^d := by have hh := pow_four_ge d; omega
  have hcost (ω : BenesCoins d) : palindromeCost d e ω = palindromeLowCost 1 d e ω+
      (palindromeFamilyCost 1 d d e ω+palindromeFamilyCost 2 d d e ω) := by
    have hh := palindromeCost_family 1 d d e ω
    rw [palindromeLowCost_eq _ _ hd] at hh
    simpa only [Nat.add_assoc] using hh.symm
  have hq2 := one_le_pow₀ (n:=2) hq
  have hlog2 : Real.log (q^2) ≤ 1/500 := by rw [Real.log_pow]; norm_num; linarith
  have hlow : finiteMean (fun ω : BenesCoins d => (q^2)^(palindromeLowCost 1 d e ω)) ≤
      Real.exp (Fintype.card ι) := by
    calc
      _ ≤ finiteMean (fun _ω : BenesCoins d => (q^2)^(Fintype.card ι)) := by
        apply finiteMean_mono
        intro ω
        apply pow_le_pow_right₀ hq2
        simpa only [one_mul] using palindromeLowCost_le 1 d e ω
      _ = (q^2)^(Fintype.card ι) := finiteMean_const _
      _ = Real.exp (Fintype.card ι * Real.log (q^2)) := by
        rw [Real.exp_nat_mul,Real.exp_log (by positivity : 0<q^2)]
      _ ≤ _ := Real.exp_le_exp.mpr (by
        have hh := mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg (Fintype.card ι) : (0:ℝ)≤_)
        nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card ι)])
  have hhigh := palindrome_high_full_mgf 1 d d (by decide) e (q^2) hq2 hlog2
  have hh := finiteMean_mul_exp_le (fun ω : BenesCoins d => q^(palindromeLowCost 1 d e ω))
    (fun ω : BenesCoins d => q^(palindromeFamilyCost 1 d d e ω+palindromeFamilyCost 2 d d e ω))
    (Fintype.card ι) (Fintype.card ι*heightDecay 1)
    (by simpa only [pow_right_comm] using hlow) (by simpa only [pow_right_comm] using hhigh)
  simp only [←pow_add,←hcost] at hh
  apply hh.trans (Real.exp_le_exp.mpr _)
  have hk : (0:ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  have hD := heightDecay_nonneg 1
  nlinarith

lemma momentBase_one_le : 1 ≤ momentBase := by
  exact Real.one_le_rpow (by norm_num) (by norm_num)

lemma momentBase_log : Real.log momentBase ≤ 1/1000 := by
  rw [momentBase,Real.log_rpow (by norm_num)]
  have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
  norm_num at hh ⊢
  linarith

lemma momentBase_pow (c : ℕ) : momentBase^c = (2:ℝ)^((c:ℝ)*(1/1000:ℝ)) := by
  rw [mul_comm,Real.rpow_mul_natCast (by norm_num)]
  rfl

lemma palindromeRowMoment_le_cost (d : ℕ) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) :
    palindromeRowMoment d e (1/1000) ≤
      finiteMean (fun ω : BenesCoins d => momentBase^(palindromeCost d e ω)) := by
  have hn : (0:ℝ) < ((2^d:ℕ):ℝ)^(Fintype.card ι) := by positivity
  have hn0 : (0:ℝ) ≤ ((2^d).descFactorial (Fintype.card ι):ℝ) /
      ((2^d:ℕ):ℝ)^(Fintype.card ι) := by positivity
  have hn1 : ((2^d).descFactorial (Fintype.card ι):ℝ) /
      ((2^d:ℕ):ℝ)^(Fintype.card ι) ≤ 1 := by
    apply (div_le_one hn).mpr
    exact_mod_cast Nat.descFactorial_le_pow (2^d) (Fintype.card ι)
  have hpow := Real.rpow_le_one hn0 hn1 (by norm_num : (0:ℝ)≤1/1000)
  have hm := palindrome_row_density_moment d e (1/1000) (by norm_num)
  simp_rw [←momentBase_pow] at hm
  exact hm.trans (mul_le_of_le_one_left (finiteMean_nonneg (fun _ =>
    pow_nonneg (le_trans (by norm_num) momentBase_one_le) _)) hpow)

theorem palindrome_row_moment_coarse (d : ℕ) {ι : Type*} [Fintype ι] (e : ι ↪ Card d) :
    palindromeRowMoment d e (1/1000) ≤ Real.exp (Fintype.card ι*(1+heightDecay 1)) :=
  (palindromeRowMoment_le_cost d e).trans
    (palindrome_cost_mgf_coarse d e momentBase momentBase_one_le momentBase_log)


lemma log_small_density {p : ℝ} (hp : 0 < p) (hs : p ≤ 1/256) :
    Real.log p ≤ -8*Real.log 2 := by
  have he : Real.log (1/256:ℝ) = -8*Real.log 2 := by
    rw [show (1/256:ℝ) = 1/2^8 by norm_num,
      Real.log_div (by norm_num) (by positivity),Real.log_one,Real.log_pow]
    ring
  exact (Real.log_le_log hp hs).trans_eq he

lemma densityCutoff_bounds {p : ℝ} (hp : 0 < p) (hs : p ≤ 1/256) :
    0 < densityCutoff p ∧
    (densityCutoff p:ℝ)*(4*Real.log 2) ≤ -Real.log p ∧
    -Real.log p < ((densityCutoff p:ℝ)+1)*(4*Real.log 2) := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hd : 0 < 4*Real.log 2 := by positivity
  have hh := log_small_density hp hs
  have hx : 1 ≤ -Real.log p/(4*Real.log 2) := by
    apply (le_div_iff₀ hd).mpr
    nlinarith
  refine ⟨Nat.floor_pos.mpr hx,?_,?_⟩
  · exact (le_div_iff₀ hd).mp (Nat.floor_le (by linarith : 0 ≤ -Real.log p/(4*Real.log 2)))
  · exact (div_lt_iff₀ hd).mp (Nat.lt_floor_add_one (-Real.log p/(4*Real.log 2)))

lemma densityCutoff_decay {p : ℝ} (hp : 0 < p) (hs : p ≤ 1/256) :
    Real.exp (-(densityCutoff p:ℝ)/64) ≤ Real.exp (1/64) * p^(1/512:ℝ) := by
  have hh := (densityCutoff_bounds hp hs).2.2
  have hb : Real.log 2 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    linarith
  have hH : 0 ≤ (densityCutoff p:ℝ)+1 := by positivity
  have hu := mul_le_mul_of_nonneg_left hb hH
  rw [Real.rpow_def_of_pos hp,←Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith

lemma densityCutoff_power {p q : ℝ} (hp : 0 < p) (hs : p ≤ 1/256)
    (hq : 0 < q) (hlog : Real.log q ≤ Real.log 2/4) (n : ℕ) (hn : n ≤ 4)
    (hq1 : 1 ≤ q) :
    p*(2:ℝ)^(densityCutoff p)*q^(n*densityCutoff p) ≤ p^(1/2:ℝ) := by
  have hcut := (densityCutoff_bounds hp hs).2.1
  have hH : 0 ≤ (densityCutoff p:ℝ) := Nat.cast_nonneg _
  have hn' : (n:ℝ) ≤ 4 := by exact_mod_cast hn
  have hln := Real.log_nonneg hq1
  have hl := mul_le_mul_of_nonneg_right hn' hln
  have hnl : (n:ℝ)*Real.log q ≤ Real.log 2 := by linarith
  have hm := mul_le_mul_of_nonneg_left hnl hH
  have heq : p*(2:ℝ)^(densityCutoff p)*q^(n*densityCutoff p) =
      Real.exp (Real.log p+(densityCutoff p:ℝ)*Real.log 2+
        (n*densityCutoff p:ℕ)*Real.log q) := by
    rw [Real.exp_add,Real.exp_add,Real.exp_nat_mul,Real.exp_nat_mul,
      Real.exp_log hp,Real.exp_log hq,Real.exp_log (by norm_num : (0:ℝ)<2)]
  rw [heq,Real.rpow_def_of_pos hp]
  apply Real.exp_le_exp.mpr
  push_cast
  nlinarith

lemma densityCutoff_sparse {p q : ℝ} (hp : 0 < p) (hs : p ≤ 1/256)
    (hq : 0 < q) (hlog : Real.log q ≤ Real.log 2/4) (hq1 : 1 ≤ q) :
    (2:ℝ)^(densityCutoff p)*(p*(q^2)^(densityCutoff p)) ≤ 1/2 := by
  have hh := densityCutoff_power hp hs hq hlog 2 (by decide) hq1
  rw [←pow_mul] at ⊢
  have hle : p^(1/2:ℝ) ≤ 1/2 := by
    have hlogp := log_small_density hp hs
    have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    rw [Real.rpow_def_of_pos hp]
    calc
      _ ≤ Real.exp (-Real.log 2) := by apply Real.exp_le_exp.mpr; nlinarith
      _ = 1/2 := by rw [Real.exp_neg,Real.exp_log (by norm_num : (0:ℝ)<2)]; norm_num
  nlinarith [hh.trans hle]


lemma momentBase_log_exact : Real.log momentBase = Real.log 2/1000 := by
  rw [momentBase,Real.log_rpow (by norm_num)]
  ring

lemma densityCutoff_le_height (d k : ℕ) (hk : 0 < k) :
    densityCutoff ((k:ℝ)/(2:ℝ)^d) ≤ d := by
  have hk' : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hp : 0 < (k:ℝ)/(2:ℝ)^d := by positivity
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogk := Real.log_nonneg hk'
  by_cases hx : 0 ≤ -Real.log ((k:ℝ)/(2:ℝ)^d)/(4*Real.log 2)
  · have hh := (le_div_iff₀ (by positivity : 0 < 4*Real.log 2)).mp (Nat.floor_le hx)
    have hd : (0:ℝ) ≤ d := Nat.cast_nonneg _
    have hH : (0:ℝ) ≤ densityCutoff ((k:ℝ)/(2:ℝ)^d) := Nat.cast_nonneg _
    change (densityCutoff ((k:ℝ)/(2:ℝ)^d):ℝ)*(4*Real.log 2) ≤ -Real.log ((k:ℝ)/(2:ℝ)^d) at hh
    rw [Real.log_div (by positivity) (by positivity),Real.log_pow] at hh
    have hle : (densityCutoff ((k:ℝ)/(2:ℝ)^d):ℝ) ≤ d := by nlinarith
    exact_mod_cast hle
  · have hz := Nat.floor_of_nonpos (le_of_not_ge hx)
    simp only [densityCutoff,hz,Nat.zero_le]

lemma densityTailConstant_nonneg : 0 ≤ densityTailConstant := by
  have h := Real.exp_lt_one_iff.mpr (by norm_num : -(1:ℝ)/64 < 0)
  apply div_nonneg (by positivity) (by linarith)

lemma heightDecay_cutoff {p : ℝ} (hp : 0 < p) (hs : p ≤ 1/256) :
    heightDecay (densityCutoff p) ≤ densityTailConstant*p^(1/512:ℝ) := by
  have hden : 0 ≤ 1-Real.exp (-(1:ℝ)/64) := by
    have h := Real.exp_lt_one_iff.mpr (by norm_num : -(1:ℝ)/64 < 0)
    linarith
  have hh := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (densityCutoff_decay hp hs) (by norm_num : (0:ℝ)≤68)) hden
  simpa only [heightDecay,densityTailConstant,mul_assoc,div_mul_eq_mul_div] using hh

lemma sparse_low_algebra (r H k : ℕ) (q : ℝ) :
    (2:ℝ)^r*(2*((2:ℝ)^H*(((k:ℝ)/(2:ℝ)^(H+r))*(q^2)^H))^2) =
    2*k*(((k:ℝ)/(2:ℝ)^(H+r))*(2:ℝ)^H*q^(4*H)) := by
  rw [pow_add,←pow_mul,show 4*H = (2*H)*2 by omega,pow_mul]
  have hH : (2:ℝ)^H ≠ 0 := by positivity
  have hr : (2:ℝ)^r ≠ 0 := by positivity
  field_simp
  ring

lemma palindrome_row_moment_small (d : ℕ) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (hk : 0 < Fintype.card ι)
    (hs : (Fintype.card ι:ℝ)/(2:ℝ)^d ≤ 1/256) :
    palindromeRowMoment d e (1/1000) ≤
      Real.exp (Fintype.card ι*(1+densityTailConstant)*
        ((Fintype.card ι:ℝ)/(2:ℝ)^d)^(1/512:ℝ)) := by
  generalize hpdef : ((Fintype.card ι:ℝ)/(2:ℝ)^d) = p at hs ⊢
  have hp : 0 < p := by rw [←hpdef]; positivity
  have hle := densityCutoff_le_height d (Fintype.card ι) hk
  rw [hpdef] at hle
  obtain ⟨r,hr⟩ := Nat.exists_eq_add_of_le hle
  subst d
  have hH := (densityCutoff_bounds hp hs).1
  have hq := momentBase_one_le
  have hqp : 0 < momentBase := by linarith
  have hlog : Real.log momentBase ≤ Real.log 2/4 := by
    rw [momentBase_log_exact]
    have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    linarith
  have hsp := densityCutoff_sparse hp hs hqp hlog hq
  rw [←hpdef] at hsp
  have hh := palindrome_cost_mgf_cutoff r (densityCutoff p) hH e momentBase hq momentBase_log
    (by simpa only [hpdef] using hsp)
  apply (palindromeRowMoment_le_cost _ e).trans (hh.trans (Real.exp_le_exp.mpr _))
  rw [sparse_low_algebra,hpdef]
  have hlow := densityCutoff_power hp hs hqp hlog 4 (by decide) hq
  have hp1 : p ≤ 1 := by linarith
  have he := Real.rpow_le_rpow_of_exponent_ge hp hp1 (by norm_num : (1:ℝ)/512 ≤ 1/2)
  have hlow' := mul_le_mul_of_nonneg_left (hlow.trans he)
    (by positivity : (0:ℝ)≤2*Fintype.card ι)
  have hhigh := mul_le_mul_of_nonneg_left (heightDecay_cutoff hp hs)
    (Nat.cast_nonneg (Fintype.card ι): (0:ℝ)≤_)
  have hnon : 0 ≤ Fintype.card ι*densityTailConstant*p^(1/512:ℝ) :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) densityTailConstant_nonneg)
      (Real.rpow_nonneg (le_of_lt hp) _)
  nlinarith

lemma densityConstant_pos : 0 < densityConstant := by
  dsimp [densityConstant]
  have hh := heightDecay_nonneg 1
  have ht := densityTailConstant_nonneg
  linarith

theorem palindrome_row_moment_bound (d : ℕ) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (hk : 0 < Fintype.card ι) :
    palindromeRowMoment d e (1/1000) ≤ Real.exp (densityConstant*Fintype.card ι*
        ((Fintype.card ι:ℝ)/(2:ℝ)^d)^(1/512:ℝ)) := by
  have hp : 0 < (Fintype.card ι:ℝ)/(2:ℝ)^d := by positivity
  have hp1 : (Fintype.card ι:ℝ)/(2:ℝ)^d ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    have h := Fintype.card_le_of_injective e e.injective
    rw [card_positions] at h
    exact_mod_cast h
  have hk0 : (0:ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  have hpow := Real.rpow_nonneg (le_of_lt hp) (1/512:ℝ)
  by_cases hs : (Fintype.card ι:ℝ)/(2:ℝ)^d ≤ 1/256
  · apply (palindrome_row_moment_small d e hk hs).trans (Real.exp_le_exp.mpr _)
    have hD : 1+densityTailConstant ≤ densityConstant := by
      dsimp [densityConstant]
      have := heightDecay_nonneg 1
      linarith
    have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hD hk0) hpow
    nlinarith
  · have hlow : (1:ℝ)/256 ≤ ((Fintype.card ι:ℝ)/(2:ℝ)^d)^(1/512:ℝ) := by
      have he := Real.rpow_le_rpow_of_exponent_ge hp hp1 (by norm_num : (1:ℝ)/512 ≤ 1)
      rw [Real.rpow_one] at he
      exact (le_of_not_ge hs).trans he
    have hD : 256*(1+heightDecay 1) ≤ densityConstant := by
      dsimp [densityConstant]
      have := densityTailConstant_nonneg
      linarith
    apply (palindrome_row_moment_coarse d e).trans (Real.exp_le_exp.mpr _)
    have hD0 : 0 ≤ 1+heightDecay 1 := by have := heightDecay_nonneg 1; linarith
    have ha := mul_le_mul_of_nonneg_left hlow (mul_nonneg (by norm_num : (0:ℝ)≤256) hD0)
    have hb := mul_le_mul_of_nonneg_right hD hpow
    have hc := mul_le_mul_of_nonneg_right (ha.trans hb) hk0
    nlinarith

variable {α : Type*} [Fintype α] [DecidableEq α]

lemma perturbCycleMap_injective (p q : Equiv.Perm α) (S B : Finset α)
    (h : ∀ x ∉ B, p x = q x) : Function.Injective (perturbCycleMap p q S B h) := by
  classical
  intro C D he
  by_cases hC : ∃ x ∈ C.val, x ∈ B <;>
    by_cases hD : ∃ x ∈ D.val, x ∈ B
  · simp only [perturbCycleMap,dite_eq_left hC,dite_eq_left hD,Sum.inr.injEq] at he
    have hx : hC.choose = hD.choose := congrArg Subtype.val he
    exact RoutingNetwork.SelectedCycle.eq_of_mem C D hC.choose_spec.1
      (hx.symm ▸ hD.choose_spec.1)
  · simp only [perturbCycleMap,dite_eq_left hC,dite_eq_right hD] at he
    cases he
  · simp only [perturbCycleMap,dite_eq_right hC,dite_eq_left hD] at he
    cases he
  · simp only [perturbCycleMap,dite_eq_right hC,dite_eq_right hD,Sum.inl.injEq] at he
    have hval : C.val = D.val := congrArg (fun Z : RoutingNetwork.SelectedCycle q S => Z.val) he
    exact Subtype.ext hval

theorem selectedCycle_perturb_le (p q : Equiv.Perm α) (S B : Finset α)
    (h : ∀ x ∉ B, p x = q x) :
    Fintype.card (RoutingNetwork.SelectedCycle p S) ≤
      Fintype.card (RoutingNetwork.SelectedCycle q S)+B.card := by
  have hh := Fintype.card_le_of_injective _ (perturbCycleMap_injective p q S B h)
  simpa only [Fintype.card_sum,Fintype.card_coe] using hh


lemma permDistance_sum (p q : Equiv.Perm α) :
    permDistance p q = ∑ x : α, if p x = q x then 0 else 1 := by
  classical
  simp [permDistance,Finset.card_filter]

lemma permDistance_refl (p : Equiv.Perm α) : permDistance p p = 0 := by
  simp [permDistance]

lemma permDistance_le (p q : Equiv.Perm α) : permDistance p q ≤ Fintype.card α :=
  (Finset.card_filter_le _ _).trans_eq (Finset.card_univ)

lemma permDistance_symm (p q : Equiv.Perm α) : permDistance p q = permDistance q p := by
  simp only [permDistance,ne_comm]

lemma permDistance_triangle (p q r : Equiv.Perm α) :
    permDistance p r ≤ permDistance p q+permDistance q r := by
  classical
  simp only [permDistance_sum,←Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x _
  by_cases hpq : p x = q x <;> by_cases hqr : q x = r x <;>
    by_cases hpr : p x = r x <;> simp only [hpq,hqr,hpr,↓reduceIte] <;>
    omega

lemma permDistance_mul_left (p q g : Equiv.Perm α) :
    permDistance (g*p) (g*q) = permDistance p q := by
  classical
  unfold permDistance
  congr 1
  ext x
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  exact not_congr g.injective.eq_iff

lemma permDistance_mul_right (p q g : Equiv.Perm α) :
    permDistance (p*g) (q*g) = permDistance p q := by
  classical
  simp only [permDistance_sum,Equiv.Perm.mul_apply]
  exact Fintype.sum_equiv g _ _ (fun _ => rfl)

lemma permDistance_inv (p q : Equiv.Perm α) : permDistance p⁻¹ q⁻¹ = permDistance p q := by
  have hh := permDistance_mul_left p⁻¹ q⁻¹ q
  have hhh := permDistance_mul_right (q*p⁻¹) 1 p
  simp only [mul_inv_cancel,one_mul,inv_mul_cancel_right] at hh hhh
  rw [←hhh] at hh
  rw [←hh,permDistance_symm]

lemma permDistance_mul_le (p q g h : Equiv.Perm α) :
    permDistance (p*g) (q*h) ≤ permDistance p q+permDistance g h := by
  have hh := permDistance_triangle (p*g) (q*g) (q*h)
  simpa only [permDistance_mul_left,permDistance_mul_right] using hh

lemma selectedCycle_distance_le (p q : Equiv.Perm α) (S : Finset α) :
    Fintype.card (RoutingNetwork.SelectedCycle p S) ≤
      Fintype.card (RoutingNetwork.SelectedCycle q S)+permDistance p q := by
  apply selectedCycle_perturb_le
  intro x hx
  simpa only [Finset.mem_filter,Finset.mem_univ,true_and,not_not] using hx

lemma permDistance_alternating (p q : Equiv.Perm α) :
    permDistance (CycleColoring.alternatingPerm p) (CycleColoring.alternatingPerm q) = permDistance p q := by
  classical
  simp only [permDistance_sum,Fintype.sum_prod_type,Fintype.sum_bool]
  simp [CycleColoring.alternatingPerm]

lemma alternatingCycles_distance_le {ι : Type*} [Fintype ι]
    (e : ι ↪ Bool × α) (p q : Bool → Equiv.Perm α) :
    PairRouting.alternatingCycles e p ≤ PairRouting.alternatingCycles e q+
      (permDistance (p false) (q false)+permDistance (p true) (q true)) := by
  have hh := selectedCycle_distance_le
    (CycleColoring.alternatingPerm (PairRouting.alternatingProjection p))
    (CycleColoring.alternatingPerm (PairRouting.alternatingProjection q)) (PairRouting.labelSet e)
  rw [permDistance_alternating] at hh
  apply hh.trans
  apply Nat.add_le_add_left
  dsimp only [PairRouting.alternatingProjection]
  exact (permDistance_mul_le _ _ _ _).trans_eq (by
    change permDistance (p false)⁻¹ (q false)⁻¹ + _ = _
    rw [permDistance_inv])

end Thorp
namespace Thorp

lemma permDistance_childLift (d : ℕ) (p q : Bool → Equiv.Perm (Card d)) :
    permDistance (childLift p) (childLift q) =
      permDistance (p false) (q false)+permDistance (p true) (q true) := by
  classical
  rw [permDistance_sum]
  have hh : (∑ x : Card (d+1), if childLift p x = childLift q x then 0 else 1) =
      ∑ x : Bool × Card d, if p x.1 x.2 = q x.1 x.2 then 0 else 1 := by
    apply Fintype.sum_equiv (headTailEquiv d)
    intro x
    have hx : (headTailEquiv d) x = (x 0,Fin.tail x) := rfl
    rw [hx]
    congr 1
    apply propext
    constructor
    · intro h
      have ht := congrArg Fin.tail h
      simpa only [childLift,Equiv.coe_fn_mk,Fin.tail_cons] using ht
    · intro h
      dsimp only [childLift,Equiv.coe_fn_mk]
      exact congrArg (fun z : Card d => (Fin.cons (x 0) z : Card (d+1))) h
  rw [hh]
  simp only [Fintype.sum_prod_type,Fintype.sum_bool,permDistance_sum]
  omega

lemma centralDistance_step (L r : ℕ) (C D : Card (r+1) → Equiv.Perm (Card L)) :
    centralDistance L (r+1) C D =
      centralDistance L r (fun u => C (Fin.cons false u)) (fun u => D (Fin.cons false u))+
      centralDistance L r (fun u => C (Fin.cons true u)) (fun u => D (Fin.cons true u)) := by
  classical
  unfold centralDistance
  rw [Fintype.sum_equiv (headTailEquiv r) _
    (fun x : Bool × Card r => permDistance (C (Fin.cons x.1 x.2)) (D (Fin.cons x.1 x.2)))
      (fun x => by
        change permDistance (C x) (D x) =
          permDistance (C (Fin.cons (x 0) (Fin.tail x))) (D (Fin.cons (x 0) (Fin.tail x)))
        rw [Fin.cons_self_tail])]
  simp only [Fintype.sum_prod_type,Fintype.sum_bool]
  omega

end Thorp

end ThorpNine.Adaptive

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Adaptive_InputTree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Adaptive

namespace Thorp

lemma centralDistance_exceptional (L r : ℕ) (C D : Card r → Equiv.Perm (Card L))
    (E : Finset (Card r)) (h : ∀ u ∉ E, C u = D u) :
    centralDistance L r C D ≤ E.card*2^L := by
  classical
  calc
    _ ≤ ∑ u : Card r, if u ∈ E then 2^L else 0 := by
      apply Finset.sum_le_sum
      intro u _
      split_ifs with hu
      · simpa only [card_positions] using permDistance_le (C u) (D u)
      · rw [h u hu,permDistance_refl]
    _ = _ := by simp


lemma InputTree.levelCost_node (t d : ℕ) (ξ : Card d → Bool) (T : Bool → InputTree d)
    {ι : Type*} [Fintype ι] (e : ι ↪ Card (d+1))
    (Y : (SwitchIndex d → Bool) × (SwitchIndex d → Bool)) (η : Card d → Bool) :
    (InputTree.node ξ T).levelCost t e ((coinStepEquiv d).symm (Y,η)) =
      let x := e.trans (headTailEquiv d).toEmbedding
      let c := PairRouting.colors x ξ
      let hc := PairRouting.colors_compatible x ξ
      if t = d+1 then PairRouting.alternatingCycles (PairRouting.switchedEmbedding x ξ)
        (fun b => if b then butterflyPerm d (decodeButterfly d Y.2) * (T true).perm⁻¹
          else butterflyPerm d (decodeButterfly d Y.1) * (T false).perm⁻¹)
      else (T false).levelCost t (PairRouting.childEmbedding x c hc false) Y.1 +
        (T true).levelCost t (PairRouting.childEmbedding x c hc true) Y.2 := by
  rw [InputTree.levelCost]
  rfl

lemma InputTree.levelCost_gt (t d : ℕ) (T : InputTree d) (ht : d < t)
    {ι : Type*} [Fintype ι] (e : ι ↪ Card d) (Y : SwitchIndex d → Bool) :
    T.levelCost t e Y = 0 := by
  induction T generalizing ι with
  | tip p => rfl
  | @node d ξ T ih =>
    rw [InputTree.levelCost,ite_eq_right (by omega : t ≠ d+1),ih false (by omega),ih true (by omega)]

lemma InputTree.levelCost_adapted (t d : ℕ) (T : InputTree d)
    {ι : Type*} [Fintype ι] (e : ι ↪ Card d) :
    LayerAdapted d (t-1) (fun Y => T.levelCost t e Y) := by
  induction T generalizing ι with
  | tip p => intro Y Y' _; rfl
  | @node d ξ T ih =>
    intro Y Y' h
    dsimp only
    conv_lhs => rw [←(coinStepEquiv d).symm_apply_apply Y]
    conv_rhs => rw [←(coinStepEquiv d).symm_apply_apply Y']
    rw [InputTree.levelCost_node t d ξ T e ((coinStepEquiv d Y).1) ((coinStepEquiv d Y).2),
      InputTree.levelCost_node t d ξ T e ((coinStepEquiv d Y').1) ((coinStepEquiv d Y').2)]
    by_cases ht : t = d+1
    · subst t
      rw [ite_eq_left rfl,ite_eq_left rfl]
      have he₀ : (coinStepEquiv d Y).1.1 = (coinStepEquiv d Y').1.1 := by
        funext i
        exact h (Sum.inr (false,i)) (by simpa only [switchHeight,Nat.add_sub_cancel] using switchHeight_le d i)
      have he₁ : (coinStepEquiv d Y).1.2 = (coinStepEquiv d Y').1.2 := by
        funext i
        exact h (Sum.inr (true,i)) (by simpa only [switchHeight,Nat.add_sub_cancel] using switchHeight_le d i)
      rw [he₀,he₁]
    · rw [ite_eq_right ht,ite_eq_right ht]
      congr 1
      · apply ih false
        intro i hi
        exact h (Sum.inr (false,i)) hi
      · apply ih true
        intro i hi
        exact h (Sum.inr (true,i)) hi

theorem InputTree.level_partial_mgf (r s u : ℕ) (hu : u < r)
    (T : InputTree (s+r)) {ι : Type*} [Fintype ι] (e : ι ↪ Card (s+r))
    (lo : Card r × SwitchIndex s → Bool) (J : ℕ) (hJ : 0 < J) (q : ℝ) (hq : 1 ≤ q) :
    finiteMean (fun hi : Card s × SwitchIndex r → Bool =>
      q^(T.levelCost (s+u+1) e (assembleBits r s lo hi))) ≤
      Real.exp (Fintype.card ι * cycleCoefficient u J q) := by
  classical
  induction r generalizing u ι with
  | zero => omega
  | succ r ih =>
    simp only [Nat.add_succ] at *
    cases T with
    | tip p =>
      simp only [InputTree.levelCost,pow_zero,finiteMean_const]
      exact Real.one_le_exp (mul_nonneg (Nat.cast_nonneg _) (cycleCoefficient_nonneg u J q hq))
    | node ξ T =>
      let x := e.trans (headTailEquiv (s+r)).toEmbedding
      let c := PairRouting.colors x ξ
      let hc := PairRouting.colors_compatible x ξ
      let e₀ := PairRouting.childEmbedding x c hc false
      let e₁ := PairRouting.childEmbedding x c hc true
      let e' := PairRouting.switchedEmbedding x ξ
      let lo₀ : Card r × SwitchIndex s → Bool := fun j => lo (Fin.cons false j.1,j.2)
      let lo₁ : Card r × SwitchIndex s → Bool := fun j => lo (Fin.cons true j.1,j.2)
      let Y₀ := fun hi : Card s × SwitchIndex r → Bool => assembleBits r s lo₀ hi
      let Y₁ := fun hi : Card s × SwitchIndex r → Bool => assembleBits r s lo₁ hi
      let N := fun hi : (Card s × SwitchIndex r → Bool) × (Card s × SwitchIndex r → Bool) =>
        PairRouting.alternatingCycles e' (fun b =>
          if b then butterflyPerm (s+r) (decodeButterfly (s+r) (Y₁ hi.2)) * (T true).perm⁻¹
          else butterflyPerm (s+r) (decodeButterfly (s+r) (Y₀ hi.1)) * (T false).perm⁻¹)
      let L₀ := fun hi : Card s × SwitchIndex r → Bool =>
        (T false).levelCost (s+u+1) e₀ (Y₀ hi)
      let L₁ := fun hi : Card s × SwitchIndex r → Bool =>
        (T true).levelCost (s+u+1) e₁ (Y₁ hi)
      have hs (hi : (Card s × SwitchIndex r → Bool) × (Card s × SwitchIndex r → Bool))
          (η : Card s × Card r → Bool) :
          (InputTree.node ξ T).levelCost (s+u+1) e
            (assembleBits (r+1) s lo ((highStepEquiv r s).symm (hi,η))) =
            if u = r then N hi else L₀ hi.1 + L₁ hi.2 := by
        rw [assembleBits_step]
        rw [InputTree.levelCost_node (s+u+1) (s+r) ξ T e (Y₀ hi.1,Y₁ hi.2) (fun y => η (((cardSplit r s) y).2,((cardSplit r s) y).1))]
        simp only [Nat.add_right_cancel_iff,Nat.add_left_cancel_iff]
        rfl
      rw [finiteMean_equiv (highStepEquiv r s),finiteMean_prod]
      simp_rw [hs,finiteMean_const]
      by_cases hur : u = r
      · subst u
        simp only [ite_true]
        rw [finiteMean_prod,finiteMean_comm]
        calc
          _ ≤ finiteMean (fun _hi : Card s × SwitchIndex r → Bool =>
            Real.exp (Fintype.card ι * cycleCoefficient r J q)) := by
            apply finiteMean_mono
            intro hi
            have hn := node_partial_mgf r s e' (T false).perm (T true).perm
              (butterflyPerm (s+r) (decodeButterfly (s+r) (Y₁ hi))) lo₀ J hJ q hq
            exact hn
          _ = _ := finiteMean_const _
      · simp only [ite_eq_right hur,pow_add]
        rw [finiteMean_prod_mul (fun hi => q ^ L₀ hi) (fun hi => q ^ L₁ hi)]
        have hu' : u < r := by omega
        have h₀ := ih u hu' (T false) e₀ lo₀
        have h₁ := ih u hu' (T true) e₁ lo₁
        have hp := mul_le_mul h₀ h₁ (finiteMean_nonneg (fun _ => pow_nonneg (by linarith) _))
          (Real.exp_nonneg _)
        refine hp.trans_eq ?_
        rw [←Real.exp_add]
        congr 1
        have hcount := PairRouting.color_card_add c
        have hcount' : (Fintype.card {i : ι // c i = false} : ℝ) +
            Fintype.card {i : ι // c i = true} = Fintype.card ι := by exact_mod_cast hcount
        change (Fintype.card {i : ι // c i = false} : ℝ) * cycleCoefficient u J q +
            Fintype.card {i : ι // c i = true} * cycleCoefficient u J q = _
        rw [←add_mul,hcount']


lemma InputTree.slabCost_adapted (l d : ℕ) (T : InputTree d) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) :
    LayerAdapted d (2*l) (fun Y => InputTree.slabCost l d T e Y) := by
  apply layerAdapted_sum
  intro i _
  exact layerAdapted_mono (InputTree.levelCost_adapted (l+i.1+1) d T e) (by omega)

theorem InputTree.slab_partial_mgf (r s l : ℕ) (hl : 0 < l) (hs : 2*s ≤ l) (T : InputTree (s+r))
    {ι : Type*} [Fintype ι] (e : ι ↪ Card (s+r))
    (lo : Card r × SwitchIndex s → Bool) (q : ℝ) (hq : 1 ≤ q)
    (hlog : Real.log q ≤ 1/250) :
    finiteMean (fun hi : Card s × SwitchIndex r → Bool =>
      q^(InputTree.slabCost l (s+r) T e (assembleBits r s lo hi))) ≤
      Real.exp (Fintype.card ι * (68*Real.exp (-(l:ℝ)/64))) := by
  classical
  let : NeZero l := ⟨ne_of_gt hl⟩
  have hqp : 0 < q := lt_of_lt_of_le (by norm_num) hq
  calc
    _ ≤ finiteMean (fun hi : Card s × SwitchIndex r → Bool =>
      finiteMean (fun i : Fin l => q^(l*T.levelCost (l+i.1+1) e
        (assembleBits r s lo hi)))) := by
      apply finiteMean_mono
      intro hi
      simpa only [InputTree.slabCost,Fintype.card_fin] using
        pow_sum_le_mean_powers (fun i : Fin l => T.levelCost (l+i.1+1) e
          (assembleBits r s lo hi)) q hqp
    _ = finiteMean (fun i : Fin l => finiteMean (fun hi : Card s × SwitchIndex r → Bool =>
      q^(l*T.levelCost (l+i.1+1) e (assembleBits r s lo hi)))) := finiteMean_comm _
    _ ≤ finiteMean (fun _i : Fin l =>
      Real.exp (Fintype.card ι * (68*Real.exp (-(l:ℝ)/64)))) := by
      apply finiteMean_mono
      intro i
      by_cases ht : l+i.1+1 ≤ s+r
      · have hs' : s ≤ l+i.1 := by omega
        have he : l+i.1+1 = s+(l+i.1-s)+1 := by omega
        have hu : l+i.1-s < r := by omega
        have hm := InputTree.level_partial_mgf r s (l+i.1-s) hu T e lo
          ⌈Real.exp ((l:ℝ)/32)⌉₊ (cycleCutoff_pos l) (q^l) (one_le_pow₀ hq)
        have hc := cycleCoefficient_decay l (l+i.1-s) (by
          rw [Nat.cast_sub hs',Nat.cast_add]
          have hsr : (2:ℝ)*s ≤ l := by exact_mod_cast hs
          have hi : (0:ℝ) ≤ i.1 := Nat.cast_nonneg _
          linarith) (q^l) (one_le_pow₀ hq) (by
            rw [Real.log_pow]
            nlinarith [mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg l)])
        simp_rw [he,pow_mul]
        exact hm.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg _)))
      · have hz := InputTree.levelCost_gt (l+i.1+1) (s+r) T (by omega) e
        simp only [hz,Nat.mul_zero,pow_zero,finiteMean_const]
        exact Real.one_le_exp_iff.mpr (by positivity)
    _ = _ := finiteMean_const _


lemma boundaryOutput_adapted (L r : ℕ) :
    LayerAdapted (L+r) L (boundaryOutput L r) := by
  induction r with
  | zero =>
    intro Y Y' h
    have he : Y = Y' := funext (fun i => h i (by simpa only [Nat.add_zero] using switchHeight_le L i))
    rw [he]
  | succ r ih =>
    intro Y Y' h
    funext u
    dsimp only [boundaryOutput]
    cases hb : u 0 <;> simp only [Bool.false_eq_true,↓reduceIte]
    · exact congrFun (ih _ _ (fun i hi => h (Sum.inr (false,i)) hi)) (Fin.tail u)
    · exact congrFun (ih _ _ (fun i hi => h (Sum.inr (true,i)) hi)) (Fin.tail u)

lemma modifiedBoundary_adapted (L r : ℕ) (E : Finset (Card r))
    (U : Card r → Equiv.Perm (Card L)) :
    LayerAdapted (L+r) L (modifiedBoundary L r E U) := by
  intro Y Y' h
  unfold modifiedBoundary
  rw [boundaryOutput_adapted L r Y Y' h]

lemma permDistance_boundaryTree (L r : ℕ) (U V : Card r → Equiv.Perm (Card L))
    (X : SwitchIndex (L+r) → Bool) :
    permDistance (boundaryTree L r U X).perm (boundaryTree L r V X).perm =
      centralDistance L r U V := by
  induction r with
  | zero =>
    simp only [boundaryTree,InputTree.perm,centralDistance,Fintype.sum_unique]
    congr 1
  | succ r ih =>
    simp only [boundaryTree,InputTree.perm,permDistance_mul_left]
    rw [permDistance_childLift,centralDistance_step,ih,ih]

lemma boundaryTree_levelCost_perturb (t L r : ℕ) (U V : Card r → Equiv.Perm (Card L))
    (X : SwitchIndex (L+r) → Bool) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card (L+r)) (Y : SwitchIndex (L+r) → Bool) :
    (boundaryTree L r U X).levelCost t e Y ≤
      (boundaryTree L r V X).levelCost t e Y + centralDistance L r U V := by
  induction r generalizing ι with
  | zero => simp only [boundaryTree,InputTree.levelCost,Nat.zero_add,Nat.zero_le]
  | succ r ih =>
    rw [boundaryTree,boundaryTree,InputTree.levelCost,InputTree.levelCost]
    by_cases ht : t = L+r+1
    · simp only [ite_eq_left ht]
      have hh := alternatingCycles_distance_le
        (PairRouting.switchedEmbedding (e.trans (headTailEquiv (L+r)).toEmbedding)
          (coinStepEquiv (L+r) X).2)
        (fun b => if b then butterflyPerm (L+r) (decodeButterfly (L+r) (coinStepEquiv (L+r) Y).1.2) *
            (boundaryTree L r (fun u => U (Fin.cons true u)) (coinStepEquiv (L+r) X).1.2).perm⁻¹
          else butterflyPerm (L+r) (decodeButterfly (L+r) (coinStepEquiv (L+r) Y).1.1) *
            (boundaryTree L r (fun u => U (Fin.cons false u)) (coinStepEquiv (L+r) X).1.1).perm⁻¹)
        (fun b => if b then butterflyPerm (L+r) (decodeButterfly (L+r) (coinStepEquiv (L+r) Y).1.2) *
            (boundaryTree L r (fun u => V (Fin.cons true u)) (coinStepEquiv (L+r) X).1.2).perm⁻¹
          else butterflyPerm (L+r) (decodeButterfly (L+r) (coinStepEquiv (L+r) Y).1.1) *
            (boundaryTree L r (fun u => V (Fin.cons false u)) (coinStepEquiv (L+r) X).1.1).perm⁻¹)
      simpa only [Bool.false_eq_true,↓reduceIte,permDistance_mul_left,permDistance_inv,
        permDistance_boundaryTree,←centralDistance_step] using hh
    · simp only [ite_eq_right ht,Bool.false_eq_true,↓reduceIte]
      rw [centralDistance_step]
      have h₀ := ih (fun u => U (Fin.cons false u)) (fun u => V (Fin.cons false u))
        (coinStepEquiv (L+r) X).1.1
        (PairRouting.childEmbedding (e.trans (headTailEquiv (L+r)).toEmbedding)
          (PairRouting.colors (e.trans (headTailEquiv (L+r)).toEmbedding) (coinStepEquiv (L+r) X).2)
          (PairRouting.colors_compatible _ _) false) (coinStepEquiv (L+r) Y).1.1
      have h₁ := ih (fun u => U (Fin.cons true u)) (fun u => V (Fin.cons true u))
        (coinStepEquiv (L+r) X).1.2
        (PairRouting.childEmbedding (e.trans (headTailEquiv (L+r)).toEmbedding)
          (PairRouting.colors (e.trans (headTailEquiv (L+r)).toEmbedding) (coinStepEquiv (L+r) X).2)
          (PairRouting.colors_compatible _ _) true) (coinStepEquiv (L+r) Y).1.2
      omega

lemma boundaryTree_slabCost_perturb (l L r : ℕ) (U V : Card r → Equiv.Perm (Card L))
    (X : SwitchIndex (L+r) → Bool) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card (L+r)) (Y : SwitchIndex (L+r) → Bool) :
    InputTree.slabCost l (L+r) (boundaryTree L r U X) e Y ≤
      InputTree.slabCost l (L+r) (boundaryTree L r V X) e Y + l*centralDistance L r U V := by
  have hh := Finset.sum_le_sum (fun (i : Fin l) (_ : i ∈ Finset.univ) =>
    boundaryTree_levelCost_perturb (l+i.val+1) L r U V X e Y)
  simpa only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,Nat.cast_id,InputTree.slabCost] using hh

lemma modifiedBoundary_distance_le (L r : ℕ) (E : Finset (Card r))
    (U : Card r → Equiv.Perm (Card L)) (Y : SwitchIndex (L+r) → Bool) :
    centralDistance L r (modifiedBoundary L r E U Y) U ≤ E.card*2^L := by
  apply centralDistance_exceptional
  intro u hu
  exact ite_eq_right hu


lemma InputTree.slabCost_gt (l d : ℕ) (T : InputTree d) (hd : d ≤ l)
    {ι : Type*} [Fintype ι] (e : ι ↪ Card d) (Y : SwitchIndex d → Bool) :
    InputTree.slabCost l d T e Y = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  exact InputTree.levelCost_gt _ _ T (by omega) _ _

lemma InputTree.random_slab_adapted_mul_le (d s l : ℕ) (hsd : s ≤ d) (hl : 0 < l)
    (hs : 2*s ≤ l) (T : (SwitchIndex d → Bool) → InputTree d)
    (hT : LayerAdapted d s T) {ι : Type*} [Fintype ι] (e : ι ↪ Card d)
    (F : (SwitchIndex d → Bool) → ℝ) (hF : ∀ Y, 0 ≤ F Y) (hA : LayerAdapted d s F)
    (q : ℝ) (hq : 1 ≤ q) (hlog : Real.log q ≤ 1/250) :
    finiteMean (fun Y => F Y*q^(InputTree.slabCost l d (T Y) e Y)) ≤
      finiteMean F * Real.exp (Fintype.card ι * (68*Real.exp (-(l:ℝ)/64))) := by
  obtain ⟨r,rfl⟩ := Nat.exists_eq_add_of_le hsd
  apply adapted_mul_mean_le r s F _ hF hA
  intro lo
  let hi₀ : Card s × SwitchIndex r → Bool := fun _ => false
  have he (hi : Card s × SwitchIndex r → Bool) :
      T (assembleBits r s lo hi) = T (assembleBits r s lo hi₀) :=
    hT _ _ (assembleBits_agree r s lo hi hi₀)
  simp_rw [he]
  exact InputTree.slab_partial_mgf r s l hl hs _ e lo q hq hlog

lemma InputTree.slab_mgf (l d : ℕ) (hl : 0 < l) (T : InputTree d)
    {ι : Type*} [Fintype ι] (e : ι ↪ Card d) (q : ℝ) (hq : 1 ≤ q)
    (hlog : Real.log q ≤ 1/250) :
    finiteMean (fun Y => q^(InputTree.slabCost l d T e Y)) ≤
      Real.exp (Fintype.card ι * (68*Real.exp (-(l:ℝ)/64))) := by
  have hh := InputTree.random_slab_adapted_mul_le d 0 l (Nat.zero_le _) hl (Nat.zero_le _)
    (fun _ => T) (fun _ _ _ => rfl) e (fun _ => 1) (fun _ => by norm_num)
    (fun _ _ _ => rfl) q hq hlog
  simpa only [one_mul,finiteMean_const] using hh

lemma InputTree.random_slabCost_adapted (l d s : ℕ) (T : (SwitchIndex d → Bool) → InputTree d)
    (hT : LayerAdapted d s T) {ι : Type*} [Fintype ι] (e : ι ↪ Card d) :
    LayerAdapted d (max s (2*l)) (fun Y => InputTree.slabCost l d (T Y) e Y) := by
  intro Y Y' h
  dsimp only
  rw [hT _ _ (agreeThrough_mono (le_max_left _ _) h)]
  exact InputTree.slabCost_adapted l d (T Y') e Y Y'
    (agreeThrough_mono (le_max_right _ _) h)

lemma InputTree.familyCost_adapted (L n d s : ℕ) (T : (SwitchIndex d → Bool) → InputTree d)
    (hT : LayerAdapted d s T) {ι : Type*} [Fintype ι] (e : ι ↪ Card d) :
    LayerAdapted d (max s (familyEnd L n)) (fun Y => InputTree.familyCost L n d T e Y) := by
  apply layerAdapted_sum
  intro j hj
  exact layerAdapted_mono (InputTree.random_slabCost_adapted (L*4^j) d s T hT e)
    (max_le_max_left s (familyEnd_ge L n j (Finset.mem_range.mp hj)))

theorem InputTree.family_mgf_first (L n d s : ℕ) (hL : 0 < L) (hs : s ≤ L)
    (T : (SwitchIndex d → Bool) → InputTree d) (hT : LayerAdapted d s T)
    {ι : Type*} [Fintype ι] (e : ι ↪ Card d) (q : ℝ) (hq : 1 ≤ q)
    (hlog : Real.log q ≤ 1/250) (p : ℝ) (hp : 0 ≤ p)
    (hfirst : finiteMean (fun Y => q^(InputTree.slabCost L d (T Y) e Y)) ≤
      Real.exp (p+Fintype.card ι*(68*Real.exp (-(L:ℝ)/64)))) :
    finiteMean (fun Y => q^(InputTree.familyCost L n d T e Y)) ≤
      Real.exp (p+Fintype.card ι*(68*∑ j ∈ Finset.range n,
        Real.exp (-((L*4^j:ℕ):ℝ)/64))) := by
  induction n with
  | zero =>
    simp only [InputTree.familyCost,Finset.range_zero,Finset.sum_empty,pow_zero,
      finiteMean_const,mul_zero,add_zero]
    exact Real.one_le_exp hp
  | succ n ih =>
    by_cases hn : n = 0
    · subst n
      simpa only [InputTree.familyCost,Nat.zero_add,Finset.sum_range_one,pow_zero,mul_one] using hfirst
    · let l := L*4^n
      have hl : 0 < l := Nat.mul_pos hL (pow_pos (by decide) _)
      have hsl : 2*familyEnd L n ≤ l := familyEnd_two L n
      have hs' : s ≤ familyEnd L n := by
        have hh := familyEnd_ge L n 0 (Nat.pos_of_ne_zero hn)
        simp only [pow_zero,mul_one] at hh
        omega
      have hc : ∀ Y, InputTree.familyCost L (n+1) d T e Y =
          InputTree.familyCost L n d T e Y+InputTree.slabCost l d (T Y) e Y := by
        intro Y
        exact Finset.sum_range_succ _ _
      have hm : finiteMean (fun Y => q^(InputTree.familyCost L (n+1) d T e Y)) ≤
          finiteMean (fun Y => q^(InputTree.familyCost L n d T e Y)) *
            Real.exp (Fintype.card ι*(68*Real.exp (-(l:ℝ)/64))) := by
        by_cases hld : l ≤ d
        · simp_rw [hc,pow_add]
          apply InputTree.random_slab_adapted_mul_le d (familyEnd L n) l (by omega) hl hsl T
            (layerAdapted_mono hT hs') e _ (fun _ => pow_nonneg (by linarith) _)
          · apply layerAdapted_comp
            exact layerAdapted_mono (InputTree.familyCost_adapted L n d s T hT e) (max_le hs' le_rfl)
          · exact hq
          · exact hlog
        · simp_rw [hc,InputTree.slabCost_gt l d _ (by omega),Nat.add_zero]
          exact le_mul_of_one_le_right
            (finiteMean_nonneg (fun _ => pow_nonneg (by linarith) _))
            (Real.one_le_exp_iff.mpr (by positivity))
      refine (hm.trans (mul_le_mul_of_nonneg_right ih (Real.exp_nonneg _))).trans_eq ?_
      rw [←Real.exp_add,Finset.sum_range_succ]
      congr 1
      dsimp only [l]
      ring

lemma InputTree.family_mgf_first_decay (L n d s : ℕ) (hL : 0 < L) (hs : s ≤ L)
    (T : (SwitchIndex d → Bool) → InputTree d) (hT : LayerAdapted d s T)
    {ι : Type*} [Fintype ι] (e : ι ↪ Card d) (q : ℝ) (hq : 1 ≤ q)
    (hlog : Real.log q ≤ 1/250) (p : ℝ) (hp : 0 ≤ p)
    (hfirst : finiteMean (fun Y => q^(InputTree.slabCost L d (T Y) e Y)) ≤
      Real.exp (p+Fintype.card ι*(68*Real.exp (-(L:ℝ)/64)))) :
    finiteMean (fun Y => q^(InputTree.familyCost L n d T e Y)) ≤
      Real.exp (p+Fintype.card ι*heightDecay L) := by
  apply (InputTree.family_mgf_first L n d s hL hs T hT e q hq hlog p hp hfirst).trans
  apply Real.exp_le_exp.mpr
  apply add_le_add_right
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  have hh := mul_le_mul_of_nonneg_left (sum_family_decay L n hL) (by norm_num : (0:ℝ)≤68)
  simpa only [heightDecay,mul_div_assoc] using hh


lemma modifiedInputTree_adapted (L r : ℕ) (E : Finset (Card r))
    (U : Card r → Equiv.Perm (Card L)) (X : SwitchIndex (L+r) → Bool) :
    LayerAdapted (L+r) L (modifiedInputTree L r E U X) := by
  intro Y Y' h
  unfold modifiedInputTree
  rw [modifiedBoundary_adapted L r E U Y Y' h]

lemma modified_slab_mgf (l L r : ℕ) (hl : 0 < l) (E : Finset (Card r))
    (U : Card r → Equiv.Perm (Card L)) (X : SwitchIndex (L+r) → Bool)
    {ι : Type*} [Fintype ι] (e : ι ↪ Card (L+r)) (q : ℝ) (hq : 1 ≤ q)
    (hlog : Real.log q ≤ 1/250) :
    finiteMean (fun Y => q^(InputTree.slabCost l (L+r) (modifiedInputTree L r E U X Y) e Y)) ≤
      Real.exp (((l*E.card*2^L:ℕ):ℝ)*Real.log q+
        Fintype.card ι*(68*Real.exp (-(l:ℝ)/64))) := by
  have hqp : 0 < q := by linarith
  have hpoint (Y : SwitchIndex (L+r) → Bool) :
      InputTree.slabCost l (L+r) (modifiedInputTree L r E U X Y) e Y ≤
        InputTree.slabCost l (L+r) (boundaryTree L r U X) e Y+l*E.card*2^L := by
    apply (boundaryTree_slabCost_perturb l L r (modifiedBoundary L r E U Y) U X e Y).trans
    apply Nat.add_le_add_left
    simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left l (modifiedBoundary_distance_le L r E U Y)
  calc
    _ ≤ finiteMean (fun Y => q^(InputTree.slabCost l (L+r) (boundaryTree L r U X) e Y+l*E.card*2^L)) :=
      finiteMean_mono (fun Y => pow_le_pow_right₀ hq (hpoint Y))
    _ = finiteMean (fun Y => q^(InputTree.slabCost l (L+r) (boundaryTree L r U X) e Y)) *
        q^(l*E.card*2^L) := by simp_rw [pow_add]; exact finiteMean_mul_const _ _
    _ ≤ Real.exp (Fintype.card ι*(68*Real.exp (-(l:ℝ)/64))) * q^(l*E.card*2^L) :=
      mul_le_mul_of_nonneg_right (InputTree.slab_mgf l (L+r) hl _ e q hq hlog) (pow_nonneg (by linarith) _)
    _ = _ := by
      have he : Real.exp (((l*E.card*2^L:ℕ):ℝ)*Real.log q) = q^(l*E.card*2^L) := by
        rw [Real.exp_nat_mul,Real.exp_log hqp]
      rw [Real.exp_add,he,mul_comm]

lemma modified_family_mgf (l n L r : ℕ) (hl : 0 < l) (hLl : L ≤ l) (E : Finset (Card r))
    (U : Card r → Equiv.Perm (Card L)) (X : SwitchIndex (L+r) → Bool)
    {ι : Type*} [Fintype ι] (e : ι ↪ Card (L+r)) (q : ℝ) (hq : 1 ≤ q)
    (hlog : Real.log q ≤ 1/250) :
    finiteMean (fun Y => q^(InputTree.familyCost l n (L+r) (modifiedInputTree L r E U X) e Y)) ≤
      Real.exp (((l*E.card*2^L:ℕ):ℝ)*Real.log q+Fintype.card ι*heightDecay l) := by
  exact InputTree.family_mgf_first_decay l n (L+r) L hl hLl _
    (modifiedInputTree_adapted L r E U X) e q hq hlog _
    (mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg hq))
    (modified_slab_mgf l L r hl E U X e q hq hlog)

theorem modified_high_mgf (L n r : ℕ) (hL : 0 < L) (E : Finset (Card r))
    (U : Card r → Equiv.Perm (Card L)) (X : SwitchIndex (L+r) → Bool)
    {ι : Type*} [Fintype ι] (e : ι ↪ Card (L+r)) (q : ℝ) (hq : 1 ≤ q)
    (hlog : Real.log q ≤ 1/500) :
    finiteMean (fun Y => q^(InputTree.familyCost L n (L+r) (modifiedInputTree L r E U X) e Y+
      InputTree.familyCost (2*L) n (L+r) (modifiedInputTree L r E U X) e Y)) ≤
      Real.exp (Fintype.card ι*heightDecay L +
        3*((L*E.card*2^L:ℕ):ℝ)*Real.log q) := by
  have hq2 := one_le_pow₀ (n:=2) hq
  have hlog2 : Real.log (q^2) ≤ 1/250 := by rw [Real.log_pow]; norm_num; linarith
  have h₀ := modified_family_mgf L n L r hL le_rfl E U X e (q^2) hq2 hlog2
  have h₁ := modified_family_mgf (2*L) n L r (by omega) (by omega) E U X e (q^2) hq2 hlog2
  have h₁' : finiteMean (fun Y => (q^2)^(InputTree.familyCost (2*L) n (L+r)
      (modifiedInputTree L r E U X) e Y)) ≤
      Real.exp ((((2*L)*E.card*2^L:ℕ):ℝ)*Real.log (q^2)+Fintype.card ι*heightDecay L) := by
    apply h₁.trans
    apply Real.exp_le_exp.mpr
    exact add_le_add_right (mul_le_mul_of_nonneg_left
      (heightDecay_antitone (show L ≤ 2*L by omega)) (Nat.cast_nonneg _)) _
  have hh := finiteMean_mul_exp_le
    (fun Y => q^(InputTree.familyCost L n (L+r) (modifiedInputTree L r E U X) e Y))
    (fun Y => q^(InputTree.familyCost (2*L) n (L+r) (modifiedInputTree L r E U X) e Y))
    _ _ (by simpa only [pow_right_comm] using h₀) (by simpa only [pow_right_comm] using h₁')
  simp only [←pow_add] at hh
  refine hh.trans_eq ?_
  congr 1
  simp only [Real.log_pow,Nat.cast_mul,Nat.cast_ofNat]
  ring

lemma InputTree.lowCost_slab (L d : ℕ) (T : InputTree d)
    {ι : Type*} [Fintype ι] (e : ι ↪ Card d) (Y : SwitchIndex d → Bool) :
    InputTree.lowCost L d T e Y+InputTree.slabCost L d T e Y = InputTree.lowCost (2*L) d T e Y := by
  rw [InputTree.lowCost,InputTree.lowCost,show 2*L=L+L by omega,Finset.sum_range_add]
  congr 1
  exact Fin.sum_univ_eq_sum_range (fun i => T.levelCost (L+i+1) e Y) L

lemma InputTree.cost_family (L n d : ℕ) (T : (SwitchIndex d → Bool) → InputTree d)
    {ι : Type*} [Fintype ι] (e : ι ↪ Card d) (Y : SwitchIndex d → Bool) :
    InputTree.lowCost L d (T Y) e Y + InputTree.familyCost L n d T e Y +
      InputTree.familyCost (2*L) n d T e Y = InputTree.lowCost (L*4^n) d (T Y) e Y := by
  induction n with
  | zero => simp only [InputTree.familyCost,Finset.range_zero,Finset.sum_empty,Nat.add_zero,
      pow_zero,mul_one]
  | succ n ih =>
    have he : (2*L)*4^n = 2*(L*4^n) := by ring
    have he' : L*4^(n+1) = 2*(2*(L*4^n)) := by rw [pow_succ]; ring
    simp only [InputTree.familyCost,Finset.sum_range_succ] at ih ⊢
    rw [he,he',←InputTree.lowCost_slab,←InputTree.lowCost_slab,←ih]
    omega

lemma InputTree.lowCost_ge (H d : ℕ) (hd : d ≤ H) (T : InputTree d)
    {ι : Type*} [Fintype ι] (e : ι ↪ Card d) (Y : SwitchIndex d → Bool) :
    InputTree.lowCost H d T e Y = InputTree.lowCost d d T e Y := by
  symm
  apply Finset.sum_subset (Finset.range_mono hd)
  intro i _ hi
  have hi' : d ≤ i := by simpa only [Finset.mem_range,not_lt] using hi
  exact InputTree.levelCost_gt (i+1) d T (by omega) e Y

lemma boundaryTree_levelCost_low (t L r : ℕ) (ht : t ≤ L)
    (U : Card r → Equiv.Perm (Card L)) (X : SwitchIndex (L+r) → Bool)
    {ι : Type*} [Fintype ι] (e : ι ↪ Card (L+r)) (Y : SwitchIndex (L+r) → Bool) :
    (boundaryTree L r U X).levelCost t e Y = 0 := by
  induction r generalizing ι with
  | zero => rfl
  | succ r ih =>
    rw [boundaryTree,InputTree.levelCost,ite_eq_right (by omega : t ≠ L+r+1),ih,ih]

lemma boundaryTree_lowCost_zero (L r : ℕ) (U : Card r → Equiv.Perm (Card L))
    (X : SwitchIndex (L+r) → Bool) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card (L+r)) (Y : SwitchIndex (L+r) → Bool) :
    InputTree.lowCost L (L+r) (boundaryTree L r U X) e Y = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  exact boundaryTree_levelCost_low (i+1) L r (by simpa only [Finset.mem_range,Nat.lt_iff_add_one_le] using hi) U X e Y

theorem modified_cost_mgf (L r : ℕ) (hL : 0 < L) (E : Finset (Card r))
    (U : Card r → Equiv.Perm (Card L)) (X : SwitchIndex (L+r) → Bool)
    {ι : Type*} [Fintype ι] (e : ι ↪ Card (L+r)) (q : ℝ) (hq : 1 ≤ q)
    (hlog : Real.log q ≤ 1/500) :
    finiteMean (fun Y => q^(InputTree.lowCost (L+r) (L+r) (modifiedInputTree L r E U X Y) e Y)) ≤
      Real.exp (Fintype.card ι*heightDecay L +
        3*((L*E.card*2^L:ℕ):ℝ)*Real.log q) := by
  have hbound : L+r ≤ L*4^(L+r) := by
    have h₀ := pow_four_ge (L+r)
    have h₁ := Nat.mul_le_mul_right (4^(L+r)) hL
    nlinarith
  have he (Y : SwitchIndex (L+r) → Bool) :=
    InputTree.cost_family L (L+r) (L+r) (modifiedInputTree L r E U X) e Y
  have hz (Y : SwitchIndex (L+r) → Bool) :
      InputTree.lowCost L (L+r) (modifiedInputTree L r E U X Y) e Y = 0 :=
    boundaryTree_lowCost_zero L r _ X e Y
  simp only [hz,Nat.zero_add,InputTree.lowCost_ge _ _ hbound] at he
  simp_rw [←he]
  exact modified_high_mgf L (L+r) r hL E U X e q hq hlog


lemma mem_exceptionChild {r : ℕ} (E : Finset (Card (r+1))) (b : Bool) (u : Card r) :
    u ∈ exceptionChild E b ↔ Fin.cons b u ∈ E := by
  classical
  simp only [exceptionChild,Finset.mem_filter,Finset.mem_univ,true_and]

lemma exceptionChild_card_add {r : ℕ} (E : Finset (Card (r+1))) :
    (exceptionChild E false).card+(exceptionChild E true).card = E.card := by
  classical
  have he : (∑ u : Card (r+1), if u ∈ E then 1 else 0) = E.card := by simp
  rw [Fintype.sum_equiv (headTailEquiv r) _
    (fun x : Bool × Card r => if Fin.cons x.1 x.2 ∈ E then 1 else 0)
    (fun x => by change (if x ∈ E then 1 else 0) = (if Fin.cons (x 0) (Fin.tail x) ∈ E then 1 else 0); rw [Fin.cons_self_tail])] at he
  simp only [Fintype.sum_prod_type,Fintype.sum_bool] at he
  simpa only [exceptionChild,Finset.card_filter,add_comm] using he

lemma modifiedBoundary_cons (L r : ℕ) (E : Finset (Card (r+1)))
    (U : Card (r+1) → Equiv.Perm (Card L)) (Y : SwitchIndex (L+r+1) → Bool) (b : Bool) :
    (fun u => modifiedBoundary L (r+1) E U Y (Fin.cons b u)) =
    modifiedBoundary L r (exceptionChild E b) (fun u => U (Fin.cons b u))
      (if b then (coinStepEquiv (L+r) Y).1.2 else (coinStepEquiv (L+r) Y).1.1) := by
  funext u
  simp only [modifiedBoundary,mem_exceptionChild,boundaryOutput,Fin.cons_zero,Fin.tail_cons]

lemma modifiedInputTree_node (L r : ℕ) (E : Finset (Card (r+1)))
    (ω : ModifiedCoins L r × ModifiedCoins L r) (coins : (Card (L+r) → Bool) × (Card (L+r) → Bool)) :
    let z := (modifiedStepEquiv L r).symm (ω,coins)
    modifiedInputTree L (r+1) E z.1 z.2.2 z.2.1 =
      InputTree.node coins.1 (fun b =>
        let w := if b then ω.2 else ω.1
        modifiedInputTree L r (exceptionChild E b) w.1 w.2.2 w.2.1) := by
  dsimp only
  unfold modifiedInputTree
  rw [boundaryTree]
  change InputTree.node coins.1 (fun b => boundaryTree L r _ _) = _
  congr 1
  funext b
  rw [modifiedBoundary_cons]
  cases b <;> rfl

lemma modifiedPerm_step (L r : ℕ) (E : Finset (Card (r+1)))
    (ω : ModifiedCoins L r × ModifiedCoins L r) (coins : (Card (L+r) → Bool) × (Card (L+r) → Bool)) :
    modifiedPerm L (r+1) E ((modifiedStepEquiv L r).symm (ω,coins)) =
      pairSwitch coins.2 * childLift (fun b => modifiedPerm L r (exceptionChild E b)
        (if b then ω.2 else ω.1)) * pairSwitch coins.1 := by
  rw [modifiedPerm,modifiedInputTree_node,InputTree.perm,mul_inv_rev,pairSwitch_inv,childLift_inv]
  change (butterflyPerm (L+r+1) (decodeButterfly (L+r+1)
    ((coinStepEquiv (L+r)).symm ((ω.1.2.1,ω.2.2.1),coins.2)))) * _ = _
  rw [butterflyPerm_step,mul_assoc,←mul_assoc (childLift _),childLift_mul,←mul_assoc]
  congr 2
  apply congrArg childLift
  funext b
  cases b <;> rfl

lemma modifiedPerm_coordinates (L r : ℕ) (E : Finset (Card (r+1)))
    (ω : ModifiedCoins L r × ModifiedCoins L r) (coins : (Card (L+r) → Bool) × (Card (L+r) → Bool))
    (x : Card (L+r+1)) :
    headTailEquiv (L+r) (modifiedPerm L (r+1) E ((modifiedStepEquiv L r).symm (ω,coins)) x) =
      PairRouting.sandwich coins.1 coins.2 (fun b => modifiedPerm L r (exceptionChild E b)
        (if b then ω.2 else ω.1)) (headTailEquiv (L+r) x) := by
  rw [modifiedPerm_step]
  simp only [Equiv.Perm.mul_apply,headTail_switch,headTail_child]
  rfl

lemma InputTree.lowCost_node (d : ℕ) (ξ : Card d → Bool) (T : Bool → InputTree d)
    {ι : Type*} [Fintype ι] (e : ι ↪ Card (d+1)) (Y : (SwitchIndex d → Bool) × (SwitchIndex d → Bool))
    (η : Card d → Bool) :
    InputTree.lowCost (d+1) (d+1) (.node ξ T) e ((coinStepEquiv d).symm (Y,η)) =
      let x := e.trans (headTailEquiv d).toEmbedding
      let c := PairRouting.colors x ξ
      let hc := PairRouting.colors_compatible x ξ
      PairRouting.alternatingCycles (PairRouting.switchedEmbedding x ξ)
        (fun b => if b then butterflyPerm d (decodeButterfly d Y.2) * (T true).perm⁻¹
          else butterflyPerm d (decodeButterfly d Y.1) * (T false).perm⁻¹) +
        InputTree.lowCost d d (T false) (PairRouting.childEmbedding x c hc false) Y.1 +
        InputTree.lowCost d d (T true) (PairRouting.childEmbedding x c hc true) Y.2 := by
  dsimp only
  rw [InputTree.lowCost,Finset.sum_range_succ,InputTree.levelCost_node,ite_eq_left rfl]
  have he : (∑ i ∈ Finset.range d,
      (.node ξ T : InputTree (d+1)).levelCost (i+1) e ((coinStepEquiv d).symm (Y,η))) =
      InputTree.lowCost d d (T false)
        (PairRouting.childEmbedding (e.trans (headTailEquiv d).toEmbedding)
          (PairRouting.colors (e.trans (headTailEquiv d).toEmbedding) ξ) (PairRouting.colors_compatible _ _) false) Y.1 +
      InputTree.lowCost d d (T true)
        (PairRouting.childEmbedding (e.trans (headTailEquiv d).toEmbedding)
          (PairRouting.colors (e.trans (headTailEquiv d).toEmbedding) ξ) (PairRouting.colors_compatible _ _) true) Y.2 := by
    rw [InputTree.lowCost,InputTree.lowCost,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [InputTree.levelCost_node,ite_eq_right (by simp only [Finset.mem_range] at hi; omega : i+1 ≠ d+1)]
  rw [he]
  omega

lemma modifiedCost_step (L r : ℕ) (E : Finset (Card (r+1)))
    {ι : Type*} [Fintype ι] (e : ι ↪ Card (L+r+1))
    (ω : ModifiedCoins L r × ModifiedCoins L r) (coins : (Card (L+r) → Bool) × (Card (L+r) → Bool)) :
    modifiedCost L (r+1) E e ((modifiedStepEquiv L r).symm (ω,coins)) =
      modifiedAssignmentCost L r E (e.trans (headTailEquiv (L+r)).toEmbedding)
        (PairRouting.colors (e.trans (headTailEquiv (L+r)).toEmbedding) coins.1)
        (PairRouting.colors_compatible _ _) ω := by
  rw [modifiedCost,modifiedInputTree_node]
  change InputTree.lowCost (L+r+1) (L+r+1) _ e
    ((coinStepEquiv (L+r)).symm ((ω.1.2.1,ω.2.2.1),coins.2)) = _
  rw [InputTree.lowCost_node]
  unfold modifiedAssignmentCost
  dsimp only
  simp only [Bool.false_eq_true,↓reduceIte]
  rw [PairRouting.switchedEmbedding_eq_colored _ _ (PairRouting.colors_compatible _ _) _ rfl]
  congr 2


namespace PairRouting
variable {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α] [DecidableEq ι]

omit [Fintype α] [DecidableEq ι] in
lemma childEmbedding_surjective (x : ι ↪ Bool × α) (hx : Function.Surjective x)
    (c : ι → Bool) (hc : Compatible x c) (b : Bool) :
    Function.Surjective (childEmbedding x c hc b) := by
  intro y
  have hs : Function.Surjective (coloredEmbedding x c hc) :=
    (pairLayer (chosenCoin x c)).surjective.comp hx
  obtain ⟨i,hi⟩ := hs (b,y)
  rw [coloredEmbedding_apply] at hi
  exact ⟨⟨i,congrArg Prod.fst hi⟩,congrArg Prod.snd hi⟩

omit [DecidableEq ι] in
lemma uniformPerm_tuple_upper (e f : ι ↪ α) (he : Function.Surjective e) (p : Equiv.Perm α) :
    finiteMean (fun u : Equiv.Perm α => if ∀ i, (p*u⁻¹) (e i) = f i then (1:ℝ) else 0) ≤
      1/(Fintype.card (Equiv.Perm α):ℝ) := by
  classical
  let M : Equiv.Perm α → Prop := fun u => ∀ i, (p*u⁻¹) (e i) = f i
  have huniq (u v : Equiv.Perm α) (hu : M u) (hv : M v) : u = v := by
    have hh : p*u⁻¹ = p*v⁻¹ := by
      ext x
      obtain ⟨i,rfl⟩ := he x
      exact (hu i).trans (hv i).symm
    exact inv_injective (mul_left_cancel hh)
  unfold finiteMean
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  change (∑ u, if M u then (1:ℝ) else 0) ≤ 1
  by_cases h : ∃ u, M u
  · obtain ⟨u,hu⟩ := h
    rw [Finset.sum_eq_single u]
    · simp only [hu,↓reduceIte,le_refl]
    · intro v _ hv
      exact ite_eq_right (fun hh => hv (huniq v u hh hu))
    · simp
  · push Not at h
    simp only [h,ite_false,Finset.sum_const_zero,zero_le_one]

end PairRouting

lemma centralFactor_nonneg (L r : ℕ) (E : Finset (Card r)) (a : ℝ) :
    0 ≤ centralFactor L r E a := Real.rpow_nonneg (Nat.cast_nonneg _) _

lemma centralFactor_step (L r : ℕ) (E : Finset (Card (r+1))) (a : ℝ) :
    centralFactor L (r+1) E a =
      centralFactor L r (exceptionChild E false) a * centralFactor L r (exceptionChild E true) a := by
  unfold centralFactor
  rw [←Real.rpow_add (Nat.cast_pos.mpr (Nat.factorial_pos _))]
  congr 1
  have he : ((exceptionChild E false).card:ℝ)+(exceptionChild E true).card = E.card := by
    exact_mod_cast exceptionChild_card_add E
  rw [pow_succ,←he]
  ring

lemma modifiedPerm_zero (L : ℕ) (E : Finset (Card 0)) (ω : ModifiedCoins L 0) :
    modifiedPerm L 0 E ω =
      if (fun j => Fin.elim0 j : Card 0) ∈ E then 1
      else butterflyPerm L (decodeButterfly L ω.2.1)*(ω.1 (fun j => Fin.elim0 j))⁻¹ := by
  unfold modifiedPerm modifiedInputTree boundaryTree InputTree.perm modifiedBoundary boundaryOutput
  split_ifs
  · exact mul_inv_cancel _
  · rfl

lemma modifiedCost_zero (L : ℕ) (E : Finset (Card 0)) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card L) (ω : ModifiedCoins L 0) : modifiedCost L 0 E e ω = 0 := by
  simp only [modifiedCost,modifiedInputTree,boundaryTree,InputTree.lowCost,
    InputTree.levelCost,Finset.sum_const_zero]

lemma centralFactor_zero (L : ℕ) (E : Finset (Card 0)) (a : ℝ) :
    centralFactor L 0 E a =
      if (fun j => Fin.elim0 j : Card 0) ∈ E then 1 else (Nat.factorial (2^L):ℝ)^(-a) := by
  classical
  let z : Card 0 := fun j => Fin.elim0 j
  have he : (E.card:ℝ) = if z ∈ E then 1 else 0 := by
    by_cases hz : z ∈ E
    · have he : E = {z} := by
        ext u
        rw [Subsingleton.elim u z]
        simp only [hz,Finset.mem_singleton]
      rw [he,ite_eq_left (by simpa only [he] using hz),Finset.card_singleton,Nat.cast_one]
    · have he : E = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (fun u hu => hz (Subsingleton.elim u z ▸ hu))
      rw [he,Finset.card_empty,Nat.cast_zero,ite_eq_right (by simp)]
  unfold centralFactor
  rw [pow_zero,he]
  split_ifs <;> simp

lemma modified_probability_zero_le (L : ℕ) (E : Finset (Card 0))
    {ι : Type*} [Fintype ι] (e f : ι ↪ Card L) (he : Function.Surjective e) :
    PairRouting.tupleProbability (modifiedPerm L 0 E) e f ≤
      if (fun j => Fin.elim0 j : Card 0) ∈ E then 1 else 1/(Nat.factorial (2^L):ℝ) := by
  classical
  rw [PairRouting.tupleProbability,finiteMean_prod,finiteMean_comm]
  let B : ℝ := if (fun j => Fin.elim0 j : Card 0) ∈ E then 1 else 1/(Nat.factorial (2^L):ℝ)
  change _ ≤ B
  calc
    _ ≤ finiteMean (fun _ω : BenesCoins L => B) := by
      apply finiteMean_mono
      intro ω
      simp only [modifiedPerm_zero]
      by_cases h : (fun j => Fin.elim0 j : Card 0) ∈ E
      · simp only [h,↓reduceIte,Equiv.Perm.one_apply,finiteMean_const,B]
        split_ifs <;> norm_num
      · simp only [h,↓reduceIte,B]
        rw [finiteMean_pi_eval (A := fun _ : Card 0 => Equiv.Perm (Card L)) (fun j => Fin.elim0 j) (fun u : Equiv.Perm (Card L) =>
          if ∀ i, (butterflyPerm L (decodeButterfly L ω.1)*u⁻¹) (e i) = f i then (1:ℝ) else 0)]
        convert PairRouting.uniformPerm_tuple_upper e f he (butterflyPerm L (decodeButterfly L ω.1)) using 1
        all_goals try with_reducible_and_instances rfl
        rw [Fintype.card_perm,card_positions]
    _ = _ := finiteMean_const B

end Thorp

end ThorpNine.Adaptive

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Adaptive_ModifiedRoutingMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Adaptive

namespace Thorp

lemma modifiedRoutingMoment_nonneg (L r : ℕ) (E : Finset (Card r))
    {ι : Type*} [Fintype ι] (e f : ι ↪ Card (L+r)) (a : ℝ) :
    0 ≤ modifiedRoutingMoment L r E e f a := by
  classical
  exact finiteMean_nonneg (fun _ => by split_ifs <;> positivity)

lemma modifiedRoutingMoment_zero (L : ℕ) (E : Finset (Card 0))
    {ι : Type*} [Fintype ι] (e f : ι ↪ Card L) (a : ℝ) :
    modifiedRoutingMoment L 0 E e f a = PairRouting.tupleProbability (modifiedPerm L 0 E) e f := by
  simp only [modifiedRoutingMoment,modifiedCost_zero,Nat.cast_zero,zero_mul,Real.rpow_zero,
    PairRouting.tupleProbability]

lemma modified_pointwise_zero (L : ℕ) (E : Finset (Card 0))
    {ι : Type*} [Fintype ι] (e f : ι ↪ Card L) (he : Function.Surjective e) (a : ℝ) (ha : 0 ≤ a) :
    (PairRouting.tupleProbability (modifiedPerm L 0 E) e f)^(1+a) ≤
      centralFactor L 0 E a * modifiedRoutingMoment L 0 E e f a := by
  have hp := PairRouting.tupleProbability_nonneg (modifiedPerm L 0 E) e f
  rw [modifiedRoutingMoment_zero]
  have hbound := modified_probability_zero_le L E e f he
  have hpow := Real.rpow_le_rpow hp hbound ha
  have hfpos : (0:ℝ) < Nat.factorial (2^L) := Nat.cast_pos.mpr (Nat.factorial_pos _)
  have heq : (if (fun j => Fin.elim0 j : Card 0) ∈ E then (1:ℝ) else 1/(Nat.factorial (2^L):ℝ))^a =
      centralFactor L 0 E a := by
    rw [centralFactor_zero]
    split_ifs
    · exact Real.one_rpow _
    · rw [one_div,Real.inv_rpow (le_of_lt hfpos),Real.rpow_neg (le_of_lt hfpos)]
  rw [heq] at hpow
  rw [Real.rpow_add' hp (by linarith : (1+a:ℝ) ≠ 0),Real.rpow_one,mul_comm]
  exact mul_le_mul_of_nonneg_right hpow hp


lemma modified_matches_step (L r : ℕ) (E : Finset (Card (r+1))) {ι : Type*}
    (e f : ι ↪ Card (L+r+1)) (ω : ModifiedCoins L r × ModifiedCoins L r)
    (coins : (Card (L+r) → Bool) × (Card (L+r) → Bool)) :
    (∀ i, modifiedPerm L (r+1) E ((modifiedStepEquiv L r).symm (ω,coins)) (e i) = f i) ↔
    (∀ i, PairRouting.sandwich coins.1 coins.2 (fun b => modifiedPerm L r (exceptionChild E b) (if b then ω.2 else ω.1))
      ((e.trans (headTailEquiv (L+r)).toEmbedding) i) = ((f.trans (headTailEquiv (L+r)).toEmbedding) i)) := by
  apply forall_congr'
  intro i
  rw [←(headTailEquiv (L+r)).injective.eq_iff,modifiedPerm_coordinates]
  rfl

lemma modifiedRoutingMoment_step (L r : ℕ) (E : Finset (Card (r+1))) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e f : ι ↪ Card (L+r+1)) (a : ℝ) :
    let x := e.trans (headTailEquiv (L+r)).toEmbedding
    let y := f.trans (headTailEquiv (L+r)).toEmbedding
    modifiedRoutingMoment L (r+1) E e f a = PairRouting.outerWeight x y *
      ∑ c : {c // c ∈ PairRouting.compatibleSet x y},
        finiteMean (fun ω : ModifiedCoins L r × ModifiedCoins L r =>
          if PairRouting.ChildMatches (fun b => modifiedPerm L r (exceptionChild E b) (if b then ω.2 else ω.1)) x y c.val
          then (2:ℝ)^((modifiedAssignmentCost L r E x c.val
            ((PairRouting.mem_compatibleSet x y c.val).mp c.property).1 ω:ℝ)*a) else 0) := by
  classical
  intro x y
  let : Fintype (ModifiedCoins L r) := inferInstance
  rw [modifiedRoutingMoment,finiteMean_equiv (modifiedStepEquiv L r),finiteMean_prod]
  have he (ω : ModifiedCoins L r × ModifiedCoins L r) :
      finiteMean (fun coins : (Card (L+r) → Bool) × (Card (L+r) → Bool) =>
        if ∀ i, modifiedPerm L (r+1) E ((modifiedStepEquiv L r).symm (ω,coins)) (e i) = f i
        then (2:ℝ)^((modifiedCost L (r+1) E e ((modifiedStepEquiv L r).symm (ω,coins)):ℝ)*a) else 0) =
      PairRouting.outerWeight x y *
        ∑ c : {c // c ∈ PairRouting.compatibleSet x y},
          if PairRouting.ChildMatches (fun b => modifiedPerm L r (exceptionChild E b) (if b then ω.2 else ω.1)) x y c.val
          then (2:ℝ)^((modifiedAssignmentCost L r E x c.val
            ((PairRouting.mem_compatibleSet x y c.val).mp c.property).1 ω:ℝ)*a) else 0 := by
    let W : (ι → Bool) → ℝ := fun c =>
      if hc : PairRouting.Compatible x c then (2:ℝ)^((modifiedAssignmentCost L r E x c hc ω:ℝ)*a) else 0
    calc
      _ = finiteMean (fun coins : (Card (L+r) → Bool) × (Card (L+r) → Bool) =>
        if ∀ i, PairRouting.sandwich coins.1 coins.2 (fun b => modifiedPerm L r (exceptionChild E b) (if b then ω.2 else ω.1))
          (x i) = y i then W (PairRouting.colors x coins.1) else 0) := by
        apply finiteMean_congr
        intro coins
        simp only [modified_matches_step,modifiedCost_step]
        simp only [W,PairRouting.colors_compatible,↓reduceDIte]
        rfl
      _ = _ := by
        rw [PairRouting.sandwich_weighted_probability_subtype]
        congr 1
        apply Finset.sum_congr rfl
        intro c _
        simp only [W,((PairRouting.mem_compatibleSet x y c.val).mp c.property).1,↓reduceDIte]
  simp_rw [he]
  simp_rw [mul_comm (PairRouting.outerWeight x y)]
  rw [finiteMean_mul_const,finiteMean_sum,mul_comm]

lemma modified_child_moment_product (L r : ℕ) (E : Finset (Card (r+1))) {ι : Type*} [Fintype ι]
    (x y : ι ↪ Bool × Card (L+r)) (c : ι → Bool)
    (hcx : PairRouting.Compatible x c) (hcy : PairRouting.Compatible y c) (a : ℝ) :
    modifiedRoutingMoment L r (exceptionChild E false) (PairRouting.childEmbedding x c hcx false) (PairRouting.childEmbedding y c hcy false) a *
      modifiedRoutingMoment L r (exceptionChild E true) (PairRouting.childEmbedding x c hcx true) (PairRouting.childEmbedding y c hcy true) a =
    finiteMean (fun ω : ModifiedCoins L r × ModifiedCoins L r =>
      if PairRouting.ChildMatches (fun b => modifiedPerm L r (exceptionChild E b) (if b then ω.2 else ω.1)) x y c
      then (2:ℝ)^(((modifiedCost L r (exceptionChild E false) (PairRouting.childEmbedding x c hcx false) ω.1 : ℝ) +
        modifiedCost L r (exceptionChild E true) (PairRouting.childEmbedding x c hcx true) ω.2)*a) else 0) := by
  classical
  unfold modifiedRoutingMoment
  rw [←finiteMean_prod_mul]
  apply finiteMean_congr
  intro ω
  let M₀ := ∀ i : {i // c i = false}, modifiedPerm L r (exceptionChild E false) ω.1 (x i.val).2 = (y i.val).2
  let M₁ := ∀ i : {i // c i = true}, modifiedPerm L r (exceptionChild E true) ω.2 (x i.val).2 = (y i.val).2
  have hp : (fun b : Bool => modifiedPerm L r (exceptionChild E b) (if b then ω.2 else ω.1)) =
      (fun b => if b then modifiedPerm L r (exceptionChild E true) ω.2 else modifiedPerm L r (exceptionChild E false) ω.1) := by
    funext b
    cases b <;> rfl
  have hs : PairRouting.ChildMatches (fun b => modifiedPerm L r (exceptionChild E b) (if b then ω.2 else ω.1)) x y c ↔
      M₀ ∧ M₁ := by rw [hp]; exact PairRouting.childMatches_split _ _ _ _ _
  change (if M₀ then _ else 0) * (if M₁ then _ else 0) = _
  by_cases h₀ : M₀ <;> by_cases h₁ : M₁
  · simp only [hs,h₀,h₁,true_and,↓reduceIte]
    rw [←Real.rpow_add (by norm_num : (0:ℝ)<2)]
    congr 1
    ring
  · simp only [hs,h₀,h₁,and_false,↓reduceIte,mul_zero]
  · simp only [hs,h₀,h₁,false_and,↓reduceIte,zero_mul]
  · simp only [hs,h₀,h₁,false_and,↓reduceIte,mul_zero]

lemma modified_probability_step (L r : ℕ) (E : Finset (Card (r+1))) {ι : Type*} [Fintype ι]
    (e f : ι ↪ Card (L+r+1)) :
    PairRouting.tupleProbability (modifiedPerm L (r+1) E) e f =
    finiteMean (fun ω : ModifiedCoins L r × ModifiedCoins L r =>
      finiteMean (fun coins : (Card (L+r) → Bool) × (Card (L+r) → Bool) =>
        if ∀ i, PairRouting.sandwich coins.1 coins.2 (fun b => if b then modifiedPerm L r (exceptionChild E true) ω.2 else modifiedPerm L r (exceptionChild E false) ω.1)
          ((e.trans (headTailEquiv (L+r)).toEmbedding) i) = ((f.trans (headTailEquiv (L+r)).toEmbedding) i)
        then (1:ℝ) else 0)) := by
  classical
  let : Fintype (ModifiedCoins L r) := inferInstance
  rw [PairRouting.tupleProbability,finiteMean_equiv (modifiedStepEquiv L r),finiteMean_prod]
  have hp (b : Bool) (p q : ModifiedCoins L r) :
      modifiedPerm L r (exceptionChild E b) (if b then p else q) =
      (if b then modifiedPerm L r (exceptionChild E true) p else modifiedPerm L r (exceptionChild E false) q) := by
    cases b <;> rfl
  simp only [modified_matches_step,hp]


lemma modified_assignment_moment_bound (L r : ℕ) (E : Finset (Card (r+1))) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x y : ι ↪ Bool × Card (L+r)) (c : ι → Bool) (hc : c ∈ PairRouting.compatibleSet x y)
    (a : ℝ) (ha : 0 ≤ a) :
    let hcx := ((PairRouting.mem_compatibleSet x y c).mp hc).1
    PairRouting.outerWeight x y ^ a * ((PairRouting.compatibleSet x y).card:ℝ)^a *
      ((2:ℝ)^(-(r:ℝ)*Fintype.card ι*a) *
        finiteMean (fun ω : ModifiedCoins L r × ModifiedCoins L r =>
          if PairRouting.ChildMatches (fun b => modifiedPerm L r (exceptionChild E b) (if b then ω.2 else ω.1)) x y c
          then (2:ℝ)^(((modifiedCost L r (exceptionChild E false) (PairRouting.childEmbedding x c hcx false) ω.1 : ℝ) +
            modifiedCost L r (exceptionChild E true) (PairRouting.childEmbedding x c hcx true) ω.2)*a) else 0)) ≤
    (2:ℝ)^(-((r:ℝ)+1)*Fintype.card ι*a) *
      finiteMean (fun ω : ModifiedCoins L r × ModifiedCoins L r =>
        if PairRouting.ChildMatches (fun b => modifiedPerm L r (exceptionChild E b) (if b then ω.2 else ω.1)) x y c
        then (2:ℝ)^((modifiedAssignmentCost L r E x c hcx ω:ℝ)*a) else 0) := by
  classical
  intro hcx
  have hscale (q : ℝ) (F : ModifiedCoins L r × ModifiedCoins L r → ℝ) :
      q * finiteMean F = finiteMean (fun ω => q * F ω) := by
    simp_rw [mul_comm q,finiteMean_mul_const]
  rw [←mul_assoc,hscale,hscale]
  apply finiteMean_mono
  intro ω
  split_ifs with hm
  · have hh := PairRouting.assignment_factor_bound x y c hc
      (fun b => modifiedPerm L r (exceptionChild E b) (if b then ω.2 else ω.1)) hm a ha
    calc
      _ ≤ ((2:ℝ)^(((PairRouting.alternatingCycles (PairRouting.coloredEmbedding x c hcx)
          (fun b => modifiedPerm L r (exceptionChild E b) (if b then ω.2 else ω.1)):ℝ)-Fintype.card ι)*a) *
          (2:ℝ)^(-(r:ℝ)*Fintype.card ι*a)) *
          (2:ℝ)^(((modifiedCost L r (exceptionChild E false) (PairRouting.childEmbedding x c hcx false) ω.1 : ℝ) +
            modifiedCost L r (exceptionChild E true) (PairRouting.childEmbedding x c hcx true) ω.2)*a) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hh (by positivity)) (by positivity)
      _ = _ := by
        simp only [←Real.rpow_add (by norm_num : (0:ℝ)<2),modifiedAssignmentCost,Nat.cast_add]
        congr 1
        ring
  · simp only [mul_zero]
    exact le_rfl


lemma modified_child_power_product_bound (L r : ℕ) (E : Finset (Card (r+1)))
    {ι : Type*} [Fintype ι] (x y : ι ↪ Bool × Card (L+r)) (c : ι → Bool)
    (hcx : PairRouting.Compatible x c) (hcy : PairRouting.Compatible y c) (a : ℝ)
    (hfalse : (PairRouting.tupleProbability (modifiedPerm L r (exceptionChild E false))
        (PairRouting.childEmbedding x c hcx false) (PairRouting.childEmbedding y c hcy false))^(1+a) ≤
      ((2:ℝ)^(-(r:ℝ)*Fintype.card {i // c i = false}*a)*centralFactor L r (exceptionChild E false) a) *
        modifiedRoutingMoment L r (exceptionChild E false)
          (PairRouting.childEmbedding x c hcx false) (PairRouting.childEmbedding y c hcy false) a)
    (htrue : (PairRouting.tupleProbability (modifiedPerm L r (exceptionChild E true))
        (PairRouting.childEmbedding x c hcx true) (PairRouting.childEmbedding y c hcy true))^(1+a) ≤
      ((2:ℝ)^(-(r:ℝ)*Fintype.card {i // c i = true}*a)*centralFactor L r (exceptionChild E true) a) *
        modifiedRoutingMoment L r (exceptionChild E true)
          (PairRouting.childEmbedding x c hcx true) (PairRouting.childEmbedding y c hcy true) a) :
    (PairRouting.tupleProbability (modifiedPerm L r (exceptionChild E false))
      (PairRouting.childEmbedding x c hcx false) (PairRouting.childEmbedding y c hcy false))^(1+a) *
      (PairRouting.tupleProbability (modifiedPerm L r (exceptionChild E true))
        (PairRouting.childEmbedding x c hcx true) (PairRouting.childEmbedding y c hcy true))^(1+a) ≤
    ((2:ℝ)^(-(r:ℝ)*Fintype.card ι*a)*centralFactor L (r+1) E a) *
      finiteMean (fun ω : ModifiedCoins L r × ModifiedCoins L r =>
        if PairRouting.ChildMatches (fun b => modifiedPerm L r (exceptionChild E b) (if b then ω.2 else ω.1)) x y c
        then (2:ℝ)^(((modifiedCost L r (exceptionChild E false) (PairRouting.childEmbedding x c hcx false) ω.1 : ℝ) +
          modifiedCost L r (exceptionChild E true) (PairRouting.childEmbedding x c hcx true) ω.2)*a) else 0) := by
  have hh := mul_le_mul hfalse htrue
    (Real.rpow_nonneg (PairRouting.tupleProbability_nonneg _ _ _) _)
    (mul_nonneg (mul_nonneg (by positivity) (centralFactor_nonneg _ _ _ _))
      (modifiedRoutingMoment_nonneg _ _ _ _ _ _))
  have he : -(r:ℝ)*Fintype.card {i // c i = false}*a + -(r:ℝ)*Fintype.card {i // c i = true}*a =
      -(r:ℝ)*Fintype.card ι*a := by
    rw [←add_mul,←mul_add,←Nat.cast_add,PairRouting.color_card_add]
  calc
    _ ≤ _ := hh
    _ = ((2:ℝ)^(-(r:ℝ)*Fintype.card {i // c i = false}*a)*
        (2:ℝ)^(-(r:ℝ)*Fintype.card {i // c i = true}*a)) *
      (centralFactor L r (exceptionChild E false) a * centralFactor L r (exceptionChild E true) a) *
      (modifiedRoutingMoment L r (exceptionChild E false)
        (PairRouting.childEmbedding x c hcx false) (PairRouting.childEmbedding y c hcy false) a *
      modifiedRoutingMoment L r (exceptionChild E true)
        (PairRouting.childEmbedding x c hcx true) (PairRouting.childEmbedding y c hcy true) a) := by ring
    _ = _ := by rw [←Real.rpow_add (by norm_num : (0:ℝ)<2),he,←centralFactor_step,modified_child_moment_product]


theorem modified_pointwise_moment (L r : ℕ) (E : Finset (Card r)) {ι : Type*} [Fintype ι]
    (e f : ι ↪ Card (L+r)) (he : Function.Surjective e) (a : ℝ) (ha : 0 ≤ a) :
    (PairRouting.tupleProbability (modifiedPerm L r E) e f)^(1+a) ≤
      ((2:ℝ)^(-(r:ℝ)*Fintype.card ι*a)*centralFactor L r E a) * modifiedRoutingMoment L r E e f a := by
  classical
  induction r generalizing ι with
  | zero =>
      simpa only [Nat.cast_zero,neg_zero,zero_mul,Real.rpow_zero,one_mul] using
        modified_pointwise_zero L E e f he a ha
  | succ r ih =>
      let x := e.trans (headTailEquiv (L+r)).toEmbedding
      let y := f.trans (headTailEquiv (L+r)).toEmbedding
      let W := PairRouting.outerWeight x y
      let C := PairRouting.compatibleSet x y
      let p : (ι → Bool) → ℝ := fun c =>
        (PairRouting.tupleProbability (modifiedPerm L r (exceptionChild E false))
          (fun i : {i // c i = false} => (x i.val).2)
          (fun i : {i // c i = false} => (y i.val).2))^(1+a) *
        (PairRouting.tupleProbability (modifiedPerm L r (exceptionChild E true))
          (fun i : {i // c i = true} => (x i.val).2)
          (fun i : {i // c i = true} => (y i.val).2))^(1+a)
      let m : {c // c ∈ C} → ℝ := fun c =>
        finiteMean (fun ω : ModifiedCoins L r × ModifiedCoins L r =>
          if PairRouting.ChildMatches (fun b => modifiedPerm L r (exceptionChild E b) (if b then ω.2 else ω.1)) x y c.val
          then (2:ℝ)^((modifiedAssignmentCost L r E x c.val
            ((PairRouting.mem_compatibleSet x y c.val).mp c.property).1 ω:ℝ)*a) else 0)
      have hp (c : {c // c ∈ C}) : W^a * (C.card:ℝ)^a * p c.val ≤
          ((2:ℝ)^(-((r:ℝ)+1)*Fintype.card ι*a)*centralFactor L (r+1) E a) * m c := by
        obtain ⟨hcx,hcy⟩ := (PairRouting.mem_compatibleSet x y c.val).mp c.property
        have h₀ := ih (exceptionChild E false) (PairRouting.childEmbedding x c.val hcx false)
          (PairRouting.childEmbedding y c.val hcy false)
          (PairRouting.childEmbedding_surjective x ((headTailEquiv (L+r)).surjective.comp he) c.val hcx false)
        have h₁ := ih (exceptionChild E true) (PairRouting.childEmbedding x c.val hcx true)
          (PairRouting.childEmbedding y c.val hcy true)
          (PairRouting.childEmbedding_surjective x ((headTailEquiv (L+r)).surjective.comp he) c.val hcx true)
        have hh := modified_child_power_product_bound L r E x y c.val hcx hcy a h₀ h₁
        have hh' := mul_le_mul_of_nonneg_left hh
          (mul_nonneg (Real.rpow_nonneg (le_of_lt (PairRouting.outerWeight_pos x y)) a)
            (Real.rpow_nonneg (Nat.cast_nonneg C.card) a))
        apply hh'.trans
        have hm := modified_assignment_moment_bound L r E x y c.val c.property a ha
        convert mul_le_mul_of_nonneg_left hm (centralFactor_nonneg L (r+1) E a) using 1 <;> ring
      have hnode := PairRouting.sandwich_power_bound (modifiedPerm L r (exceptionChild E false)) (modifiedPerm L r (exceptionChild E true)) x y a ha
      rw [←modified_probability_step L r E e f] at hnode
      change (PairRouting.tupleProbability (modifiedPerm L (r+1) E) e f)^(1+a) ≤
        W^(1+a) * (C.card:ℝ)^a * ∑ c ∈ C, p c at hnode
      have hsum : ∑ c ∈ C, p c = ∑ c : {c // c ∈ C}, p c.val := by
        rw [Finset.sum_subtype C (fun _ => Iff.rfl)]
      have hW : 0 < W := PairRouting.outerWeight_pos x y
      calc
        _ ≤ W^(1+a) * (C.card:ℝ)^a * ∑ c ∈ C, p c := hnode
        _ = W * ∑ c : {c // c ∈ C}, W^a * (C.card:ℝ)^a * p c.val := by
          rw [Real.rpow_add hW,Real.rpow_one,hsum,←Finset.mul_sum]
          ring
        _ ≤ W * ∑ c : {c // c ∈ C}, ((2:ℝ)^(-((r:ℝ)+1)*Fintype.card ι*a)*centralFactor L (r+1) E a) * m c :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun c _ => hp c)) (le_of_lt hW)
        _ = _ := by
          rw [←Finset.mul_sum,modifiedRoutingMoment_step]
          simp only [Nat.cast_add,Nat.cast_one]
          change W * (((2:ℝ)^(-((r:ℝ)+1)*Fintype.card ι*a)*centralFactor L (r+1) E a) * ∑ c, m c) =
            ((2:ℝ)^(-((r:ℝ)+1)*Fintype.card ι*a)*centralFactor L (r+1) E a) * (W * ∑ c, m c)
          ring


lemma modifiedRoutingMoment_sum (L r : ℕ) (E : Finset (Card r)) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card (L+r)) (a : ℝ) :
    (∑ f : ι ↪ Card (L+r), modifiedRoutingMoment L r E e f a) =
      finiteMean (fun ω : ModifiedCoins L r => (2:ℝ)^((modifiedCost L r E e ω:ℝ)*a)) := by
  classical
  unfold modifiedRoutingMoment
  rw [←finiteMean_sum]
  apply finiteMean_congr
  intro ω
  let f₀ : ι ↪ Card (L+r) := e.trans (modifiedPerm L r E ω).toEmbedding
  rw [Finset.sum_eq_single f₀]
  · have hm : ∀ i, modifiedPerm L r E ω (e i) = f₀ i := fun _ => rfl
    simp only [hm,implies_true,↓reduceIte]
  · intro f _ hf
    have hm : ¬ ∀ i, modifiedPerm L r E ω (e i) = f i := by
      intro hh
      apply hf
      ext i : 1
      exact (hh i).symm
    exact ite_eq_right hm
  · simp

lemma full_tuple_card (d : ℕ) {ι : Type*} [Fintype ι] (e : ι ↪ Card d)
    (he : Function.Surjective e) : Fintype.card ι = 2^d := by
  rw [←card_positions d]
  exact Fintype.card_congr (Equiv.ofBijective e ⟨e.injective,he⟩)

lemma exception_card_le (r : ℕ) (E : Finset (Card r)) : E.card ≤ 2^r := by
  simpa only [card_positions] using E.card_le_univ

lemma modifiedNormalization_pos (L r : ℕ) (E : Finset (Card r)) :
    0 < modifiedNormalization L r E := by unfold modifiedNormalization; positivity

lemma modified_normalization_identity (L r : ℕ) (E : Finset (Card r)) (a : ℝ) :
    (Nat.factorial (2^(L+r)):ℝ)^a *
      ((2:ℝ)^(-(r:ℝ)*(2^(L+r):ℕ)*a)*centralFactor L r E a) =
    modifiedNormalization L r E ^ a := by
  rw [←mul_assoc,density_normalization,centralFactor,modifiedNormalization,
    Real.div_rpow (by positivity) (by positivity),Real.div_rpow (by positivity) (by positivity),
    Real.mul_rpow (by positivity) (by positivity)]
  have hc : ((2^r-E.card:ℕ):ℝ) = (2:ℝ)^r-E.card := by
    rw [Nat.cast_sub (exception_card_le r E),Nat.cast_pow,Nat.cast_ofNat]
  rw [←Real.rpow_natCast (Nat.factorial (2^L):ℝ),←Real.rpow_mul (by positivity),hc,
    show -((2:ℝ)^r-E.card)*a = -(((2:ℝ)^r-E.card)*a) by ring,
    Real.rpow_neg (by positivity)]
  ring

theorem modified_row_density_moment (L r : ℕ) (E : Finset (Card r)) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card (L+r)) (he : Function.Surjective e) (a : ℝ) (ha : 0 ≤ a) :
    modifiedRowMoment L r E e a ≤ modifiedNormalization L r E ^ a *
      finiteMean (fun ω : ModifiedCoins L r => (2:ℝ)^((modifiedCost L r E e ω:ℝ)*a)) := by
  classical
  have : Nonempty (ι ↪ Card (L+r)) := ⟨e⟩
  rw [modifiedRowMoment,finite_row_power _ (fun f => PairRouting.tupleProbability_nonneg _ _ _)]
  calc
    _ ≤ (Fintype.card (ι ↪ Card (L+r)):ℝ)^a *
      ∑ f : ι ↪ Card (L+r), ((2:ℝ)^(-(r:ℝ)*Fintype.card ι*a)*centralFactor L r E a) *
        modifiedRoutingMoment L r E e f a :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun f _ => modified_pointwise_moment L r E e f he a ha))
        (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    _ = _ := by
      rw [←Finset.mul_sum,modifiedRoutingMoment_sum,←mul_assoc,Fintype.card_embedding_eq,
        card_positions,full_tuple_card (L+r) e he,Nat.descFactorial_self,modified_normalization_identity]

lemma modified_total_cost_mgf (L r : ℕ) (hL : 0 < L) (E : Finset (Card r))
    {ι : Type*} [Fintype ι] (e : ι ↪ Card (L+r)) :
    finiteMean (fun ω : ModifiedCoins L r => momentBase^(modifiedCost L r E e ω)) ≤
      Real.exp (Fintype.card ι*heightDecay L +
        3*((L*E.card*2^L:ℕ):ℝ)*Real.log momentBase) := by
  let B := Real.exp (Fintype.card ι*heightDecay L +
    3*((L*E.card*2^L:ℕ):ℝ)*Real.log momentBase)
  rw [finiteMean_prod]
  apply le_trans (finiteMean_mono (fun U => ?_)) (finiteMean_const B).le
  rw [finiteMean_prod,finiteMean_comm]
  apply le_trans (finiteMean_mono (fun X => ?_)) (finiteMean_const B).le
  exact modified_cost_mgf L r hL E U X e momentBase momentBase_one_le (momentBase_log.trans (by norm_num))

lemma modifiedRowMoment_bound (L r : ℕ) (hL : 0 < L) (E : Finset (Card r))
    {ι : Type*} [Fintype ι] (e : ι ↪ Card (L+r)) (he : Function.Surjective e) :
    modifiedRowMoment L r E e (1/1000) ≤
      modifiedNormalization L r E ^ (1/1000:ℝ) *
        Real.exp ((2^(L+r):ℕ)*heightDecay L +
          3*((L*E.card*2^L:ℕ):ℝ)*Real.log momentBase) := by
  have hm := modified_row_density_moment L r E e he (1/1000) (by norm_num)
  simp_rw [←momentBase_pow] at hm
  apply hm.trans
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (modifiedNormalization_pos L r E).le _)
  simpa only [full_tuple_card (L+r) e he] using modified_total_cost_mgf L r hL E e


lemma log_factorial_upper {n : ℕ} (hn : 1 ≤ n) :
    Real.log (Nat.factorial n) ≤ (n:ℝ)*Real.log n-n+Real.log n+1 := by
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases hz : n = 0
      · subst n; norm_num
      have hn0 : (0:ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hz)
      have hn1 : (0:ℝ) < n+1 := by positivity
      have h := Real.one_sub_inv_le_log_of_pos (div_pos hn1 hn0)
      rw [Real.log_div (ne_of_gt hn1) (ne_of_gt hn0),inv_div] at h
      have hh := mul_le_mul_of_nonneg_left h hn1.le
      have hcancel : ((n:ℝ)+1)*(1-(n:ℝ)/(n+1)) = 1 := by field_simp; ring
      rw [hcancel] at hh
      have hi := ih (by omega)
      rw [Nat.factorial_succ,Nat.cast_mul,Real.log_mul (by positivity) (by positivity),Nat.cast_add,Nat.cast_one]
      nlinarith

lemma log_modifiedNormalization (L r : ℕ) (E : Finset (Card r)) :
    Real.log (modifiedNormalization L r E) =
      Real.log (Nat.factorial (2^(L+r))) -
        ((2^(L+r):ℕ)*((r:ℝ)*Real.log 2)+((2:ℝ)^r-E.card)*Real.log (Nat.factorial (2^L))) := by
  unfold modifiedNormalization
  rw [Real.log_div (by positivity) (by positivity),Real.log_mul (by positivity) (by positivity),
    Real.log_pow,Real.log_pow,Real.log_pow,
    Nat.cast_sub (exception_card_le r E),Nat.cast_pow,Nat.cast_ofNat]
  simp only [Nat.cast_pow,Nat.cast_ofNat]

lemma log_modifiedNormalization_le (L r : ℕ) (E : Finset (Card r)) :
    Real.log (modifiedNormalization L r E) ≤
      ((L+r:ℕ):ℝ)*Real.log 2+1+E.card*Real.log (Nat.factorial (2^L)) := by
  have hN : 1 ≤ 2^(L+r) := one_le_pow₀ (by norm_num)
  have hS : 1 ≤ 2^L := one_le_pow₀ (by norm_num)
  have hu := log_factorial_upper hN
  have hl := mul_le_mul_of_nonneg_left (log_factorial_lower hS) (by positivity : (0:ℝ) ≤ (2:ℝ)^r)
  simp only [Nat.cast_pow,Nat.cast_ofNat,Real.log_pow,Nat.cast_add] at hu hl ⊢
  rw [log_modifiedNormalization]
  simp only [pow_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] at hu hl ⊢
  nlinarith

lemma modified_moment_exponential (L r : ℕ) (hL : 0 < L) (E : Finset (Card r))
    {ι : Type*} [Fintype ι] (e : ι ↪ Card (L+r)) (he : Function.Surjective e) :
    modifiedRowMoment L r E e (1/1000) ≤
      Real.exp (((L+r:ℕ)*Real.log 2+1+E.card*Real.log (Nat.factorial (2^L)))/1000 +
        (2^(L+r):ℕ)*heightDecay L+3*((L*E.card*2^L:ℕ):ℝ)*Real.log momentBase) := by
  apply (modifiedRowMoment_bound L r hL E e he).trans
  rw [Real.rpow_def_of_pos (modifiedNormalization_pos L r E),←Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h := log_modifiedNormalization_le L r E
  linarith

lemma log_power_factorial_le (L : ℕ) :
    Real.log (Nat.factorial (2^L)) ≤ (2:ℝ)^L*L := by
  have hf : (Nat.factorial (2^L):ℝ) ≤ ((2^L:ℕ):ℝ)^(2^L) := by
    exact_mod_cast Nat.factorial_le_pow (2^L)
  have hh := Real.log_le_log (by positivity) hf
  rw [Real.log_pow,Nat.cast_pow,Nat.cast_ofNat,Real.log_pow] at hh
  apply hh.trans
  have hl := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
  have hn : 0 ≤ (2:ℝ)^L*(L:ℝ) := by positivity
  nlinarith

lemma modified_moment_exception_bound (L r : ℕ) (hL : 0 < L) (E : Finset (Card r))
    {ι : Type*} [Fintype ι] (e : ι ↪ Card (L+r)) (he : Function.Surjective e)
    (ε : ℝ) (hE : (E.card:ℝ) ≤ ε*(2:ℝ)^r) :
    modifiedRowMoment L r E e (1/1000) ≤
      Real.exp (((L+r:ℕ)*Real.log 2+1)/1000 +
        (2:ℝ)^(L+r)*(heightDecay L+ε*L/250)) := by
  apply (modified_moment_exponential L r hL E e he).trans
  apply Real.exp_le_exp.mpr
  have hs := mul_le_mul_of_nonneg_left (log_power_factorial_le L) (Nat.cast_nonneg E.card)
  have hb := mul_le_mul_of_nonneg_left momentBase_log
    (by positivity : (0:ℝ) ≤ 3*((L*E.card*2^L:ℕ):ℝ))
  have hexc := mul_le_mul_of_nonneg_left hE (by positivity : (0:ℝ) ≤ (2:ℝ)^L*L/250)
  simp only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,pow_add] at hs hb hexc ⊢
  nlinarith


lemma heightDecay_tendsto : Filter.Tendsto heightDecay Filter.atTop (nhds 0) := by
  have h : Filter.Tendsto (fun L : ℕ => (-(1:ℝ)/64)*(L:ℝ)) Filter.atTop Filter.atBot :=
    (Filter.tendsto_const_mul_atBot_of_neg (by norm_num : -(1:ℝ)/64 < 0)).mpr
      tendsto_natCast_atTop_atTop
  have ht := ((Real.tendsto_exp_atBot.comp h).const_mul 68).div_const (1-Real.exp (-(1:ℝ)/64))
  convert ht using 1
  · funext L
    unfold heightDecay
    dsimp only [Function.comp_apply]
    rw [show -(L:ℝ)/64 = (-(1:ℝ)/64)*(L:ℝ) by ring]
  · simp

lemma modifiedOverhead_tendsto (L : ℕ) :
    Filter.Tendsto (modifiedOverhead L) Filter.atTop (nhds 0) := by
  have h₁ := tendsto_pow_const_div_const_pow_of_one_lt 1 (by norm_num : (1:ℝ)<2)
  have h₀ := tendsto_pow_const_div_const_pow_of_one_lt 0 (by norm_num : (1:ℝ)<2)
  simp only [pow_one] at h₁
  simp only [pow_zero] at h₀
  have ht := ((h₁.const_mul (Real.log 2)).add (h₀.const_mul ((L:ℝ)*Real.log 2+1))).div_const
    ((2:ℝ)^L*1000)
  convert ht using 1
  · funext r
    simp only [modifiedOverhead,Nat.cast_add,pow_add]
    field_simp
    ring
  · simp

theorem modified_arbitrarily_small_rate (η : ℝ) (hη : 0 < η) :
    ∃ L : ℕ, 0 < L ∧ ∃ ε : ℝ, 0 < ε ∧ ε < 1/2 ∧
      ∀ᶠ r : ℕ in Filter.atTop, ∀ (E : Finset (Card r)), (E.card:ℝ) ≤ ε*(2:ℝ)^r →
        ∀ (e : Card (L+r) ↪ Card (L+r)),
          modifiedRowMoment L r E e (1/1000) ≤ Real.exp (η*(2:ℝ)^(L+r)) := by
  have hsmall : ∀ᶠ L : ℕ in Filter.atTop, heightDecay L < η/3 :=
    heightDecay_tendsto.eventually (gt_mem_nhds (by linarith : (0:ℝ)<η/3))
  obtain ⟨L,hdec,hL⟩ := (hsmall.and (Filter.eventually_ge_atTop 1)).exists
  have hL0 : (0:ℝ) < L := Nat.cast_pos.mpr hL
  let ε : ℝ := min (1/4) (η*250/(3*L))
  have hε : 0 < ε := lt_min (by norm_num) (by positivity)
  have hε1 : ε < 1/2 := (min_le_left _ _).trans_lt (by norm_num)
  have hεL : ε*L/250 ≤ η/3 := by
    have h := min_le_right (1/4:ℝ) (η*250/(3*L))
    change ε ≤ η*250/(3*L) at h
    have hh := mul_le_mul_of_nonneg_right h hL0.le
    have he : (η*250/(3*(L:ℝ)))*(L:ℝ)/250 = η/3 := by field_simp
    exact (div_le_div_of_nonneg_right hh (by norm_num)).trans he.le
  refine ⟨L,hL,ε,hε,hε1,?_⟩
  have hr : ∀ᶠ r : ℕ in Filter.atTop, modifiedOverhead L r < η/3 :=
    (modifiedOverhead_tendsto L).eventually (gt_mem_nhds (by linarith : (0:ℝ)<η/3))
  filter_upwards [hr] with r hr
  intro E hE e
  have he := Finite.surjective_of_injective e.injective
  apply (modified_moment_exception_bound L r hL E e he ε hE).trans
  apply Real.exp_le_exp.mpr
  have hn : (0:ℝ) < (2:ℝ)^(L+r) := by positivity
  have hd : modifiedOverhead L r * (2:ℝ)^(L+r) =
      (((L+r:ℕ):ℝ)*Real.log 2+1)/1000 := by
    unfold modifiedOverhead
    field_simp
  have hh := mul_le_mul_of_nonneg_right hr.le hn.le
  rw [hd] at hh
  have ht := mul_le_mul_of_nonneg_left (show heightDecay L+ε*L/250 ≤ 2*η/3 by linarith) hn.le
  linarith


namespace DensityTransfer
open scoped BigOperators

lemma applyKernel_apply {X : Type*} [Fintype X] (P : X → X → ℝ)
    (v : EuclideanSpace ℂ X) (x : X) :
    applyKernel P v x = ∑ y, (P x y : ℂ)*v y := rfl

lemma applyKernel_add {X : Type*} [Fintype X] (P Q : X → X → ℝ)
    (v : EuclideanSpace ℂ X) :
    applyKernel (fun x y => P x y+Q x y) v = applyKernel P v+applyKernel Q v := by
  ext x
  simp only [applyKernel_apply,Complex.ofReal_add,add_mul,Finset.sum_add_distrib]
  rfl

lemma kernel_component_sq {X : Type*} [Fintype X] (P : X → X → ℝ)
    (hP : ∀ x y, 0 ≤ P x y) (v : EuclideanSpace ℂ X) (x : X) :
    ‖applyKernel P v x‖^2 ≤ (∑ y, P x y) * ∑ y, P x y*‖v y‖^2 := by
  have hs : ‖applyKernel P v x‖ ≤ ∑ y, P x y*‖v y‖ := by
    rw [applyKernel_apply]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro y _
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hP x y)]
  apply (pow_le_pow_left₀ (norm_nonneg _) hs 2).trans
  exact Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (fun y _ => hP x y) (fun y _ => mul_nonneg (hP x y) (sq_nonneg _))
    (fun y _ => by ring_nf; exact le_rfl)

lemma schur_bound {X : Type*} [Fintype X] (P : X → X → ℝ)
    (hP : ∀ x y, 0 ≤ P x y) (δ : ℝ) (hδ : 0 ≤ δ)
    (hrow : ∀ x, ∑ y, P x y ≤ δ) (hcol : ∀ y, ∑ x, P x y ≤ δ)
    (v : EuclideanSpace ℂ X) : ‖applyKernel P v‖ ≤ δ*‖v‖ := by
  have hsq : ‖applyKernel P v‖^2 ≤ δ^2*‖v‖^2 := by
    rw [EuclideanSpace.norm_sq_eq,EuclideanSpace.norm_sq_eq]
    calc
      _ ≤ ∑ x, δ * ∑ y, P x y*‖v y‖^2 := by
        apply Finset.sum_le_sum
        intro x _
        apply (kernel_component_sq P hP v x).trans
        exact mul_le_mul_of_nonneg_right (hrow x)
          (Finset.sum_nonneg (fun y _ => mul_nonneg (hP x y) (sq_nonneg _)))
      _ = δ * ∑ y, (∑ x, P x y)*‖v y‖^2 := by
        rw [←Finset.mul_sum,Finset.sum_comm]
        congr 1
        apply Finset.sum_congr rfl
        intro y _
        exact (Finset.sum_mul Finset.univ _ _).symm
      _ ≤ δ * ∑ y, δ*‖v y‖^2 := by
        apply mul_le_mul_of_nonneg_left _ hδ
        exact Finset.sum_le_sum (fun y _ => mul_le_mul_of_nonneg_right (hcol y) (sq_nonneg _))
      _ = _ := by rw [←Finset.mul_sum]; ring
  have hn := norm_nonneg (applyKernel P v)
  have hr := mul_nonneg hδ (norm_nonneg v)
  nlinarith

lemma hilbert_schmidt_family {X I : Type*} [Fintype X] [Fintype I]
    (P : X → X → ℝ) (v : I → EuclideanSpace ℂ X) (hv : Orthonormal ℂ v) :
    (∑ i, ‖applyKernel P (v i)‖^2) ≤ ∑ x, ∑ y, (P x y)^2 := by
  simp_rw [EuclideanSpace.norm_sq_eq]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro x _
  let w : EuclideanSpace ℂ X := WithLp.toLp 2 (fun y => (P x y : ℂ))
  have he (i : I) : ‖applyKernel P (v i) x‖ = ‖inner ℂ (v i) w‖ := by
    rw [norm_inner_symm]
    congr 1
    simp only [applyKernel_apply,PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro y _
    simp [w,RCLike.inner_apply,mul_comm]
  simp_rw [he]
  have h := hv.sum_inner_products_le (s := Finset.univ) w
  apply h.trans_eq
  rw [EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro y _
  simp [w,Complex.norm_real,Real.norm_eq_abs,sq_abs]


lemma tail_density_pointwise (t a z : ℝ) (ht : 0 ≤ t) (ha : 0 ≤ a) (hz : 0 < z) :
    (if z < t then t else 0) ≤ t^(1+a)*z^(-a) := by
  split_ifs with h
  · rw [Real.rpow_neg hz.le,←div_eq_mul_inv]
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hz a)).mpr
    rw [Real.rpow_add (lt_trans hz h),Real.rpow_one]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hz.le h.le ha) ht
  · positivity

lemma tail_density_mean {X : Type*} [Fintype X] (f : X → ℝ) (hf : ∀ x, 0 ≤ f x)
    (a z : ℝ) (ha : 0 ≤ a) (hz : 0 < z) :
    finiteMean (fun x => if z < f x then f x else 0) ≤ finiteMean (fun x => f x^(1+a))*z^(-a) := by
  rw [←finiteMean_mul_const]
  exact finiteMean_mono (fun x => tail_density_pointwise (f x) a z (hf x) ha hz)

lemma tail_add_head {X : Type*} [Fintype X] (P : X → X → ℝ) (z : ℝ) :
    (fun x y => tailKernel P z x y+headKernel P z x y) = P := by
  funext x y
  unfold tailKernel headKernel
  split_ifs <;> simp

lemma tailKernel_nonneg {X : Type*} [Fintype X] (P : X → X → ℝ) (z : ℝ)
    (hP : ∀ x y, 0 ≤ P x y) (x y : X) : 0 ≤ tailKernel P z x y := by
  unfold tailKernel
  split_ifs <;> simp only [hP,le_refl]

lemma tailKernel_row {X : Type*} [Fintype X] [Nonempty X] (P : X → X → ℝ)
    (hP : ∀ x y, 0 ≤ P x y) (a z M : ℝ) (ha : 0 ≤ a) (hz : 0 < z)
    (hM : ∀ x, finiteMean (fun y => ((Fintype.card X:ℝ)*P x y)^(1+a)) ≤ M) (x : X) :
    ∑ y, tailKernel P z x y ≤ M*z^(-a) := by
  have hn : (Fintype.card X:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have he : finiteMean (fun y => if z < (Fintype.card X:ℝ)*P x y then
      (Fintype.card X:ℝ)*P x y else 0) = ∑ y, tailKernel P z x y := by
    unfold finiteMean
    calc
      _ = (∑ y, (Fintype.card X:ℝ)*tailKernel P z x y)/(Fintype.card X:ℝ) := by
        congr 1
        apply Finset.sum_congr rfl
        intro y _
        by_cases hy : z < (Fintype.card X:ℝ)*P x y
        · simp only [tailKernel,hy,↓reduceIte]
        · simp only [tailKernel,hy,↓reduceIte,mul_zero]
      _ = _ := by rw [←Finset.mul_sum]; field_simp
  rw [←he]
  exact (tail_density_mean _ (fun y => mul_nonneg (Nat.cast_nonneg _) (hP x y)) a z ha hz).trans
    (mul_le_mul_of_nonneg_right (hM x) (Real.rpow_nonneg hz.le _))

lemma tailKernel_schur {X : Type*} [Fintype X] [Nonempty X] (P : X → X → ℝ)
    (hP : ∀ x y, 0 ≤ P x y) (hsym : ∀ x y, P x y = P y x)
    (a z M : ℝ) (ha : 0 ≤ a) (hz : 0 < z) (hM0 : 0 ≤ M)
    (hM : ∀ x, finiteMean (fun y => ((Fintype.card X:ℝ)*P x y)^(1+a)) ≤ M)
    (v : EuclideanSpace ℂ X) :
    ‖applyKernel (tailKernel P z) v‖ ≤ (M*z^(-a))*‖v‖ := by
  apply schur_bound _ (tailKernel_nonneg P z hP) _ (by positivity)
    (tailKernel_row P hP a z M ha hz hM)
  intro y
  have hs : (fun x => tailKernel P z x y) = (fun x => tailKernel P z y x) := by
    funext x
    simp only [tailKernel,hsym x y]
  rw [hs]
  exact tailKernel_row P hP a z M ha hz hM y

lemma headKernel_hs {X : Type*} [Fintype X] [Nonempty X] (P : X → X → ℝ)
    (hP : ∀ x y, 0 ≤ P x y) (hrow : ∀ x, ∑ y, P x y = 1) (z : ℝ) (hz : 0 ≤ z) :
    (∑ x, ∑ y, (headKernel P z x y)^2) ≤ z := by
  have hn : (0:ℝ) < Fintype.card X := Nat.cast_pos.mpr Fintype.card_pos
  have he (x y : X) : (headKernel P z x y)^2 ≤ (z/(Fintype.card X:ℝ))*P x y := by
    unfold headKernel
    split_ifs with h
    · simp only [zero_pow (by omega : (2:ℕ) ≠ 0)]
      exact mul_nonneg (div_nonneg hz hn.le) (hP x y)
    · have h' : (Fintype.card X:ℝ)*P x y ≤ z := le_of_not_gt h
      have hh := mul_le_mul_of_nonneg_right h' (hP x y)
      rw [show (z/(Fintype.card X:ℝ))*P x y = (z*P x y)/(Fintype.card X:ℝ) by ring]
      apply (le_div_iff₀ hn).mpr
      nlinarith
  calc
    _ ≤ ∑ x, ∑ y, (z/(Fintype.card X:ℝ))*P x y :=
      Finset.sum_le_sum (fun x _ => Finset.sum_le_sum (fun y _ => he x y))
    _ = z := by
      simp only [←Finset.mul_sum,hrow,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      field_simp


theorem multiplicity_amplification {X I : Type*} [Fintype X] [Nonempty X]
    [Fintype I] [Nonempty I] (P : X → X → ℝ)
    (hP : ∀ x y, 0 ≤ P x y) (hsym : ∀ x y, P x y = P y x)
    (hrow : ∀ x, ∑ y, P x y = 1) (a z M : ℝ) (ha : 0 ≤ a) (hz : 0 < z) (hM0 : 0 ≤ M)
    (hM : ∀ x, finiteMean (fun y => ((Fintype.card X:ℝ)*P x y)^(1+a)) ≤ M)
    (v : I → EuclideanSpace ℂ X) (hv : Orthonormal ℂ v)
    (μ : ℝ) (hvμ : ∀ i, μ ≤ ‖applyKernel P (v i)‖) :
    μ ≤ M*z^(-a)+Real.sqrt (z/(Fintype.card I:ℝ)) := by
  let δ : ℝ := M*z^(-a)
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hm : (0:ℝ) < Fintype.card I := Nat.cast_pos.mpr Fintype.card_pos
  change μ ≤ δ+_
  by_cases hμ : μ ≤ δ
  · exact hμ.trans (le_add_of_nonneg_right (Real.sqrt_nonneg _))
  have hmd : 0 ≤ μ-δ := by linarith
  have hsmall (i : I) : μ-δ ≤ ‖applyKernel (headKernel P z) (v i)‖ := by
    have hr := tailKernel_schur P hP hsym a z M ha hz hM0 hM (v i)
    rw [hv.norm_eq_one i,mul_one] at hr
    have he := applyKernel_add (tailKernel P z) (headKernel P z) (v i)
    rw [tail_add_head] at he
    have hn := norm_add_le (applyKernel (tailKernel P z) (v i)) (applyKernel (headKernel P z) (v i))
    rw [←he] at hn
    have hh := hvμ i
    change ‖applyKernel (tailKernel P z) (v i)‖ ≤ δ at hr
    linarith
  have hsum : (Fintype.card I:ℝ)*(μ-δ)^2 ≤ z := by
    calc
      _ = ∑ i : I, (μ-δ)^2 := by simp
      _ ≤ ∑ i : I, ‖applyKernel (headKernel P z) (v i)‖^2 :=
        Finset.sum_le_sum (fun i _ => pow_le_pow_left₀ hmd (hsmall i) 2)
      _ ≤ ∑ x, ∑ y, (headKernel P z x y)^2 := hilbert_schmidt_family _ v hv
      _ ≤ z := headKernel_hs P hP hrow z hz.le
  have hsq : (μ-δ)^2 ≤ z/(Fintype.card I:ℝ) := (le_div_iff₀ hm).mpr (by nlinarith)
  have hs := (Real.le_sqrt hmd (div_nonneg hz.le hm.le)).mpr hsq
  linarith

end DensityTransfer
namespace PairRouting
open scoped BigOperators

lemma tupleProbability_row_sum {ι β Ω : Type*} [Fintype ι] [Fintype β]
    [DecidableEq β] [Fintype Ω] [Nonempty Ω]
    (P : Ω → Equiv.Perm β) (e : ι ↪ β) :
    (∑ f : ι ↪ β, tupleProbability P e f) = 1 := by
  classical
  simp only [tupleProbability]
  rw [←finiteMean_sum]
  have h (ω : Ω) (f : ι ↪ β) : (∀ i, P ω (e i) = f i) ↔ e.trans (P ω).toEmbedding = f := by
    constructor
    · intro h; ext i; exact h i
    · intro h i; exact congrArg (fun g : ι ↪ β => g i) h
  simp_rw [h]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,↓reduceIte,finiteMean_const]

lemma tupleProbability_inverse {ι β Ω : Type*} [Fintype ι] [DecidableEq β]
    [Fintype Ω] (P : Ω → Equiv.Perm β) (e f : ι → β) :
    tupleProbability (fun ω => (P ω)⁻¹) e f = tupleProbability P f e := by
  classical
  apply finiteMean_congr
  intro ω
  congr 1
  apply propext
  constructor
  · intro h i
    have hh := congrArg (P ω) (h i)
    simpa only [Equiv.Perm.inv_def,Equiv.apply_symm_apply] using hh.symm
  · intro h i
    have hh := congrArg (fun x => (P ω).symm x) (h i)
    simpa only [Equiv.Perm.inv_def,Equiv.symm_apply_apply] using hh.symm

lemma tupleProbability_equiv {ι β Ω Ω' : Type*} [Fintype ι] [DecidableEq β]
    [Fintype Ω] [Fintype Ω'] (P : Ω → Equiv.Perm β) (τ : Ω ≃ Ω') (e f : ι → β) :
    tupleProbability P e f = tupleProbability (fun ω => P (τ.symm ω)) e f :=
  finiteMean_equiv τ _

lemma tupleProbability_symmetric {ι β Ω : Type*} [Fintype ι] [DecidableEq β]
    [Fintype Ω] (P : Ω → Equiv.Perm β) (τ : Equiv.Perm Ω)
    (hτ : ∀ ω, P (τ ω) = (P ω)⁻¹) (e f : ι → β) :
    tupleProbability P e f = tupleProbability P f e := by
  rw [tupleProbability_equiv P τ.symm]
  simp only [Equiv.symm_symm,hτ]
  exact tupleProbability_inverse P e f

end PairRouting

lemma palindromePerm_reverse (d : ℕ) (ω : BenesCoins d) :
    palindromePerm d (ω.2,ω.1) = (palindromePerm d ω)⁻¹ := by
  simp only [palindromePerm,mul_inv_rev]
  rfl

lemma palindrome_kernel_symmetric (d : ℕ) {ι : Type*} [Fintype ι]
    (e f : ι ↪ Card d) :
    PairRouting.tupleProbability (palindromePerm d) e f =
      PairRouting.tupleProbability (palindromePerm d) f e :=
  PairRouting.tupleProbability_symmetric _ (Equiv.prodComm _ _) (palindromePerm_reverse d) e f

end Thorp

end ThorpNine.Adaptive

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Adaptive_ModifiedReverseEquiv
attribute [-instance] _root_.OAI.ThorpNine.Adaptive.Thorp.Specht.tabloidMulAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Adaptive

namespace Thorp.Specht
open scoped BigOperators Classical

lemma strictMono_fin_nat_ge {n : ℕ} (f : Fin n → ℕ) (hf : StrictMono f) :
    ∀ i, i.val ≤ f i := by
  intro i
  induction h : i.val using Nat.strong_induction_on generalizing i with
  | h n ih =>
    by_cases hn : n = 0
    · omega
    · have hn' : n-1 < i.val := by omega
      let j : Fin _ := ⟨n-1, hn'.trans i.isLt⟩
      have hj := ih (n-1) (by omega) j rfl
      have hij := hf (show j < i from hn')
      dsimp [j] at hj hij
      omega

lemma rankCell_row_le {μ : YoungDiagram} (f : Cell μ → ℕ)
    (hf : ∀ x y, col x = col y → f x = f y → x = y) (x : Cell μ) :
    row (rankCell f hf x) ≤ f x := by
  rw [←rankCell_orderEmb f hf x]
  exact strictMono_fin_nat_ge _ (OrderEmbedding.strictMono _) _

theorem column_transporter (μ : YoungDiagram) (p : Equiv.Perm (Cell μ))
    (hp : ∀ x y, col x = col y → row (p x) = row (p y) → x = y) :
    ∃ c : Equiv.Perm (Cell μ), (∀ x, col (c x) = col x) ∧
      ∀ x, row (c x) = row (p x) := by
  classical
  let c := rankPerm (fun x => row (p x)) hp
  refine ⟨c, fun x => rfl, ?_⟩
  have hle (x : Cell μ) : row (c x) ≤ row (p x) := rankCell_row_le _ hp x
  have hsum : ∑ x, row (c x) = ∑ x, row (p x) := by
    rw [Equiv.sum_comp, Equiv.sum_comp]
  exact fun x => (Finset.sum_eq_sum_iff_of_le (fun x _ => hle x)).mp hsum x (Finset.mem_univ _)


lemma tabloidRep_delta {μ : YoungDiagram} (p : Equiv.Perm (Cell μ)) (f : Tabloid μ) :
    tabloidRep μ p (delta f) = delta (tabloidAct p f) := by
  classical
  ext g
  simp only [tabloidRep_apply,delta,Equiv.Perm.inv_def]
  congr 1
  exact propext (Equiv.symm_apply_eq (tabloidAct p))

lemma colGroup_row_stabilizer {μ : YoungDiagram} (c : colGroup μ)
    (hc : tabloidAct c (baseTabloid μ) = baseTabloid μ) : (c : Equiv.Perm (Cell μ)) = 1 := by
  apply Equiv.ext
  intro x
  have hr := congrArg (fun f : Tabloid μ => ((f.1 ((c : Equiv.Perm _) x)) : ℕ)) hc
  simp only [tabloidAct_apply,Equiv.Perm.inv_def,Equiv.symm_apply_apply,baseTabloid,rowIndex] at hr
  apply Subtype.ext
  exact Prod.ext hr.symm (c.2 x)

lemma tabloid_column_transporter {μ : YoungDiagram} (f : Tabloid μ)
    (hf : ∀ x y, col x = col y → f.1 x = f.1 y → x = y) :
    ∃ c : colGroup μ, f = tabloidAct c (baseTabloid μ) := by
  obtain ⟨p,hp⟩ := f.2
  have hp' : ∀ x y, col x = col y → row (p x) = row (p y) → x = y := by
    intro x y hcol hrow
    apply hf x y hcol
    rw [hp]
    exact Fin.ext hrow
  obtain ⟨c,hcol,hrow⟩ := column_transporter μ p hp'
  refine ⟨⟨c⁻¹, (colGroup μ).inv_mem hcol⟩, ?_⟩
  apply Subtype.ext
  funext x
  apply Fin.ext
  simp only [tabloidAct_apply,baseTabloid,rowIndex,inv_inv,hp,Function.comp_apply]
  exact (hrow x).symm


lemma permSign_sq {α : Type*} [Fintype α] [DecidableEq α] (p : Equiv.Perm α) :
    permSign p * permSign p = 1 := by
  calc
    permSign p * permSign p = permSign (p*p⁻¹) := by rw [permSign_mul,permSign_inv]
    _ = 1 := by simp

variable {α V : Type*} [Fintype α] [DecidableEq α] [AddCommGroup V] [Module ℂ V]

lemma alternator_mul (C : Subgroup (Equiv.Perm α))
    (ρ : Representation ℂ (Equiv.Perm α) V) (c : C) :
    alternator C ρ * ρ c = permSign (c : Equiv.Perm α) • alternator C ρ := by
  classical
  rw [alternator,Finset.sum_mul,Finset.smul_sum]
  apply Fintype.sum_equiv (Equiv.mulRight c)
  intro a
  simp only [smul_mul_assoc,←map_mul,Equiv.coe_mulRight,Subgroup.coe_mul,permSign_mul,smul_smul]
  congr 1
  have h := permSign_sq (c : Equiv.Perm α)
  calc
    permSign (a : Equiv.Perm α) = permSign (a : Equiv.Perm α)*1 := by ring
    _ = permSign (a : Equiv.Perm α)*(permSign (c : Equiv.Perm α)*permSign (c : Equiv.Perm α)) := by rw [h]
    _ = _ := by ring

lemma mul_alternator (C : Subgroup (Equiv.Perm α))
    (ρ : Representation ℂ (Equiv.Perm α) V) (c : C) :
    ρ c * alternator C ρ = permSign (c : Equiv.Perm α) • alternator C ρ := by
  classical
  rw [alternator,Finset.mul_sum,Finset.smul_sum]
  apply Fintype.sum_equiv (Equiv.mulLeft c)
  intro a
  simp only [mul_smul_comm,←map_mul,Equiv.coe_mulLeft,Subgroup.coe_mul,permSign_mul,smul_smul]
  congr 1
  have h := permSign_sq (c : Equiv.Perm α)
  calc
    permSign (a : Equiv.Perm α) = 1*permSign (a : Equiv.Perm α) := by ring
    _ = (permSign (c : Equiv.Perm α)*permSign (c : Equiv.Perm α))*permSign (a : Equiv.Perm α) := by rw [h]
    _ = _ := by ring

lemma alternator_apply_action (C : Subgroup (Equiv.Perm α))
    (ρ : Representation ℂ (Equiv.Perm α) V) (c : C) (v : V) :
    alternator C ρ (ρ c v) = permSign (c : Equiv.Perm α) • alternator C ρ v := by
  exact congrArg (fun T : Module.End ℂ V => T v) (alternator_mul C ρ c)

lemma action_alternator_apply (C : Subgroup (Equiv.Perm α))
    (ρ : Representation ℂ (Equiv.Perm α) V) (c : C) (v : V) :
    ρ c (alternator C ρ v) = permSign (c : Equiv.Perm α) • alternator C ρ v := by
  exact congrArg (fun T : Module.End ℂ V => T v) (mul_alternator C ρ c)

lemma alternator_eq_zero_of_odd_stabilizer (C : Subgroup (Equiv.Perm α))
    (ρ : Representation ℂ (Equiv.Perm α) V) (c : C) (v : V)
    (hc : permSign (c : Equiv.Perm α) = -1) (hv : ρ c v = v) :
    alternator C ρ v = 0 := by
  have h := alternator_apply_action C ρ c v
  rw [hv,hc,neg_one_smul] at h
  have h2 : (2:ℂ) • alternator C ρ v = 0 := by
    rw [two_smul]
    nth_rw 1 [h]
    exact neg_add_cancel _
  exact (smul_eq_zero.mp h2).resolve_left (by norm_num)

end Thorp.Specht
namespace Thorp.Specht
open scoped BigOperators Classical

lemma swap_mem_colGroup {μ : YoungDiagram} (x y : Cell μ) (hc : col x = col y) :
    Equiv.swap x y ∈ colGroup μ := by
  classical
  intro z
  by_cases hx : z=x
  · subst z; simpa using hc.symm
  by_cases hy : z=y
  · subst z; simpa using hc
  simp [Equiv.swap_apply_of_ne_of_ne hx hy]

lemma swap_fixes_tabloid {μ : YoungDiagram} (f : Tabloid μ) (x y : Cell μ)
    (hxy : f.1 x = f.1 y) : tabloidAct (Equiv.swap x y) f = f := by
  classical
  apply Subtype.ext
  funext z
  simp only [tabloidAct_apply, Equiv.swap_inv]
  by_cases hx : z=x
  · subst z; simpa using hxy.symm
  by_cases hy : z=y
  · subst z; simpa using hxy
  simp [Equiv.swap_apply_of_ne_of_ne hx hy]

lemma alternator_delta_rank_one {μ : YoungDiagram} (f : Tabloid μ) :
    ∃ z : ℂ, alternator (colGroup μ) (tabloidRep μ) (delta f) = z • polytabloid μ := by
  classical
  by_cases hf : ∀ x y, col x = col y → f.1 x = f.1 y → x = y
  · obtain ⟨c,rfl⟩ := tabloid_column_transporter f hf
    refine ⟨permSign (c:Equiv.Perm (Cell μ)), ?_⟩
    rw [←tabloidRep_delta]
    exact alternator_apply_action _ _ c _
  · push Not at hf
    obtain ⟨x,y,hcol,hrow,hne⟩ := hf
    refine ⟨0, ?_⟩
    rw [zero_smul]
    apply alternator_eq_zero_of_odd_stabilizer _ _ ⟨Equiv.swap x y,swap_mem_colGroup x y hcol⟩
    · exact permSign_swap hne
    · rw [tabloidRep_delta,swap_fixes_tabloid f x y hrow]

lemma polytabloid_formula (μ : YoungDiagram) :
    polytabloid μ = ∑ c : colGroup μ, permSign (c:Equiv.Perm (Cell μ)) •
      delta (tabloidAct c (baseTabloid μ)) := by
  classical
  simp only [polytabloid,alternator,LinearMap.sum_apply,LinearMap.smul_apply,tabloidRep_delta]

lemma polytabloid_base (μ : YoungDiagram) : polytabloid μ (baseTabloid μ) = 1 := by
  classical
  rw [polytabloid_formula,Finset.sum_apply]
  rw [Finset.sum_eq_single (1 : colGroup μ)]
  · simp [delta]
  · intro c hc hne
    have hn : baseTabloid μ ≠ tabloidAct c (baseTabloid μ) := by
      intro h
      apply hne
      exact Subtype.ext (colGroup_row_stabilizer c h.symm)
    simp [Pi.smul_apply,delta,hn]
  · simp

lemma polytabloid_ne_zero (μ : YoungDiagram) : polytabloid μ ≠ 0 := by
  intro h
  have hv := congrArg (fun v : Tabloid μ → ℂ => v (baseTabloid μ)) h
  simp [polytabloid_base] at hv

lemma delta_decomposition {μ : YoungDiagram} (v : Tabloid μ → ℂ) :
    v = ∑ f : Tabloid μ, v f • delta f := by
  classical
  funext g
  simp only [Finset.sum_apply,Pi.smul_apply,delta,smul_eq_mul,mul_ite,mul_one,mul_zero]
  simp

theorem alternator_rank_one (μ : YoungDiagram) (v : Tabloid μ → ℂ) :
    ∃ z : ℂ, alternator (colGroup μ) (tabloidRep μ) v = z • polytabloid μ := by
  classical
  choose z hz using fun f : Tabloid μ => alternator_delta_rank_one f
  refine ⟨∑ f, v f * z f, ?_⟩
  conv_lhs => rw [delta_decomposition v]
  simp only [map_sum,map_smul,hz,smul_smul,Finset.sum_smul]

lemma alternator_rank_one_exact (μ : YoungDiagram) (v : Tabloid μ → ℂ) :
    alternator (colGroup μ) (tabloidRep μ) v =
      (alternator (colGroup μ) (tabloidRep μ) v (baseTabloid μ)) • polytabloid μ := by
  obtain ⟨z,hz⟩ := alternator_rank_one μ v
  rw [hz]
  simp only [Pi.smul_apply,polytabloid_base,smul_eq_mul,mul_one]


lemma pairing_delta {μ : YoungDiagram} (f : Tabloid μ) (v : Tabloid μ → ℂ) :
    pairing (delta f) v = v f := by
  classical
  simp [pairing,delta]

lemma pairing_sum_left {μ : YoungDiagram} {ι : Type*} [Fintype ι]
    (v : ι → Tabloid μ → ℂ) (w : Tabloid μ → ℂ) :
    pairing (∑ i, v i) w = ∑ i, pairing (v i) w := by
  simp only [pairing,Finset.sum_apply,map_sum,Finset.mul_sum]
  exact Finset.sum_comm

lemma pairing_smul_left {μ : YoungDiagram} (a : ℂ) (v w : Tabloid μ → ℂ) :
    pairing (a • v) w = starRingEnd ℂ a * pairing v w := by
  simp only [pairing,Pi.smul_apply,smul_eq_mul,map_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro f hf
  ring

lemma pairing_zero_left {μ : YoungDiagram} (v : Tabloid μ → ℂ) : pairing 0 v = 0 := by
  simp [pairing]

lemma pairing_add_left {μ : YoungDiagram} (u v w : Tabloid μ → ℂ) :
    pairing (u+v) w = pairing u w + pairing v w := by
  simp [pairing,mul_add,Finset.sum_add_distrib]

lemma pairing_self_eq_zero {μ : YoungDiagram} (v : Tabloid μ → ℂ) :
    pairing v v = 0 ↔ v = 0 := by
  change inner ℂ (WithLp.toLp 2 v : EuclideanSpace ℂ (Tabloid μ)) (WithLp.toLp 2 v) = 0 ↔ v = 0
  rw [inner_self_eq_zero]
  constructor
  · intro h; exact congrArg WithLp.ofLp h
  · intro h; subst v; rfl

lemma pairing_action {μ : YoungDiagram} (p : Equiv.Perm (Cell μ)) (v w : Tabloid μ → ℂ) :
    pairing (tabloidRep μ p v) w = pairing v (tabloidRep μ p⁻¹ w) := by
  classical
  simp only [pairing,tabloidRep_apply,inv_inv]
  apply Fintype.sum_equiv (tabloidAct p⁻¹)
  intro f
  have hcancel : tabloidAct p (tabloidAct p⁻¹ f) = f := by
    rw [tabloidAct_inv]
    exact (tabloidAct p).apply_symm_apply f
  rw [hcancel]

lemma alternator_base_pairing (μ : YoungDiagram) (v : Tabloid μ → ℂ) :
    alternator (colGroup μ) (tabloidRep μ) v (baseTabloid μ) = pairing (polytabloid μ) v := by
  classical
  simp only [polytabloid_formula,pairing_sum_left,pairing_smul_left,conj_permSign,pairing_delta]
  simp only [alternator,LinearMap.sum_apply,LinearMap.smul_apply,Finset.sum_apply,Pi.smul_apply,
    smul_eq_mul,tabloidRep_apply]
  apply Fintype.sum_equiv (Equiv.inv (colGroup μ))
  intro c
  simp only [Equiv.inv_apply,Subgroup.coe_inv,permSign_inv]

theorem alternator_pairing (μ : YoungDiagram) (v : Tabloid μ → ℂ) :
    alternator (colGroup μ) (tabloidRep μ) v = pairing (polytabloid μ) v • polytabloid μ := by
  rw [alternator_rank_one_exact,alternator_base_pairing]


lemma polytabloid_mem_space (μ : YoungDiagram) : polytabloid μ ∈ space μ := by
  simpa using orbit_mem_space μ 1

lemma alternator_mem_invariant (μ : YoungDiagram) (W : Submodule ℂ (Tabloid μ → ℂ))
    (hW : ∀ p v, v ∈ W → tabloidRep μ p v ∈ W) (v : Tabloid μ → ℂ) (hv : v ∈ W) :
    alternator (colGroup μ) (tabloidRep μ) v ∈ W := by
  classical
  simp only [alternator,LinearMap.sum_apply,LinearMap.smul_apply]
  exact W.sum_mem (fun c _ => W.smul_mem _ (hW c v hv))

theorem submodule_theorem (μ : YoungDiagram) (W : Submodule ℂ (Tabloid μ → ℂ))
    (hW : ∀ p v, v ∈ W → tabloidRep μ p v ∈ W) :
    space μ ≤ W ∨ ∀ v ∈ W, ∀ w ∈ space μ, pairing w v = 0 := by
  classical
  by_cases hSW : space μ ≤ W
  · exact Or.inl hSW
  right
  have he : polytabloid μ ∉ W := by
    intro he
    apply hSW
    apply Submodule.span_le.mpr
    rintro _ ⟨p,rfl⟩
    exact hW p _ he
  have hpair : ∀ v ∈ W, pairing (polytabloid μ) v = 0 := by
    intro v hv
    by_contra hne
    apply he
    have hal := alternator_mem_invariant μ W hW v hv
    rw [alternator_pairing] at hal
    have hh := W.smul_mem (pairing (polytabloid μ) v)⁻¹ hal
    simpa only [smul_smul,inv_mul_cancel₀ hne,one_smul] using hh
  intro v hv w hw
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨p,rfl⟩ := hw
    rw [pairing_action]
    exact hpair _ (hW p⁻¹ v hv)
  | zero => exact pairing_zero_left v
  | add u w hu hw ihu ihw => rw [pairing_add_left,ihu,ihw,add_zero]
  | smul a w hw ih => rw [pairing_smul_left,ih,mul_zero]

theorem space_simple (μ : YoungDiagram) (W : Submodule ℂ (Tabloid μ → ℂ))
    (hW : ∀ p v, v ∈ W → tabloidRep μ p v ∈ W) (hWS : W ≤ space μ) :
    W = ⊥ ∨ W = space μ := by
  obtain hSW | horth := submodule_theorem μ W hW
  · exact Or.inr (le_antisymm hWS hSW)
  · left
    apply le_antisymm _ bot_le
    intro v hv
    exact (pairing_self_eq_zero v).mp (horth v hv v (hWS hv))


theorem representation_irreducible (μ : YoungDiagram) :
    Representation.IsIrreducible (representation μ) := by
  have hnt : (⊥ : Subrepresentation (representation μ)) ≠ ⊤ := by
    intro h
    have he : (⟨polytabloid μ,polytabloid_mem_space μ⟩ : space μ) ∈
        (⊥ : Subrepresentation (representation μ)) := by rw [h]; trivial
    have he' : (⟨polytabloid μ,polytabloid_mem_space μ⟩ : space μ) = 0 := he
    exact polytabloid_ne_zero μ (congrArg Subtype.val he')
  refine { exists_pair_ne := ⟨⊥,⊤,hnt⟩, eq_bot_or_eq_top := ?_ }
  intro U
  let W : Submodule ℂ (Tabloid μ → ℂ) := U.toSubmodule.map (space μ).subtype
  have hW : ∀ p v, v ∈ W → tabloidRep μ p v ∈ W := by
    intro p v hv
    obtain ⟨u,hu,rfl⟩ := hv
    exact ⟨representation μ p u,U.apply_mem_toSubmodule p hu,rfl⟩
  have hWS : W ≤ space μ := by
    intro v hv
    obtain ⟨u,hu,rfl⟩ := hv
    exact u.2
  obtain hbot | htop := space_simple μ W hW hWS
  · left
    apply le_antisymm _ bot_le
    intro u hu
    have hmem : (u : Tabloid μ → ℂ) ∈ W := ⟨u,hu,rfl⟩
    rw [hbot,Submodule.mem_bot] at hmem
    change u = 0
    exact Subtype.ext hmem
  · right
    apply le_antisymm le_top
    intro u hu
    have hmem : (u : Tabloid μ → ℂ) ∈ W := by rw [htop]; exact u.2
    obtain ⟨v,hv,hvu⟩ := hmem
    have heq : v = u := Subtype.ext hvu
    exact heq ▸ hv


end Thorp.Specht

end ThorpNine.Adaptive

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Adaptive_ShapePartitionEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Adaptive

namespace Thorp.PermutationHilbert

section
open scoped BigOperators ComplexConjugate Classical
open Complex

variable {X : Type*} [Fintype X]

lemma act_single [DecidableEq X] (p : Equiv.Perm X) (x : X) :
    act p (EuclideanSpace.single x (1:ℂ)) = EuclideanSpace.single (p x) 1 := by
  exact EuclideanSpace.piLpCongrLeft_single p x 1

lemma trace_projection (W : Submodule ℂ (H X)) :
    ∑ x, (W.starProjection (EuclideanSpace.single x (1:ℂ))) x = Module.finrank ℂ W := by
  classical
  have hp : LinearMap.IsProj W W.starProjection.toLinearMap := by
    constructor
    · intro x; exact (W.orthogonalProjectionOnto x).2
    · intro x hx; exact W.starProjection_eq_self_iff.mpr hx
  have ht := hp.trace
  rw [LinearMap.trace_eq_matrix_trace ℂ (EuclideanSpace.basisFun X ℂ).toBasis] at ht
  simpa only [Matrix.trace,Matrix.diag_apply,LinearMap.toMatrix_apply,EuclideanSpace.basisFun_repr,
    EuclideanSpace.basisFun_apply,OrthonormalBasis.coe_toBasis,
    OrthonormalBasis.coe_toBasis_repr_apply,ContinuousLinearMap.coe_coe] using ht

lemma projection_diagonal (W : Submodule ℂ (H X)) (x : X) :
    (W.starProjection (EuclideanSpace.single x (1:ℂ))) x =
      (‖W.starProjection (EuclideanSpace.single x (1:ℂ))‖^2 : ℝ) := by
  classical
  have hh := W.inner_starProjection_left_eq_right
    (EuclideanSpace.single x (1:ℂ)) (W.starProjection (EuclideanSpace.single x (1:ℂ)))
  have hf : W.starProjection (W.starProjection (EuclideanSpace.single x (1:ℂ))) =
      W.starProjection (EuclideanSpace.single x (1:ℂ)) :=
    W.starProjection_eq_self_iff.mpr (W.orthogonalProjectionOnto _).2
  rw [hf] at hh
  rw [inner_self_eq_norm_sq_to_K,EuclideanSpace.inner_single_left] at hh
  simpa using hh.symm

lemma projection_comm (W : Submodule ℂ (H X)) (p : Equiv.Perm X)
    (hW : W.map (act p).toLinearEquiv.toLinearMap = W) (v : H X) :
    act p (W.starProjection v) = W.starProjection (act p v) := by
  have hh := (act p).toLinearIsometry.map_starProjection W v
  change act p (W.starProjection v) =
    (W.map (act p).toLinearEquiv.toLinearMap).starProjection (act p v) at hh
  simpa only [hW] using hh

lemma uniform_diagonal (W : Submodule ℂ (H X))
    (htrans : ∀ x y : X, ∃ p : Equiv.Perm X, p x = y ∧
      W.map (act p).toLinearEquiv.toLinearMap = W) (x : X) :
    (Fintype.card X:ℝ) * ‖W.starProjection (EuclideanSpace.single x (1:ℂ))‖^2 =
      Module.finrank ℂ W := by
  classical
  have hh (y : X) : (W.starProjection (EuclideanSpace.single y (1:ℂ))) y =
      (‖W.starProjection (EuclideanSpace.single x (1:ℂ))‖^2 : ℝ) := by
    obtain ⟨p,hp,hW⟩ := htrans x y
    subst y
    rw [projection_diagonal,←act_single p x,←projection_comm W p hW,(act p).norm_map]
  have ht := trace_projection W
  simp_rw [hh] at ht
  have hhreal : (∑ _y : X, ‖W.starProjection (EuclideanSpace.single x (1:ℂ))‖^2) =
      (Module.finrank ℂ W:ℝ) := by exact_mod_cast ht
  simpa using hhreal

theorem uncertainty (W : Submodule ℂ (H X))
    (htrans : ∀ x y : X, ∃ p : Equiv.Perm X, p x = y ∧
      W.map (act p).toLinearEquiv.toLinearMap = W)
    (v : H X) (hv : v ∈ W) (x : X) :
    (Fintype.card X:ℝ) * ‖v x‖^2 ≤ (Module.finrank ℂ W:ℝ) * ‖v‖^2 := by
  classical
  have hh : inner ℂ (W.starProjection (EuclideanSpace.single x (1:ℂ))) v = v x := by
    rw [W.inner_starProjection_left_eq_right,W.starProjection_eq_self_iff.mpr hv,
      EuclideanSpace.inner_single_left]
    simp
  have hc := norm_inner_le_norm (𝕜 := ℂ) (W.starProjection (EuclideanSpace.single x (1:ℂ))) v
  rw [hh] at hc
  have hs : ‖v x‖^2 ≤ ‖W.starProjection (EuclideanSpace.single x (1:ℂ))‖^2 * ‖v‖^2 := by
    nlinarith [norm_nonneg (v x),norm_nonneg v,
      norm_nonneg (W.starProjection (EuclideanSpace.single x (1:ℂ)))]
  calc
    (Fintype.card X:ℝ) * ‖v x‖^2 ≤
      (Fintype.card X:ℝ) * (‖W.starProjection (EuclideanSpace.single x (1:ℂ))‖^2 * ‖v‖^2) :=
      mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg _)
    _ = _ := by rw [←mul_assoc,uniform_diagonal W htrans x]

end
open scoped BigOperators Classical

end Thorp.PermutationHilbert
namespace Thorp.Specht
open scoped BigOperators Classical

lemma finrank_hilbertSpace (μ : YoungDiagram) :
    Module.finrank ℂ (hilbertSpace μ) = Module.finrank ℂ (space μ) :=
  (hilbertEquiv μ).finrank_map_eq (space μ)

lemma hilbertSpace_invariant (μ : YoungDiagram) (p : Equiv.Perm (Cell μ)) :
    (hilbertSpace μ).map (PermutationHilbert.act (tabloidAct p)).toLinearEquiv.toLinearMap =
      hilbertSpace μ := by
  apply le_antisymm
  · rintro _ ⟨v,⟨w,hw,rfl⟩,rfl⟩
    exact ⟨tabloidRep μ p w,action_mem_space μ p w hw,hilbert_action μ p w⟩
  · rintro _ ⟨w,hw,rfl⟩
    refine ⟨hilbertEquiv μ (tabloidRep μ p⁻¹ w),
      ⟨tabloidRep μ p⁻¹ w,action_mem_space μ p⁻¹ w hw,rfl⟩, ?_⟩
    change PermutationHilbert.act (tabloidAct p) (hilbertEquiv μ (tabloidRep μ p⁻¹ w)) = hilbertEquiv μ w
    rw [←hilbert_action]
    change hilbertEquiv μ ((tabloidRep μ p * tabloidRep μ p⁻¹) w) = _
    rw [←map_mul,mul_inv_cancel,map_one]
    rfl

lemma tabloidAct_transitive (μ : YoungDiagram) (f g : Tabloid μ) :
    ∃ p : Equiv.Perm (Cell μ), tabloidAct p f = g := by
  obtain ⟨q,hq⟩ := f.2
  obtain ⟨r,hr⟩ := g.2
  refine ⟨r⁻¹*q, ?_⟩
  apply Subtype.ext
  funext x
  simp only [tabloidAct_apply,mul_inv_rev,Equiv.Perm.mul_apply,hq,hr,
    Function.comp_apply,Equiv.Perm.inv_def,Equiv.apply_symm_apply,Equiv.symm_symm]

lemma polytabloid_pairing (μ : YoungDiagram) :
    pairing (polytabloid μ) (polytabloid μ) = Fintype.card (colGroup μ) := by
  have h := alternator_pairing μ (polytabloid μ)
  have he (c : colGroup μ) : tabloidRep μ c (polytabloid μ) =
      permSign (c:Equiv.Perm (Cell μ)) • polytabloid μ :=
    action_alternator_apply (colGroup μ) (tabloidRep μ) c _
  have hb := congrArg (fun v : Tabloid μ → ℂ => v (baseTabloid μ)) h
  simp only [alternator,LinearMap.sum_apply,LinearMap.smul_apply,he,
    Pi.smul_apply,smul_eq_mul,Finset.sum_apply,polytabloid_base,mul_one] at hb
  simp only [permSign_sq,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] at hb
  exact hb.symm

lemma polytabloid_norm_sq (μ : YoungDiagram) :
    ‖hilbertEquiv μ (polytabloid μ)‖^2 = (Fintype.card (colGroup μ):ℝ) := by
  have hp := polytabloid_pairing μ
  change inner ℂ (hilbertEquiv μ (polytabloid μ)) (hilbertEquiv μ (polytabloid μ)) = _ at hp
  rw [inner_self_eq_norm_sq_to_K] at hp
  have hre := congrArg Complex.re hp
  simpa [pow_two] using hre

theorem dimension_times_column_ge_tabloids (μ : YoungDiagram) :
    Fintype.card (Tabloid μ) ≤ Module.finrank ℂ (space μ) * Fintype.card (colGroup μ) := by
  have ht (f g : Tabloid μ) : ∃ p : Equiv.Perm (Tabloid μ), p f = g ∧
      (hilbertSpace μ).map (PermutationHilbert.act p).toLinearEquiv.toLinearMap = hilbertSpace μ := by
    obtain ⟨p,hp⟩ := tabloidAct_transitive μ f g
    exact ⟨tabloidAct p,hp,hilbertSpace_invariant μ p⟩
  have hu := PermutationHilbert.uncertainty (hilbertSpace μ) ht
    (hilbertEquiv μ (polytabloid μ)) ⟨polytabloid μ,polytabloid_mem_space μ,rfl⟩ (baseTabloid μ)
  have he : hilbertEquiv μ (polytabloid μ) (baseTabloid μ) = 1 := polytabloid_base μ
  rw [he,norm_one,one_pow,mul_one,finrank_hilbertSpace,polytabloid_norm_sq] at hu
  exact_mod_cast hu


lemma tabloid_orbit_all (μ : YoungDiagram) :
    MulAction.orbit (Equiv.Perm (Cell μ)) (baseTabloid μ) = Set.univ := by
  ext f
  simp only [Set.mem_univ,iff_true]
  obtain ⟨p,hp⟩ := tabloidAct_transitive μ (baseTabloid μ) f
  exact ⟨p,hp⟩

lemma tabloid_stabilizer (μ : YoungDiagram) :
    MulAction.stabilizer (Equiv.Perm (Cell μ)) (baseTabloid μ) = rowGroup μ := by
  ext p
  change tabloidAct p (baseTabloid μ) = baseTabloid μ ↔ ∀ x, rowIndex (p x) = rowIndex x
  constructor
  · intro h x
    have hh := congrArg (fun f : Tabloid μ => f.1 (p x)) h
    simpa only [tabloidAct_apply,baseTabloid,Equiv.Perm.inv_def,Equiv.symm_apply_apply] using hh.symm
  · intro h
    apply Subtype.ext
    funext x
    exact (h (p⁻¹ x)).symm.trans (by simp [baseTabloid])

lemma card_tabloid_mul_row (μ : YoungDiagram) :
    Fintype.card (Tabloid μ)*Fintype.card (rowGroup μ) = μ.card.factorial := by
  have hh := MulAction.card_orbit_mul_card_stabilizer_eq_card_group
    (Equiv.Perm (Cell μ)) (baseTabloid μ)
  have hc : Fintype.card (MulAction.orbit (Equiv.Perm (Cell μ)) (baseTabloid μ)) =
      Fintype.card (Tabloid μ) := by
    rw [tabloid_orbit_all,Fintype.card_setUniv]
  simpa only [hc,tabloid_stabilizer,Fintype.card_perm,card_cell] using hh

theorem factorial_le_dimension_row_column (μ : YoungDiagram) :
    μ.card.factorial ≤ Module.finrank ℂ (space μ)*Fintype.card (rowGroup μ)*Fintype.card (colGroup μ) := by
  rw [←card_tabloid_mul_row]
  nlinarith [dimension_times_column_ge_tabloids μ]


end Thorp.Specht

namespace Thorp.UnitaryFinite
open scoped BigOperators ComplexConjugate Classical

variable {G : Type*} [Group G] [Fintype G]
variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]

omit [Fintype G] [FiniteDimensional ℂ V] in
lemma unitary_inner_inv (ρ : Representation ℂ G V) (hρ : IsUnitary ρ) (g : G) (v w : V) :
    inner ℂ v (ρ g⁻¹ w) = inner ℂ (ρ g v) w := by
  have h := hρ g v (ρ g⁻¹ w)
  have he : ρ g (ρ g⁻¹ w) = w := by
    change (ρ g * ρ g⁻¹) w = w
    rw [←map_mul,mul_inv_cancel,map_one]
    rfl
  rw [he] at h
  exact h.symm

end Thorp.UnitaryFinite

end ThorpNine.Adaptive

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Adaptive_Representative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Adaptive

namespace Thorp.UnitaryFinite
open scoped BigOperators ComplexConjugate Classical
variable {G : Type*} [Group G] [Fintype G]
variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
omit [FiniteDimensional ℂ V] in
lemma averageMap_self_trace (ρ : Representation ℂ G V) (A : Module.End ℂ V) :
    LinearMap.trace ℂ V (averageMap ρ ρ A).toLinearMap =
      (Fintype.card G:ℂ) * LinearMap.trace ℂ V A := by
  change LinearMap.trace ℂ V (∑ g, ρ g * A * ρ g⁻¹) = _
  rw [map_sum]
  have hj (g : G) : LinearMap.trace ℂ V (ρ g*A*ρ g⁻¹) = LinearMap.trace ℂ V A := by
    rw [LinearMap.trace_mul_cycle,←map_mul,inv_mul_cancel,map_one,one_mul]
  simp only [hj,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]

lemma averageMap_scalar (ρ : Representation ℂ G V) [Representation.IsIrreducible ρ]
    (A : Module.End ℂ V) :
    ∃ c : ℂ, (averageMap ρ ρ A).toLinearMap = c • LinearMap.id ∧
      c * (Module.finrank ℂ V:ℂ) = (Fintype.card G:ℂ)*LinearMap.trace ℂ V A := by
  obtain ⟨c,hc⟩ := (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed (ρ := ρ)).surjective (averageMap ρ ρ A)
  have he : (averageMap ρ ρ A).toLinearMap = c • LinearMap.id := by
    rw [←hc]
    rfl
  refine ⟨c,he,?_⟩
  rw [←averageMap_self_trace ρ A,he,map_smul,LinearMap.trace_id,smul_eq_mul]

theorem coefficient_orthogonality (ρ : Representation ℂ G V) [Representation.IsIrreducible ρ]
    (hρ : IsUnitary ρ) (u v w z : V) :
    (Module.finrank ℂ V:ℂ) * ∑ g, inner ℂ u (ρ g v) * inner ℂ (ρ g w) z =
      (Fintype.card G:ℂ) * inner ℂ w v * inner ℂ u z := by
  obtain ⟨c,hc,htrace⟩ := averageMap_scalar ρ (InnerProductSpace.rankOne ℂ v w).toLinearMap
  rw [InnerProductSpace.trace_rankOne] at htrace
  have happ := congrArg (fun A : Module.End ℂ V => inner ℂ u (A z)) hc
  change inner ℂ u ((∑ g, ρ g * (InnerProductSpace.rankOne ℂ v w).toLinearMap * ρ g⁻¹) z) = _ at happ
  simp only [LinearMap.sum_apply,Module.End.mul_apply,ContinuousLinearMap.coe_coe,
    InnerProductSpace.rankOne_apply,map_smul,unitary_inner_inv ρ hρ,inner_sum,
    inner_smul_right,LinearMap.smul_apply,LinearMap.id_apply] at happ
  have hsum : ∑ g, inner ℂ u (ρ g v) * inner ℂ (ρ g w) z = c * inner ℂ u z := by
    simpa only [mul_comm] using happ
  rw [hsum]
  calc
    _ = (c*(Module.finrank ℂ V:ℂ))*inner ℂ u z := by ring
    _ = _ := by rw [htrace]

end Thorp.UnitaryFinite
namespace Thorp.UnitaryFinite
open scoped BigOperators ComplexConjugate Classical

variable {G X : Type*} [Group G] [Fintype G] [Fintype X]
  (a : G →* Equiv.Perm X) (x₀ : X) (ha : ∀ x, ∃ g, a g x₀=x)

omit [Fintype G] [Fintype X] in
lemma representative_apply (x : X) : a (representative a x₀ ha x) x₀=x :=
  Classical.choose_spec (ha x)

include ha in
lemma orbit_sum (F : X → ℂ) :
    (Fintype.card X:ℂ)*∑ g, F (a g x₀) = (Fintype.card G:ℂ)*∑ x, F x := by
  have ht (x : X) : ∑ g, F (a g x)=∑ g, F (a g x₀) := by
    obtain ⟨t,rfl⟩ := ha x
    symm
    apply Fintype.sum_equiv (Equiv.mulRight t⁻¹)
    intro g
    simp
  calc
    _ = ∑ x : X, ∑ g : G, F (a g x) := by simp only [ht,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    _ = ∑ g : G, ∑ x : X, F (a g x) := Finset.sum_comm
    _ = ∑ g : G, ∑ x : X, F x := by
      apply Finset.sum_congr rfl
      intro g _
      exact Equiv.sum_comp (a g) F
    _ = _ := by simp

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V)

omit [Fintype G] [Fintype X] [FiniteDimensional ℂ V] in
lemma coefficient_at (w : V) (hw : IsFixed a x₀ ρ w) (v : V) (g : G) :
    coefficient a x₀ ha ρ w v (a g x₀) = inner ℂ (ρ g w) v := by
  let r := representative a x₀ ha (a g x₀)
  have hr : a r x₀=a g x₀ := representative_apply a x₀ ha _
  have hs : a (g⁻¹*r) x₀=x₀ := by
    simp only [map_mul,Equiv.Perm.mul_apply]
    rw [hr,←Equiv.Perm.mul_apply,←map_mul,inv_mul_cancel,map_one]
    rfl
  have he := congrArg (ρ g) (hw (g⁻¹*r) hs)
  have hh : ρ r w=ρ g w := by
    simpa only [map_mul,Module.End.mul_apply,←Module.End.mul_apply,←map_mul,
      mul_inv_cancel_left] using he
  change inner ℂ (ρ r w) v= _
  rw [hh]

lemma coefficient_inner [Representation.IsIrreducible ρ] (hρ : IsUnitary ρ)
    (w z : V) (hw : IsFixed a x₀ ρ w) (hz : IsFixed a x₀ ρ z) (v t : V) :
    (Module.finrank ℂ V:ℂ)*inner ℂ (coefficient a x₀ ha ρ w v) (coefficient a x₀ ha ρ z t) =
      (Fintype.card X:ℂ)*inner ℂ z w*inner ℂ v t := by
  have hs := orbit_sum a x₀ ha (fun x => star (coefficient a x₀ ha ρ w v x)*coefficient a x₀ ha ρ z t x)
  simp only [coefficient_at a x₀ ha ρ w hw,coefficient_at a x₀ ha ρ z hz] at hs
  simp only [←starRingEnd_apply,inner_conj_symm] at hs
  simp only [starRingEnd_apply] at hs
  have ho := coefficient_orthogonality ρ hρ v w z t
  have hcard : (Fintype.card G:ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  apply mul_left_cancel₀ hcard
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply,starRingEnd_apply]
  have hsum : ∑ x, coefficient a x₀ ha ρ z t x * star (coefficient a x₀ ha ρ w v x) =
      ∑ x, star (coefficient a x₀ ha ρ w v x)*coefficient a x₀ ha ρ z t x := by
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [hsum]
  calc
    _ = (Module.finrank ℂ V:ℂ)*((Fintype.card G:ℂ)*∑ x,
        star (coefficient a x₀ ha ρ w v x)*coefficient a x₀ ha ρ z t x) := by ring
    _ = (Fintype.card X:ℂ)*((Module.finrank ℂ V:ℂ)*∑ g,
        inner ℂ v (ρ g w)*inner ℂ (ρ g z) t) := by rw [←hs]; ring
    _ = _ := by rw [ho]; ring

omit [Fintype G] [Fintype X] [FiniteDimensional ℂ V] in
lemma coefficient_action (hρ : IsUnitary ρ) (w : V) (hw : IsFixed a x₀ ρ w)
    (v : V) (g : G) (x : X) :
    coefficient a x₀ ha ρ w v (a g x) = coefficient a x₀ ha ρ w (ρ g⁻¹ v) x := by
  obtain ⟨r,rfl⟩ := ha x
  rw [←Equiv.Perm.mul_apply,←map_mul,coefficient_at a x₀ ha ρ w hw,
    coefficient_at a x₀ ha ρ w hw]
  simp only [map_mul,Module.End.mul_apply,unitary_inner_inv ρ hρ]

lemma normalizedCoefficient_inner [Representation.IsIrreducible ρ] (hρ : IsUnitary ρ)
    (w z : V) (hw : IsFixed a x₀ ρ w) (hz : IsFixed a x₀ ρ z) (v t : V) :
    inner ℂ (normalizedCoefficient a x₀ ha ρ w v) (normalizedCoefficient a x₀ ha ρ z t) =
      inner ℂ z w*inner ℂ v t := by
  let : Nonempty X := ⟨x₀⟩
  have hX : (Fintype.card X:ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hs : (Real.sqrt ((Module.finrank ℂ V:ℝ)/(Fintype.card X:ℝ)) : ℂ)^2 =
      (Module.finrank ℂ V:ℂ)/(Fintype.card X:ℂ) := by
    rw [←Complex.ofReal_pow,Real.sq_sqrt (by positivity)]
    simp
  simp only [normalizedCoefficient,inner_smul_left,inner_smul_right]
  simp only [Complex.conj_ofReal]
  rw [←mul_assoc,←pow_two,hs]
  have hi := coefficient_inner a x₀ ha ρ hρ w z hw hz v t
  field_simp
  simpa only [mul_assoc] using hi

lemma normalizedCoefficient_orthonormal [Representation.IsIrreducible ρ] (hρ : IsUnitary ρ)
    {I : Type*} (w : I → V) (hw : Orthonormal ℂ w)
    (hfix : ∀ i, IsFixed a x₀ ρ (w i)) (v : V) (hv : ‖v‖=1) :
    Orthonormal ℂ (fun i => normalizedCoefficient a x₀ ha ρ (w i) v) := by
  rw [orthonormal_iff_ite] at hw ⊢
  intro i j
  rw [normalizedCoefficient_inner a x₀ ha ρ hρ _ _ (hfix i) (hfix j),hw,
    inner_self_eq_norm_sq_to_K,hv]
  simp [eq_comm]

lemma normalizedCoefficient_norm [Representation.IsIrreducible ρ] (hρ : IsUnitary ρ)
    (w : V) (hw : IsFixed a x₀ ρ w) (hn : ‖w‖=1) (v : V) :
    ‖normalizedCoefficient a x₀ ha ρ w v‖=‖v‖ := by
  have he := normalizedCoefficient_inner a x₀ ha ρ hρ w w hw hw v v
  rw [inner_self_eq_norm_sq_to_K,inner_self_eq_norm_sq_to_K,hn] at he
  simp only [inner_self_eq_norm_sq_to_K] at he
  norm_num at he
  have hs : ‖normalizedCoefficient a x₀ ha ρ w v‖^2=‖v‖^2 := by exact_mod_cast he
  nlinarith [norm_nonneg (normalizedCoefficient a x₀ ha ρ w v),norm_nonneg v]

end Thorp.UnitaryFinite

namespace Thorp.UnitaryFinite

section
open scoped BigOperators ComplexConjugate Classical

variable {G : Type*} [Group G] [Fintype G]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

omit [Fintype G] in
lemma continuousRepresentation_adjoint (ρ : Representation ℂ G V) (hρ : IsUnitary ρ) (g : G) :
    (continuousRepresentation ρ g).adjoint=continuousRepresentation ρ g⁻¹ := by
  ext w
  apply ext_inner_left ℂ
  intro v
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact (unitary_inner_inv ρ hρ g v w).symm

end
open scoped BigOperators Classical
variable {G : Type*} [Group G] [Fintype G]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

omit [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] in
lemma minorantGap_pos {p : G → ℝ} (c : FiniteConvolution.Minorant p) : 0 < minorantGap c := by
  have hn : (1:ℝ) ≤ 2^c.exponent := one_le_pow₀ (by norm_num)
  have hq : c.mass/(2*(2:ℝ)^c.exponent) ≤ 1/2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [c.mass_le_one]
  unfold minorantGap
  linarith

omit [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] in
lemma minorantGap_lt_one {p : G → ℝ} (c : FiniteConvolution.Minorant p) : minorantGap c < 1 := by
  unfold minorantGap
  exact sub_lt_self _ (div_pos c.mass_pos (by positivity))

end Thorp.UnitaryFinite

namespace Thorp
open scoped BigOperators Classical

lemma blockGap_pos (d : ℕ) : 0<blockGap d := UnitaryFinite.minorantGap_pos _
lemma blockGap_lt_one (d : ℕ) : blockGap d<1 := UnitaryFinite.minorantGap_lt_one _

end Thorp

end ThorpNine.Adaptive

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Adaptive_BlockProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Adaptive

namespace Thorp.UnitaryFinite
open scoped BigOperators Classical

variable {G : Type*} [Group G] [Fintype G]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
variable {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]

omit [Fintype G] in
lemma sampleOperator_inv (ρ : Representation ℂ G V) (hρ : IsUnitary ρ) (P : Ω → G) :
    sampleOperator ρ (fun ω => (P ω)⁻¹)=(sampleOperator ρ P).adjoint := by
  simp only [sampleOperator,map_smulₛₗ,map_sum,map_inv₀,map_natCast,
    continuousRepresentation_adjoint ρ hρ]

end Thorp.UnitaryFinite

end ThorpNine.Adaptive

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Adaptive_ModifiedStageEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Adaptive

namespace Thorp.UnitaryFinite
open scoped BigOperators ComplexConjugate Classical

variable {G X Ω : Type*} [Group G] [Fintype G] [Fintype X] [Fintype Ω]

omit [Fintype G] in
lemma actionKernel_apply (a : G →* Equiv.Perm X) (P : Ω → G)
    (v : EuclideanSpace ℂ X) (x : X) :
    DensityTransfer.applyKernel (actionKernel a P) v x =
      (Fintype.card Ω:ℂ)⁻¹ * ∑ ω, v (a (P ω) x) := by
  simp only [DensityTransfer.applyKernel_apply,actionKernel,finiteMean,
    Complex.ofReal_sum,div_eq_mul_inv,Finset.sum_mul]
  rw [Finset.sum_comm]
  calc
    _ = ∑ ω, (Fintype.card Ω:ℂ)⁻¹ * ∑ y : X, if a (P ω) x=y then v y else 0 := by
      apply Finset.sum_congr rfl
      intro ω _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      split_ifs <;> simp_all
    _ = _ := by simp [Finset.mul_sum]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

omit [Fintype G] [FiniteDimensional ℂ V] in
lemma coefficient_random (a : G →* Equiv.Perm X) (x₀ : X)
    (ha : ∀ x, ∃ g, a g x₀=x) (ρ : Representation ℂ G V) (hρ : IsUnitary ρ)
    (P : Ω → G) (w : V) (hw : IsFixed a x₀ ρ w) (v : V) :
    DensityTransfer.applyKernel (actionKernel a P) (normalizedCoefficient a x₀ ha ρ w v) =
      normalizedCoefficient a x₀ ha ρ w (randomOperator ρ P v) := by
  ext x
  rw [actionKernel_apply]
  simp only [normalizedCoefficient,PiLp.smul_apply,smul_eq_mul,Finset.mul_sum,
    coefficient,randomOperator,LinearMap.smul_apply,LinearMap.sum_apply,
    inner_smul_right,inner_sum]
  apply Finset.sum_congr rfl
  intro ω _
  have h := coefficient_action a x₀ ha ρ hρ w hw v (P ω) x
  change inner ℂ (ρ (representative a x₀ ha (a (P ω) x)) w) v =
    inner ℂ (ρ (representative a x₀ ha x) w) (ρ (P ω)⁻¹ v) at h
  rw [h]
  ring

theorem operator_amplification (a : G →* Equiv.Perm X) (x₀ : X)
    (ha : ∀ x, ∃ g, a g x₀=x) (ρ : Representation ℂ G V) [Representation.IsIrreducible ρ]
    (hρ : IsUnitary ρ) (P : Ω → G)
    (hsym : ∀ x y, actionKernel a P x y=actionKernel a P y x)
    (hrow : ∀ x, ∑ y, actionKernel a P x y=1)
    (b z M : ℝ) (hb : 0≤b) (hz : 0<z) (hM0 : 0≤M)
    (hM : ∀ x, finiteMean (fun y => ((Fintype.card X:ℝ)*actionKernel a P x y)^(1+b)) ≤ M)
    (hm : 0 < Module.finrank ℂ (fixedSpace a x₀ ρ)) (v : V) (hv : ‖v‖=1) :
    ‖randomOperator ρ P v‖ ≤ M*z^(-b)+Real.sqrt (z/(Module.finrank ℂ (fixedSpace a x₀ ρ):ℝ)) := by
  let K := fixedSpace a x₀ ρ
  let m := Module.finrank ℂ K
  let : Nonempty X := ⟨x₀⟩
  let : Nonempty (Fin m) := ⟨⟨0,hm⟩⟩
  let B := stdOrthonormalBasis ℂ K
  let w : Fin m → V := fun i => (B i : V)
  have hfix (i : Fin m) : IsFixed a x₀ ρ (w i) := (B i).2
  have hw : Orthonormal ℂ w := B.orthonormal.comp_linearIsometry K.subtypeₗᵢ
  have hc := normalizedCoefficient_orthonormal a x₀ ha ρ hρ w hw hfix v hv
  have hn (i : Fin m) : ‖DensityTransfer.applyKernel (actionKernel a P)
      (normalizedCoefficient a x₀ ha ρ (w i) v)‖ = ‖randomOperator ρ P v‖ := by
    rw [coefficient_random a x₀ ha ρ hρ P (w i) (hfix i),
      normalizedCoefficient_norm a x₀ ha ρ hρ (w i) (hfix i) (hw.norm_eq_one i)]
  have h := DensityTransfer.multiplicity_amplification (actionKernel a P)
    (fun x y => finiteMean_nonneg (fun _ => by split_ifs <;> norm_num)) hsym hrow
    b z M hb hz hM0 hM _ hc (‖randomOperator ρ P v‖) (fun i => (hn i).ge)
  simpa only [Fintype.card_fin] using h

end Thorp.UnitaryFinite
namespace Thorp.UnitaryFinite
open scoped BigOperators Classical

variable {α ι : Type*} [Fintype α] [Fintype ι]

omit [Fintype α] in
lemma tupleAction_transitive (e f : ι ↪ α) : ∃ p, tupleAction p e=f := by
  obtain ⟨p,hp⟩ := Equiv.Perm.exists_extending_pair e f e.injective f.injective
  exact ⟨p,Function.Embedding.ext hp⟩

omit [Fintype α] in
lemma tupleAction_kernel [DecidableEq α] {Ω : Type*} [Fintype Ω] (P : Ω → Equiv.Perm α)
    (e f : ι ↪ α) : actionKernel tupleAction P e f=PairRouting.tupleProbability P e f := by
  unfold actionKernel PairRouting.tupleProbability
  congr 1
  funext ω
  congr 1
  exact propext Function.Embedding.ext_iff

end Thorp.UnitaryFinite
namespace Thorp.UnitaryFinite
open scoped BigOperators Classical

lemma irreducible_of_equiv {G V W : Type*} [Group G]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (e : Representation.Equiv ρ σ) [Representation.IsIrreducible ρ] :
    Representation.IsIrreducible σ := by
  rw [Representation.irreducible_iff_isSimpleModule_asModule]
  have hi := (Representation.irreducible_iff_isSimpleModule_asModule ρ).mp inferInstance
  let f : ρ.asModule →ₗ[MonoidAlgebra ℂ G] σ.asModule :=
    Representation.IntertwiningMap.equivLinearMapAsModule ρ σ e.toIntertwiningMap
  have hf : Function.Bijective f := e.toLinearEquiv.bijective
  exact (f.isSimpleModule_iff_of_bijective hf).mp hi

end Thorp.UnitaryFinite

namespace Thorp.Specht
open scoped BigOperators Classical

lemma unitaryRepresentation_irreducible (μ : YoungDiagram) :
    Representation.IsIrreducible (unitaryRepresentation μ) := by
  let := representation_irreducible μ
  exact UnitaryFinite.irreducible_of_equiv _ _ (unitaryEquiv μ)

lemma unitaryRepresentation_unitary (μ : YoungDiagram) :
    UnitaryFinite.IsUnitary (G := Equiv.Perm (Cell μ)) (V := hilbertSpace μ) (unitaryRepresentation μ) := by
  intro p v w
  change inner ℂ (unitaryRepresentation μ p v : PermutationHilbert.H (Tabloid μ))
      (unitaryRepresentation μ p w : PermutationHilbert.H (Tabloid μ)) = _
  rw [unitaryRepresentation_coe,unitaryRepresentation_coe]
  exact (PermutationHilbert.act (tabloidAct p)).inner_map_map v w


end Thorp.Specht
namespace Thorp.UnitaryFinite
open scoped BigOperators Classical

variable {G H X Ω : Type*} [Group G] [Group H] [Fintype G] [Fintype X] [Fintype Ω]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

omit [Fintype G] in
lemma sampleOperator_inv_apply (ρ : Representation ℂ G V) (P : Ω → G) (v : V) :
    sampleOperator ρ (fun ω => (P ω)⁻¹) v=randomOperator ρ P v := by
  simp only [sampleOperator,randomOperator,smul_apply,
    sum_apply,continuousRepresentation_apply,LinearMap.smul_apply,LinearMap.sum_apply]

theorem sampleOperator_amplification (a : G →* Equiv.Perm X) (x₀ : X)
    (ha : ∀ x, ∃ g, a g x₀=x) (ρ : Representation ℂ G V) [Representation.IsIrreducible ρ]
    (hρ : IsUnitary ρ) (P : Ω → G)
    (hsym : ∀ x y, actionKernel a P x y=actionKernel a P y x)
    (hrow : ∀ x, ∑ y, actionKernel a P x y=1)
    (b z M : ℝ) (hb : 0≤b) (hz : 0<z) (hM0 : 0≤M)
    (hM : ∀ x, finiteMean (fun y => ((Fintype.card X:ℝ)*actionKernel a P x y)^(1+b)) ≤ M)
    (hm : 0 < Module.finrank ℂ (fixedSpace a x₀ ρ)) :
    ‖sampleOperator ρ P‖ ≤ M*z^(-b)+Real.sqrt (z/(Module.finrank ℂ (fixedSpace a x₀ ρ):ℝ)) := by
  rw [←ContinuousLinearMap.adjoint.norm_map (sampleOperator ρ P),←sampleOperator_inv ρ hρ]
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro v hv
  rw [sampleOperator_inv_apply]
  exact operator_amplification a x₀ ha ρ hρ P hsym hrow b z M hb hz hM0 hM hm v hv

omit [Fintype G] [Fintype X] [Fintype Ω] [FiniteDimensional ℂ V] in
lemma irreducible_comp_equiv (ρ : Representation ℂ G V) [Representation.IsIrreducible ρ]
    (e : H ≃* G) : Representation.IsIrreducible (ρ.comp e.toMonoidHom) := by
  exact (subrepresentationEquiv ρ e).isSimpleOrder_iff.mpr inferInstance

end Thorp.UnitaryFinite

namespace Thorp.Specht
open scoped BigOperators Classical

variable {α ι : Type*} [Fintype α] [Fintype ι]

omit [Fintype α] in
lemma relabelledUnitary_unitary (μ : YoungDiagram) (e : α ≃ Cell μ) :
    UnitaryFinite.IsUnitary (V := hilbertSpace μ) (relabelledUnitary μ e) := by
  intro g v w
  exact unitaryRepresentation_unitary μ (e.permCongr g) v w

omit [Fintype α] in
lemma relabelledUnitary_irreducible (μ : YoungDiagram) (e : α ≃ Cell μ) :
    Representation.IsIrreducible (relabelledUnitary μ e) := by
  let := unitaryRepresentation_irreducible μ
  exact UnitaryFinite.irreducible_comp_equiv (V := hilbertSpace μ) (unitaryRepresentation μ) e.permCongrHom

end Thorp.Specht


end ThorpNine.Adaptive

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Adaptive_InsertionPerm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Adaptive

namespace Thorp.DimensionEstimates
open scoped BigOperators Classical

lemma amplification_numerical (m u : ℝ) (hm : 1 ≤ m) (hu : u ≤ Real.log m/4000) :
    Real.exp u*(Real.exp (Real.log m/2))^(-(1/1000:ℝ))+
      Real.sqrt (Real.exp (Real.log m/2)/m) ≤ 2*Real.exp (-Real.log m/4000) := by
  have hmp : 0 < m := lt_of_lt_of_le zero_lt_one hm
  have hl : 0≤Real.log m := Real.log_nonneg hm
  have he : Real.exp (Real.log m/2)/m=Real.exp (-Real.log m/2) := by
    calc
      _ = Real.exp (Real.log m/2)/Real.exp (Real.log m) := by rw [Real.exp_log hmp]
      _ = _ := by rw [←Real.exp_sub]; congr 1; ring
  have hs : Real.sqrt (Real.exp (-Real.log m/2))=Real.exp (-Real.log m/4) := by
    rw [Real.sqrt_eq_rpow,Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp]
    congr 1
    ring
  rw [Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp,←Real.exp_add,he,hs]
  have h₁ : u+(Real.log m/2)*(-(1/1000:ℝ))≤ -Real.log m/4000 := by linarith
  have h₂ : -Real.log m/4≤ -Real.log m/4000 := by linarith
  linarith [Real.exp_le_exp.mpr h₁,Real.exp_le_exp.mpr h₂]

lemma amplification_absorb (x : ℝ) (hx : 8000*Real.log 2≤x) :
    2*Real.exp (-x/4000)≤Real.exp (-x/8000) := by
  rw [show (2:ℝ)=Real.exp (Real.log 2) by rw [Real.exp_log (by norm_num)],←Real.exp_add]
  exact Real.exp_le_exp.mpr (by linarith)

lemma amplification_decay (m u : ℝ) (hm : 1 ≤ m) (hu : u ≤ Real.log m/4000)
    (hl : 8000*Real.log 2≤Real.log m) :
    Real.exp u*(Real.exp (Real.log m/2))^(-(1/1000:ℝ))+
      Real.sqrt (Real.exp (Real.log m/2)/m) ≤ Real.exp (-Real.log m/8000) :=
  (amplification_numerical m u hm hu).trans (amplification_absorb _ hl)

end Thorp.DimensionEstimates

namespace Thorp.UnitaryFinite
open scoped BigOperators Classical

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

omit [FiniteDimensional ℂ V] in
lemma full_tuple_fixed (d : ℕ) (ρ : Representation ℂ (Equiv.Perm (Card d)) V) :
    fixedSpace tupleAction (Function.Embedding.refl (Card d)) ρ=⊤ := by
  apply Submodule.eq_top_iff'.mpr
  intro v g hg
  have he : g=1 := by
    apply Equiv.ext
    intro x
    exact congrArg (fun f : Card d ↪ Card d => f x) hg
  rw [he,map_one]
  rfl

omit [FiniteDimensional ℂ V] in
lemma full_tuple_finrank (d : ℕ) (ρ : Representation ℂ (Equiv.Perm (Card d)) V) :
    Module.finrank ℂ (fixedSpace tupleAction (Function.Embedding.refl (Card d)) ρ)=Module.finrank ℂ V := by
  rw [full_tuple_fixed,finrank_top]

theorem palindrome_irrep_amplification (d : ℕ) {ι : Type*} [Fintype ι]
    (f : ι ↪ Card d) (hk : 0<Fintype.card ι)
    (ρ : Representation ℂ (Equiv.Perm (Card d)) V) [Representation.IsIrreducible ρ]
    (hρ : IsUnitary ρ) (hm : 0<Module.finrank ℂ (fixedSpace tupleAction f ρ))
    (z : ℝ) (hz : 0<z) :
    ‖sampleOperator ρ (palindromePerm d)‖ ≤
      Real.exp (densityConstant*Fintype.card ι*((Fintype.card ι:ℝ)/(2:ℝ)^d)^(1/512:ℝ))*
        z^(-(1/1000:ℝ))+Real.sqrt (z/(Module.finrank ℂ (fixedSpace tupleAction f ρ):ℝ)) := by
  apply sampleOperator_amplification tupleAction f (tupleAction_transitive f) ρ hρ
    (palindromePerm d) _ _ (1/1000) z _ (by norm_num) hz (by positivity) _ hm
  · intro e f
    simp only [tupleAction_kernel]
    exact palindrome_kernel_symmetric d e f
  · intro e
    simp only [tupleAction_kernel]
    exact PairRouting.tupleProbability_row_sum _ e
  · intro e
    simp only [tupleAction_kernel]
    exact palindrome_row_moment_bound d e hk

end Thorp.UnitaryFinite

namespace Thorp.DimensionEstimates

section
open scoped BigOperators Classical
open Filter

lemma exists_small_set_rate (κ ε₀ : ℝ) (hκ : 0<κ) (hε₀ : 0<ε₀) :
    ∃ ε : ℝ, 0<ε ∧ ε≤ε₀ ∧ ε<1/2 ∧ ∃ t : ℝ, 0≤t ∧
      t*ε+Real.log (1+Real.exp (-t))≤κ := by
  have ht : Tendsto (fun t : ℝ => Real.log (1+Real.exp (-t))) atTop (nhds 0) := by
    have he : Tendsto (fun t : ℝ => Real.exp (-t)) atTop (nhds 0) :=
      Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
    have hl := (tendsto_const_nhds.add he).log (by norm_num : (1:ℝ)+0≠0)
    simpa only [add_zero,Real.log_one] using hl
  obtain ⟨t,ht,hlog⟩ := ((eventually_ge_atTop (1:ℝ)).and
    (ht.eventually (gt_mem_nhds (by linarith : (0:ℝ)<κ/2)))).exists
  let ε := min ε₀ (min (1/4) (κ/(2*t)))
  have htp : 0<t := by linarith
  have hε : 0<ε := lt_min hε₀ (lt_min (by norm_num) (by positivity))
  refine ⟨ε,hε,min_le_left _ _,(min_le_right _ _).trans_lt ((min_le_left _ _).trans_lt (by norm_num)),t,htp.le,?_⟩
  have hsmall : ε≤κ/(2*t) := (min_le_right _ _).trans (min_le_right _ _)
  have hm := (le_div_iff₀ (by positivity : (0:ℝ)<2*t)).mp hsmall
  linarith

end
open Filter

end Thorp.DimensionEstimates

namespace Thorp.Specht
open scoped BigOperators Classical
open UnitaryFinite DimensionEstimates Filter

lemma dimension_pos (μ : YoungDiagram) : 0 < Module.finrank ℂ (space μ) := by
  have h := factorial_le_dimension_row_column μ
  by_contra hn
  have hz : Module.finrank ℂ (space μ)=0 := by omega
  rw [hz,zero_mul,zero_mul] at h
  exact (Nat.factorial_pos μ.card).not_ge h

end Thorp.Specht

namespace Thorp.UnitaryFinite
open scoped BigOperators Classical
open DimensionEstimates
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

theorem full_palindrome_decay (d : ℕ)
    (ρ : Representation ℂ (Equiv.Perm (Card d)) V) [Representation.IsIrreducible ρ]
    (hρ : IsUnitary ρ) (hm : 0<Module.finrank ℂ V)
    (hden : densityConstant*(2:ℝ)^d≤Real.log (Module.finrank ℂ V)/4000)
    (hl : 8000*Real.log 2≤Real.log (Module.finrank ℂ V)) :
    ‖sampleOperator ρ (palindromePerm d)‖≤Real.exp (-Real.log (Module.finrank ℂ V)/8000) := by
  have h := palindrome_irrep_amplification d (Function.Embedding.refl (Card d))
    (Fintype.card_pos) ρ hρ (by simpa only [full_tuple_finrank] using hm)
    (Real.exp (Real.log (Module.finrank ℂ V)/2)) (Real.exp_pos _)
  simp only [full_tuple_finrank,card_positions,Nat.cast_pow,Nat.cast_ofNat,
    div_self (by positivity : (2:ℝ)^d≠0),Real.one_rpow,mul_one] at h
  exact h.trans (amplification_decay _ _ (by exact_mod_cast hm) hden hl)

end Thorp.UnitaryFinite

namespace Thorp.DimensionEstimates
open scoped BigOperators Classical
open Filter

lemma medium_parameters (h : ℝ) (hh : 0<h) :
    ∃ L : ℕ, 0<L ∧ ∃ ε t : ℝ, 0<ε ∧ ε<1/2 ∧ 0≤t ∧
      t*ε+Real.log (1+Real.exp (-t))≤h*(2:ℝ)^L/16000 ∧
      ∀ᶠ r : ℕ in atTop, ∀ (E : Finset (Card r)), (E.card:ℝ)<ε*(2:ℝ)^r →
        ∀ e : Card (L+r) ↪ Card (L+r),
          modifiedRowMoment L r E e (1/1000)≤Real.exp ((h/4000)*(2:ℝ)^(L+r)) := by
  obtain ⟨L,hL,ε₀,hε₀,_,hM⟩ := modified_arbitrarily_small_rate (h/4000) (by positivity)
  obtain ⟨ε,hε,hεle,hεhalf,t,ht,hcount⟩ := exists_small_set_rate
    (h*(2:ℝ)^L/16000) ε₀ (by positivity) hε₀
  refine ⟨L,hL,ε,t,hε,hεhalf,ht,hcount,?_⟩
  filter_upwards [hM] with r hM
  intro E hE e
  exact hM E (hE.le.trans (mul_le_mul_of_nonneg_right hεle (by positivity))) e

end Thorp.DimensionEstimates

end ThorpNine.Adaptive

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Adaptive_TailShapes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Adaptive

namespace Thorp.DimensionEstimates
open Filter

lemma twopow_tendsto : Tendsto (fun d : ℕ => (2:ℝ)^d) atTop atTop :=
  tendsto_pow_atTop_atTop_of_one_lt (by norm_num)

lemma twopow_mul_eventually (c : ℝ) (hc : 0 < c) (B : ℝ) :
    ∀ᶠ d : ℕ in atTop, B ≤ c*(2:ℝ)^d := by
  filter_upwards [twopow_tendsto.eventually (eventually_ge_atTop (B/c))] with d hd
  exact (div_le_iff₀ hc).mp hd |>.trans_eq (mul_comm _ _)

lemma exp_two_absorb (β n : ℝ) (hx : Real.log 2≤β*n/2) :
    Real.exp (-β*n)+Real.exp (-β*n)≤Real.exp (-β*n/2) := by
  calc
    _ = Real.exp (Real.log 2-β*n) := by rw [Real.exp_sub,Real.exp_log (by norm_num)]; rw [neg_mul,Real.exp_neg]; ring
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

end Thorp.DimensionEstimates
namespace Thorp.Specht
open scoped BigOperators Classical
open Filter UnitaryFinite DimensionEstimates

theorem exponential_dimension_spectral_q77_oai (h : ℝ) (hh : 0<h) :
    ∃ a : ℝ, 0<a ∧ ∀ᶠ d : ℕ in atTop, ∀ (μ : YoungDiagram) (e : Card d ≃ Cell μ),
      h*(2:ℝ)^d≤Real.log (Module.finrank ℂ (space μ)) →
      ‖sampleOperator (V := hilbertSpace μ) (relabelledUnitary μ e) (palindromePerm d)‖ ≤
        Real.exp (-a*Real.log (Module.finrank ℂ (space μ))) := by
  obtain ⟨L,hL,ε,t,hε,_,ht,hcount,hM⟩ := medium_parameters h hh
  obtain ⟨R,hR⟩ := eventually_atTop.mp hM
  let A := 4000*densityConstant+1
  have hA : 0<A := by dsimp [A]; have := densityConstant_pos; positivity
  let β := min (-Real.log (blockGap L)*ε/(2:ℝ)^L) (h/16000)
  have hβ : 0<β := by
    apply lt_min
    · exact div_pos (mul_pos (neg_pos.mpr (Real.log_neg (blockGap_pos L) (blockGap_lt_one L))) hε) (by positivity)
    · positivity
  let a := min (1/8000:ℝ) (β/(2*A))
  have ha : 0<a := lt_min (by norm_num) (div_pos hβ (by positivity))
  refine ⟨a,ha,?_⟩
  filter_upwards [eventually_ge_atTop (L+R),twopow_mul_eventually h hh (8000*Real.log 2),
    twopow_mul_eventually (β/2) (by positivity) (Real.log 2)] with d hd hl hb
  intro μ e hdim
  let : NormedAddCommGroup (hilbertSpace μ) := inferInstance
  let : InnerProductSpace ℂ (hilbertSpace μ) := inferInstance
  let : FiniteDimensional ℂ (hilbertSpace μ) := inferInstance
  let := relabelledUnitary_irreducible μ e
  have hpos : 0<Module.finrank ℂ (hilbertSpace μ) := by rw [finrank_hilbertSpace]; exact dimension_pos μ
  have hlarge : 8000*Real.log 2≤Real.log (Module.finrank ℂ (hilbertSpace μ)) := by rw [finrank_hilbertSpace]; exact hl.trans hdim
  have hlog : 0≤Real.log (Module.finrank ℂ (space μ)) := (by positivity : (0:ℝ)≤h*(2:ℝ)^d).trans hdim
  by_cases hhigh : A*(2:ℝ)^d≤Real.log (Module.finrank ℂ (space μ))
  · have hden : densityConstant*(2:ℝ)^d≤Real.log (Module.finrank ℂ (hilbertSpace μ))/4000 := by
      rw [finrank_hilbertSpace]
      dsimp [A] at hhigh
      nlinarith [pow_pos (by norm_num : (0:ℝ)<2) d]
    have hspec := @full_palindrome_decay (hilbertSpace μ) _ _ _ d (relabelledUnitary μ e)
      inferInstance (relabelledUnitary_unitary μ e) hpos hden hlarge
    rw [finrank_hilbertSpace] at hspec
    apply hspec.trans (Real.exp_le_exp.mpr ?_)
    have := min_le_left (1/8000:ℝ) (β/(2*A))
    nlinarith
  · obtain ⟨r,rfl⟩ := Nat.exists_eq_add_of_le (show L≤d by omega)
    have hr : R ≤ r := by omega
    have hdim' : h*(2:ℝ)^(L+r)≤Real.log (Module.finrank ℂ (hilbertSpace μ)) := by rwa [finrank_hilbertSpace]
    have hs := @medium_exception_decay_q77 (hilbertSpace μ) _ _ _ L r h ε t ht hcount
      (relabelledUnitary μ e) inferInstance (relabelledUnitary_unitary μ e) hpos hdim' hlarge (hR r hr)
    have hb1 : Real.log (blockGap L)*ε*(2:ℝ)^r≤-β*(2:ℝ)^(L+r) := by
      have hb0 := min_le_left (-Real.log (blockGap L)*ε/(2:ℝ)^L) (h/16000)
      have hp := (le_div_iff₀ (by positivity : (0:ℝ)<(2:ℝ)^L)).mp hb0
      have hp := mul_le_mul_of_nonneg_right hp (by positivity : (0:ℝ)≤(2:ℝ)^r)
      rw [pow_add]
      dsimp [β]
      nlinarith
    have hb2 : -h*(2:ℝ)^(L+r)/16000≤-β*(2:ℝ)^(L+r) := by
      have hp := mul_le_mul_of_nonneg_right (min_le_right (-Real.log (blockGap L)*ε/(2:ℝ)^L) (h/16000))
        (by positivity : (0:ℝ)≤(2:ℝ)^(L+r))
      dsimp [β]
      linarith
    apply hs.trans ((add_le_add (Real.exp_le_exp.mpr hb1) (Real.exp_le_exp.mpr hb2)).trans ?_)
    apply (exp_two_absorb β ((2:ℝ)^(L+r)) (by nlinarith)).trans
    apply Real.exp_le_exp.mpr
    have hdmax := le_of_not_ge hhigh
    have hp := mul_le_mul_of_nonneg_left hdmax (by positivity : 0≤β/(2*A))
    have he : β/(2*A)*(A*(2:ℝ)^(L+r))=β*(2:ℝ)^(L+r)/2 := by field_simp
    rw [he] at hp
    have hba := mul_le_mul_of_nonneg_right (min_le_right (1/8000:ℝ) (β/(2*A))) hlog
    dsimp [a] at *
    linarith


end Thorp.Specht

end ThorpNine.Adaptive

end OAI
end

theorem solution : type_of% @OAI.ThorpNine.Adaptive.Thorp.Specht.exponential_dimension_spectral_q77_oai := @OAI.ThorpNine.Adaptive.Thorp.Specht.exponential_dimension_spectral_q77_oai
