-- Prove2me | solution 1 for OAI.ThorpNine.Casimir.Thorp.CasimirBounds.trace_bound_q77
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:07:04.265868+00:00
-- url     : https://prove2.me/submissions/bbc0d4d6-9c1d-4e05-a2d2-639fc57196e3

import Mathlib
import Definitions.Def_ThorpRouting
import Definitions.Def_OAIQ077T003

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
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Casimir_Distance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Casimir

namespace Thorp

open scoped BigOperators
open Filter

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

end ThorpNine.Casimir

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Casimir_ExposedCoins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Casimir

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

end ThorpNine.Casimir

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Casimir_RotationMeeting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Casimir

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

end ThorpNine.Casimir

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Casimir_AssignmentSlots
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Casimir

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

end ThorpNine.Casimir

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Casimir_PriorPaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Casimir

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

end ThorpNine.Casimir

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Casimir_ParallelFollow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Casimir

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

section ParallelFairLayer
variable {β : Type*} [Fintype β] [DecidableEq β]

lemma finiteMean_comm {Ω Ω' : Type*} [Fintype Ω] [Fintype Ω'] (f : Ω → Ω' → ℝ) :
    finiteMean (fun x => finiteMean (f x)) = finiteMean (fun y => finiteMean (fun x => f x y)) := by
  simp only [finiteMean,←Finset.sum_div,div_div]
  rw [Finset.sum_comm,mul_comm]

end ParallelFairLayer

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

end ThorpNine.Casimir

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Casimir_AlternatingPerm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Casimir

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

end PairRouting
end Thorp

end ThorpNine.Casimir

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Casimir_SandwichShuffle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Casimir

namespace Thorp
open scoped BigOperators
open Filter
namespace PairRouting
variable {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α] [DecidableEq ι]

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

end Thorp

end ThorpNine.Casimir

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Casimir_CutoffMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Casimir

namespace Thorp

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


lemma palindromeSlabCost_gt (l d : ℕ) (h : d ≤ l) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (ω : BenesCoins d) : palindromeSlabCost l d e ω = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  exact palindromeLevelCost_gt _ _ (by omega) _ _

end Thorp

end ThorpNine.Casimir

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Casimir_PalindromeFamilyCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Casimir

namespace Thorp

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

end Thorp

end ThorpNine.Casimir

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Casimir_ModifiedRoutingMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Casimir

namespace Thorp


namespace DensityTransfer
open scoped BigOperators

lemma applyKernel_apply {X : Type*} [Fintype X] (P : X → X → ℝ)
    (v : EuclideanSpace ℂ X) (x : X) :
    applyKernel P v x = ∑ y, (P x y : ℂ)*v y := rfl

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

end ThorpNine.Casimir

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Casimir_ModifiedReverseCoins
attribute [-instance] _root_.OAI.ThorpNine.Casimir.Thorp.Specht.tabloidMulAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Casimir

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

lemma alternator_apply_action (C : Subgroup (Equiv.Perm α))
    (ρ : Representation ℂ (Equiv.Perm α) V) (c : C) (v : V) :
    alternator C ρ (ρ c v) = permSign (c : Equiv.Perm α) • alternator C ρ v := by
  exact congrArg (fun T : Module.End ℂ V => T v) (alternator_mul C ρ c)

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

end ThorpNine.Casimir

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Casimir_Shapes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Casimir

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

end
open scoped BigOperators Classical

variable {X : Type*} [Fintype X]

lemma trace_projection_real (W : Submodule ℂ (H X)) :
    ∑ x, ‖W.starProjection (EuclideanSpace.single x (1:ℂ))‖^2 = (Module.finrank ℂ W:ℝ) := by
  have hh := trace_projection W
  simp_rw [projection_diagonal] at hh
  exact_mod_cast hh

theorem footprint_dimension (W K : Submodule ℂ (H X)) (hKW : K ≤ W)
    (htrans : ∀ x y : X, ∃ p : Equiv.Perm X, p x = y ∧
      W.map (act p).toLinearEquiv.toLinearMap = W)
    (S : Finset X) (hS : ∀ x ∈ S, W.starProjection (EuclideanSpace.single x (1:ℂ)) ∈ K) :
    (S.card:ℝ) * (Module.finrank ℂ W:ℝ) ≤
      (Fintype.card X:ℝ) * (Module.finrank ℂ K:ℝ) := by
  have he (x : X) (hx : x ∈ S) :
      K.starProjection (EuclideanSpace.single x (1:ℂ)) =
        W.starProjection (EuclideanSpace.single x (1:ℂ)) := by
    apply K.eq_starProjection_of_mem_of_inner_eq_zero (hS x hx)
    intro v hv
    exact W.starProjection_inner_eq_zero _ v (hKW hv)
  have hs : ∑ x ∈ S, ‖W.starProjection (EuclideanSpace.single x (1:ℂ))‖^2 ≤
      (Module.finrank ℂ K:ℝ) := by
    rw [←trace_projection_real K]
    calc
      _ = ∑ x ∈ S, ‖K.starProjection (EuclideanSpace.single x (1:ℂ))‖^2 := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [he x hx]
      _ ≤ _ := Finset.sum_le_univ_sum_of_nonneg (fun x => sq_nonneg _)
  have hmul := mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg (Fintype.card X): (0:ℝ) ≤ _)
  rw [Finset.mul_sum] at hmul
  simp_rw [uniform_diagonal W htrans] at hmul
  simpa using hmul

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

lemma tail_card (μ : YoungDiagram) : Fintype.card (Tail μ) = μ.card - μ.rowLen 0 := by
  have hh := Fintype.card_subtype_compl (p := fun x : Cell μ => row x=0)
  rw [Fintype.card_congr (rowEquiv μ 0),Fintype.card_fin,card_cell] at hh
  exact hh


lemma exists_perm_mem_iff {α : Type*} [Fintype α] (s t : Finset α) (hc : s.card=t.card) :
    ∃ p : Equiv.Perm α, ∀ x, p x ∈ t ↔ x ∈ s := by
  let e : s ≃ t := Finset.equivOfCardEq hc
  let ec : {x : α // x ∉ s} ≃ {x : α // x ∉ t} := Fintype.equivOfCardEq (by
    simp only [Fintype.card_subtype_compl,Fintype.card_coe,hc])
  let p := (Equiv.sumCompl (· ∈ s)).symm.trans ((Equiv.sumCongr e ec).trans (Equiv.sumCompl (· ∈ t)))
  refine ⟨p,fun x => ?_⟩
  by_cases hx : x ∈ s
  · have hp : p x ∈ t := by
      change ((Equiv.sumCompl (· ∈ t)) ((Equiv.sumCongr e ec) ((Equiv.sumCompl (· ∈ s)).symm x))) ∈ t
      rw [Equiv.sumCompl_symm_apply_of_pos hx]
      exact (e ⟨x,hx⟩).2
    exact iff_of_true hp hx
  · have hp : p x ∉ t := by
      change ((Equiv.sumCompl (· ∈ t)) ((Equiv.sumCongr e ec) ((Equiv.sumCompl (· ∈ s)).symm x))) ∉ t
      rw [Equiv.sumCompl_symm_apply_of_neg hx]
      exact (ec ⟨x,hx⟩).2
    exact iff_of_false hp hx

lemma tailSet_act {μ : YoungDiagram} (p : Equiv.Perm (Cell μ)) (f : Tabloid μ) :
    tailSet (tabloidAct p f) = (tailSet f).image p := by
  ext x
  simp only [mem_tailSet,tabloidAct_apply,Finset.mem_image]
  constructor
  · intro h; exact ⟨p⁻¹ x,h,by simp⟩
  · rintro ⟨y,hy,rfl⟩; simpa using hy

lemma card_tailSet {μ : YoungDiagram} (f : Tabloid μ) :
    (tailSet f).card = μ.card-μ.rowLen 0 := by
  obtain ⟨p,rfl⟩ := tabloidAct_transitive μ (baseTabloid μ) f
  rw [tailSet_act,Finset.card_image_of_injective _ p.injective]
  change (Finset.univ.filter (fun x : Cell μ => row x ≠ 0)).card = _
  rw [←Fintype.card_subtype]
  exact tail_card μ

lemma tail_fiber_card_eq (μ : YoungDiagram) (s t : Finset (Cell μ)) (hst : s.card=t.card) :
    (Finset.univ.filter (fun f : Tabloid μ => tailSet f=s)).card =
      (Finset.univ.filter (fun f : Tabloid μ => tailSet f=t)).card := by
  obtain ⟨p,hp⟩ := exists_perm_mem_iff s t hst
  have he : s.image p=t := by
    ext x
    constructor
    · intro hx
      obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
      exact (hp y).mpr hy
    · intro hx
      exact Finset.mem_image.mpr ⟨p⁻¹ x,(hp (p⁻¹ x)).mp (by simpa using hx),by simp⟩
  apply Finset.card_equiv (tabloidAct p)
  intro f
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,tailSet_act,←he]
  exact (Finset.image_inj p.injective).symm

lemma footprint_card_product (μ : YoungDiagram) (A : Finset (Cell μ)) :
    (footprint μ A).card * μ.card.choose (μ.card-μ.rowLen 0) =
      Fintype.card (Tabloid μ) * A.card.choose (μ.card-μ.rowLen 0) := by
  let j := μ.card-μ.rowLen 0
  let s := tailSet (baseTabloid μ)
  let c := (Finset.univ.filter (fun f : Tabloid μ => tailSet f=s)).card
  have hconstant (t : Finset (Cell μ)) (ht : t.card=j) :
      (Finset.univ.filter (fun f : Tabloid μ => tailSet f=t)).card = c :=
    tail_fiber_card_eq μ t s (ht.trans (card_tailSet _).symm)
  have hcount (A : Finset (Cell μ)) : (footprint μ A).card = A.card.choose j*c := by
    have h := Finset.sum_card_fiberwise_eq_card_filter
      (Finset.univ : Finset (Tabloid μ)) (A.powersetCard j) tailSet
    have he : (Finset.univ.filter (fun f : Tabloid μ => tailSet f ∈ A.powersetCard j)) = footprint μ A := by
      ext f
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_powersetCard,
        card_tailSet,footprint]
      simp [j]
    rw [he] at h
    rw [←h]
    calc
      _ = ∑ _t ∈ A.powersetCard j, c := by
        apply Finset.sum_congr rfl
        intro t ht
        exact hconstant t (Finset.mem_powersetCard.mp ht).2
      _ = _ := by simp [Finset.card_powersetCard]
  have hfull : (footprint μ Finset.univ).card = Fintype.card (Tabloid μ) := by
    simp only [footprint,Finset.subset_univ,Finset.filter_true,Finset.card_univ]
  have hN := hcount Finset.univ
  rw [hfull,Finset.card_univ,card_cell] at hN
  rw [hcount,hN]
  ring

lemma footprint_fixed {μ : YoungDiagram} (A : Finset (Cell μ))
    (f : Tabloid μ) (hf : f ∈ footprint μ A) (p : Equiv.Perm (Cell μ))
    (hp : ∀ x ∈ A, p x=x) : tabloidAct p f=f := by
  have htail : tailSet f ⊆ A := (Finset.mem_filter.mp hf).2
  apply Subtype.ext
  funext x
  change f.1 (p⁻¹ x) = f.1 x
  by_cases hx : x ∈ A
  · rw [show p⁻¹ x=x from p.injective (by simpa using (hp x hx).symm)]
  · have hy : p⁻¹ x ∉ A := by
      intro h
      have hh := hp (p⁻¹ x) h
      have he : x=p⁻¹ x := by simpa using hh
      exact hx (he ▸ h)
    apply Fin.ext
    have hx0 : (f.1 x).val=0 := by by_contra h; exact hx (htail (mem_tailSet f x |>.mpr h))
    have hy0 : (f.1 (p⁻¹ x)).val=0 := by by_contra h; exact hy (htail (mem_tailSet f _ |>.mpr h))
    exact hy0.trans hx0.symm

lemma fixedHilbert_le (μ : YoungDiagram) (A : Finset (Cell μ)) : fixedHilbert μ A ≤ hilbertSpace μ :=
  fun _ hv => hv.1

theorem fixedHilbert_dimension (μ : YoungDiagram) (A : Finset (Cell μ)) :
    Module.finrank ℂ (space μ) * A.card.choose (μ.card-μ.rowLen 0) ≤
      Module.finrank ℂ (fixedHilbert μ A) * μ.card.choose (μ.card-μ.rowLen 0) := by
  let : DecidableEq (Tabloid μ) := Classical.decEq _
  have ht (f g : Tabloid μ) : ∃ p : Equiv.Perm (Tabloid μ), p f=g ∧
      (hilbertSpace μ).map (PermutationHilbert.act p).toLinearEquiv.toLinearMap = hilbertSpace μ := by
    obtain ⟨p,hp⟩ := tabloidAct_transitive μ f g
    exact ⟨tabloidAct p,hp,hilbertSpace_invariant μ p⟩
  have hproj (f : Tabloid μ) (hf : f ∈ footprint μ A) :
      (hilbertSpace μ).starProjection (EuclideanSpace.single f (1:ℂ)) ∈ fixedHilbert μ A := by
    refine ⟨((hilbertSpace μ).orthogonalProjectionOnto _).2,fun p hp => ?_⟩
    rw [PermutationHilbert.projection_comm _ _ (hilbertSpace_invariant μ p),
      PermutationHilbert.act_single,footprint_fixed A f hf p hp]
  have h := PermutationHilbert.footprint_dimension (hilbertSpace μ) (fixedHilbert μ A)
    (fixedHilbert_le μ A) ht (footprint μ A) hproj
  rw [finrank_hilbertSpace] at h
  have hn : (footprint μ A).card * Module.finrank ℂ (space μ) ≤
      Fintype.card (Tabloid μ)*Module.finrank ℂ (fixedHilbert μ A) := by exact_mod_cast h
  have hc := footprint_card_product μ A
  have hpos : 0 < Fintype.card (Tabloid μ) := Fintype.card_pos_iff.mpr ⟨baseTabloid μ⟩
  have hh := Nat.mul_le_mul_right (μ.card.choose (μ.card-μ.rowLen 0)) hn
  nlinarith

end Thorp.Specht

end ThorpNine.Casimir

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Casimir_AverageMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Casimir

namespace Thorp.UnitaryFinite
open scoped BigOperators ComplexConjugate Classical

variable {G X : Type*} [Group G] [Fintype G] [Fintype X]
  (a : G →* Equiv.Perm X) (x₀ : X) (ha : ∀ x, ∃ g, a g x₀=x)

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V)

omit [Fintype G] [Fintype X] [FiniteDimensional ℂ V] in
lemma coefficient_action (hρ : IsUnitary ρ) (w : V) (hw : IsFixed a x₀ ρ w)
    (v : V) (g : G) (x : X) :
    coefficient a x₀ ha ρ w v (a g x) = coefficient a x₀ ha ρ w (ρ g⁻¹ v) x := by
  obtain ⟨r,rfl⟩ := ha x
  rw [←Equiv.Perm.mul_apply,←map_mul,coefficient_at a x₀ ha ρ w hw,
    coefficient_at a x₀ ha ρ w hw]
  simp only [map_mul,Module.End.mul_apply,unitary_inner_inv ρ hρ]

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

omit [Fintype G] [FiniteDimensional ℂ V] in
lemma unitary_norm (ρ : Representation ℂ G V) (hρ : IsUnitary ρ) (g : G) (v : V) :
    ‖ρ g v‖=‖v‖ := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ),hρ,norm_eq_sqrt_re_inner (𝕜 := ℂ)]

omit [Fintype G] in
lemma continuousRepresentation_norm_le (ρ : Representation ℂ G V) (hρ : IsUnitary ρ) (g : G) :
    ‖continuousRepresentation ρ g‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  simp only [continuousRepresentation_apply,unitary_norm ρ hρ,one_mul,le_refl]

omit [Fintype G] in
lemma continuousRepresentation_adjoint (ρ : Representation ℂ G V) (hρ : IsUnitary ρ) (g : G) :
    (continuousRepresentation ρ g).adjoint=continuousRepresentation ρ g⁻¹ := by
  ext w
  apply ext_inner_left ℂ
  intro v
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact (unitary_inner_inv ρ hρ g v w).symm

lemma weightedOperator_norm_le (ρ : Representation ℂ G V) (hρ : IsUnitary ρ)
    (p : G → ℝ) (hp : ∀ g, 0≤p g) : ‖weightedOperator ρ p‖ ≤ ∑ g, p g := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro g _
  rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hp g)]
  exact mul_le_of_le_one_right (hp g) (continuousRepresentation_norm_le ρ hρ g)

end
open scoped BigOperators Classical

end Thorp.UnitaryFinite

end ThorpNine.Casimir

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Casimir_BlockProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Casimir

namespace Thorp.UnitaryFinite
open scoped BigOperators Classical

variable {G : Type*} [Group G] [Fintype G]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
variable {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]

lemma sampleOperator_weighted (ρ : Representation ℂ G V) (P : Ω → G) :
    sampleOperator ρ P=weightedOperator ρ (sampleLaw P) := by
  unfold sampleOperator weightedOperator sampleLaw finiteMean
  simp only [Complex.ofReal_sum,div_eq_mul_inv,Finset.sum_mul,Finset.sum_smul]
  rw [Finset.sum_comm]
  simp only [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  calc
    _ = ∑ g, if P ω=g then (Fintype.card Ω:ℂ)⁻¹ • continuousRepresentation ρ g else 0 := by
      symm
      simp only [Finset.sum_ite_eq,Finset.mem_univ,↓reduceIte]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro g _
      split_ifs <;> simp_all

lemma sampleOperator_norm_le [Nonempty Ω] (ρ : Representation ℂ G V) (hρ : IsUnitary ρ) (P : Ω → G) :
    ‖sampleOperator ρ P‖≤1 := by
  rw [sampleOperator_weighted]
  exact (weightedOperator_norm_le ρ hρ _ (sampleLaw_nonneg _)).trans_eq (sampleLaw_sum P)

omit [Fintype G] in
lemma sampleOperator_prod (ρ : Representation ℂ G V) (P : Ω → G) (Q : Ξ → G) :
    sampleOperator ρ (fun ω : Ω × Ξ => P ω.1*Q ω.2)=sampleOperator ρ P*sampleOperator ρ Q := by
  simp only [sampleOperator,Fintype.card_prod,Nat.cast_mul,mul_inv_rev,map_mul,Fintype.sum_prod_type,
    Finset.sum_mul,Finset.mul_sum,smul_mul_smul,Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  apply Finset.sum_congr rfl
  intro ξ _
  rw [mul_comm]

omit [Fintype G] in
lemma sampleOperator_inv (ρ : Representation ℂ G V) (hρ : IsUnitary ρ) (P : Ω → G) :
    sampleOperator ρ (fun ω => (P ω)⁻¹)=(sampleOperator ρ P).adjoint := by
  simp only [sampleOperator,map_smulₛₗ,map_sum,map_inv₀,map_natCast,
    continuousRepresentation_adjoint ρ hρ]

lemma sampleOperator_palindrome (d : ℕ) (ρ : Representation ℂ (Equiv.Perm (Card d)) V)
    (hρ : IsUnitary ρ) :
    sampleOperator ρ (palindromePerm d)=
      sampleOperator ρ (fun ω => butterflyPerm d (decodeButterfly d ω))*
      (sampleOperator ρ (fun ω => butterflyPerm d (decodeButterfly d ω))).adjoint := by
  rw [←sampleOperator_inv ρ hρ,←sampleOperator_prod]
  rfl

end Thorp.UnitaryFinite

end ThorpNine.Casimir

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Casimir_PairAssembleEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Casimir

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


theorem tupleFixed_dimension (μ : YoungDiagram) {ι : Type*} [Fintype ι]
    (e : ι ↪ Cell μ) :
    Module.finrank ℂ (hilbertSpace μ) * (Fintype.card ι).choose (μ.card-μ.rowLen 0) ≤
      Module.finrank ℂ (UnitaryFinite.fixedSpace (V := hilbertSpace μ) UnitaryFinite.tupleAction e (unitaryRepresentation μ)) *
        μ.card.choose (μ.card-μ.rowLen 0) := by
  rw [(tupleFixedEquiv μ e).finrank_eq,finrank_hilbertSpace]
  have h := fixedHilbert_dimension μ (Finset.univ.image e)
  simpa only [Finset.card_image_of_injective _ e.injective,Finset.card_univ] using h

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

omit [Fintype α] in
lemma relabelled_tuple_dimension (μ : YoungDiagram) (e : α ≃ Cell μ) (f : ι ↪ α) :
    Module.finrank ℂ (hilbertSpace μ) * (Fintype.card ι).choose (μ.card-μ.rowLen 0) ≤
      Module.finrank ℂ (UnitaryFinite.fixedSpace (V := hilbertSpace μ) UnitaryFinite.tupleAction f (relabelledUnitary μ e)) *
        μ.card.choose (μ.card-μ.rowLen 0) := by
  rw [(relabelledTupleFixed μ e f).finrank_eq]
  exact tupleFixed_dimension μ (f.trans e.toEmbedding)

end Thorp.Specht

end ThorpNine.Casimir

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Casimir_ZeroExtend
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Casimir

namespace Thorp.DimensionEstimates
open scoped BigOperators

lemma log_factorial_lower (n : ℕ) (hn : 0<n) :
    (n:ℝ)*Real.log n-n+1 ≤ Real.log (n.factorial:ℝ) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have hn0 : (0:ℝ)<n := by exact_mod_cast hn
    have hl := Real.log_le_sub_one_of_pos (show 0<((n:ℝ)+1)/n by positivity)
    rw [Real.log_div (by positivity) hn0.ne'] at hl
    have hh := mul_le_mul_of_nonneg_left hl hn0.le
    have he : (n:ℝ)*(((n:ℝ)+1)/n-1)=1 := by field_simp; ring
    rw [he] at hh
    rw [Nat.factorial_succ,Nat.cast_mul,Real.log_mul (by positivity) (by positivity),Nat.cast_add,Nat.cast_one]
    nlinarith

open scoped Classical

end Thorp.DimensionEstimates

namespace Thorp.DimensionEstimates
open scoped BigOperators Classical


lemma log_choose_upper (N j : ℕ) (hN : 0<N) (hj : j≤N) :
    Real.log (N.choose j:ℝ) ≤ (j:ℝ)*Real.log N-Real.log (j.factorial:ℝ) := by
  have hh := Real.log_le_log (by exact_mod_cast Nat.choose_pos hj : (0:ℝ)<N.choose j)
    (Nat.choose_le_pow_div j N : (N.choose j:ℝ)≤(N:ℝ)^j/(j.factorial:ℝ))
  rw [Real.log_div (by positivity : (N:ℝ)^j≠0) (by positivity : (j.factorial:ℝ)≠0),Real.log_pow] at hh
  exact hh

open Filter

end Thorp.DimensionEstimates

end ThorpNine.Casimir

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Casimir_TailShapes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Casimir

namespace Thorp.StrongSmoothing


open scoped BigOperators

variable {X : Type*} [Fintype X] [Nonempty X]

omit [Nonempty X] in
lemma mean_nonneg (f : X → ℝ) (hf : ∀ x, 0 ≤ f x) : 0 ≤ finiteMean f :=
  finiteMean_nonneg hf

lemma mean_rpow_concave (f : X → ℝ) (hf : ∀ x, 0 ≤ f x)
    {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    finiteMean (fun x => (f x)^a) ≤ (finiteMean f)^a := by
  have hN : (0:ℝ) < Fintype.card X := Nat.cast_pos.mpr Fintype.card_pos
  have hh := (Real.concaveOn_rpow ha ha1).le_map_sum
    (t := Finset.univ) (w := fun _ : X => 1/(Fintype.card X:ℝ))
    (p := f) (fun _ _ => by positivity)
    (by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; field_simp)
    (fun x _ => hf x)
  simpa only [smul_eq_mul,one_div,←Finset.mul_sum,mul_comm _ (∑ _ : X,_),
    ←div_eq_mul_inv,finiteMean] using hh

omit [Nonempty X] in
lemma act_nonneg (K : Matrix X X ℝ) (hK : ∀ x y, 0 ≤ K x y)
    (f : X → ℝ) (hf : ∀ x, 0 ≤ f x) (y : X) : 0 ≤ act K f y :=
  Finset.sum_nonneg (fun x _ => mul_nonneg (hK x y) (hf x))

omit [Nonempty X] in
lemma act_rpow_le (K : Matrix X X ℝ) (hK : ∀ x y, 0 ≤ K x y)
    (hcol : ∀ y, ∑ x, K x y = 1) (f : X → ℝ) (hf : ∀ x, 0 ≤ f x)
    {b : ℝ} (hb : 1 ≤ b) (y : X) :
    (act K f y)^b ≤ act K (fun x => (f x)^b) y := by
  simpa only [smul_eq_mul,act] using
    (convexOn_rpow hb).map_sum_le (t := Finset.univ) (w := fun x => K x y)
      (p := f) (fun x _ => hK x y) (hcol y) (fun x _ => hf x)

lemma act_one_to_p (K : Matrix X X ℝ) (hK : ∀ x y, 0 ≤ K x y)
    {p A : ℝ} (hp : 1 ≤ p)
    (hm : ∀ x, finiteMean (fun y => ((Fintype.card X:ℝ)*K x y)^p) ≤ Real.exp A)
    (f : X → ℝ) (hf : ∀ x, 0 ≤ f x) :
    finiteMean (fun y => (act K f y)^p) ≤ Real.exp A*(finiteMean f)^p := by
  classical
  let s : ℝ := ∑ x, f x
  have hs : 0 ≤ s := Finset.sum_nonneg (fun x _ => hf x)
  have hN : (0:ℝ) < Fintype.card X := Nat.cast_pos.mpr Fintype.card_pos
  by_cases hz : s=0
  · have hfz : ∀ x, f x=0 := by
      intro x
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => hf x)).mp hz x (Finset.mem_univ _)
    simp only [act,hfz,mul_zero,Finset.sum_const_zero,finiteMean,zero_div,
      Real.zero_rpow (show p ≠ 0 by linarith),mul_zero,le_refl]
  · have hsp : 0 < s := lt_of_le_of_ne hs (Ne.symm hz)
    let w : X → ℝ := fun x => f x/s
    have hw : ∀ x, 0 ≤ w x := fun x => div_nonneg (hf x) hs
    have hws : ∑ x, w x = 1 := by simp only [w,←Finset.sum_div]; exact div_self hz
    have hact (y : X) : act K f y = finiteMean f * ∑ x, w x*((Fintype.card X:ℝ)*K x y) := by
      simp only [act,w,finiteMean,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      have hz' : (∑ x, f x) ≠ 0 := hz
      dsimp [s]
      field_simp [hz',ne_of_gt hN]
    have hj (y : X) : (act K f y)^p ≤ (finiteMean f)^p*
        ∑ x, w x*((Fintype.card X:ℝ)*K x y)^p := by
      rw [hact,Real.mul_rpow (mean_nonneg f hf)
        (Finset.sum_nonneg (fun x _ => mul_nonneg (hw x) (mul_nonneg hN.le (hK x y))))]
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (mean_nonneg f hf) _)
      exact (convexOn_rpow hp).map_sum_le
        (fun x _ => hw x) hws (fun x _ => mul_nonneg hN.le (hK x y))
    have hh := finiteMean_mono hj
    have he : finiteMean (fun y => (finiteMean f)^p*
        ∑ x, w x*((Fintype.card X:ℝ)*K x y)^p) =
        (finiteMean f)^p * ∑ x, w x*finiteMean (fun y => ((Fintype.card X:ℝ)*K x y)^p) := by
      simp_rw [mul_comm ((finiteMean f)^p), finiteMean_mul_const,
        finiteMean_sum, mul_comm (w _), finiteMean_mul_const]
    rw [he] at hh
    apply hh.trans
    have hsum : (∑ x, w x*finiteMean (fun y => ((Fintype.card X:ℝ)*K x y)^p)) ≤ Real.exp A := by
      calc
        _ ≤ ∑ x, w x*Real.exp A := Finset.sum_le_sum
          (fun x _ => mul_le_mul_of_nonneg_left (hm x) (hw x))
        _ = Real.exp A := by rw [←Finset.sum_mul,hws,one_mul]
    simpa only [mul_comm (Real.exp A)] using
      mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg (mean_nonneg f hf) _)

lemma act_b_to_pb (K : Matrix X X ℝ) (hK : ∀ x y, 0 ≤ K x y)
    (hcol : ∀ y, ∑ x, K x y = 1) {p A b : ℝ} (hp : 1 ≤ p) (hb : 1 ≤ b)
    (hm : ∀ x, finiteMean (fun y => ((Fintype.card X:ℝ)*K x y)^p) ≤ Real.exp A)
    (f : X → ℝ) (hf : ∀ x, 0 ≤ f x) :
    finiteMean (fun y => (act K f y)^(b*p)) ≤
      Real.exp A*(finiteMean (fun x => (f x)^b))^p := by
  calc
    _ ≤ finiteMean (fun y => (act K (fun x => (f x)^b) y)^p) := by
      apply finiteMean_mono
      intro y
      rw [Real.rpow_mul (act_nonneg K hK f hf y)]
      exact Real.rpow_le_rpow (Real.rpow_nonneg (act_nonneg K hK f hf y) _) (act_rpow_le K hK hcol f hf hb y) (by linarith)
    _ ≤ _ := act_one_to_p K hK hp hm _ (fun x => Real.rpow_nonneg (hf x) _)

variable [DecidableEq X]

omit [Nonempty X] in
lemma kernel_pow_nonneg (K : Matrix X X ℝ) (hK : ∀ x y, 0 ≤ K x y) (r : ℕ) :
    ∀ x y, 0 ≤ (K^r) x y := by
  classical
  induction r with
  | zero => intro x y; simp only [pow_zero,Matrix.one_apply]; split_ifs <;> norm_num
  | succ r ih =>
    intro x y
    rw [pow_succ,Matrix.mul_apply]
    exact Finset.sum_nonneg (fun z _ => mul_nonneg (ih x z) (hK z y))

omit [Nonempty X] in
lemma kernel_pow_row (K : Matrix X X ℝ) (hrow : ∀ x, ∑ y, K x y = 1) (r : ℕ) :
    ∀ x, ∑ y, (K^r) x y = 1 := by
  classical
  induction r with
  | zero => intro x; simp [Matrix.one_apply]
  | succ r ih =>
    intro x
    simp only [pow_succ,Matrix.mul_apply]
    rw [Finset.sum_comm]
    simp only [←Finset.mul_sum,hrow,mul_one,ih]

omit [Nonempty X] in
lemma rowDensity_nonneg (K : Matrix X X ℝ) (hK : ∀ x y, 0 ≤ K x y) (r : ℕ) (x y : X) :
    0 ≤ rowDensity K r x y := mul_nonneg (Nat.cast_nonneg _) (kernel_pow_nonneg K hK r x y)

omit [Nonempty X] in
lemma rowDensity_succ (K : Matrix X X ℝ) (r : ℕ) (x y : X) :
    rowDensity K (r+1) x y = act K (rowDensity K r x) y := by
  simp only [rowDensity,pow_succ,Matrix.mul_apply,act,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  ring

lemma rowDensity_mean (K : Matrix X X ℝ) (hrow : ∀ x, ∑ y, K x y = 1) (r : ℕ) (x : X) :
    finiteMean (rowDensity K r x) = 1 := by
  have hN : (Fintype.card X:ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr Fintype.card_pos)
  simp only [finiteMean,rowDensity,←Finset.mul_sum,kernel_pow_row K hrow,mul_one,div_self hN]

lemma rowDensity_moment_iter (K : Matrix X X ℝ) (hK : ∀ x y, 0 ≤ K x y)
    (hrow : ∀ x, ∑ y, K x y = 1) (hcol : ∀ y, ∑ x, K x y = 1)
    {p A : ℝ} (hp : 1 ≤ p) (hA : 0 ≤ A)
    (hm : ∀ x, finiteMean (fun y => ((Fintype.card X:ℝ)*K x y)^p) ≤ Real.exp A)
    (r : ℕ) (x : X) :
    finiteMean (fun y => (rowDensity K r x y)^(p^r)) ≤ Real.exp (A*r*p^r) := by
  induction r with
  | zero => simp [rowDensity_mean K hrow]
  | succ r ih =>
    have hpr : 1 ≤ p^r := one_le_pow₀ hp
    have hps : 1 ≤ p^(r+1) := one_le_pow₀ hp
    simp_rw [rowDensity_succ]
    calc
      _ ≤ Real.exp A*(finiteMean (fun y => (rowDensity K r x y)^(p^r)))^p := by
        rw [pow_succ]
        exact act_b_to_pb K hK hcol hp hpr hm _ (rowDensity_nonneg K hK r x)
      _ ≤ Real.exp A*(Real.exp (A*r*p^r))^p := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        exact Real.rpow_le_rpow (mean_nonneg _ (fun y => Real.rpow_nonneg
          (rowDensity_nonneg K hK r x y) _)) ih (le_trans zero_le_one hp)
      _ = Real.exp (A+A*r*p^(r+1)) := by rw [←Real.exp_mul,←Real.exp_add,pow_succ]; congr 1; ring
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        have hh := mul_le_mul_of_nonneg_left hps hA
        push_cast
        nlinarith

lemma rowDensity_second_moment (K : Matrix X X ℝ) (hK : ∀ x y, 0 ≤ K x y)
    (hrow : ∀ x, ∑ y, K x y = 1) (hcol : ∀ y, ∑ x, K x y = 1)
    {p A : ℝ} (hp : 1 ≤ p) (hA : 0 ≤ A)
    (hm : ∀ x, finiteMean (fun y => ((Fintype.card X:ℝ)*K x y)^p) ≤ Real.exp A)
    (r : ℕ) (hr : 2 ≤ p^r) (x : X) :
    finiteMean (fun y => (rowDensity K r x y)^2) ≤ Real.exp (2*A*r) := by
  have hpos : 0 < p^r := by linarith
  have hj := mean_rpow_concave (fun y => (rowDensity K r x y)^(p^r))
    (fun y => Real.rpow_nonneg (rowDensity_nonneg K hK r x y) _)
    (a := 2/(p^r)) (by positivity) ((div_le_one hpos).mpr hr)
  have he (y : X) : ((rowDensity K r x y)^(p^r))^(2/(p^r)) = (rowDensity K r x y)^2 := by
    rw [←Real.rpow_mul (rowDensity_nonneg K hK r x y)]
    rw [mul_div_cancel₀ _ (ne_of_gt hpos),Real.rpow_two]
  simp_rw [he] at hj
  apply hj.trans
  calc
    _ ≤ (Real.exp (A*r*p^r))^(2/(p^r)) :=
      Real.rpow_le_rpow (mean_nonneg _ (fun y => Real.rpow_nonneg
        (rowDensity_nonneg K hK r x y) _)) (rowDensity_moment_iter K hK hrow hcol hp hA hm r x)
        (by positivity)
    _ = _ := by rw [←Real.exp_mul]; congr 1; field_simp [ne_of_gt hpos]

lemma symmetric_kernel_smoothing (K : Matrix X X ℝ) (hK : ∀ x y, 0 ≤ K x y)
    (hrow : ∀ x, ∑ y, K x y = 1) (hcol : ∀ y, ∑ x, K x y = 1)
    (hsym : K.IsSymm) {p A : ℝ} (hp : 1 ≤ p) (hA : 0 ≤ A)
    (hm : ∀ x, finiteMean (fun y => ((Fintype.card X:ℝ)*K x y)^p) ≤ Real.exp A)
    (r : ℕ) (hr : 2 ≤ p^r) (x y : X) :
    (K^(2*r)) x y ≤ Real.exp (2*A*r)/(Fintype.card X:ℝ) := by
  have hN : (0:ℝ) < Fintype.card X := Nat.cast_pos.mpr Fintype.card_pos
  have hs : ∀ z, (K^r) z y = (K^r) y z := fun z => (hsym.pow r).apply y z
  have he : (Fintype.card X:ℝ)*(K^(2*r)) x y =
      finiteMean (fun z => rowDensity K r x z*rowDensity K r y z) := by
    simp only [finiteMean,rowDensity,two_mul,pow_add,Matrix.mul_apply,hs,Finset.mul_sum]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro z _
    field_simp
  have hh : finiteMean (fun z => rowDensity K r x z*rowDensity K r y z) ≤
      Real.exp (2*A*r) := by
    calc
      _ ≤ finiteMean (fun z => ((rowDensity K r x z)^2+(rowDensity K r y z)^2)/2) := by
        apply finiteMean_mono
        intro z
        nlinarith [sq_nonneg (rowDensity K r x z-rowDensity K r y z)]
      _ = (finiteMean (fun z => (rowDensity K r x z)^2)+
          finiteMean (fun z => (rowDensity K r y z)^2))/2 := by
        simp only [div_eq_mul_inv,finiteMean_mul_const,finiteMean_add]
      _ ≤ _ := by
        have hx := rowDensity_second_moment K hK hrow hcol hp hA hm r hr x
        have hy := rowDensity_second_moment K hK hrow hcol hp hA hm r hr y
        linarith
  apply (le_div_iff₀ hN).mpr
  simpa only [←he,mul_comm (Fintype.card X:ℝ)] using hh

end Thorp.StrongSmoothing

end ThorpNine.Casimir

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Casimir_Site
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Casimir


namespace Thorp.CasimirBounds
open scoped BigOperators Classical

theorem cycleCoefficient_decay (l r : ℕ) (hr : (l:ℝ)/2 ≤ r)
    (q : ℝ) (hq : 1 ≤ q) (hlog : Real.log q ≤ (l:ℝ)/16) :
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
  have hqE : q ≤ Real.exp ((l:ℝ)/16) := by
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
      _ ≤ (4*Real.exp ((l:ℝ)/16)*E)/Real.exp ((l:ℝ)/8) := by
        apply div_le_div₀ (by positivity) _ (Real.exp_pos _) hden
        have hs := hsqJ.trans hJE
        have hm := mul_le_mul hqE hs (Real.sqrt_nonneg _) (Real.exp_nonneg _)
        nlinarith
      _ = 4*Real.exp ((l:ℝ)/16+(l:ℝ)/32-(l:ℝ)/8) := by
        dsimp [E]
        rw [mul_assoc,←Real.exp_add,mul_div_assoc,←Real.exp_sub]
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _) (by norm_num)
        linarith
  change Real.log q / (J:ℝ) + 2*q*Real.sqrt J / Real.sqrt ((2:ℝ)^r) ≤ _
  linarith

theorem palindrome_slab_partial_mgf (r s l : ℕ) (hl : 0 < l) (hs : 2*s ≤ l)
    {ι : Type*} [Fintype ι] (e : ι ↪ Card (s+r)) (X : SwitchIndex (s+r) → Bool)
    (lo : Card r × SwitchIndex s → Bool) (q : ℝ) (hq : 1 ≤ q)
    (hlog : Real.log q ≤ 1/16) :
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

lemma palindrome_slab_adapted_mul_le (d s l : ℕ) (hsd : s ≤ d) (hl : 0 < l)
    (hs : 2*s ≤ l) {ι : Type*} [Fintype ι] (e : ι ↪ Card d)
    (X : SwitchIndex d → Bool) (F : (SwitchIndex d → Bool) → ℝ)
    (hF : ∀ Y, 0 ≤ F Y) (hA : LayerAdapted d s F) (q : ℝ) (hq : 1 ≤ q)
    (hlog : Real.log q ≤ 1/16) :
    finiteMean (fun Y => F Y*q^(palindromeSlabCost l d e (Y,X))) ≤
      finiteMean F * Real.exp (Fintype.card ι * (68*Real.exp (-(l:ℝ)/64))) := by
  obtain ⟨r,rfl⟩ := Nat.exists_eq_add_of_le hsd
  exact adapted_mul_mean_le r s F _ hF hA _
    (fun lo => palindrome_slab_partial_mgf r s l hl hs e X lo q hq hlog)

theorem palindrome_family_mgf (L n d : ℕ) (hL : 0 < L) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (X : SwitchIndex d → Bool) (q : ℝ) (hq : 1 ≤ q)
    (hlog : Real.log q ≤ 1/16) :
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

lemma palindrome_family_mgf_decay (L n d : ℕ) (hL : 0 < L) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (X : SwitchIndex d → Bool) (q : ℝ) (hq : 1 ≤ q)
    (hlog : Real.log q ≤ 1/16) :
    finiteMean (fun Y => q^(palindromeFamilyCost L n d e (Y,X))) ≤
      Real.exp (Fintype.card ι*heightDecay L) := by
  apply (palindrome_family_mgf L n d hL e X q hq hlog).trans
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  have h := mul_le_mul_of_nonneg_left (sum_family_decay L n hL) (by norm_num : (0:ℝ)≤68)
  simpa only [heightDecay,mul_div_assoc] using h

theorem palindrome_high_mgf (H n d : ℕ) (hH : 0 < H) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (X : SwitchIndex d → Bool) (q : ℝ) (hq : 1 ≤ q)
    (hlog : Real.log q ≤ 1/32) :
    finiteMean (fun Y => q^(palindromeFamilyCost H n d e (Y,X)+
      palindromeFamilyCost (2*H) n d e (Y,X))) ≤ Real.exp (Fintype.card ι*heightDecay H) := by
  have hq2 := one_le_pow₀ (n:=2) hq
  have hlog2 : Real.log (q^2) ≤ 1/16 := by rw [Real.log_pow]; norm_num; linarith
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
    (e : ι ↪ Card d) (q : ℝ) (hq : 1 ≤ q) (hlog : Real.log q ≤ 1/32) :
    finiteMean (fun ω : BenesCoins d => q^(palindromeFamilyCost H n d e ω+
      palindromeFamilyCost (2*H) n d e ω)) ≤ Real.exp (Fintype.card ι*heightDecay H) := by
  rw [finiteMean_prod,finiteMean_comm]
  calc
    _ ≤ finiteMean (fun _X : SwitchIndex d → Bool => Real.exp (Fintype.card ι*heightDecay H)) := by
      apply finiteMean_mono
      intro X
      exact palindrome_high_mgf H n d hH e X q hq hlog
    _ = _ := finiteMean_const _

end Thorp.CasimirBounds

end ThorpNine.Casimir

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Casimir_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Casimir

namespace Thorp.CasimirBounds
open scoped BigOperators Classical

theorem palindrome_cost_mgf_coarse (d : ℕ) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (q : ℝ) (hq : 1 ≤ q) (hlog : Real.log q ≤ 1/32) :
    finiteMean (fun ω : BenesCoins d => q^(palindromeCost d e ω)) ≤
      Real.exp (Fintype.card ι*(1+heightDecay 1)) := by
  have hd : d ≤ 1*4^d := by have hh := pow_four_ge d; omega
  have hcost (ω : BenesCoins d) : palindromeCost d e ω = palindromeLowCost 1 d e ω+
      (palindromeFamilyCost 1 d d e ω+palindromeFamilyCost 2 d d e ω) := by
    have hh := palindromeCost_family 1 d d e ω
    rw [palindromeLowCost_eq _ _ hd] at hh
    simpa only [Nat.add_assoc] using hh.symm
  have hqp : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have hlow (ω : BenesCoins d) : q^(palindromeLowCost 1 d e ω) ≤ Real.exp (Fintype.card ι) := by
    calc
      _ ≤ q^(Fintype.card ι) := pow_le_pow_right₀ hq (by simpa using palindromeLowCost_le 1 d e ω)
      _ = Real.exp (Fintype.card ι*Real.log q) := by rw [Real.exp_nat_mul,Real.exp_log hqp]
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card ι)])
  calc
    _ ≤ finiteMean (fun ω : BenesCoins d => Real.exp (Fintype.card ι)*
        q^(palindromeFamilyCost 1 d d e ω+palindromeFamilyCost 2 d d e ω)) := by
      apply finiteMean_mono
      intro ω
      rw [hcost,pow_add]
      exact mul_le_mul_of_nonneg_right (hlow ω) (pow_nonneg hqp.le _)
    _ = Real.exp (Fintype.card ι)*finiteMean (fun ω : BenesCoins d =>
        q^(palindromeFamilyCost 1 d d e ω+palindromeFamilyCost 2 d d e ω)) := by simpa only [mul_comm] using finiteMean_mul_const (fun ω : BenesCoins d => q^(palindromeFamilyCost 1 d d e ω+palindromeFamilyCost 2 d d e ω)) (Real.exp (Fintype.card ι))
    _ ≤ Real.exp (Fintype.card ι)*Real.exp (Fintype.card ι*heightDecay 1) := by
      exact mul_le_mul_of_nonneg_left
        (palindrome_high_full_mgf 1 d d (by decide) e q hq hlog) (Real.exp_nonneg _)
    _ = _ := by rw [←Real.exp_add]; congr 1; ring

lemma row_moment_coarse (d : ℕ) {ι : Type*} [Fintype ι] (e : ι ↪ Card d)
    (a : ℝ) (ha : 0 < a) (ha32 : a ≤ 1/32) :
    palindromeRowMoment d e a ≤ Real.exp (Fintype.card ι*(1+heightDecay 1)) := by
  let q : ℝ := (2:ℝ)^a
  have hq : 1 ≤ q := Real.one_le_rpow (by norm_num) ha.le
  have hlog : Real.log q ≤ 1/32 := by
    dsimp [q]
    rw [Real.log_rpow (by norm_num)]
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at hh
    nlinarith
  have hn : (0:ℝ) < ((2^d:ℕ):ℝ)^(Fintype.card ι) := by positivity
  have hn0 : (0:ℝ) ≤ ((2^d).descFactorial (Fintype.card ι):ℝ) /
      ((2^d:ℕ):ℝ)^(Fintype.card ι) := by positivity
  have hn1 : ((2^d).descFactorial (Fintype.card ι):ℝ) /
      ((2^d:ℕ):ℝ)^(Fintype.card ι) ≤ 1 := by
    apply (div_le_one hn).mpr
    exact_mod_cast Nat.descFactorial_le_pow (2^d) (Fintype.card ι)
  have hpow := Real.rpow_le_one hn0 hn1 ha.le
  have hm := palindrome_row_density_moment d e a ha.le
  have he (c : ℕ) : q^c = (2:ℝ)^((c:ℝ)*a) := by
    rw [mul_comm,Real.rpow_mul_natCast (by norm_num)]
  simp_rw [←he] at hm
  exact (hm.trans (mul_le_of_le_one_left (finiteMean_nonneg (fun _ =>
    pow_nonneg (le_trans (by norm_num) hq) _)) hpow)).trans
      (palindrome_cost_mgf_coarse d e q hq hlog)


lemma applyKernel_mul {X : Type*} [Fintype X] (P Q : Matrix X X ℝ)
    (v : EuclideanSpace ℂ X) :
    DensityTransfer.applyKernel (fun x y => (P*Q) x y) v =
      DensityTransfer.applyKernel (fun x y => P x y) (DensityTransfer.applyKernel (fun x y => Q x y) v) := by
  apply PiLp.ext
  intro x
  change DensityTransfer.applyKernel (fun x y => (P*Q) x y) v x = DensityTransfer.applyKernel (fun x y => P x y) (DensityTransfer.applyKernel (fun x y => Q x y) v) x
  simp only [DensityTransfer.applyKernel_apply,Matrix.mul_apply,Complex.ofReal_sum,
    Complex.ofReal_mul,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro z _
  ring

lemma applyKernel_one {X : Type*} [Fintype X] [DecidableEq X]
    (v : EuclideanSpace ℂ X) : DensityTransfer.applyKernel (fun x y => (1 : Matrix X X ℝ) x y) v = v := by
  apply PiLp.ext
  intro x
  change DensityTransfer.applyKernel (fun x y => (1 : Matrix X X ℝ) x y) v x = v x
  simp [DensityTransfer.applyKernel_apply,Matrix.one_apply,apply_ite,ite_mul]

lemma symmetric_hs_power {X : Type*} [Fintype X] [DecidableEq X]
    (P : Matrix X X ℝ) (hs : P.IsSymm) (r : ℕ) :
    (∑ x, ∑ y, ((P^r) x y)^2) = ∑ x, (P^(2*r)) x x := by
  rw [two_mul,pow_add]
  apply Finset.sum_congr rfl
  intro x _
  simp only [Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro y _
  rw [(hs.pow r).apply x y,pow_two]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteDimensional ℂ V]

lemma trace_power_le_hs (A : V →L[ℂ] V) (hs : IsSelfAdjoint A) (hn : ‖A‖ ≤ 1)
    (r : ℕ) :
    (LinearMap.trace ℂ V ((A^(2*r+1)).toLinearMap)).re ≤
      ∑ j, ‖(A^r) (stdOrthonormalBasis ℂ V j)‖^2 := by
  let B := stdOrthonormalBasis ℂ V
  rw [LinearMap.trace_eq_matrix_trace ℂ B.toBasis]
  simp only [Matrix.trace,Matrix.diag,Complex.re_sum,LinearMap.toMatrix_apply,
    OrthonormalBasis.coe_toBasis_repr_apply,OrthonormalBasis.repr_apply_apply]
  apply Finset.sum_le_sum
  intro j _
  have he : (A^(2*r+1)) (B j) = (A^r) (A ((A^r) (B j))) := by
    have hnat : 2*r+1=r+(1+r) := by omega
    rw [hnat,pow_add,pow_add,pow_one]
    rfl
  change (inner ℂ (B j) ((A^(2*r+1)) (B j))).re ≤ ‖(A^r) (B j)‖^2
  rw [he]
  conv_lhs => rw [←(hs.pow r).adjoint_eq,ContinuousLinearMap.adjoint_inner_right]
  rw [(hs.pow r).adjoint_eq]
  apply (Complex.re_le_norm _).trans
  apply (norm_inner_le_norm _ _).trans
  have hh := A.le_opNorm ((A^r) (B j))
  have ha : ‖A ((A^r) (B j))‖ ≤ ‖(A^r) (B j)‖ := by
    exact hh.trans (by simpa using mul_le_mul_of_nonneg_right hn (norm_nonneg _))
  nlinarith [norm_nonneg ((A^r) (B j))]

open UnitaryFinite
lemma palindrome_selfadjoint (d : ℕ) (ρ : Representation ℂ (Equiv.Perm (Card d)) V)
    (hρ : IsUnitary ρ) : IsSelfAdjoint (sampleOperator ρ (palindromePerm d)) := by
  rw [sampleOperator_palindrome _ _ hρ]
  change IsSelfAdjoint (_ * star _)
  simp only [isSelfAdjoint_iff,star_mul,star_star]

variable {G X : Type*} [Group G] [Fintype G] [Fintype X] [DecidableEq X]

lemma coefficient_trace_amplification (a : G →* Equiv.Perm X) (x₀ : X)
    (ha : ∀ x, ∃ g, a g x₀=x) (ρ : Representation ℂ G V)
    [Representation.IsIrreducible ρ] (hρ : IsUnitary ρ)
    (P : Matrix X X ℝ) (A : V →L[ℂ] V)
    (hmap : ∀ w, IsFixed a x₀ ρ w → ∀ v,
      DensityTransfer.applyKernel (fun x y => P x y) (normalizedCoefficient a x₀ ha ρ w v) =
        normalizedCoefficient a x₀ ha ρ w (A v))
    (hs : IsSelfAdjoint A) (hn : ‖A‖ ≤ 1) (r : ℕ) :
    (Module.finrank ℂ (fixedSpace a x₀ ρ):ℝ) *
      (LinearMap.trace ℂ V ((A^(2*r+1)).toLinearMap)).re ≤
      ∑ x, ∑ y, ((P^r) x y)^2 := by
  let W := fixedSpace a x₀ ρ
  let B := stdOrthonormalBasis ℂ V
  let C := stdOrthonormalBasis ℂ W
  let w : Fin (Module.finrank ℂ W) → V := fun i => (C i : V)
  have hfix (i) : IsFixed a x₀ ρ (w i) := (C i).2
  have hw : Orthonormal ℂ w := C.orthonormal.comp_linearIsometry W.subtypeₗᵢ
  let v : Fin (Module.finrank ℂ W) × Fin (Module.finrank ℂ V) → EuclideanSpace ℂ X :=
    fun ij => normalizedCoefficient a x₀ ha ρ (w ij.1) (B ij.2)
  have hv : Orthonormal ℂ v := by
    rw [orthonormal_iff_ite]
    intro i j
    dsimp [v]
    rw [normalizedCoefficient_inner a x₀ ha ρ hρ _ _ (hfix _) (hfix _)]
    rw [(orthonormal_iff_ite.mp hw), (orthonormal_iff_ite.mp B.orthonormal)]
    by_cases h1 : i.1=j.1 <;> by_cases h2 : i.2=j.2 <;>
      simp [h1,h2,Prod.ext_iff,eq_comm]
  have hp (s : ℕ) (i) (t : V) :
      DensityTransfer.applyKernel (fun x y => (P^s) x y) (normalizedCoefficient a x₀ ha ρ (w i) t) =
        normalizedCoefficient a x₀ ha ρ (w i) ((A^s) t) := by
    induction s with
    | zero => simp [applyKernel_one]
    | succ s ih =>
      rw [pow_succ',applyKernel_mul,ih,hmap _ (hfix _),pow_succ']
      rfl
  have hhs := DensityTransfer.hilbert_schmidt_family (fun x y => (P^r) x y) v hv
  have he : (∑ ij, ‖DensityTransfer.applyKernel (fun x y => (P^r) x y) (v ij)‖^2) =
      (Module.finrank ℂ W:ℝ) * ∑ j, ‖(A^r) (B j)‖^2 := by
    simp only [v,hp,normalizedCoefficient_norm a x₀ ha ρ hρ _ (hfix _)
      (hw.norm_eq_one _),Fintype.sum_prod_type]
    simp
  rw [he] at hhs
  exact (mul_le_mul_of_nonneg_left (trace_power_le_hs A hs hn r) (by positivity)).trans hhs

end Thorp.CasimirBounds

namespace Thorp.CasimirBounds
open scoped BigOperators Classical
open UnitaryFinite

section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

lemma palindrome_trace_amplification (d k : ℕ) (x₀ : Fin k ↪ Card d)
    (ρ : Representation ℂ (Equiv.Perm (Card d)) V) [Representation.IsIrreducible ρ]
    (hρ : IsUnitary ρ) (r : ℕ) :
    (Module.finrank ℂ (fixedSpace tupleAction x₀ ρ):ℝ) *
      (LinearMap.trace ℂ V (((sampleOperator ρ (palindromePerm d))^(2*r+1)).toLinearMap)).re ≤
    ∑ x, ∑ y, ((tupleKernel d k)^r) x y ^ 2 := by
  let ha := tupleAction_transitive x₀
  have hmap (w : V) (hw : IsFixed tupleAction x₀ ρ w) (v : V) :
      DensityTransfer.applyKernel (fun x y : Fin k ↪ Card d =>
        PairRouting.tupleProbability (palindromePerm d) x y)
        (normalizedCoefficient tupleAction x₀ ha ρ w v) =
      normalizedCoefficient tupleAction x₀ ha ρ w (sampleOperator ρ (palindromePerm d) v) := by
    have hh := coefficient_random tupleAction x₀ ha ρ hρ (palindromePerm d) w hw v
    have he : actionKernel tupleAction (palindromePerm d) =
        fun x y : Fin k ↪ Card d => PairRouting.tupleProbability (palindromePerm d) x y := by
      funext x y
      exact tupleAction_kernel _ x y
    rw [he,←sampleOperator_inv_apply,sampleOperator_inv _ hρ,
      (palindrome_selfadjoint d ρ hρ).adjoint_eq] at hh
    exact hh
  exact coefficient_trace_amplification tupleAction x₀ ha ρ hρ _ _ hmap
    (palindrome_selfadjoint d ρ hρ) (sampleOperator_norm_le ρ hρ _) r

end

lemma tupleKernel_symm (d k : ℕ) : (tupleKernel d k).IsSymm := by
  ext x y
  exact palindrome_kernel_symmetric d y x

lemma tupleKernel_power64 (d k : ℕ) (x y : Fin k ↪ Card d) :
    ((tupleKernel d k)^64) x y ≤
      Real.exp ((64*(1+heightDecay 1))*k)/(Fintype.card (Fin k ↪ Card d):ℝ) := by
  let : Nonempty (Fin k ↪ Card d) := ⟨x⟩
  have hr (x : Fin k ↪ Card d) : ∑ y, tupleKernel d k x y = 1 :=
    PairRouting.tupleProbability_row_sum _ x
  have hc (y : Fin k ↪ Card d) : ∑ x, tupleKernel d k x y = 1 := by
    simp_rw [(tupleKernel_symm d k).apply y]
    exact hr y
  have hm (x : Fin k ↪ Card d) :
      finiteMean (fun y => ((Fintype.card (Fin k ↪ Card d):ℝ)*tupleKernel d k x y)^
        (1+(1/32:ℝ))) ≤ Real.exp ((k:ℝ)*(1+heightDecay 1)) := by
    simpa only [palindromeRowMoment,Fintype.card_fin,tupleKernel] using
      row_moment_coarse d x (1/32) (by norm_num) (by norm_num)
  have hnum : 2 ≤ (1+(1/32:ℝ))^(32:ℕ) := by
    have hh := one_add_mul_le_pow (a := (1/32:ℝ)) (by norm_num) 32
    norm_num at hh ⊢
  have hh := StrongSmoothing.symmetric_kernel_smoothing (tupleKernel d k)
    (fun x y => PairRouting.tupleProbability_nonneg _ x y) hr hc (tupleKernel_symm d k)
    (p := 1+(1/32:ℝ)) (A := k*(1+heightDecay 1)) (by norm_num)
    (mul_nonneg (Nat.cast_nonneg _) (by linarith [heightDecay_nonneg 1])) hm 32 hnum x y
  have he : 2*((k:ℝ)*(1+heightDecay 1))*(32:ℝ) = (64*(1+heightDecay 1))*k := by ring
  simpa only [show 2*32=64 by norm_num,Nat.cast_ofNat,he] using hh

lemma fixed_trace_bound (d k : ℕ) (μ : YoungDiagram) (e : Card d ≃ Specht.Cell μ)
    (x₀ : Fin k ↪ Card d) :
    (Module.finrank ℂ (fixedSpace (V := Specht.hilbertSpace μ) tupleAction x₀
      (Specht.relabelledUnitary μ e)):ℝ) * traceMoment d μ e 65 ≤
        Real.exp ((64*(1+heightDecay 1))*k) := by
  let ρ := Specht.relabelledUnitary μ e
  let := Specht.relabelledUnitary_irreducible μ e
  have hh := palindrome_trace_amplification (V:=Specht.hilbertSpace μ) d k x₀ ρ
    (Specht.relabelledUnitary_unitary μ e) 32
  change _ * traceMoment d μ e 65 ≤ _ at hh
  rw [symmetric_hs_power _ (tupleKernel_symm d k)] at hh
  apply hh.trans
  have hX : (0:ℝ) < Fintype.card (Fin k ↪ Card d) := by
    let : Nonempty (Fin k ↪ Card d) := ⟨x₀⟩
    exact Nat.cast_pos.mpr Fintype.card_pos
  calc
    _ ≤ ∑ x : Fin k ↪ Card d,
        Real.exp ((64*(1+heightDecay 1))*k)/(Fintype.card (Fin k ↪ Card d):ℝ) :=
      Finset.sum_le_sum (fun x _ => tupleKernel_power64 d k x x)
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      exact mul_div_cancel₀ _ (ne_of_gt hX)

lemma levelScale_ge (n k : ℕ) (hk : k ≤ n) : (k:ℝ) ≤ levelScale n k := by
  by_cases h : k=0
  · simp [h,levelScale]
  have hkp : (0:ℝ)<k := by exact_mod_cast Nat.pos_of_ne_zero h
  have hlog : 0 ≤ Real.log ((n:ℝ)/k) := Real.log_nonneg ((one_le_div hkp).mpr (by exact_mod_cast hk))
  dsimp [levelScale]
  nlinarith

lemma choose_le_exp_levelScale (n k : ℕ) (hn : 0<n) (hk : k≤n) :
    (n.choose k:ℝ) ≤ Real.exp (levelScale n k) := by
  by_cases h : k=0
  · simp [h,levelScale]
  have hkp : 0<k := Nat.pos_of_ne_zero h
  have hh := DimensionEstimates.log_choose_upper n k hn hk
  have hf := DimensionEstimates.log_factorial_lower k hkp
  have he : Real.log ((n:ℝ)/k) = Real.log n-Real.log k :=
    Real.log_div (by positivity) (by positivity)
  have hl : Real.log (n.choose k:ℝ) ≤ levelScale n k := by
    dsimp [levelScale]
    rw [he]
    linarith
  rw [←Real.exp_log (by exact_mod_cast Nat.choose_pos hk : (0:ℝ)<n.choose k)]
  exact Real.exp_le_exp.mpr hl

lemma trace_bound_q77_oai (d : ℕ) (μ : YoungDiagram) (e : Card d ≃ Specht.Cell μ) :
    (Module.finrank ℂ (Specht.space μ):ℝ)*traceMoment d μ e 65 ≤
      Real.exp ((1+64*(1+heightDecay 1))*levelScale (2^d) (μ.card-μ.rowLen 0)) := by
  let k := μ.card-μ.rowLen 0
  have hn : μ.card=2^d := by
    rw [←Specht.card_cell,←Fintype.card_congr e,card_positions]
  have hk : k≤2^d := by dsimp [k]; omega
  let x₀ : Fin k ↪ Card d := (Fin.castLEEmb (show k≤Fintype.card (Card d) by simpa [card_positions] using hk)).trans
    (Fintype.equivFin (Card d)).symm.toEmbedding
  let m := Module.finrank ℂ (fixedSpace (V := Specht.hilbertSpace μ) tupleAction x₀
    (Specht.relabelledUnitary μ e))
  have hd : (Module.finrank ℂ (Specht.space μ):ℝ) ≤ (m:ℝ)*((2^d).choose k:ℝ) := by
    have hh := Specht.relabelled_tuple_dimension μ e x₀
    simp only [Fintype.card_fin] at hh
    change Module.finrank ℂ (Specht.hilbertSpace μ) * k.choose k ≤ m * μ.card.choose k at hh
    rw [Nat.choose_self,mul_one,Specht.finrank_hilbertSpace,hn] at hh
    exact_mod_cast hh
  have hm := fixed_trace_bound d k μ e x₀
  by_cases ht : 0≤traceMoment d μ e 65
  · calc
      _ ≤ ((m:ℝ)*((2^d).choose k:ℝ))*traceMoment d μ e 65 :=
        mul_le_mul_of_nonneg_right hd ht
      _ = ((2^d).choose k:ℝ)*((m:ℝ)*traceMoment d μ e 65) := by ring
      _ ≤ ((2^d).choose k:ℝ)*Real.exp ((64*(1+heightDecay 1))*k) :=
        mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg _)
      _ ≤ Real.exp (levelScale (2^d) k)*Real.exp ((64*(1+heightDecay 1))*levelScale (2^d) k) := by
        apply mul_le_mul (choose_le_exp_levelScale _ _ (by positivity) hk) _ (by positivity) (Real.exp_nonneg _)
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_left (levelScale_ge _ _ hk) (by linarith [heightDecay_nonneg 1])
      _ = _ := by rw [←Real.exp_add]; congr 1; ring
  · exact (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (le_of_not_ge ht)).trans (Real.exp_nonneg _)

end Thorp.CasimirBounds

namespace Thorp.Specht
open scoped BigOperators Classical
open UnitaryFinite

noncomputable instance cardRepresentation_irreducible (d : ℕ) (μ : Shapes (2^d)) :
    Representation.IsIrreducible (cardRepresentation d μ) :=
  relabelledUnitary_irreducible _ _

end Thorp.Specht

end ThorpNine.Casimir

end OAI
end

theorem solution : type_of% @OAI.ThorpNine.Casimir.Thorp.CasimirBounds.trace_bound_q77_oai := @OAI.ThorpNine.Casimir.Thorp.CasimirBounds.trace_bound_q77_oai
