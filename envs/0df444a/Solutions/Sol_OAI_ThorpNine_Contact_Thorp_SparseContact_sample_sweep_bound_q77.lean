-- Prove2me | solution 1 for OAI.ThorpNine.Contact.Thorp.SparseContact.sample_sweep_bound_q77
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:13:29.78789+00:00
-- url     : https://prove2.me/submissions/4d97c0a6-94b4-4b89-849f-8abb2714027a

import Mathlib
import Definitions.Def_ThorpRouting
import Definitions.Def_OAIQ077T000
import Definitions.Def_OAIQ077T001

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
-- module Solutions.OAIQ077_TR.ThorpRouting_Contact_Coins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Contact

namespace Thorp

open scoped BigOperators
open Filter

lemma card_positions (d : ℕ) : Fintype.card (Card d) = 2 ^ d := by
  simp [Card]

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

lemma inclusionMoment_nonneg {α Ω : Type*} [Fintype Ω]
    (F : Ω → Finset α) (s : Finset α) : 0 ≤ inclusionMoment F s := by
  classical
  unfold inclusionMoment finiteMean
  positivity

lemma indicator_subset_prod {α : Type*} [DecidableEq α] (A s : Finset α) :
    (if s ⊆ A then (1 : ℝ) else 0) = ∏ i ∈ s, (if i ∈ A then 1 else 0) := by
  by_cases h : s ⊆ A
  · rw [ite_eq_left h]
    exact (Finset.prod_eq_one (fun index hindex => ite_eq_left (h hindex))).symm
  · rw [ite_eq_right h]
    obtain ⟨i, hi, hiA⟩ := Finset.not_subset.mp h
    exact (Finset.prod_eq_zero hi (ite_eq_right hiA)).symm

lemma inclusionMoment_const {α Ω : Type*} [DecidableEq α] [Fintype Ω] [Nonempty Ω]
    (A s : Finset α) : inclusionMoment (fun _ : Ω => A) s =
      if s ⊆ A then 1 else 0 := by
  classical
  have hn : (Fintype.card Ω : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  by_cases h : s ⊆ A <;> simp [inclusionMoment, finiteMean, h, hn]

lemma cylinder_const {α Ω : Type*} [Fintype Ω] [Nonempty Ω] (A : Finset α) :
    CylinderBound (inclusionMoment (fun _ : Ω => A))
      (fun i => inclusionMoment (fun _ : Ω => A) {i}) := by
  classical
  intro s
  simp only [inclusionMoment_const, Finset.singleton_subset_iff]
  exact (indicator_subset_prod A s).le

namespace QueryTree

variable {ι : Type*} [DecidableEq ι]

lemma flipCoin_apply_eq (i : ι) (ω : ι → Bool) : flipCoin i ω i = !(ω i) := by
  change Function.update ω i (!(ω i)) i = _
  exact Function.update_self _ _ _

lemma flipCoin_apply_ne (i j : ι) (h : j ≠ i) (ω : ι → Bool) :
    flipCoin i ω j = ω j := by
  change Function.update ω i (!(ω i)) j = _
  exact Function.update_of_ne h _ _

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

end QueryTree

end Thorp

end ThorpNine.Contact

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Contact_ExposedCoins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Contact

namespace Thorp
open scoped BigOperators
open Filter

lemma card_routeDomain (d : ℕ) (x y : Card d) : (routeDomain d x y).card = d := by
  classical
  induction d with
  | zero => rfl
  | succ d ih =>
    change (insert (Sum.inl (Fin.tail y))
      ((routeDomain d (Fin.tail x) (Fin.tail y)).image
        (fun i => (Sum.inr (x 0,i) : Sum (Card d) (Bool × SwitchIndex d)))) :
      Finset (Sum (Card d) (Bool × SwitchIndex d))).card = d + 1
    rw [Finset.card_insert_of_notMem (by simp)]
    rw [Finset.card_image_of_injective _ (by intro i j h; cases h; rfl), ih]

lemma xor_eq_iff (a b c : Bool) : Bool.xor a b = c ↔ b = Bool.xor a c := by
  cases a <;> cases b <;> cases c <;> decide

lemma butterfly_endpoint_iff (d : ℕ) (ω : SwitchIndex d → Bool) (x y : Card d) :
    butterflyPerm d (decodeButterfly d ω) x = y ↔
      ∀ i ∈ routeDomain d x y, ω i = routeValue d x y i := by
  classical
  induction d with
  | zero =>
    have he : butterflyPerm 0 (decodeButterfly 0 ω) x = y := Subsingleton.elim _ _
    simp [he, routeDomain]
  | succ d ih =>
    let v := butterflyPerm d (decodeButterfly d (fun i => ω (Sum.inr (x 0,i)))) (Fin.tail x)
    change Fin.cons (Bool.xor (x 0) (ω (Sum.inl v))) v = y ↔ _
    have hv : v = Fin.tail y ↔
        ∀ i ∈ routeDomain d (Fin.tail x) (Fin.tail y),
          ω (Sum.inr (x 0,i)) = routeValue d (Fin.tail x) (Fin.tail y) i :=
      ih _ _ _
    constructor
    · intro h i hi
      have ht : v = Fin.tail y := by simpa using congrArg Fin.tail h
      have hh : ω (Sum.inl (Fin.tail y)) = Bool.xor (x 0) (y 0) := by
        have he := congrFun h 0
        simp only [Fin.cons_zero, ht] at he
        exact (xor_eq_iff _ _ _).mp he
      rcases Finset.mem_insert.mp hi with htop | hchild
      · subst i
        exact hh
      · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hchild
        exact hv.mp ht j hj
    · intro h
      have hh := h (Sum.inl (Fin.tail y)) (Finset.mem_insert_self _ _)
      have ht : v = Fin.tail y := hv.mpr (fun i hi =>
        h (Sum.inr (x 0,i)) (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hi)))
      have hh' : Bool.xor (x 0) (ω (Sum.inl (Fin.tail y))) = y 0 :=
        (xor_eq_iff _ _ _).mpr hh
      rw [ht, hh', Fin.cons_self_tail]

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

lemma butterfly_single_card_uniform (d : ℕ) (x y : Card d) :
    finiteMean (fun ω : SwitchIndex d → Bool =>
      if butterflyPerm d (decodeButterfly d ω) x = y then (1 : ℝ) else 0) = 1 / (2 : ℝ) ^ d := by
  have he : finiteMean (fun ω : SwitchIndex d → Bool =>
      if butterflyPerm d (decodeButterfly d ω) x = y then (1 : ℝ) else 0) =
      finiteMean (fun ω : SwitchIndex d → Bool =>
        if ∀ i ∈ routeDomain d x y, ω i = routeValue d x y i then (1 : ℝ) else 0) :=
    finiteMean_congr (fun ω => by simp only [butterfly_endpoint_iff])
  rw [he, mean_coinCylinder, card_routeDomain]

lemma switchUsers_ne (d : ℕ) (b : Butterfly d) (i : SwitchIndex d) :
    (switchUsers d b i).1 ≠ (switchUsers d b i).2 := by
  induction d with
  | zero => exact Empty.elim i
  | succ d ih =>
    cases i with
    | inl y =>
      intro h
      have := congrFun h 0
      simp only [switchUsers, Fin.cons_zero] at this
      exact Bool.false_ne_true this
    | inr z =>
      intro h
      exact ih (b.2 z.1) z.2 (by simpa only [switchUsers, Fin.tail_cons] using congrArg Fin.tail h)

lemma cons_eq_iff {d : ℕ} (ε : Bool) (a : Card d) (x : Card (d + 1)) :
    Fin.cons ε a = x ↔ ε = x 0 ∧ a = Fin.tail x := by
  constructor
  · intro h
    exact ⟨by simpa only [Fin.cons_zero] using congrFun h 0,
      by simpa only [Fin.tail_cons] using congrArg Fin.tail h⟩
  · rintro ⟨rfl,rfl⟩
    exact Fin.cons_self_tail x

lemma mem_routeDomain_iff_user (d : ℕ) (b : Butterfly d) (x : Card d) (i : SwitchIndex d) :
    i ∈ routeDomain d x (butterflyPerm d b x) ↔
      (switchUsers d b i).1 = x ∨ (switchUsers d b i).2 = x := by
  classical
  induction d with
  | zero => exact Empty.elim i
  | succ d ih =>
    cases i with
    | inl y =>
      change Sum.inl y ∈ insert (Sum.inl (Fin.tail (butterflyPerm (d+1) b x)))
        ((routeDomain d (Fin.tail x) (Fin.tail (butterflyPerm (d+1) b x))).image
          (fun i => (Sum.inr (x 0,i) : Sum (Card d) (Bool × SwitchIndex d)))) ↔ _
      simp only [Finset.mem_insert, Sum.inl.injEq, Finset.mem_image,
        Sum.inr_ne_inl, and_false, exists_false, or_false]
      change y = butterflyPerm d (b.2 (x 0)) (Fin.tail x) ↔ _
      simp only [switchUsers, cons_eq_iff]
      cases x 0 <;> simp [Equiv.symm_apply_eq]
    | inr z =>
      obtain ⟨ε,i⟩ := z
      change Sum.inr (ε,i) ∈ insert (Sum.inl (Fin.tail (butterflyPerm (d+1) b x)))
        ((routeDomain d (Fin.tail x) (Fin.tail (butterflyPerm (d+1) b x))).image
          (fun i => (Sum.inr (x 0,i) : Sum (Card d) (Bool × SwitchIndex d)))) ↔ _
      simp only [Finset.mem_insert, Sum.inr_ne_inl, false_or, Finset.mem_image,
        Sum.inr.injEq, Prod.mk.injEq]
      change (∃ j, j ∈ routeDomain d (Fin.tail x) (butterflyPerm d (b.2 (x 0)) (Fin.tail x)) ∧
        x 0 = ε ∧ j = i) ↔ _
      simp only [switchUsers, cons_eq_iff]
      constructor
      · rintro ⟨j,hj,hε,rfl⟩
        subst ε
        rcases (ih (b.2 (x 0)) (Fin.tail x) j).mp hj with h | h
        · exact Or.inl ⟨rfl,h⟩
        · exact Or.inr ⟨rfl,h⟩
      · rintro (⟨hε,h⟩ | ⟨hε,h⟩)
        · subst ε
          exact ⟨i,(ih (b.2 (x 0)) (Fin.tail x) i).mpr (Or.inl h),rfl,rfl⟩
        · subst ε
          exact ⟨i,(ih (b.2 (x 0)) (Fin.tail x) i).mpr (Or.inr h),rfl,rfl⟩

lemma mem_childMarks {d : ℕ} (s : Finset (Card (d + 1))) (ε : Bool) (x : Card d) :
    x ∈ childMarks s ε ↔ Fin.cons ε x ∈ s := by
  classical
  constructor
  · intro h
    obtain ⟨y,hy,hxy⟩ := Finset.mem_image.mp h
    obtain ⟨hys,hyε⟩ := Finset.mem_filter.mp hy
    rw [← hxy, ← hyε, Fin.cons_self_tail]
    exact hys
  · intro h
    exact Finset.mem_image.mpr ⟨Fin.cons ε x,
      Finset.mem_filter.mpr ⟨h,by simp⟩,by simp⟩

lemma finiteMean_mul_const {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) (c : ℝ) :
    finiteMean (fun ω => f ω * c) = finiteMean f * c := by
  unfold finiteMean
  rw [← Finset.sum_mul]
  ring

lemma finiteMean_sum {Ω α : Type*} [Fintype Ω] (s : Finset α) (f : α → Ω → ℝ) :
    finiteMean (fun ω => ∑ i ∈ s, f i ω) = ∑ i ∈ s, finiteMean (f i) := by
  simp only [finiteMean,Finset.sum_div]
  exact Finset.sum_comm

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

end Thorp

end ThorpNine.Contact

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Contact_ParallelFollow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Contact

namespace Thorp
open scoped BigOperators
open Filter

lemma finiteMean_prod {Ω Ω' : Type*} [Fintype Ω] [Fintype Ω'] (f : Ω × Ω' → ℝ) :
    finiteMean f = finiteMean (fun x => finiteMean (fun y => f (x,y))) := by
  simp only [finiteMean, Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul,
    ←Finset.sum_div, div_div, mul_comm]

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

lemma finiteMean_const {Ω : Type*} [Fintype Ω] [Nonempty Ω] (c : ℝ) :
    finiteMean (fun _ : Ω => c) = c := by
  simp only [finiteMean,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  exact mul_div_cancel_left₀ c (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

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

omit [Fintype β] in
lemma subset_pairLayer_image_iff (S A : Finset (Bool × β)) (ξ : β → Bool) :
    S ⊆ A.image (pairLayer ξ) ↔ S.image (pairLayer ξ) ⊆ A := by
  have hi (x : Bool × β) : pairLayer ξ (pairLayer ξ x) = x := (pairLayer ξ).left_inv x
  constructor
  · intro h
    have h' := Finset.image_subset_image h (f := pairLayer ξ)
    simpa only [Finset.image_image,Function.comp_def,hi,Finset.image_id'] using h'
  · intro h
    have h' := Finset.image_subset_image h (f := pairLayer ξ)
    simpa only [Finset.image_image,Function.comp_def,hi,Finset.image_id'] using h'

lemma finiteMean_comm {Ω Ω' : Type*} [Fintype Ω] [Fintype Ω'] (f : Ω → Ω' → ℝ) :
    finiteMean (fun x => finiteMean (f x)) = finiteMean (fun y => finiteMean (fun x => f x y)) := by
  simp only [finiteMean,←Finset.sum_div,div_div]
  rw [Finset.sum_comm,mul_comm]

lemma inclusionMoment_fairSetLayer {Ω : Type*} [Fintype Ω]
    (F : Ω → Finset (Bool × β)) (S : Finset (Bool × β)) :
    inclusionMoment (fairSetLayer F) S =
      finiteMean (fun ξ : β → Bool => inclusionMoment F (S.image (pairLayer ξ))) := by
  classical
  simp only [inclusionMoment_eq]
  have he : (fun ω : Ω × (β → Bool) => if S ⊆ fairSetLayer F ω then (1:ℝ) else 0) =
      (fun ω : Ω × (β → Bool) => if S.image (pairLayer ω.2) ⊆ F ω.1 then (1:ℝ) else 0) := by
    funext ω
    simp only [fairSetLayer,subset_pairLayer_image_iff]
  apply (congrArg finiteMean he).trans
  exact (finiteMean_prod (fun ω : Ω × (β → Bool) =>
    if S.image (pairLayer ω.2) ⊆ F ω.1 then (1:ℝ) else 0)).trans
      (finiteMean_comm (fun ω ξ => if S.image (pairLayer ξ) ⊆ F ω then (1:ℝ) else 0))

lemma inclusionMoment_fairSetLayer_singleton {Ω : Type*} [Fintype Ω]
    (F : Ω → Finset (Bool × β)) (x : Bool × β) :
    inclusionMoment (fairSetLayer F) {x} =
      (inclusionMoment F {x}+inclusionMoment F {(!x.1,x.2)})/2 := by
  rw [inclusionMoment_fairSetLayer]
  simp only [Finset.image_singleton,pairLayer,Equiv.coe_fn_mk]
  rw [finiteMean_pi_eval (A := fun _ : β => Bool) x.2 (fun c : Bool => inclusionMoment F {(Bool.xor x.1 c,x.2)})]
  rw [finiteMean_bool]
  rcases x with ⟨b,x⟩
  cases b <;> simp only [Bool.xor_false,Bool.false_xor,Bool.true_xor, Bool.not_false,Bool.not_true]

lemma cylinder_fairSetLayer {Ω : Type*} [Fintype Ω]
    (F : Ω → Finset (Bool × β))
    (h : CylinderBound (inclusionMoment F) (fun x => inclusionMoment F {x})) :
    CylinderBound (inclusionMoment (fairSetLayer F))
      (fun x => inclusionMoment (fairSetLayer F) {x}) := by
  have hh := h.fair_parallel (fun x => inclusionMoment_nonneg F {x})
  intro S
  rw [inclusionMoment_fairSetLayer]
  simp only [inclusionMoment_fairSetLayer_singleton]
  exact hh S

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

omit [Fintype Ω'] in
lemma inclusionMoment_image_equiv (e : α ≃ β) (F : Ω → Finset α) (S : Finset β) :
    inclusionMoment (fun ω => (F ω).image e) S = inclusionMoment F (S.image e.symm) := by
  classical
  simp only [inclusionMoment_eq]
  apply finiteMean_congr
  intro ω
  simp only [subset_image_equiv_iff]

omit [Fintype Ω'] in
lemma cylinder_image_equiv (e : α ≃ β) (F : Ω → Finset α)
    (h : CylinderBound (inclusionMoment F) (fun x => inclusionMoment F {x})) :
    CylinderBound (inclusionMoment (fun ω => (F ω).image e))
      (fun x => inclusionMoment (fun ω => (F ω).image e) {x}) := by
  intro S
  simp only [inclusionMoment_image_equiv,Finset.image_singleton]
  have hh := h (S.image e.symm)
  simpa only [Finset.prod_image e.symm.injective.injOn] using hh

omit [DecidableEq β] in
lemma inclusionMoment_comp_equiv (e : Ω ≃ Ω') (F : Ω' → Finset α) (S : Finset α) :
    inclusionMoment (fun ω => F (e ω)) S = inclusionMoment F S := by
  classical
  simp only [inclusionMoment_eq]
  simpa only [Equiv.apply_symm_apply] using
    finiteMean_equiv e (fun ω => if S ⊆ F (e ω) then (1 : ℝ) else 0)

omit [DecidableEq β] in
lemma cylinder_comp_equiv (e : Ω ≃ Ω') (F : Ω' → Finset α)
    (h : CylinderBound (inclusionMoment F) (fun x => inclusionMoment F {x})) :
    CylinderBound (inclusionMoment (fun ω => F (e ω)))
      (fun x => inclusionMoment (fun ω => F (e ω)) {x}) := by
  intro S
  simpa only [inclusionMoment_comp_equiv] using h S
end RelabelMarks

lemma finiteMean_prod_mul {Ω Ω' : Type*} [Fintype Ω] [Fintype Ω']
    (f : Ω → ℝ) (g : Ω' → ℝ) :
    finiteMean (fun ω : Ω × Ω' => f ω.1*g ω.2) = finiteMean f * finiteMean g := by
  simp only [finiteMean,Fintype.sum_prod_type,Fintype.card_prod,Nat.cast_mul,
    ←Finset.mul_sum,←Finset.sum_mul]
  ring

section JoinChildren
variable {β : Type*} [DecidableEq β]

lemma mem_childJoin (A B : Finset β) (b : Bool) (x : β) :
    (b,x) ∈ childJoin A B ↔ (if b then x ∈ B else x ∈ A) := by
  cases b <;> simp [childJoin]

lemma mem_boolFiber (S : Finset (Bool × β)) (b : Bool) (x : β) :
    x ∈ boolFiber S b ↔ (b,x) ∈ S := by
  constructor
  · intro h
    obtain ⟨⟨c,y⟩,hy,hxy⟩ := Finset.mem_image.mp h
    obtain ⟨hy,hc⟩ := Finset.mem_filter.mp hy
    change c = b at hc
    change y = x at hxy
    simpa only [hc,hxy] using hy
  · intro h
    exact Finset.mem_image.mpr ⟨(b,x),Finset.mem_filter.mpr ⟨h,rfl⟩,rfl⟩

lemma childJoin_boolFiber (S : Finset (Bool × β)) :
    childJoin (boolFiber S false) (boolFiber S true) = S := by
  ext ⟨b,x⟩
  rw [mem_childJoin]
  cases b <;> simp only [Bool.false_eq_true,↓reduceIte,mem_boolFiber]

lemma subset_childJoin_iff (S : Finset (Bool × β)) (A B : Finset β) :
    S ⊆ childJoin A B ↔ boolFiber S false ⊆ A ∧ boolFiber S true ⊆ B := by
  constructor
  · intro h
    constructor
    · intro x hx
      exact (mem_childJoin A B false x).mp (h ((mem_boolFiber S false x).mp hx))
    · intro x hx
      exact (mem_childJoin A B true x).mp (h ((mem_boolFiber S true x).mp hx))
  · rintro ⟨h₀,h₁⟩ ⟨b,x⟩ hx
    rw [mem_childJoin]
    cases b
    · exact h₀ ((mem_boolFiber S false x).mpr hx)
    · exact h₁ ((mem_boolFiber S true x).mpr hx)

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

lemma inclusionMoment_childJoin {Ω Ω' : Type*} [Fintype Ω] [Fintype Ω']
    (F : Ω → Finset β) (G : Ω' → Finset β) (S : Finset (Bool × β)) :
    inclusionMoment (fun ω : Ω × Ω' => childJoin (F ω.1) (G ω.2)) S =
      inclusionMoment F (boolFiber S false) * inclusionMoment G (boolFiber S true) := by
  classical
  simp only [inclusionMoment_eq]
  rw [←finiteMean_prod_mul]
  apply finiteMean_congr
  intro ω
  simp only [subset_childJoin_iff]
  split_ifs <;> simp_all

lemma cylinder_childJoin {Ω Ω' : Type*} [Fintype Ω] [Fintype Ω'] [Nonempty Ω] [Nonempty Ω']
    (F : Ω → Finset β) (G : Ω' → Finset β)
    (hF : CylinderBound (inclusionMoment F) (fun x => inclusionMoment F {x}))
    (hG : CylinderBound (inclusionMoment G) (fun x => inclusionMoment G {x})) :
    CylinderBound (inclusionMoment (fun ω : Ω × Ω' => childJoin (F ω.1) (G ω.2)))
      (fun x => inclusionMoment (fun ω : Ω × Ω' => childJoin (F ω.1) (G ω.2)) {x}) := by
  intro S
  rw [inclusionMoment_childJoin,prod_boolFibers]
  have hf (b : Bool) (x : β) : boolFiber {(b,x)} b = {x} := by
    ext y
    simp only [mem_boolFiber,Finset.mem_singleton,Prod.mk.injEq,true_and]
  have hn (b : Bool) (x : β) : boolFiber {(!b,x)} b = ∅ := by
    ext y
    cases b <;> simp [mem_boolFiber]
  have h₀ (x : β) : inclusionMoment (fun ω : Ω × Ω' => childJoin (F ω.1) (G ω.2)) {(false,x)} =
      inclusionMoment F {x} * inclusionMoment G ∅ := by
    rw [inclusionMoment_childJoin,hf]
    have hh := hn true x
    exact congrArg (fun T => inclusionMoment F {x} * inclusionMoment G T) hh
  have h₁ (x : β) : inclusionMoment (fun ω : Ω × Ω' => childJoin (F ω.1) (G ω.2)) {(true,x)} =
      inclusionMoment F ∅ * inclusionMoment G {x} := by
    rw [inclusionMoment_childJoin,hf]
    have hh := hn false x
    exact congrArg (fun T => inclusionMoment F T * inclusionMoment G {x}) hh
  have emF : inclusionMoment F ∅ = 1 := by simp [inclusionMoment,finiteMean_const]
  have emG : inclusionMoment G ∅ = 1 := by simp [inclusionMoment,finiteMean_const]
  simp only [h₀,h₁,emF,emG,mul_one,one_mul]
  exact mul_le_mul (hF _) (hG _) (inclusionMoment_nonneg _ _)
    (Finset.prod_nonneg (fun x _ => inclusionMoment_nonneg F {x}))
end JoinChildren

lemma childMarks_join (d : ℕ) (A : Finset (Card (d+1))) :
    A = (childMarks A false).image (Fin.cons false) ∪
      (childMarks A true).image (Fin.cons true) := by
  classical
  ext x
  constructor
  · intro hx
    cases hb : x 0
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr
        ⟨Fin.tail x,(mem_childMarks _ _ _).mpr (by simpa only [←hb,Fin.cons_self_tail] using hx),
          by simp only [←hb,Fin.cons_self_tail]⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨Fin.tail x,(mem_childMarks _ _ _).mpr (by simpa only [←hb,Fin.cons_self_tail] using hx),
          by simp only [←hb,Fin.cons_self_tail]⟩)
  · intro hx
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
      exact (mem_childMarks _ _ _).mp hy
    · obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
      exact (mem_childMarks _ _ _).mp hy

lemma butterflyMarks_succ (d : ℕ) (A : Finset (Card (d+1))) (ω : SwitchIndex (d+1) → Bool) :
    butterflyMarks (d+1) A ω =
      (fairSetLayer (fun p : (SwitchIndex d → Bool) × (SwitchIndex d → Bool) =>
        childJoin (butterflyMarks d (childMarks A false) p.1)
          (butterflyMarks d (childMarks A true) p.2)) (coinStepEquiv d ω)).image
            (headTailEquiv d).symm := by
  classical
  unfold butterflyMarks fairSetLayer childJoin
  rw [Finset.image_union,Finset.image_union]
  simp only [Finset.image_image]
  conv_lhs => rw [childMarks_join d A]
  rw [Finset.image_union]
  simp only [Finset.image_image]
  apply congrArg₂ (· ∪ ·)
  · apply Finset.image_congr
    intro x _
    simp only [Function.comp_def,butterflyPerm,decodeButterfly,Equiv.Perm.coe_mul,
      childLift,pairSwitch,switchFun,Equiv.coe_fn_mk,Fin.cons_zero,Fin.tail_cons,
      coinStepEquiv,headTailEquiv,Equiv.symm_symm,pairLayer]
    rfl
  · apply Finset.image_congr
    intro x _
    simp only [Function.comp_def,butterflyPerm,decodeButterfly,Equiv.Perm.coe_mul,
      childLift,pairSwitch,switchFun,Equiv.coe_fn_mk,Fin.cons_zero,Fin.tail_cons,
      coinStepEquiv,headTailEquiv,Equiv.symm_symm,pairLayer]
    rfl

lemma butterflyMarks_cylinder (d : ℕ) (A : Finset (Card d)) :
    CylinderBound (inclusionMoment (butterflyMarks d A))
      (fun x => inclusionMoment (butterflyMarks d A) {x}) := by
  induction d with
  | zero =>
    have he : butterflyMarks 0 A = fun _ : SwitchIndex 0 → Bool => A := by
      funext ω
      simp [butterflyMarks,butterflyPerm]
    rw [he]
    exact cylinder_const A
  | succ d ih =>
    have h := cylinder_childJoin (butterflyMarks d (childMarks A false))
      (butterflyMarks d (childMarks A true)) (ih _) (ih _)
    have hh := cylinder_image_equiv (headTailEquiv d).symm _ (cylinder_fairSetLayer _ h)
    have hs := cylinder_comp_equiv (coinStepEquiv d) _ hh
    simpa only [←butterflyMarks_succ] using hs

lemma indicator_mem_image_perm {α : Type*} [DecidableEq α]
    (A : Finset α) (p : Equiv.Perm α) (y : α) :
    (if y ∈ A.image p then (1 : ℝ) else 0) = ∑ x ∈ A, if p x = y then 1 else 0 := by
  classical
  by_cases h : y ∈ A.image p
  · obtain ⟨x,hx,hxy⟩ := Finset.mem_image.mp h
    rw [ite_eq_left (Finset.mem_image.mpr ⟨x,hx,hxy⟩)]
    symm
    calc
      _ = (if p x = y then (1:ℝ) else 0) := Finset.sum_eq_single_of_mem x hx (by
        intro z _ hzx
        exact ite_eq_right (fun hz => hzx (p.injective (hz.trans hxy.symm))))
      _ = 1 := ite_eq_left hxy
  · rw [ite_eq_right h]
    symm
    apply Finset.sum_eq_zero
    intro x hx
    exact ite_eq_right (fun hxy => h (Finset.mem_image.mpr ⟨x,hx,hxy⟩))

lemma butterflyMarks_singleton (d : ℕ) (A : Finset (Card d)) (y : Card d) :
    inclusionMoment (butterflyMarks d A) {y} = (A.card : ℝ)/(2:ℝ)^d := by
  classical
  unfold inclusionMoment
  simp only [Finset.singleton_subset_iff,butterflyMarks,indicator_mem_image_perm]
  rw [finiteMean_sum]
  simp only [butterfly_single_card_uniform,Finset.sum_const,nsmul_eq_mul]
  ring

lemma butterflyMarks_inclusion (d : ℕ) (A S : Finset (Card d)) :
    inclusionMoment (butterflyMarks d A) S ≤ ((A.card : ℝ)/(2:ℝ)^d)^S.card := by
  have h := butterflyMarks_cylinder d A S
  simpa only [butterflyMarks_singleton,Finset.prod_const] using h

end Thorp

end ThorpNine.Contact

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Contact_AlternatingPerm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Contact

namespace Thorp
open scoped BigOperators
open Filter

lemma finiteMean_nonneg {Ω : Type*} [Fintype Ω] {f : Ω → ℝ}
    (h : ∀ ω, 0 ≤ f ω) : 0 ≤ finiteMean f := by
  exact div_nonneg (Finset.sum_nonneg (fun ω _ => h ω)) (Nat.cast_nonneg _)

end Thorp

end ThorpNine.Contact

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Contact_ModifiedRoutingMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Contact

namespace Thorp


namespace DensityTransfer
open scoped BigOperators

lemma applyKernel_apply {X : Type*} [Fintype X] (P : X → X → ℝ)
    (v : EuclideanSpace ℂ X) (x : X) :
    applyKernel P v x = ∑ y, (P x y : ℂ)*v y := rfl

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

end DensityTransfer

end Thorp

end ThorpNine.Contact

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Contact_ShapePartitionEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Contact

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

end ThorpNine.Contact

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Contact_Representative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Contact

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

end Thorp.UnitaryFinite

end ThorpNine.Contact

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Contact_BlockProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Contact

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

end ThorpNine.Contact

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Contact_ModifiedStageEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Contact

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

variable {G H X Ω : Type*} [Group G] [Group H] [Fintype G] [Fintype X] [Fintype Ω]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

omit [Fintype G] in
lemma sampleOperator_inv_apply (ρ : Representation ℂ G V) (P : Ω → G) (v : V) :
    sampleOperator ρ (fun ω => (P ω)⁻¹) v=randomOperator ρ P v := by
  simp only [sampleOperator,randomOperator,smul_apply,
    sum_apply,continuousRepresentation_apply,LinearMap.smul_apply,LinearMap.sum_apply]

end Thorp.UnitaryFinite

namespace Thorp.SparseContact
open scoped BigOperators Classical

lemma small_dominating_set {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hG : ∀ v, ∃ w, G.Adj v w) :
    ∃ R : Finset V, 2 * R.card ≤ Fintype.card V ∧
      ∀ v, v ∉ R → ∃ w ∈ R, G.Adj v w := by
  classical
  obtain ⟨F, hFG, hF, hreach⟩ := G.exists_isAcyclic_reachable_eq_le
  let c := hF.coloringTwo
  have hneigh (v : V) : ∃ w, F.Adj v w := by
    obtain ⟨w, hvw⟩ := hG v
    have hr : F.Reachable v w := by rw [hreach]; exact hvw.reachable
    exact hr.nonempty_neighborSet_left hvw.ne
  let A : Finset V := Finset.univ.filter (fun v => c v = 0)
  let B : Finset V := Finset.univ.filter (fun v => c v ≠ 0)
  have hab : A.card + B.card = Fintype.card V := by
    exact Finset.card_filter_add_card_filter_not _
  have hcolor {v w : V} (hvw : F.Adj v w) : c v ≠ c w := c.valid hvw
  by_cases h : A.card ≤ B.card
  · refine ⟨A, by omega, ?_⟩
    intro v hv
    obtain ⟨w, hvw⟩ := hneigh v
    have hv0 : c v ≠ 0 := by simpa [A] using hv
    have hw0 : c w = 0 := by
      have hv1 : c v = 1 := by omega
      have hn := hcolor hvw
      omega
    exact ⟨w, by simp [A, hw0], hFG hvw⟩
  · refine ⟨B, by omega, ?_⟩
    intro v hv
    obtain ⟨w, hvw⟩ := hneigh v
    have hv0 : c v = 0 := by simpa [B] using hv
    have hw0 : c w ≠ 0 := by simpa [hv0] using (hcolor hvw).symm
    exact ⟨w, by simp [B, hw0], hFG hvw⟩

lemma powerset_weight_le_exp {V : Type*} [DecidableEq V] (S : Finset V)
    (p : V → ℝ) (hp : ∀ v, 0 ≤ p v) :
    (∑ L ∈ S.powerset, ∏ v ∈ L, p v) ≤ Real.exp (∑ v ∈ S, p v) := by
  rw [← Finset.prod_one_add, Real.exp_sum]
  apply Finset.prod_le_prod
  · intro v _; exact add_nonneg (by norm_num) (hp v)
  · intro v _
    have h := Real.add_one_le_exp (p v)
    linarith

lemma fixed_size_weight_le {V : Type*} [DecidableEq V] (S : Finset V)
    (p : V → ℝ) (hp : ∀ v, 0 ≤ p v) (m : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    (∑ L ∈ S.powersetCard m, ∏ v ∈ L, p v) ≤
      δ^m * Real.exp ((∑ v ∈ S, p v)/δ) := by
  have hsplit (L : Finset V) (hL : L ∈ S.powersetCard m) :
      (∏ v ∈ L, p v) = δ^m * ∏ v ∈ L, (p v / δ) := by
    rw [Finset.prod_div_distrib, Finset.prod_const, (Finset.mem_powersetCard.mp hL).2]
    field_simp
  calc
    _ = δ^m * ∑ L ∈ S.powersetCard m, ∏ v ∈ L, (p v/δ) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl hsplit
    _ ≤ δ^m * ∑ L ∈ S.powerset, ∏ v ∈ L, (p v/δ) := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg hδ.le _)
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro L hL
        exact Finset.mem_powerset.mpr (Finset.mem_powersetCard.mp hL).1
      · intro L _ _; exact Finset.prod_nonneg (fun v _ => div_nonneg (hp v) hδ.le)
    _ ≤ δ^m * Real.exp (∑ v ∈ S, p v/δ) :=
      mul_le_mul_of_nonneg_left
        (powerset_weight_le_exp S (fun v => p v/δ) (fun v => div_nonneg (hp v) hδ.le))
        (pow_nonneg hδ.le _)
    _ = _ := by rw [Finset.sum_div]

lemma neighborhood_weight_le {V : Type*} [Fintype V] (G : SimpleGraph V)
    (p : V → ℝ) (hp : ∀ v, 0 ≤ p v) (δ : ℝ)
    (hdeg : ∀ v, (∑ w, if G.Adj v w then p w else 0) ≤ δ) (R : Finset V) :
    (∑ w ∈ neighborhood G R, p w) ≤ R.card * δ := by
  classical
  calc
    _ ≤ ∑ w ∈ neighborhood G R, ∑ v ∈ R, if G.Adj v w then p w else 0 := by
      apply Finset.sum_le_sum
      intro w hw
      obtain ⟨v, hv, hvw⟩ := (Finset.mem_filter.mp hw).2
      have h : (if G.Adj v w then p w else 0) ≤
          ∑ u ∈ R, if G.Adj u w then p w else 0 :=
        Finset.single_le_sum (f := fun u => if G.Adj u w then p w else 0) (fun u _ => by split_ifs; exact hp w; exact le_rfl) hv
      simpa only [ite_eq_left hvw] using h
    _ ≤ ∑ w, ∑ v ∈ R, if G.Adj v w then p w else 0 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro w _ _
      exact Finset.sum_nonneg (fun v _ => by split_ifs; exact hp w; exact le_rfl)
    _ = ∑ v ∈ R, ∑ w, if G.Adj v w then p w else 0 := Finset.sum_comm
    _ ≤ ∑ v ∈ R, δ := Finset.sum_le_sum (fun v _ => hdeg v)
    _ = _ := by simp

lemma root_leaves_weight_le {V : Type*} [Fintype V] (G : SimpleGraph V)
    (p : V → ℝ) (hp : ∀ v, 0 ≤ p v) (k : ℕ) (δ : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hdeg : ∀ v, (∑ w, if G.Adj v w then p w else 0) ≤ δ)
    (R : Finset V) (hR : 2 * R.card ≤ k) :
    (∑ L ∈ (neighborhood G R).powersetCard (k-R.card), ∏ v ∈ L, p v) ≤
      δ^((k:ℝ)/2) * Real.exp R.card := by
  classical
  have hmass := neighborhood_weight_le G p hp δ hdeg R
  have hpow : δ^(k-R.card) ≤ δ^((k:ℝ)/2) := by
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_ge hδ hδ1
    have hr : R.card ≤ k := by omega
    rw [Nat.cast_sub hr]
    have hh : (2:ℝ)*R.card ≤ k := by exact_mod_cast hR
    linarith
  apply (fixed_size_weight_le (neighborhood G R) p hp _ δ hδ).trans
  apply mul_le_mul hpow
  · apply Real.exp_le_exp.mpr
    exact (div_le_iff₀ hδ).mpr hmass
  · positivity
  · positivity

lemma small_dominating_subset {V : Type*} [Fintype V] (G : SimpleGraph V)
    (S : Finset V) (hS : NoIsolated G S) :
    ∃ R : Finset V, R ⊆ S ∧ 2 * R.card ≤ S.card ∧ S \ R ⊆ neighborhood G R := by
  classical
  let H := G.induce (S : Set V)
  have hH : ∀ v : S, ∃ w : S, H.Adj v w := by
    intro v
    obtain ⟨w, hw, hvw⟩ := hS v v.2
    exact ⟨⟨w, hw⟩, hvw⟩
  obtain ⟨R, hR, hdom⟩ := small_dominating_set H hH
  let T := R.image (fun v : S => (v : V))
  have hc : T.card = R.card := Finset.card_image_of_injective _ Subtype.val_injective
  refine ⟨T, ?_, ?_, ?_⟩
  · intro v hv
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hv
    exact w.2
  · simpa [hc, H] using hR
  · intro v hv
    have hvS := (Finset.mem_sdiff.mp hv).1
    have hvR : (⟨v, hvS⟩ : S) ∉ R := by
      intro hh
      exact (Finset.mem_sdiff.mp hv).2 (Finset.mem_image.mpr ⟨⟨v,hvS⟩, hh, rfl⟩)
    obtain ⟨w, hw, hvw⟩ := hdom ⟨v,hvS⟩ hvR
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ⟨w, Finset.mem_image.mpr ⟨w,hw,rfl⟩, hvw.symm⟩⟩

lemma noIsolated_weight_le {V : Type*} [Fintype V] (G : SimpleGraph V)
    (p : V → ℝ) (hp : ∀ v, 0 ≤ p v) (k : ℕ) (δ : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hdeg : ∀ v, (∑ w, if G.Adj v w then p w else 0) ≤ δ) :
    (∑ S : {S : Finset V // S.card = k ∧ NoIsolated G S}, ∏ v ∈ S.val, p v) ≤
      δ^((k:ℝ)/2) * Real.exp (Real.exp 1 * ∑ v, p v) := by
  classical
  let I := {S : Finset V // S.card = k ∧ NoIsolated G S}
  let root (S : I) := (small_dominating_subset G S.val S.property.2).choose
  have hroot (S : I) : root S ⊆ S.val ∧ 2*(root S).card ≤ k ∧
      S.val \ root S ⊆ neighborhood G (root S) := by
    simpa only [root, S.property.1] using
      (small_dominating_subset G S.val S.property.2).choose_spec
  let enc (S : I) : Finset V × Finset V := (root S, S.val \ root S)
  have hrec (S : I) : (enc S).1 ∪ (enc S).2 = S.val :=
    Finset.union_sdiff_of_subset (hroot S).1
  have hinj : Function.Injective enc := by
    intro S T h
    apply Subtype.ext
    rw [← hrec S, ← hrec T, h]
  let W (z : Finset V × Finset V) : ℝ :=
    if 2*z.1.card ≤ k ∧ z.2 ∈ (neighborhood G z.1).powersetCard (k-z.1.card)
    then (∏ v ∈ z.1, p v) * ∏ v ∈ z.2, p v else 0
  have hW (z : Finset V × Finset V) : 0 ≤ W z := by
    dsimp [W]
    split_ifs
    · exact mul_nonneg (Finset.prod_nonneg (fun v _ => hp v))
        (Finset.prod_nonneg (fun v _ => hp v))
    · exact le_rfl
  have hwenc (S : I) : W (enc S) = ∏ v ∈ S.val, p v := by
    have hmem : (enc S).2 ∈ (neighborhood G (enc S).1).powersetCard (k-(enc S).1.card) := by
      refine Finset.mem_powersetCard.mpr ⟨(hroot S).2.2, ?_⟩
      change (S.val \ root S).card = k-(root S).card
      rw [Finset.card_sdiff_of_subset (hroot S).1, S.property.1]
    dsimp only [W]
    rw [ite_eq_left ⟨(hroot S).2.1,hmem⟩]
    exact (mul_comm _ _).trans (Finset.prod_sdiff (hroot S).1)
  have hsum : (∑ S : I, ∏ v ∈ S.val, p v) ≤ ∑ z, W z := by
    calc
      _ = ∑ z ∈ Finset.univ.image enc, W z := by
        rw [Finset.sum_image (fun S _ T _ h => hinj h)]
        exact Finset.sum_congr rfl (fun S _ => (hwenc S).symm)
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun z _ _ => hW z)
  apply hsum.trans
  rw [Fintype.sum_prod_type]
  calc
    (∑ R : Finset V, ∑ L : Finset V, W (R,L)) ≤
        ∑ R : Finset V, δ^((k:ℝ)/2) * Real.exp R.card * ∏ v ∈ R, p v := by
      apply Finset.sum_le_sum
      intro R _
      by_cases hR : 2*R.card ≤ k
      · have he : (∑ L : Finset V, W (R,L)) =
            (∏ v ∈ R, p v) *
              ∑ L ∈ (neighborhood G R).powersetCard (k-R.card), ∏ v ∈ L, p v := by
          simp only [W, hR, true_and]
          rw [← Finset.sum_filter]
          simp only [Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.mul_sum]
        rw [he]
        have h := mul_le_mul_of_nonneg_left (root_leaves_weight_le G p hp k δ hδ hδ1 hdeg R hR)
          (Finset.prod_nonneg (s := R) (fun v _ => hp v))
        simpa only [mul_comm, mul_left_comm, mul_assoc] using h
      · simp only [W, hR, false_and, ite_false, Finset.sum_const_zero]
        exact mul_nonneg (mul_nonneg (Real.rpow_nonneg hδ.le _) (Real.exp_pos _).le)
          (Finset.prod_nonneg (fun v _ => hp v))
    _ = δ^((k:ℝ)/2) * ∑ R : Finset V, ∏ v ∈ R, (Real.exp 1 * p v) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro R _
      rw [Finset.prod_mul_distrib, Finset.prod_const, ← Real.exp_nat_mul]
      simp only [mul_one, mul_assoc]
    _ ≤ δ^((k:ℝ)/2) * Real.exp (∑ v, Real.exp 1 * p v) := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hδ.le _)
      simpa only [Finset.powerset_univ] using
        powerset_weight_le_exp Finset.univ (fun v => Real.exp 1 * p v)
          (fun v => mul_nonneg (Real.exp_pos _).le (hp v))
    _ = _ := by rw [← Finset.mul_sum]


lemma noIsolated_probability_le {V Ω : Type*} [Fintype V] [Fintype Ω]
    (G : SimpleGraph V) (O : Ω → Finset V) (k : ℕ)
    (hcard : ∀ ω, (O ω).card = k) (p : V → ℝ) (hp : ∀ v, 0 ≤ p v)
    (hcyl : ∀ D, inclusionMoment O D ≤ ∏ v ∈ D, p v)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hdeg : ∀ v, (∑ w, if G.Adj v w then p w else 0) ≤ δ) :
    finiteMean (fun ω => if NoIsolated G (O ω) then (1:ℝ) else 0) ≤
      δ^((k:ℝ)/2) * Real.exp (Real.exp 1 * ∑ v, p v) := by
  classical
  let I := {S : Finset V // S.card = k ∧ NoIsolated G S}
  calc
    _ ≤ finiteMean (fun ω => ∑ S : I, if S.val ⊆ O ω then (1:ℝ) else 0) := by
      apply finiteMean_mono
      intro ω
      split_ifs with h
      · exact (Finset.single_le_sum (f := fun S : I => if S.val ⊆ O ω then (1:ℝ) else 0)
          (fun S _ => by positivity) (Finset.mem_univ (⟨O ω,hcard ω,h⟩ : I))) |>.trans' (by simp)
      · positivity
    _ = ∑ S : I, inclusionMoment O S.val := by
      rw [finiteMean_sum]
      rfl
    _ ≤ ∑ S : I, ∏ v ∈ S.val, p v := Finset.sum_le_sum (fun S _ => hcyl S.val)
    _ ≤ _ := noIsolated_weight_le G p hp k δ hδ hδ1 hdeg

lemma typedSet_fiber {N X : Type*} [Fintype N] [Fintype X]
    (S : Finset (N × X)) : typedSet (fiber S) = S := by
  classical
  ext v
  simp

lemma typedSet_prod {N X : Type*} [Fintype N] [Fintype X]
    (A : N → Finset X) (p : N × X → ℝ) :
    (∏ v ∈ typedSet A, p v) = ∏ t, ∏ x ∈ A t, p (t,x) := by
  classical
  simp only [typedSet, Finset.prod_filter, Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro t _
  rw [← Finset.prod_filter]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]

lemma typedSet_card {N X : Type*} [Fintype N] [Fintype X]
    (A : N → Finset X) : (typedSet A).card = ∑ t, (A t).card := by
  classical
  simp only [Finset.card_eq_sum_ones, typedSet, Finset.sum_filter, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro t _
  rw [← Finset.sum_filter]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]

lemma subset_typedSet {N X : Type*} [Fintype N] [Fintype X]
    (A : N → Finset X) (D : Finset (N × X)) :
    D ⊆ typedSet A ↔ ∀ t, fiber D t ⊆ A t := by
  constructor
  · intro h t x hx
    exact mem_typedSet A (t,x) |>.mp (h (mem_fiber D t x |>.mp hx))
  · intro h v hv
    exact mem_typedSet A v |>.mpr (h v.1 (mem_fiber D v.1 v.2 |>.mpr hv))

end Thorp.SparseContact

end ThorpNine.Contact

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Contact_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Contact

namespace Thorp.SparseContact
open scoped BigOperators Classical

lemma typedMarks_card {N : Type*} [Fintype N] (d : ℕ)
    (A : N → Finset (Card d)) (ω : N → (SwitchIndex d → Bool)) :
    (typedMarks d A ω).card = ∑ t, (A t).card := by
  classical
  rw [typedMarks, typedSet_card]
  apply Finset.sum_congr rfl
  intro t _
  exact Finset.card_image_of_injective _ (butterflyPerm d (decodeButterfly d (ω t))).injective

lemma typedMarks_inclusion {N : Type*} [Fintype N] (d : ℕ)
    (A : N → Finset (Card d)) (D : Finset (N × Card d)) :
    inclusionMoment (typedMarks d A) D ≤
      ∏ v ∈ D, ((A v.1).card:ℝ)/(2:ℝ)^d := by
  classical
  have he : inclusionMoment (typedMarks d A) D =
      ∏ t, inclusionMoment (butterflyMarks d (A t)) (fiber D t) := by
    rw [inclusionMoment_eq]
    have hh (ω : N → (SwitchIndex d → Bool)) :
        (if D ⊆ typedMarks d A ω then (1:ℝ) else 0) =
        ∏ t, if fiber D t ⊆ butterflyMarks d (A t) (ω t) then (1:ℝ) else 0 := by
      rw [Fintype.prod_boole]
      simp only [typedMarks, subset_typedSet]
    rw [finiteMean_congr hh]
    simp only [inclusionMoment_eq]
    exact finiteMean_pi_prod (ι := N) (Ω := fun _ => SwitchIndex d → Bool)
      (fun t (ω : SwitchIndex d → Bool) =>
        if fiber D t ⊆ butterflyMarks d (A t) ω then (1:ℝ) else 0)
  have hprod : (∏ v ∈ D, ((A v.1).card:ℝ)/(2:ℝ)^d) =
      ∏ t, ∏ x ∈ fiber D t, ((A t).card:ℝ)/(2:ℝ)^d := by
    conv_lhs => rw [← typedSet_fiber D]
    exact typedSet_prod _ _
  rw [he, hprod]
  apply Finset.prod_le_prod
  · intro t _; exact inclusionMoment_nonneg _ _
  · intro t _
    simpa only [Finset.prod_const] using butterflyMarks_inclusion d (A t) (fiber D t)

lemma returnRoute_card {N : Type*} (d : ℕ) (b : N → Butterfly d) (v : N × Card d) :
    (returnRoute d b v).card = d := card_routeDomain _ _ _

lemma mem_returnRoute {N : Type*} (d : ℕ) (b : N → Butterfly d)
    (t : N) (y : Card d) (i : SwitchIndex d) :
    i ∈ returnRoute d b (t,y) ↔
      y = butterflyPerm d (b t) (switchUsers d (b t) i).1 ∨
      y = butterflyPerm d (b t) (switchUsers d (b t) i).2 := by
  have h := mem_routeDomain_iff_user d (b t) ((butterflyPerm d (b t)).symm y) i
  simpa only [Equiv.apply_symm_apply, returnRoute, Equiv.eq_symm_apply, eq_comm] using h

lemma returnRoute_incidence {N : Type*} [Fintype N] (d : ℕ) (b : N → Butterfly d)
    (p : N → ℝ) (i : SwitchIndex d) :
    (∑ v : N × Card d, if i ∈ returnRoute d b v then p v.1 else 0) =
      2 * ∑ t, p t := by
  classical
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  have hne : butterflyPerm d (b t) (switchUsers d (b t) i).1 ≠
      butterflyPerm d (b t) (switchUsers d (b t) i).2 :=
    (butterflyPerm d (b t)).injective.ne (switchUsers_ne d (b t) i)
  simp only [mem_returnRoute]
  have he (y : Card d) :
      (if y = butterflyPerm d (b t) (switchUsers d (b t) i).1 ∨
        y = butterflyPerm d (b t) (switchUsers d (b t) i).2 then p t else 0) =
      (if y = butterflyPerm d (b t) (switchUsers d (b t) i).1 then p t else 0) +
      (if y = butterflyPerm d (b t) (switchUsers d (b t) i).2 then p t else 0) := by
    split_ifs <;> simp_all
  simp only [he, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

lemma returnGraph_degree {N : Type*} [Fintype N] (d : ℕ) (b : N → Butterfly d)
    (p : N → ℝ) (hp : ∀ t, 0 ≤ p t) (v : N × Card d) :
    (∑ w, if (returnGraph d b).Adj v w then p w.1 else 0) ≤
      2*d*∑ t, p t := by
  classical
  calc
    _ ≤ ∑ w, ∑ i ∈ returnRoute d b v, if i ∈ returnRoute d b w then p w.1 else 0 := by
      apply Finset.sum_le_sum
      intro w _
      split_ifs with h
      · obtain ⟨i, hi, hw⟩ := Finset.not_disjoint_iff.mp h.2
        have hh := Finset.single_le_sum
          (f := fun i => if i ∈ returnRoute d b w then p w.1 else 0)
          (fun i _ => by split_ifs; exact hp _; exact le_rfl) hi
        simpa only [ite_eq_left hw] using hh
      · exact Finset.sum_nonneg (fun i _ => by split_ifs; exact hp _; exact le_rfl)
    _ = ∑ i ∈ returnRoute d b v, ∑ w, if i ∈ returnRoute d b w then p w.1 else 0 :=
      Finset.sum_comm
    _ = _ := by simp only [returnRoute_incidence, Finset.sum_const, returnRoute_card,
        nsmul_eq_mul]; ring

lemma typed_weight_sum {N : Type*} [Fintype N] (d : ℕ)
    (A : N → Finset (Card d)) :
    (∑ v : N × Card d, ((A v.1).card:ℝ)/(2:ℝ)^d) = ∑ t, ((A t).card:ℝ) := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro t _
  simp only [Finset.sum_const, Finset.card_univ, card_positions, Nat.cast_pow,
    Nat.cast_ofNat, nsmul_eq_mul]
  field_simp

lemma mixed_return_noIsolated {N : Type*} [Fintype N] (d : ℕ)
    (A : N → Finset (Card d)) (b : N → Butterfly d) (k : ℕ)
    (hk : ∑ t, (A t).card = k)
    (hδ : 0 < 2*(d:ℝ)*k/(2:ℝ)^d) (hδ1 : 2*(d:ℝ)*k/(2:ℝ)^d ≤ 1) :
    finiteMean (fun ω : N → (SwitchIndex d → Bool) =>
      if NoIsolated (returnGraph d b) (typedMarks d A ω) then (1:ℝ) else 0) ≤
      (2*(d:ℝ)*k/(2:ℝ)^d)^((k:ℝ)/2) * Real.exp (Real.exp 1*k) := by
  have hs : (∑ t, ((A t).card:ℝ)) = k := by exact_mod_cast hk
  have hm := noIsolated_probability_le (returnGraph d b) (typedMarks d A) k
    (fun ω => (typedMarks_card d A ω).trans hk)
    (fun v => ((A v.1).card:ℝ)/(2:ℝ)^d) (fun v => by positivity)
    (typedMarks_inclusion d A) _ hδ hδ1
    (fun v => (returnGraph_degree d b (fun t => ((A t).card:ℝ)/(2:ℝ)^d)
      (fun t => by positivity) v).trans_eq (by rw [← Finset.sum_div, hs]; ring))
  simpa only [typed_weight_sum, hs] using hm


lemma mean_fresh_cylinder {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (v : ι → Bool) (f : (ι → Bool) → ℝ)
    (hf : ∀ i ∈ s, ∀ ω, f (QueryTree.flipCoin i ω) = f ω) :
    finiteMean (fun ω => if ∀ i ∈ s, ω i = v i then f ω else 0) =
      finiteMean f / (2:ℝ)^s.card := by
  induction s using Finset.induction_on with
  | empty => simp [finiteMean]
  | @insert i s hi ih =>
    let g := fun ω => if ∀ j ∈ s, ω j = v j then f ω else 0
    have hg : ∀ ω, g (QueryTree.flipCoin i ω) = g ω := by
      intro ω
      have he : (∀ j ∈ s, QueryTree.flipCoin i ω j = v j) ↔ ∀ j ∈ s, ω j = v j := by
        apply forall₂_congr
        intro j hj
        rw [QueryTree.flipCoin_apply_ne i j (fun h => hi (h ▸ hj))]
      simp only [g, he, hf i (Finset.mem_insert_self _ _) ω]
    have he (ω : ι → Bool) :
        (if ∀ j ∈ insert i s, ω j = v j then f ω else 0) =
        (if ω i = v i then g ω else 0) := by
      by_cases h : ω i = v i <;> simp [h,g]
    rw [finiteMean_congr he, QueryTree.mean_indicator_bit g i (v i) hg]
    have hs := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    change finiteMean (fun ω => if ∀ j ∈ s, ω j = v j then f ω else 0) / 2 = _
    rw [hs, Finset.card_insert_of_notMem hi, pow_succ]
    ring

lemma endpointProb_nonneg {L : Type*} (d : ℕ) (A : Finset L)
    (x y : L → Card d) : 0 ≤ endpointProb d A x y := by
  classical
  exact finiteMean_nonneg (fun _ => by positivity)

lemma endpointProb_insert_isolated {L : Type*} (d : ℕ) (A : Finset L)
    (x y : L → Card d) (i : L)
    (hiso : ∀ j ∈ A, Disjoint (routeDomain d (x i) (y i)) (routeDomain d (x j) (y j))) :
    endpointProb d (insert i A) x y = endpointProb d A x y / (2:ℝ)^d := by
  classical
  let f := fun ω : SwitchIndex d → Bool =>
    if ∀ j ∈ A, butterflyPerm d (decodeButterfly d ω) (x j) = y j then (1:ℝ) else 0
  have hf : ∀ t ∈ routeDomain d (x i) (y i), ∀ ω, f (QueryTree.flipCoin t ω) = f ω := by
    intro t ht ω
    have he : (∀ j ∈ A, butterflyPerm d (decodeButterfly d (QueryTree.flipCoin t ω)) (x j) = y j) ↔
        ∀ j ∈ A, butterflyPerm d (decodeButterfly d ω) (x j) = y j := by
      apply forall₂_congr
      intro j hj
      rw [butterfly_endpoint_iff, butterfly_endpoint_iff]
      apply forall₂_congr
      intro s hs
      rw [QueryTree.flipCoin_apply_ne t s (fun h =>
        Finset.disjoint_left.mp (hiso j hj) ht (h ▸ hs))]
    simp only [f, he]
  have he (ω : SwitchIndex d → Bool) :
      (if ∀ j ∈ insert i A, butterflyPerm d (decodeButterfly d ω) (x j) = y j then (1:ℝ) else 0) =
      (if ∀ t ∈ routeDomain d (x i) (y i), ω t = routeValue d (x i) (y i) t then f ω else 0) := by
    by_cases h : butterflyPerm d (decodeButterfly d ω) (x i) = y i
    · have hh := (butterfly_endpoint_iff d ω (x i) (y i)).mp h
      rw [ite_eq_left hh]
      simp only [Finset.forall_mem_insert, h, true_and, f]
    · have hh := mt (butterfly_endpoint_iff d ω (x i) (y i)).mpr h
      simp only [Finset.forall_mem_insert, h, false_and, hh, ite_false]
  change finiteMean _ = _
  rw [finiteMean_congr he, mean_fresh_cylinder _ _ f hf, card_routeDomain]
  rfl

lemma partialKernel_insert_isolated {L : Type*} [Fintype L] (d : ℕ) (A : Finset L)
    (x y : L → Card d) (i : L) (hi : i ∉ A)
    (hiso : ∀ j ∈ A, Disjoint (routeDomain d (x i) (y i)) (routeDomain d (x j) (y j))) :
    partialKernel d (insert i A) x y = partialKernel d A x y := by
  classical
  rw [partialKernel, endpointProb_insert_isolated d A x y i hiso,
    Finset.card_insert_of_notMem hi, pow_succ, partialKernel]
  field_simp

lemma alternating_cube_cancel {L : Type*} [Fintype L] (f : Finset L → ℝ)
    (i : L) (hf : ∀ A, i ∉ A → f (insert i A) = f A) :
    (∑ A : Finset L, (-1:ℝ)^A.card * f A) = 0 := by
  classical
  have hi : i ∈ (Finset.univ : Finset L) := Finset.mem_univ _
  rw [← Finset.powerset_univ, ← Finset.insert_erase hi, Finset.sum_powerset_insert]
  · rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro A hA
    have hiA : i ∉ A := fun hh => Finset.notMem_erase i Finset.univ
      ((Finset.mem_powerset.mp hA) hh)
    rw [hf A hiA, Finset.card_insert_of_notMem hiA, pow_succ]
    ring
  · exact Finset.notMem_erase _ _

lemma alternating_kernel_cancel {L : Type*} [Fintype L] (d : ℕ)
    (x y : L → Card d) (h : ¬ContactEvent d x y) :
    (∑ A : Finset L, (-1:ℝ)^A.card * partialKernel d A x y) = 0 := by
  classical
  unfold ContactEvent at h
  push Not at h
  obtain ⟨i, hi⟩ := h
  apply alternating_cube_cancel _ i
  intro A hiA
  apply partialKernel_insert_isolated d A x y i hiA
  intro j hj
  exact hi j (fun hij => hiA (hij ▸ hj))


lemma mem_labelsOf {L : Type*} (A : Finset L) (i : L) (t : Option L) :
    i ∈ labelsOf A t ↔ networkOf A i = t := by
  classical
  cases t with
  | none => simp [labelsOf, networkOf]
  | some j => by_cases hj : j ∈ A <;> by_cases hi : i ∈ A <;> simp_all [labelsOf, networkOf] <;> intro h <;> subst j <;> contradiction

lemma mixedTuple_eq_iff {L : Type*} (d : ℕ) (A : Finset L)
    (ω : Option L → (SwitchIndex d → Bool)) (x y : L → Card d) :
    mixedTuple d A ω x = y ↔ ∀ t, ∀ i ∈ labelsOf A t,
      butterflyPerm d (decodeButterfly d (ω t)) (x i) = y i := by
  constructor
  · intro h t i hi
    have he := congrFun h i
    simpa only [mixedTuple, mem_labelsOf A i t |>.mp hi] using he
  · intro h
    funext i
    exact h (networkOf A i) i (mem_labelsOf A i _ |>.mpr rfl)

lemma mixedReturn_eq_iff {L : Type*} (d : ℕ) (A : Finset L)
    (ω : Option L → (SwitchIndex d → Bool)) (y z : L → Card d) :
    mixedReturn d A ω y = z ↔ mixedTuple d A ω z = y := by
  constructor
  · intro h
    funext i
    exact (Equiv.symm_apply_eq _).mp (congrFun h i) |>.symm
  · intro h
    funext i
    exact (Equiv.symm_apply_eq _).mpr (congrFun h i).symm

lemma endpointProb_singleton {L : Type*} (d : ℕ) (i : L) (x y : L → Card d) :
    endpointProb d {i} x y = 1/(2:ℝ)^d := by
  classical
  simpa [endpointProb] using butterfly_single_card_uniform d (x i) (y i)

lemma mixedTuple_mass {L : Type*} [Fintype L] (d : ℕ) (A : Finset L)
    (x y : L → Card d) :
    finiteMean (fun ω : Option L → (SwitchIndex d → Bool) =>
      if mixedTuple d A ω x = y then (1:ℝ) else 0) = partialKernel d A x y := by
  classical
  have he (ω : Option L → (SwitchIndex d → Bool)) :
      (if mixedTuple d A ω x = y then (1:ℝ) else 0) =
      ∏ t, if ∀ i ∈ labelsOf A t, butterflyPerm d (decodeButterfly d (ω t)) (x i) = y i
        then (1:ℝ) else 0 := by
    simp only [Fintype.prod_boole, mixedTuple_eq_iff]
  rw [finiteMean_congr he]
  rw [finiteMean_pi_prod (fun t (w : SwitchIndex d → Bool) =>
    if ∀ i ∈ labelsOf A t, butterflyPerm d (decodeButterfly d w) (x i) = y i then (1:ℝ) else 0)]
  have hfac (t : Option L) : (finiteMean (fun w : SwitchIndex d → Bool =>
      if ∀ i ∈ labelsOf A t, butterflyPerm d (decodeButterfly d w) (x i) = y i then (1:ℝ) else 0)) =
      endpointProb d (labelsOf A t) x y := by
        unfold endpointProb
        apply finiteMean_congr
        intro w
        split_ifs <;> rfl
  simp only [hfac]
  rw [Fintype.prod_option]
  have hi (i : L) : endpointProb d (labelsOf A (some i)) x y =
      if i ∈ A then 1 else 1/(2:ℝ)^d := by
    by_cases h : i ∈ A
    · simp [labelsOf, h, endpointProb, finiteMean_const]
    · simp only [labelsOf, ite_eq_right h, endpointProb_singleton]
  rw [show labelsOf A none = A from rfl]
  simp only [hi]
  have hp : (∏ i : L, if i ∈ A then (1:ℝ) else 1/(2:ℝ)^d) =
      (1/(2:ℝ)^d)^((Fintype.card L) - A.card) := by
    rw [Finset.prod_ite]
    simp only [Finset.prod_const_one, one_mul]
    simp only [Finset.filter_not, Finset.filter_mem_eq_inter, Finset.univ_inter,
      Finset.prod_const, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ]
  rw [hp, partialKernel, one_div, inv_pow]
  have hc : A.card ≤ Fintype.card L := Finset.card_le_univ _
  have hn : (((2:ℝ)^d)^A.card) * (((2:ℝ)^d)^(Fintype.card L - A.card)) =
      ((2:ℝ)^d)^(Fintype.card L) := by rw [← pow_add, Nat.add_sub_of_le hc]
  have hnz : ((2:ℝ)^d)^(Fintype.card L) ≠ 0 := by positivity
  have hmz : ((2:ℝ)^d)^(Fintype.card L - A.card) ≠ 0 := by positivity
  field_simp
  rw [← hn]
  ring

lemma mixedReturn_mass {L : Type*} [Fintype L] (d : ℕ) (A : Finset L)
    (y z : L → Card d) :
    finiteMean (fun ω : Option L → (SwitchIndex d → Bool) =>
      if mixedReturn d A ω y = z then (1:ℝ) else 0) = partialKernel d A z y := by
  simpa only [mixedReturn_eq_iff] using mixedTuple_mass d A z y

lemma typedMarks_mixedInitial {L : Type*} [Fintype L] (d : ℕ) (A : Finset L)
    (x : L → Card d) (ω : Option L → (SwitchIndex d → Bool)) :
    typedMarks d (mixedInitial d A x) ω = Finset.univ.image
      (fun i => (networkOf A i, mixedTuple d A ω x i)) := by
  classical
  ext v
  simp only [typedMarks, mem_typedSet, butterflyMarks, mixedInitial,
    Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨z, ⟨i,hi,rfl⟩, hv⟩
    have ht := mem_labelsOf A i v.1 |>.mp hi
    exact ⟨i, Prod.ext ht (by simpa only [mixedTuple, ht] using hv)⟩
  · rintro ⟨i, hi⟩
    have ht := congrArg Prod.fst hi
    have hv := congrArg Prod.snd hi
    change networkOf A i = v.1 at ht
    change mixedTuple d A ω x i = v.2 at hv
    exact ⟨x i, ⟨i, mem_labelsOf A i v.1 |>.mpr ht, rfl⟩,
      by simpa only [mixedTuple, ht] using hv⟩

lemma typedTuple_injective {L : Type*} (d : ℕ) (A : Finset L)
    (x : L → Card d) (hx : Function.Injective x)
    (ω : Option L → (SwitchIndex d → Bool)) :
    Function.Injective (fun i => (networkOf A i, mixedTuple d A ω x i)) := by
  intro i j h
  have ht := congrArg Prod.fst h
  have hv := congrArg Prod.snd h
  change networkOf A i = networkOf A j at ht
  dsimp only [mixedTuple] at hv
  rw [ht] at hv
  exact hx ((butterflyPerm d (decodeButterfly d (ω (networkOf A j)))).injective hv)

lemma mixedInitial_card {L : Type*} [Fintype L] (d : ℕ) (A : Finset L)
    (x : L → Card d) (hx : Function.Injective x) :
    (∑ t, (mixedInitial d A x t).card) = Fintype.card L := by
  classical
  let ω : Option L → (SwitchIndex d → Bool) := fun _ _ => false
  rw [← typedMarks_card d (mixedInitial d A x) ω, typedMarks_mixedInitial,
    Finset.card_image_of_injective _ (typedTuple_injective d A x hx ω), Finset.card_univ]

lemma contactEvent_mixedReturn_iff {L : Type*} [Fintype L] (d : ℕ) (A : Finset L)
    (x : L → Card d) (hx : Function.Injective x)
    (ω b : Option L → (SwitchIndex d → Bool)) :
    ContactEvent d (mixedReturn d A b (mixedTuple d A ω x)) (mixedTuple d A ω x) ↔
      NoIsolated (returnGraph d (fun t => decodeButterfly d (b t)))
        (typedMarks d (mixedInitial d A x) ω) := by
  classical
  rw [typedMarks_mixedInitial]
  let f := fun i => (networkOf A i, mixedTuple d A ω x i)
  have hf : Function.Injective f := typedTuple_injective d A x hx ω
  constructor
  · intro h v hv
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨j,hij,hc⟩ := h i
    exact ⟨f j, Finset.mem_image.mpr ⟨j, Finset.mem_univ _,rfl⟩,
      hf.ne hij, hc⟩
  · intro h i
    obtain ⟨v,hv,hij,hc⟩ := h (f i) (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hv
    exact ⟨j, fun he => hij (congrArg f he), hc⟩

lemma probability_mixed_contact {L : Type*} [Fintype L] (d : ℕ) (A : Finset L)
    (x : L → Card d) (hx : Function.Injective x)
    (b : Option L → (SwitchIndex d → Bool))
    (hδ : 0 < 2*(d:ℝ)*(Fintype.card L)/(2:ℝ)^d)
    (hδ1 : 2*(d:ℝ)*(Fintype.card L)/(2:ℝ)^d ≤ 1) :
    finiteMean (fun ω : Option L → (SwitchIndex d → Bool) =>
      if ContactEvent d (mixedReturn d A b (mixedTuple d A ω x)) (mixedTuple d A ω x)
        then (1:ℝ) else 0) ≤
      (2*(d:ℝ)*(Fintype.card L)/(2:ℝ)^d)^((Fintype.card L:ℝ)/2) *
        Real.exp (Real.exp 1*(Fintype.card L)) := by
  classical
  simp only [contactEvent_mixedReturn_iff d A x hx]
  convert mixed_return_noIsolated d (mixedInitial d A x) (fun t => decodeButterfly d (b t))
      (Fintype.card L) (mixedInitial_card d A x hx) hδ hδ1 using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  exact Subsingleton.elim _ _


lemma finiteMean_pushforward {Ω X : Type*} [Fintype Ω] [Fintype X]
    (g : Ω → X) (f : X → ℝ) :
    finiteMean (fun ω => f (g ω)) =
      ∑ y, finiteMean (fun ω => if g ω = y then (1:ℝ) else 0) * f y := by
  classical
  simp_rw [← finiteMean_mul_const, ← finiteMean_sum]
  apply finiteMean_congr
  intro ω
  simp

lemma mixedTuple_expectation {L : Type*} [Fintype L] (d : ℕ) (A : Finset L)
    (x : L → Card d) (f : (L → Card d) → ℝ) :
    finiteMean (fun ω : Option L → (SwitchIndex d → Bool) => f (mixedTuple d A ω x)) =
      ∑ y, partialKernel d A x y * f y := by
  classical
  rw [finiteMean_pushforward (fun ω : Option L → (SwitchIndex d → Bool) => mixedTuple d A ω x) f]
  apply Finset.sum_congr rfl
  intro y _
  congr 1
  convert mixedTuple_mass d A x y using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  funext ω
  split_ifs <;> rfl

lemma mixedReturn_expectation {L : Type*} [Fintype L] (d : ℕ) (A : Finset L)
    (y : L → Card d) (f : (L → Card d) → ℝ) :
    finiteMean (fun ω : Option L → (SwitchIndex d → Bool) => f (mixedReturn d A ω y)) =
      ∑ z, partialKernel d A z y * f z := by
  classical
  rw [finiteMean_pushforward (fun ω : Option L → (SwitchIndex d → Bool) => mixedReturn d A ω y) f]
  apply Finset.sum_congr rfl
  intro z _
  congr 1
  convert mixedReturn_mass d A y z using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  funext ω
  split_ifs <;> rfl

lemma partialKernel_nonneg {L : Type*} [Fintype L] (d : ℕ) (A : Finset L)
    (x y : L → Card d) : 0 ≤ partialKernel d A x y :=
  mul_nonneg (by positivity) (endpointProb_nonneg d A x y)

lemma retainedKernel_nonneg {L : Type*} [Fintype L] (d : ℕ) (A : Finset L)
    (x : L ↪ Card d) (y : L → Card d) : 0 ≤ retainedKernel d A x y := by
  classical
  unfold retainedKernel
  split_ifs
  · exact partialKernel_nonneg d A x y
  · exact le_rfl

lemma retainedKernel_le {L : Type*} [Fintype L] (d : ℕ) (A : Finset L)
    (x : L ↪ Card d) (y : L → Card d) : retainedKernel d A x y ≤ partialKernel d A x y := by
  classical
  unfold retainedKernel
  split_ifs
  · exact le_rfl
  · exact partialKernel_nonneg d A x y

lemma retained_square_row {L : Type*} [Fintype L] (d : ℕ) (A : Finset L)
    (x : L ↪ Card d)
    (hδ : 0 < 2*(d:ℝ)*(Fintype.card L)/(2:ℝ)^d)
    (hδ1 : 2*(d:ℝ)*(Fintype.card L)/(2:ℝ)^d ≤ 1) :
    (∑ x' : L ↪ Card d, ∑ y : L → Card d, retainedKernel d A x y * retainedKernel d A x' y) ≤
      (2*(d:ℝ)*(Fintype.card L)/(2:ℝ)^d)^((Fintype.card L:ℝ)/2) *
        Real.exp (Real.exp 1*(Fintype.card L)) := by
  classical
  let f := fun y z : L → Card d => if ContactEvent d z y then (1:ℝ) else 0
  have hsub (y : L → Card d) : (∑ x' : L ↪ Card d, retainedKernel d A x' y) ≤
      ∑ z : L → Card d, partialKernel d A z y * f y z := by
    have he (x' : L ↪ Card d) : retainedKernel d A x' y = partialKernel d A x' y * f y x' := by
      unfold retainedKernel f
      split_ifs <;> ring
    simp_rw [he]
    rw [← Finset.sum_image (f := fun z => partialKernel d A z y * f y z)
      (Function.Embedding.coe_injective.injOn)]
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    intro z _ _
    exact mul_nonneg (partialKernel_nonneg d A z y) (by dsimp [f]; positivity)
  calc
    _ = ∑ y, retainedKernel d A x y * ∑ x' : L ↪ Card d, retainedKernel d A x' y := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ ≤ ∑ y, partialKernel d A x y * ∑ z : L → Card d, partialKernel d A z y * f y z := by
      apply Finset.sum_le_sum
      intro y _
      exact mul_le_mul (retainedKernel_le d A x y) (hsub y)
        (Finset.sum_nonneg (fun x' _ => retainedKernel_nonneg d A x' y)) (partialKernel_nonneg d A x y)
    _ = finiteMean (fun ω : Option L → (SwitchIndex d → Bool) =>
        finiteMean (fun b : Option L → (SwitchIndex d → Bool) =>
          f (mixedTuple d A ω x) (mixedReturn d A b (mixedTuple d A ω x)))) := by
      rw [mixedTuple_expectation d A x (fun y =>
        finiteMean (fun b : Option L → (SwitchIndex d → Bool) => f y (mixedReturn d A b y)))]
      simp only [mixedReturn_expectation]
    _ = finiteMean (fun b : Option L → (SwitchIndex d → Bool) =>
        finiteMean (fun ω : Option L → (SwitchIndex d → Bool) =>
          f (mixedTuple d A ω x) (mixedReturn d A b (mixedTuple d A ω x)))) := finiteMean_comm _
    _ ≤ _ := by
      apply (finiteMean_mono (fun b => probability_mixed_contact d A x x.injective b hδ hδ1)).trans_eq
      exact finiteMean_const _

lemma rectOperator_adjoint {X Y : Type*} [Fintype X] [Fintype Y]
    (P : X → Y → ℝ) : ContinuousLinearMap.adjoint (rectOperator P) =
      rectOperator (fun y x => P x y) := by
  apply Eq.symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro v w
  simp only [PiLp.inner_apply, RCLike.inner_apply, rectOperator_apply,
    map_sum, map_mul, Complex.conj_ofReal, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  ring

lemma rectOperator_comp_transpose {X Y : Type*} [Fintype X] [Fintype Y]
    (P : X → Y → ℝ) : (rectOperator P).comp (rectOperator (fun y x => P x y)) =
      rectOperator (fun x x' => ∑ y, P x y * P x' y) := by
  ext v x
  simp only [ContinuousLinearMap.comp_apply, rectOperator_apply, Finset.mul_sum,
    Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x' _
  apply Finset.sum_congr rfl
  intro y _
  ring

lemma rectOperator_norm_sq_le {X Y : Type*} [Fintype X] [Fintype Y]
    (P : X → Y → ℝ) (hP : ∀ x y, 0 ≤ P x y) (B : ℝ) (hB : 0 ≤ B)
    (hrow : ∀ x, (∑ x', ∑ y, P x y * P x' y) ≤ B) :
    ‖rectOperator P‖^2 ≤ B := by
  let S := fun x x' => ∑ y, P x y * P x' y
  have hs : ∀ x x', S x x' = S x' x := by
    intro x x'
    unfold S
    apply Finset.sum_congr rfl
    intro y _
    ring
  have hbound : ‖rectOperator S‖ ≤ B := by
    apply ContinuousLinearMap.opNorm_le_bound _ hB
    intro v
    exact DensityTransfer.schur_bound S
      (fun x x' => Finset.sum_nonneg (fun y _ => mul_nonneg (hP x y) (hP x' y))) B hB
      hrow (fun x' => by
        calc (∑ x, S x x') = ∑ x, S x' x := Finset.sum_congr rfl (fun x _ => hs x x')
             _ ≤ B := hrow x') v
  have hn := ContinuousLinearMap.norm_adjoint_comp_self
    (ContinuousLinearMap.adjoint (rectOperator P))
  rw [ContinuousLinearMap.adjoint_adjoint, (ContinuousLinearMap.adjoint.norm_map _),
    rectOperator_adjoint, rectOperator_comp_transpose] at hn
  rw [pow_two, ← hn]
  exact hbound

lemma retained_norm_sq {L : Type*} [Fintype L] (d : ℕ) (A : Finset L)
    (hδ : 0 < 2*(d:ℝ)*(Fintype.card L)/(2:ℝ)^d)
    (hδ1 : 2*(d:ℝ)*(Fintype.card L)/(2:ℝ)^d ≤ 1) :
    ‖rectOperator (retainedKernel d A)‖^2 ≤
      (2*(d:ℝ)*(Fintype.card L)/(2:ℝ)^d)^((Fintype.card L:ℝ)/2) *
        Real.exp (Real.exp 1*(Fintype.card L)) :=
  rectOperator_norm_sq_le _ (retainedKernel_nonneg d A) _ (by positivity)
    (fun x => retained_square_row d A x hδ hδ1)


lemma sum_injections {L α M : Type*} [Fintype L] [Fintype α] [AddCommMonoid M]
    (F : (L → α) → M) (hF : ∀ y, ¬Function.Injective y → F y = 0) :
    (∑ y : L → α, F y) = ∑ y : L ↪ α, F y := by
  classical
  rw [← Finset.sum_image Function.Embedding.coe_injective.injOn]
  apply Eq.symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro y _ hy
  apply hF y
  intro h
  exact hy (Finset.mem_image.mpr ⟨⟨y,h⟩, Finset.mem_univ _, rfl⟩)

@[simp] lemma zeroExtend_inj {L α : Type*} [Fintype L] [Fintype α]
    (f : EuclideanSpace ℂ (L ↪ α)) (y : L ↪ α) : zeroExtend f y = f y := by
  classical
  simp only [zeroExtend, WithLp.ofLp_toLp, dite_eq_left y.injective]
  congr 1

lemma zeroExtend_noninj {L α : Type*} [Fintype L] [Fintype α]
    (f : EuclideanSpace ℂ (L ↪ α)) (y : L → α) (hy : ¬Function.Injective y) : zeroExtend f y = 0 := by
  classical
  simp only [zeroExtend, WithLp.ofLp_toLp, dite_eq_right hy]

lemma sum_zeroExtend_mul {L α : Type*} [Fintype L] [Fintype α]
    (f : EuclideanSpace ℂ (L ↪ α)) (g : (L → α) → ℂ) :
    (∑ y : L → α, g y * zeroExtend f y) = ∑ y : L ↪ α, g y * f y := by
  rw [sum_injections _ (fun y hy => by rw [zeroExtend_noninj f y hy, mul_zero])]
  simp only [zeroExtend_inj]

lemma norm_zeroExtend {L α : Type*} [Fintype L] [Fintype α]
    (f : EuclideanSpace ℂ (L ↪ α)) : ‖zeroExtend f‖ = ‖f‖ := by
  have hs : ‖zeroExtend f‖^2 = ‖f‖^2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
      sum_injections _ (fun y hy => by rw [zeroExtend_noninj f y hy]; simp)]
    simp only [zeroExtend_inj]
  nlinarith [norm_nonneg (zeroExtend f), norm_nonneg f]

lemma partial_proper_zero {L : Type*} [Fintype L] (d : ℕ) (A : Finset L)
    (hA : A ≠ Finset.univ) (f : EuclideanSpace ℂ (L ↪ Card d)) (hf : Harmonic f) :
    rectOperator (fun (x : L ↪ Card d) (y : L → Card d) => partialKernel d A x y) (zeroExtend f) = 0 := by
  classical
  ext x
  rw [rectOperator_apply, sum_zeroExtend_mul]
  change (∑ y : L ↪ Card d, (partialKernel d A x y : ℂ) * f y) = 0
  simp only [partialKernel, endpointProb, finiteMean, Complex.ofReal_mul, Complex.ofReal_div,
    Complex.ofReal_sum, Complex.ofReal_natCast]
  simp_rw [div_eq_mul_inv, mul_assoc, ← Finset.mul_sum]
  rw [mul_eq_zero]
  right
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro ω _
  calc
    _ = ∑ y : L ↪ Card d, (↑(Fintype.card (SwitchIndex d → Bool)) : ℂ)⁻¹ *
        (if ∀ i ∈ A, y i = butterflyPerm d (decodeButterfly d ω) (x i) then f y else 0) :=
      by
        apply Finset.sum_congr rfl
        intro y _
        have hh : (∀ i ∈ A, butterflyPerm d (decodeButterfly d ω) (x i) = y i) ↔
            (∀ i ∈ A, y i = butterflyPerm d (decodeButterfly d ω) (x i)) :=
          forall₂_congr fun _ _ => eq_comm
        by_cases h : ∀ i ∈ A, butterflyPerm d (decodeButterfly d ω) (x i) = y i
        · simp only [ite_eq_left h, ite_eq_left (hh.mp h), Complex.ofReal_one, one_mul]
        · simp only [ite_eq_right h, ite_eq_right (mt hh.mpr h), Complex.ofReal_zero, zero_mul, mul_zero]
    _ = 0 := by
      rw [← Finset.mul_sum]
      apply mul_eq_zero_of_right
      convert hf A hA (fun i => butterflyPerm d (decodeButterfly d ω) (x i)) using 1
      all_goals try with_reducible_and_instances rfl
      apply Finset.sum_congr rfl
      intro y _
      split_ifs <;> rfl

lemma partial_full_action {L : Type*} [Fintype L] (d : ℕ)
    (f : EuclideanSpace ℂ (L ↪ Card d)) :
    rectOperator (fun (x : L ↪ Card d) (y : L → Card d) => partialKernel d Finset.univ x y) (zeroExtend f) =
      DensityTransfer.applyKernel (UnitaryFinite.actionKernel UnitaryFinite.tupleAction
        (fun ω : SwitchIndex d → Bool => butterflyPerm d (decodeButterfly d ω))) f := by
  classical
  ext x
  rw [rectOperator_apply, sum_zeroExtend_mul]
  apply Finset.sum_congr rfl
  intro y _
  congr 2
  simp only [partialKernel, Finset.card_univ, div_self (by positivity : ((2:ℝ)^d)^(Fintype.card L) ≠ 0),
    one_mul, endpointProb, UnitaryFinite.actionKernel]
  apply finiteMean_congr
  intro ω
  congr 1
  simp only [Finset.mem_univ, forall_const, Function.Embedding.ext_iff]
  rfl

lemma alternating_retained_eq {L : Type*} [Fintype L] (d : ℕ)
    (x : L ↪ Card d) (y : L → Card d) :
    (∑ A : Finset L, (-1:ℝ)^A.card * retainedKernel d A x y) =
      ∑ A : Finset L, (-1:ℝ)^A.card * partialKernel d A x y := by
  classical
  by_cases h : ContactEvent d x y
  · simp only [retainedKernel, ite_eq_left h]
  · simp only [retainedKernel, ite_eq_right h, mul_zero, Finset.sum_const_zero]
    exact (alternating_kernel_cancel d x y h).symm

lemma alternating_harmonic_action {L : Type*} [Fintype L] (d : ℕ)
    (f : EuclideanSpace ℂ (L ↪ Card d)) (hf : Harmonic f) :
    (∑ A : Finset L, ((-1:ℂ)^A.card) • rectOperator (retainedKernel d A) (zeroExtend f)) =
      ((-1:ℂ)^(Fintype.card L)) • DensityTransfer.applyKernel
        (UnitaryFinite.actionKernel UnitaryFinite.tupleAction
          (fun ω : SwitchIndex d → Bool => butterflyPerm d (decodeButterfly d ω))) f := by
  classical
  calc
    _ = ∑ A : Finset L, ((-1:ℂ)^A.card) •
        rectOperator (fun (x : L ↪ Card d) y => partialKernel d A x y) (zeroExtend f) := by
      ext x
      simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, rectOperator_apply, smul_eq_mul, Finset.mul_sum]
      rw [Finset.sum_comm, Finset.sum_comm (s := (Finset.univ : Finset (Finset L)))]
      apply Finset.sum_congr rfl
      intro y _
      simp_rw [← mul_assoc, ← Finset.sum_mul]
      congr 1
      have he := congrArg (fun t : ℝ => (t:ℂ)) (alternating_retained_eq d x y)
      simpa only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_neg,
        Complex.ofReal_one] using he
    _ = ((-1:ℂ)^(Fintype.card L)) •
        rectOperator (fun (x : L ↪ Card d) y => partialKernel d Finset.univ x y) (zeroExtend f) := by
      rw [Finset.sum_eq_single (Finset.univ : Finset L)]
      · simp only [Finset.card_univ]
      · intro A _ hA
        rw [partial_proper_zero d A hA f hf, smul_zero]
      · simp
    _ = _ := by rw [partial_full_action]

lemma harmonic_action_bound {L : Type*} [Fintype L] (d : ℕ)
    (f : EuclideanSpace ℂ (L ↪ Card d)) (hf : Harmonic f)
    (hδ : 0 < 2*(d:ℝ)*(Fintype.card L)/(2:ℝ)^d)
    (hδ1 : 2*(d:ℝ)*(Fintype.card L)/(2:ℝ)^d ≤ 1) :
    ‖DensityTransfer.applyKernel (UnitaryFinite.actionKernel UnitaryFinite.tupleAction
      (fun ω : SwitchIndex d → Bool => butterflyPerm d (decodeButterfly d ω))) f‖ ≤
      (2:ℝ)^(Fintype.card L) *
        Real.sqrt ((2*(d:ℝ)*(Fintype.card L)/(2:ℝ)^d)^((Fintype.card L:ℝ)/2) *
          Real.exp (Real.exp 1*(Fintype.card L))) * ‖f‖ := by
  classical
  let B := (2*(d:ℝ)*(Fintype.card L)/(2:ℝ)^d)^((Fintype.card L:ℝ)/2) *
          Real.exp (Real.exp 1*(Fintype.card L))
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hnorm (A : Finset L) : ‖rectOperator (retainedKernel d A)‖ ≤ Real.sqrt B := by
    have hh := retained_norm_sq d A hδ hδ1
    have hs := Real.sq_sqrt hB
    have hn := Real.sqrt_nonneg B
    nlinarith
  calc
    _ = ‖((-1:ℂ)^(Fintype.card L)) • DensityTransfer.applyKernel
        (UnitaryFinite.actionKernel UnitaryFinite.tupleAction
          (fun ω : SwitchIndex d → Bool => butterflyPerm d (decodeButterfly d ω))) f‖ := by
      simp only [norm_smul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    _ = ‖∑ A : Finset L, ((-1:ℂ)^A.card) • rectOperator (retainedKernel d A) (zeroExtend f)‖ := by
      rw [alternating_harmonic_action d f hf]
    _ ≤ ∑ A : Finset L, ‖((-1:ℂ)^A.card) • rectOperator (retainedKernel d A) (zeroExtend f)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ A : Finset L, Real.sqrt B * ‖f‖ := by
      apply Finset.sum_le_sum
      intro A _
      simp only [norm_smul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
      calc _ ≤ ‖rectOperator (retainedKernel d A)‖ * ‖zeroExtend f‖ :=
              ContinuousLinearMap.le_opNorm _ _
           _ ≤ Real.sqrt B * ‖zeroExtend f‖ := mul_le_mul_of_nonneg_right (hnorm A) (norm_nonneg _)
           _ = _ := by rw [norm_zeroExtend]
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_finset, nsmul_eq_mul,
      Nat.cast_pow, Nat.cast_ofNat]; ring

section Generic
variable {L V : Type*} [Fintype L] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteDimensional ℂ V]

lemma sample_sweep_bound_q77_oai (d : ℕ) (ρ : Representation ℂ (Equiv.Perm (Card d)) V)
    [Representation.IsIrreducible ρ] (hρ : UnitaryFinite.IsUnitary ρ)
    (x₀ : L ↪ Card d) (w : V) (hw : UnitaryFinite.IsFixed UnitaryFinite.tupleAction x₀ ρ w)
    (hn : ‖w‖ = 1)
    (hh : ∀ v, Harmonic (UnitaryFinite.normalizedCoefficient UnitaryFinite.tupleAction x₀
      (UnitaryFinite.tupleAction_transitive x₀) ρ w v))
    (hδ : 0 < 2*(d:ℝ)*(Fintype.card L)/(2:ℝ)^d)
    (hδ1 : 2*(d:ℝ)*(Fintype.card L)/(2:ℝ)^d ≤ 1) :
    ‖UnitaryFinite.sampleOperator ρ (fun ω : SwitchIndex d → Bool => butterflyPerm d (decodeButterfly d ω))‖ ≤
      (2:ℝ)^(Fintype.card L) *
        Real.sqrt ((2*(d:ℝ)*(Fintype.card L)/(2:ℝ)^d)^((Fintype.card L:ℝ)/2) *
          Real.exp (Real.exp 1*(Fintype.card L))) := by
  rw [← ContinuousLinearMap.adjoint.norm_map (UnitaryFinite.sampleOperator ρ
    (fun ω : SwitchIndex d → Bool => butterflyPerm d (decodeButterfly d ω))),
    ← UnitaryFinite.sampleOperator_inv ρ hρ]
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  rw [UnitaryFinite.sampleOperator_inv_apply]
  have ha := harmonic_action_bound d _ (hh v) hδ hδ1
  rw [UnitaryFinite.coefficient_random UnitaryFinite.tupleAction x₀
    (UnitaryFinite.tupleAction_transitive x₀) ρ hρ _ w hw,
    UnitaryFinite.normalizedCoefficient_norm _ _ _ ρ hρ w hw hn,
    UnitaryFinite.normalizedCoefficient_norm _ _ _ ρ hρ w hw hn] at ha
  exact ha

end Generic

end Thorp.SparseContact

end ThorpNine.Contact

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.ThorpNine.Contact.Thorp.SparseContact.sample_sweep_bound_q77_oai.{u_1, u_2} := @OAI.ThorpNine.Contact.Thorp.SparseContact.sample_sweep_bound_q77_oai.{u_1, u_2}
