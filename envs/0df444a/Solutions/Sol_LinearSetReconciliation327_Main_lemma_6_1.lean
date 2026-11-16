-- Prove2me | solution 1 for LinearSetReconciliation327.Main.lemma_6_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @djwj233
-- created : 2026-11-15T14:54:01.498914+00:00
-- url     : https://prove2.me/submissions/783b841c-b841-454c-9ce0-ef2b66b37e83
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_Basic
import Definitions.Def_LinearSetReconciliation327_Main_Framework
import Definitions.Def_LinearSetReconciliation327_Main_TopLevel
import Theorems.Thm_LinearSetReconciliation327_Main_lemma_4_5
import Theorems.Thm_LinearSetReconciliation327_Main_proposition_2_1

open scoped ENNReal
open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

namespace LinearSetReconciliation327.Main

/-! ## Generic finite-probability helpers -/

lemma prU_nonneg {α : Type} [Fintype α] (P : α → Prop) : 0 ≤ prU P := by
  unfold prU
  positivity

lemma prU_le_one {α : Type} [Fintype α] [Nonempty α] (P : α → Prop) : prU P ≤ 1 := by
  classical
  unfold prU
  have hc : (0:ℝ) < (Fintype.card α : ℝ) := by exact_mod_cast Fintype.card_pos
  rw [div_le_one hc]
  have h := Finset.card_filter_le (s := (univ : Finset α)) (p := P)
  have h2 : ((univ.filter P).card : ℝ) ≤ ((univ : Finset α).card : ℝ) := by exact_mod_cast h
  simpa using h2

lemma expU_le {α : Type} [Fintype α] {f g : α → ℝ} (h : ∀ a, f a ≤ g a) : expU f ≤ expU g := by
  unfold expU
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun a _ => h a) (by positivity)

lemma card_filter_classical {α : Type} (s : Finset α) (p : α → Prop) [DecidablePred p] :
    ((s.filter p).card : ℝ) =
      ((@Finset.filter α p (fun a => Classical.propDecidable (p a)) s).card : ℝ) :=
  congrArg (fun z : Finset α => (z.card : ℝ))
    (Finset.filter_congr_decidable s p (fun a => Classical.propDecidable (p a))).symm

lemma expU_indicator {α : Type} [Fintype α] (P : α → Prop) [DecidablePred P] :
    expU (fun a => if P a then (1:ℝ) else 0) = prU P := by
  have hsum : (∑ a : α, if P a then (1:ℝ) else 0) =
      ((@Finset.filter α P (fun a => Classical.propDecidable (P a)) univ).card : ℝ) := by
    have h1 : (∑ a : α, if P a then (1:ℝ) else 0) =
        ((∑ a : α, if P a then (1:ℕ) else 0 : ℕ) : ℝ) := by
      rw [Nat.cast_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      split_ifs <;> simp
    rw [h1, Finset.sum_boole]
    exact card_filter_classical univ P
  unfold expU prU
  rw [hsum]

lemma expU_sum_finset {α ι : Type} [Fintype α] (s : Finset ι) (f : ι → α → ℝ) :
    expU (fun a => ∑ i ∈ s, f i a) = ∑ i ∈ s, expU (f i) := by
  unfold expU
  rw [← Finset.sum_div, Finset.sum_comm]

lemma expU_const {α : Type} [Fintype α] [Nonempty α] (c : ℝ) : expU (fun _ : α => c) = c := by
  unfold expU
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hc : ((Fintype.card α : ℕ) : ℝ) ≠ 0 := by
    have h : 0 < Fintype.card α := Fintype.card_pos
    exact_mod_cast h.ne'
  field_simp

lemma expU_fst_prod {α β : Type} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    (f : α → ℝ) : expU (fun p : α × β => f p.1) = expU f := by
  have hsum : (∑ p : α × β, f p.1) = (Fintype.card β : ℝ) * (∑ a : α, f a) := by
    rw [← Finset.univ_product_univ, Finset.sum_product]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [← Finset.mul_sum]
  have hb : ((Fintype.card β : ℕ) : ℝ) ≠ 0 := by
    have h : 0 < Fintype.card β := Fintype.card_pos
    exact_mod_cast h.ne'
  have ha : ((Fintype.card α : ℕ) : ℝ) ≠ 0 := by
    have h : 0 < Fintype.card α := Fintype.card_pos
    exact_mod_cast h.ne'
  unfold expU
  rw [hsum, Fintype.card_prod, Nat.cast_mul]
  field_simp

lemma prU_equiv {α β : Type} [Fintype α] [Fintype β] (e : α ≃ β) (P : β → Prop) :
    prU (fun a => P (e a)) = prU P := by
  classical
  unfold prU
  rw [Fintype.card_congr e]
  have h : (univ.filter fun a : α => P (e a)).card = (univ.filter P).card := by
    refine Finset.card_bij (fun a _ => e a) ?_ ?_ ?_
    · intro a ha
      simpa using ha
    · intro a1 _ a2 _ h
      exact e.injective h
    · intro b hb
      exact ⟨e.symm b, by simpa using hb, by simp⟩
  rw [h]

lemma expU_equiv {α β : Type} [Fintype α] [Fintype β] (e : α ≃ β) (f : β → ℝ) :
    expU (fun a => f (e a)) = expU f := by
  unfold expU
  rw [Fintype.card_congr e, Equiv.sum_comp e f]

/-! ## Row geometry -/

open Classical in
lemma mem_rowImage {N m : ℕ} {π : Equiv.Perm (Fin N)} {j : ℕ} {S : Finset ℕ} {y : ℕ} :
    y ∈ rowImage N m π j S ↔
      ∃ i : Fin N, i.val ∈ S ∧ (π i).val % m = j ∧ (π i).val / m = y := by
  rw [rowImage, Finset.mem_image]
  constructor
  · rintro ⟨i, hi, rfl⟩
    rw [Finset.mem_filter] at hi
    exact ⟨i, hi.2.1, hi.2.2, rfl⟩
  · rintro ⟨i, hS, hmod, hdiv⟩
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hS, hmod⟩, hdiv⟩

lemma rowImage_mono {N m : ℕ} (π : Equiv.Perm (Fin N)) (j : ℕ) {S T : Finset ℕ}
    (h : S ⊆ T) : rowImage N m π j S ⊆ rowImage N m π j T := by
  intro y hy
  rw [mem_rowImage] at hy ⊢
  obtain ⟨i, hiS, h1, h2⟩ := hy
  exact ⟨i, h hiS, h1, h2⟩

lemma rowImage_card_le {N m : ℕ} (π : Equiv.Perm (Fin N)) (j : ℕ) {S T : Finset ℕ}
    (h : S ⊆ T) : (rowImage N m π j S).card ≤ (rowImage N m π j T).card :=
  Finset.card_le_card (rowImage_mono π j h)

/-- A position `t < N` sits in row `t % m` at local index `t / m`, which is smaller than the row
length. -/
lemma div_lt_rowLen {N m : ℕ} (hm : 0 < m) {t : ℕ} (ht : t < N) :
    t / m < rowLen N m (t % m) := by
  set r := t % m
  have hrlt : r < m := Nat.mod_lt _ hm
  have ht_eq : m * (t / m) + r = t := Nat.div_add_mod t m
  have hmaps : Set.MapsTo (fun a => m * a + r) ↑(range (t / m + 1))
      ↑((range N).filter fun p => p % m = r) := by
    intro a ha
    simp only [mem_coe, mem_range] at ha
    simp only [mem_coe, mem_filter, mem_range]
    refine ⟨?_, ?_⟩
    · have h1 : m * a ≤ m * (t / m) := Nat.mul_le_mul_left m (by omega)
      omega
    · rw [show m * a + r = r + m * a by ring, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hrlt]
  have hinj : Set.InjOn (fun a => m * a + r) ↑(range (t / m + 1)) := by
    intro a _ b _ hab
    have h : m * a = m * b := Nat.add_right_cancel hab
    exact Nat.eq_of_mul_eq_mul_left hm h
  have hle := Finset.card_le_card_of_injOn (fun a => m * a + r) hmaps hinj
  rw [card_range] at hle
  simpa [rowLen] using hle

lemma rowImage_subset_range_rowLen {N m : ℕ} (hm : 0 < m) (π : Equiv.Perm (Fin N)) (j : ℕ)
    (S : Finset ℕ) : rowImage N m π j S ⊆ range (rowLen N m j) := by
  intro y hy
  rw [mem_rowImage] at hy
  obtain ⟨i, -, hmod, hdiv⟩ := hy
  rw [mem_range, ← hdiv, ← hmod]
  exact div_lt_rowLen hm (π i).isLt

/-- The cardinality of a row image is the number of source positions of `S` landing in that row. -/
lemma rowImage_card_eq_sum {N m : ℕ} (hm : 0 < m) (π : Equiv.Perm (Fin N)) (j : ℕ)
    (S : Finset ℕ) :
    (rowImage N m π j S).card =
      ∑ i : Fin N, if (i.val ∈ S ∧ (π i).val % m = j) then 1 else 0 := by
  classical
  rw [rowImage, Finset.card_image_of_injOn (f := fun i : Fin N => (π i).val / m)]
  · rw [Finset.card_filter]
  · intro a ha b hb hab
    simp only [mem_coe, mem_filter, mem_univ, true_and] at ha hb
    have hab' : (π a).val / m = (π b).val / m := hab
    have h1 : (π a).val = (π b).val := by
      calc (π a).val = m * ((π a).val / m) + (π a).val % m := (Nat.div_add_mod _ _).symm
        _ = m * ((π b).val / m) + (π b).val % m := by rw [hab', ha.2, hb.2]
        _ = (π b).val := Nat.div_add_mod _ _
    exact π.injective (Fin.ext h1)

/-- The row loads of the labels `0, …, d-1` sum to `d`. -/
lemma sum_refLoad {n d : ℕ} (hd : 0 < d) (hdn : d ≤ n) (π : Equiv.Perm (Fin n)) :
    ∑ j ∈ range d, (rowImage n d π j (range d)).card = d := by
  classical
  have h1 : ∀ j ∈ range d, (rowImage n d π j (range d)).card =
      ∑ i : Fin n, if (i.val ∈ range d ∧ (π i).val % d = j) then 1 else 0 := by
    intro j _
    exact rowImage_card_eq_sum hd π j (range d)
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  have h2 : ∀ i : Fin n,
      (∑ j ∈ range d, if (i.val ∈ range d ∧ (π i).val % d = j) then 1 else 0)
        = if i.val < d then 1 else 0 := by
    intro i
    by_cases hi : i.val < d
    · rw [if_pos hi]
      have hmem : (π i).val % d ∈ range d := mem_range.mpr (Nat.mod_lt _ hd)
      rw [Finset.sum_eq_single ((π i).val % d)]
      · rw [if_pos ⟨mem_range.mpr hi, rfl⟩]
      · intro b _ hb
        rw [if_neg]
        intro hcon
        exact hb hcon.2.symm
      · intro hnot
        exact absurd hmem hnot
    · rw [if_neg hi]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [if_neg]
      intro hcon
      exact hi (mem_range.mp hcon.1)
  rw [Finset.sum_congr rfl fun i _ => h2 i]
  have h3 : (∑ i : Fin n, if i.val < d then (1:ℕ) else 0) = d := by
    rw [Finset.sum_boole]
    have h5 : (univ.filter fun i : Fin n => i.val < d).card = (univ : Finset (Fin d)).card := by
      refine Finset.card_bij (fun (a : Fin n)
        (ha : a ∈ univ.filter fun i : Fin n => i.val < d) =>
        (⟨a.val, by simpa using ha⟩ : Fin d)) ?_ ?_ ?_
      · intro a ha
        simp
      · intro a1 ha1 a2 ha2 h
        exact Fin.ext (by simpa using congrArg Fin.val h)
      · intro b _
        exact ⟨⟨b.val, b.isLt.trans_le hdn⟩, by simp [b.isLt], by simp⟩
    have h6 : (univ : Finset (Fin d)).card = d := by simp
    rw [h5, h6]
    simp
  rw [h3]

/-! ## Uniform permutation: position and pair marginals -/

lemma prU_mul_left {n : ℕ} (τ : Equiv.Perm (Fin n)) (Q : Equiv.Perm (Fin n) → Prop) :
    prU (fun π => Q (τ * π)) = prU Q := by
  have h := prU_equiv (Equiv.mulLeft τ) Q
  simpa [Equiv.mulLeft] using h

lemma exists_perm_pair {α : Type} [DecidableEq α] {a b a' b' : α}
    (hab : a ≠ b) (hab' : a' ≠ b') : ∃ τ : Equiv.Perm α, τ a = a' ∧ τ b = b' := by
  classical
  refine ⟨Equiv.swap (Equiv.swap a a' b) b' * Equiv.swap a a', ?_, ?_⟩
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left]
    rw [Equiv.swap_apply_of_ne_of_ne]
    · intro hc
      have h2 := congrArg (Equiv.swap a a') hc
      simp at h2
      exact hab h2
    · exact hab'
  · rw [Equiv.Perm.mul_apply]
    by_cases h : Equiv.swap a a' b = b'
    · rw [h]; simp
    · rw [Equiv.swap_apply_left]

lemma prU_pos_eq {n : ℕ} (i : Fin n) (a a' : Fin n) :
    prU (fun π : Equiv.Perm (Fin n) => π i = a) =
      prU (fun π : Equiv.Perm (Fin n) => π i = a') := by
  have h := prU_mul_left (Equiv.swap a a') (fun π : Equiv.Perm (Fin n) => π i = a')
  rw [← h]
  congr 1
  ext π
  rw [Equiv.Perm.mul_apply]
  constructor
  · intro hc
    have h2 := congrArg (Equiv.swap a a') hc
    simpa [Equiv.swap_apply_self] using h2
  · intro hc
    have h2 := congrArg (Equiv.swap a a') hc
    simpa [Equiv.swap_apply_self] using h2

lemma sum_prU_pos {n : ℕ} (i : Fin n) :
    ∑ a : Fin n, prU (fun π : Equiv.Perm (Fin n) => π i = a) = 1 := by
  have h : ∑ a : Fin n, prU (fun π : Equiv.Perm (Fin n) => π i = a)
      = expU (fun π : Equiv.Perm (Fin n) => ∑ a : Fin n, if π i = a then (1:ℝ) else 0) := by
    rw [expU_sum_finset]
    exact Finset.sum_congr rfl fun a _ => (expU_indicator _).symm
  rw [h]
  have hpt : ∀ π : Equiv.Perm (Fin n),
      (∑ a : Fin n, if π i = a then (1:ℝ) else 0) = 1 := by
    intro π
    rw [Finset.sum_ite_eq]
    simp
  rw [show (fun π : Equiv.Perm (Fin n) => ∑ a : Fin n, if π i = a then (1:ℝ) else 0)
      = fun _ => (1:ℝ) from funext hpt, expU_const]

lemma prU_pos {n : ℕ} (hn : 0 < n) (i a : Fin n) :
    prU (fun π : Equiv.Perm (Fin n) => π i = a) = 1 / (n : ℝ) := by
  have hall : ∀ a' : Fin n, prU (fun π : Equiv.Perm (Fin n) => π i = a') =
      prU (fun π : Equiv.Perm (Fin n) => π i = a) := fun a' => prU_pos_eq i a' a
  have hsum : ∑ a' : Fin n, prU (fun π : Equiv.Perm (Fin n) => π i = a') = 1 := sum_prU_pos i
  rw [Finset.sum_congr rfl fun a' _ => hall a', Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hsum
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp
  linarith

lemma prU_pos_mem {n : ℕ} (hn : 0 < n) (i : Fin n) (S : Finset (Fin n)) :
    prU (fun π : Equiv.Perm (Fin n) => π i ∈ S) = (S.card : ℝ) / n := by
  have hpt : ∀ π : Equiv.Perm (Fin n),
      (∑ a ∈ S, if π i = a then (1:ℝ) else 0) = if π i ∈ S then (1:ℝ) else 0 := by
    intro π
    rw [Finset.sum_ite_eq]
  have h1 : prU (fun π : Equiv.Perm (Fin n) => π i ∈ S)
      = ∑ a ∈ S, prU (fun π : Equiv.Perm (Fin n) => π i = a) := by
    rw [← expU_indicator (fun π : Equiv.Perm (Fin n) => π i ∈ S)]
    rw [show (fun π : Equiv.Perm (Fin n) => if π i ∈ S then (1:ℝ) else 0)
        = fun π => ∑ a ∈ S, if π i = a then (1:ℝ) else 0 from (funext hpt).symm]
    rw [expU_sum_finset]
    exact Finset.sum_congr rfl fun a _ => (expU_indicator _)
  rw [h1, Finset.sum_congr rfl fun a _ => prU_pos hn i a, ← Finset.sum_div, Finset.sum_const]
  simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp

lemma prU_congr {α : Type} [Fintype α] {P Q : α → Prop} (h : ∀ a, P a ↔ Q a) :
    prU P = prU Q := by
  unfold prU
  have h2 : (univ.filter P).card = (univ.filter Q).card :=
    congrArg Finset.card (Finset.filter_congr (fun x _ => h x))
  rw [h2]

lemma prU_false {α : Type} [Fintype α] : prU (fun _ : α => False) = 0 := by
  unfold prU
  simp

lemma prU_pair_eq_zero {n : ℕ} {i i' : Fin n} (hii : i ≠ i') (a : Fin n) :
    prU (fun π : Equiv.Perm (Fin n) => π i = a ∧ π i' = a) = 0 := by
  rw [prU_congr (Q := fun _ : Equiv.Perm (Fin n) => False) (fun π => ?_), prU_false]
  constructor
  · rintro ⟨h1, h2⟩
    exact absurd (π.injective (h1.trans h2.symm)) hii
  · intro h; exact absurd h (by simp)

lemma prU_pair_eq {n : ℕ} {i i' : Fin n} (hii : i ≠ i') {a b a' b' : Fin n}
    (hab : a ≠ b) (hab' : a' ≠ b') :
    prU (fun π : Equiv.Perm (Fin n) => π i = a ∧ π i' = b) =
      prU (fun π : Equiv.Perm (Fin n) => π i = a' ∧ π i' = b') := by
  obtain ⟨τ, hτa, hτb⟩ := exists_perm_pair (a := a) (b := b) (a' := a') (b' := b') hab hab'
  have h := prU_mul_left τ (fun π : Equiv.Perm (Fin n) => π i = a' ∧ π i' = b')
  rw [← h]
  congr 1
  ext π
  simp only [Equiv.Perm.mul_apply]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by rw [h1, hτa], by rw [h2, hτb]⟩
  · rintro ⟨h1, h2⟩
    have e1 : π i = a := by
      apply τ.injective
      rw [h1, hτa]
    have e2 : π i' = b := by
      apply τ.injective
      rw [h2, hτb]
    exact ⟨e1, e2⟩

lemma sum_prU_pair {n : ℕ} {i i' : Fin n} (hii : i ≠ i') :
    ∑ a : Fin n, ∑ b : Fin n,
      prU (fun π : Equiv.Perm (Fin n) => π i = a ∧ π i' = b) = 1 := by
  have hpt : ∀ π : Equiv.Perm (Fin n),
      (∑ a : Fin n, ∑ b : Fin n,
        if (π i = a ∧ π i' = b) then (1:ℝ) else 0) = 1 := by
    intro π
    rw [Finset.sum_eq_single (π i)]
    · rw [Finset.sum_eq_single (π i')]
      · simp
      · intro b _ hb
        rw [if_neg]
        intro h
        exact hb h.2.symm
      · intro hnot
        exact absurd (Finset.mem_univ _) hnot
    · intro a _ ha
      refine Finset.sum_eq_zero fun b _ => ?_
      rw [if_neg]
      intro h
      exact ha h.1.symm
    · intro hnot
      exact absurd (Finset.mem_univ _) hnot
  have h1 : ∑ a : Fin n, ∑ b : Fin n,
      prU (fun π : Equiv.Perm (Fin n) => π i = a ∧ π i' = b)
      = expU (fun π : Equiv.Perm (Fin n) => ∑ a : Fin n, ∑ b : Fin n,
        if (π i = a ∧ π i' = b) then (1:ℝ) else 0) := by
    rw [expU_sum_finset]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [expU_sum_finset]
    exact Finset.sum_congr rfl fun b _ => (expU_indicator _).symm
  rw [h1, show (fun π : Equiv.Perm (Fin n) => ∑ a : Fin n, ∑ b : Fin n,
        if (π i = a ∧ π i' = b) then (1:ℝ) else 0) = fun _ => (1:ℝ) from funext hpt,
    expU_const]

lemma prU_pair {n : ℕ} (hn : 2 ≤ n) {i i' : Fin n} (hii : i ≠ i') {a b : Fin n}
    (hab : a ≠ b) :
    prU (fun π : Equiv.Perm (Fin n) => π i = a ∧ π i' = b) =
      1 / ((n : ℝ) * ((n : ℝ) - 1)) := by
  have hC : ∀ a' b' : Fin n, a' ≠ b' →
      prU (fun π : Equiv.Perm (Fin n) => π i = a' ∧ π i' = b') =
        prU (fun π : Equiv.Perm (Fin n) => π i = a ∧ π i' = b) := by
    intro a' b' hab'
    exact prU_pair_eq hii hab' hab
  have hzero : ∀ a' : Fin n, prU (fun π : Equiv.Perm (Fin n) => π i = a' ∧ π i' = a') = 0 :=
    fun a' => prU_pair_eq_zero hii a'
  have hinner : ∀ a' : Fin n, (∑ b' : Fin n,
      prU (fun π : Equiv.Perm (Fin n) => π i = a' ∧ π i' = b')) =
      ((n : ℝ) - 1) * prU (fun π : Equiv.Perm (Fin n) => π i = a ∧ π i' = b) := by
    intro a'
    have hsplit : (∑ b' : Fin n, prU (fun π : Equiv.Perm (Fin n) => π i = a' ∧ π i' = b'))
        = ∑ b' ∈ (univ : Finset (Fin n)).erase a',
            prU (fun π : Equiv.Perm (Fin n) => π i = a' ∧ π i' = b') := by
      have h := Finset.sum_erase_add (s := (univ : Finset (Fin n)))
        (f := fun b' => prU (fun π : Equiv.Perm (Fin n) => π i = a' ∧ π i' = b'))
        (a := a') (Finset.mem_univ a')
      rw [hzero a', add_zero] at h
      exact h.symm
    rw [hsplit, Finset.sum_congr rfl fun b' hb' =>
      hC a' b' (Ne.symm (Finset.ne_of_mem_erase hb')), Finset.sum_const,
      Finset.card_erase_of_mem (Finset.mem_univ a'), Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    push_cast [Nat.cast_sub (by omega : 1 ≤ n)]
    ring
  have hsum := sum_prU_pair (i := i) (i' := i') hii
  rw [Finset.sum_congr rfl fun a' _ => hinner a', Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hsum
  have h1 : ((n : ℝ) - 1) ≠ 0 := by
    have : (1:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 1 < n)
    linarith
  have hn' : (n : ℝ) ≠ 0 := by
    have : (0:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
    linarith
  field_simp
  field_simp at hsum
  linarith

lemma prU_pair_mem {n : ℕ} (hn : 2 ≤ n) {i i' : Fin n} (hii : i ≠ i')
    (S : Finset (Fin n)) :
    prU (fun π : Equiv.Perm (Fin n) => π i ∈ S ∧ π i' ∈ S) =
      (S.card : ℝ) * ((S.card : ℝ) - 1) / ((n : ℝ) * ((n : ℝ) - 1)) := by
  have hpt : ∀ π : Equiv.Perm (Fin n),
      (∑ a ∈ S, ∑ b ∈ S, if (π i = a ∧ π i' = b) then (1:ℝ) else 0)
        = if (π i ∈ S ∧ π i' ∈ S) then (1:ℝ) else 0 := by
    intro π
    by_cases h1 : π i ∈ S
    · by_cases h2 : π i' ∈ S
      · rw [if_pos ⟨h1, h2⟩, Finset.sum_eq_single (π i)]
        · rw [Finset.sum_eq_single (π i')]
          · simp
          · intro b _ hb
            split_ifs with h
            · exact absurd h.2.symm hb
            · rfl
          · intro hnot; exact absurd h2 hnot
        · intro a _ ha
          refine Finset.sum_eq_zero fun b _ => ?_
          split_ifs with h
          · exact absurd h.1.symm ha
          · rfl
        · intro hnot; exact absurd h1 hnot
      · rw [if_neg (fun h => h2 h.2)]
        refine Finset.sum_eq_zero fun a _ => ?_
        refine Finset.sum_eq_zero fun b hb => ?_
        split_ifs with h
        · exact absurd (by rw [h.2]; exact hb) h2
        · rfl
    · rw [if_neg (fun h => h1 h.1)]
      refine Finset.sum_eq_zero fun a ha => ?_
      refine Finset.sum_eq_zero fun b _ => ?_
      split_ifs with h
      · exact absurd (by rw [h.1]; exact ha) h1
      · rfl
  have h1 : prU (fun π : Equiv.Perm (Fin n) => π i ∈ S ∧ π i' ∈ S)
      = ∑ a ∈ S, ∑ b ∈ S,
          prU (fun π : Equiv.Perm (Fin n) => π i = a ∧ π i' = b) := by
    rw [← expU_indicator (fun π : Equiv.Perm (Fin n) => π i ∈ S ∧ π i' ∈ S)]
    rw [show (fun π : Equiv.Perm (Fin n) => if (π i ∈ S ∧ π i' ∈ S) then (1:ℝ) else 0)
        = fun π => ∑ a ∈ S, ∑ b ∈ S, if (π i = a ∧ π i' = b) then (1:ℝ) else 0
        from (funext hpt).symm]
    rw [expU_sum_finset]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [expU_sum_finset]
    exact Finset.sum_congr rfl fun b _ => (expU_indicator _)
  have hdiag : ∀ a ∈ S, (∑ b ∈ S,
      prU (fun π : Equiv.Perm (Fin n) => π i = a ∧ π i' = b)) = ((S.card : ℝ) - 1) *
        (1 / ((n : ℝ) * ((n : ℝ) - 1))) := by
    intro a ha
    have hsplit : (∑ b ∈ S, prU (fun π : Equiv.Perm (Fin n) => π i = a ∧ π i' = b))
        = ∑ b ∈ S.erase a, prU (fun π : Equiv.Perm (Fin n) => π i = a ∧ π i' = b) := by
      have h := Finset.sum_erase_add (s := S)
        (f := fun b => prU (fun π : Equiv.Perm (Fin n) => π i = a ∧ π i' = b))
        (a := a) ha
      rw [prU_pair_eq_zero hii a, add_zero] at h
      exact h.symm
    rw [hsplit, Finset.sum_congr rfl fun b hb =>
      prU_pair (n := n) hn (i := i) (i' := i') hii (a := a) (b := b)
        (Ne.symm (Finset.ne_of_mem_erase hb)), Finset.sum_const,
      Finset.card_erase_of_mem ha, nsmul_eq_mul]
    push_cast [Finset.one_le_card.mpr ⟨a, ha⟩]
    ring
  rw [h1, Finset.sum_congr rfl hdiag, Finset.sum_const, nsmul_eq_mul]
  have hn' : (n : ℝ) ≠ 0 := by
    have : (0:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
    linarith
  have hn1 : ((n : ℝ) - 1) ≠ 0 := by
    have : (1:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 1 < n)
    linarith
  field_simp




/-! ## Parts 2 and 3: the word distribution -/

lemma two_mul_sum_range (t : ℕ) :
    2 * (∑ a ∈ range t, (a:ℝ)) = (t:ℝ) * ((t:ℝ) - 1) := by
  induction t with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ, mul_add, ih]
      push_cast
      ring

section Part23

variable (P : TopParams)

lemma Pn_pos (hargs : P.Args) : 0 < P.n := by
  have h1 := hargs.1; have h2 := hargs.2.1; omega

lemma Pd_pos (hargs : P.Args) : 0 < P.d := by have h1 := hargs.1; omega

lemma Pd_two (hargs : P.Args) : 2 ≤ P.d := hargs.1

lemma Pd_le_n (hargs : P.Args) : P.d ≤ P.n := hargs.2.1

lemma Pn_two (hargs : P.Args) : 2 ≤ P.n := by
  have h1 := hargs.1; have h2 := hargs.2.1; omega

/-- The positions of row `j` inside `Fin N`. -/
def rowSet (N d j : ℕ) : Finset (Fin N) := univ.filter (fun p : Fin N => p.val % d = j)

lemma mem_rowSet {N d j : ℕ} {p : Fin N} : p ∈ rowSet N d j ↔ p.val % d = j := by
  simp [rowSet]

lemma card_rowSet {N d j : ℕ} : (rowSet N d j).card = rowLen N d j := by
  have h : (rowSet N d j).image (fun p : Fin N => p.val) =
      (range N).filter (fun p => p % d = j) := by
    ext x
    simp only [rowSet, mem_image, mem_filter, mem_univ, mem_range, true_and]
    constructor
    · rintro ⟨p, hp, rfl⟩; exact ⟨p.isLt, hp⟩
    · rintro ⟨hx, hxj⟩; exact ⟨⟨x, hx⟩, hxj, rfl⟩
  rw [rowLen, ← h, Finset.card_image_of_injOn]
  intro a _ b _ hab
  exact Fin.ext hab

lemma card_fin_filter_lt {n d : ℕ} (hdn : d ≤ n) :
    (univ.filter fun i : Fin n => i.val < d).card = d := by
  have h5 : (univ.filter fun i : Fin n => i.val < d).card = (univ : Finset (Fin d)).card := by
    refine Finset.card_bij (fun (a : Fin n)
      (ha : a ∈ univ.filter fun i : Fin n => i.val < d) =>
      (⟨a.val, by simpa using ha⟩ : Fin d)) ?_ ?_ ?_
    · intro a ha; simp
    · intro a1 ha1 a2 ha2 h; exact Fin.ext (by simpa using congrArg Fin.val h)
    · intro b _; exact ⟨⟨b.val, b.isLt.trans_le hdn⟩, by simp [b.isLt], by simp⟩
  rw [h5]
  simp

lemma refLoad_le (hargs : P.Args) (π : Equiv.Perm (Fin P.n)) (j : ℕ) : P.refLoad π j ≤ P.d := by
  have hdn : P.d ≤ P.n := Pd_le_n P hargs
  have hinj : Set.InjOn (fun i : Fin P.n => (π i).val / P.d)
      ↑(univ.filter fun i : Fin P.n => i.val ∈ range P.d ∧ (π i).val % P.d = j) := by
    intro a ha b hb hab
    simp only [mem_coe, mem_filter, mem_univ, true_and] at ha hb
    have hab' : (π a).val / P.d = (π b).val / P.d := hab
    have h1 : (π a).val = (π b).val := by
      calc (π a).val = P.d * ((π a).val / P.d) + (π a).val % P.d := (Nat.div_add_mod _ _).symm
        _ = P.d * ((π b).val / P.d) + (π b).val % P.d := by rw [hab', ha.2, hb.2]
        _ = (π b).val := Nat.div_add_mod _ _
    exact π.injective (Fin.ext h1)
  have hcard : P.refLoad π j =
      (univ.filter fun i : Fin P.n => i.val ∈ range P.d ∧ (π i).val % P.d = j).card := by
    show (rowImage P.n P.d π j (range P.d)).card = _
    rw [rowImage, Finset.card_image_of_injOn (f := fun i : Fin P.n => (π i).val / P.d)]
    exact hinj
  rw [hcard]
  calc (univ.filter fun i : Fin P.n => i.val ∈ range P.d ∧ (π i).val % P.d = j).card
      ≤ (univ.filter fun i : Fin P.n => i.val < P.d).card := by
        refine Finset.card_le_card ?_
        intro i hi
        simp only [mem_filter, mem_univ, true_and] at hi ⊢
        simpa using hi.1
    _ = P.d := card_fin_filter_lt hdn

lemma q_nonneg (a : ℕ) : 0 ≤ P.q a :=
  Finset.sum_nonneg fun j _ => prU_nonneg _

lemma q_zero_of_gt (hargs : P.Args) {a : ℕ} (ha : P.d < a) : P.q a = 0 := by
  refine Finset.sum_eq_zero fun j _ => ?_
  have h : (fun π : Equiv.Perm (Fin P.n) => a ≤ P.refLoad π j) = fun _ => False := by
    funext π
    simp only [eq_iff_iff, iff_false]
    intro hle
    have := refLoad_le P hargs π j
    omega
  rw [h, prU_false]

lemma sum_indicator_le' {t n : ℕ} (ht : t ≤ n) :
    (∑ a ∈ range n, if a + 1 ≤ t then (1:ℝ) else 0) = (t : ℝ) := by
  rw [Finset.sum_boole]
  have h : (range n).filter (fun a => a + 1 ≤ t) = range t := by
    ext a; simp only [mem_filter, mem_range]; omega
  rw [h, card_range]

lemma sum_indicator_mul_two {t n : ℕ} (ht : t ≤ n) :
    2 * (∑ a ∈ range n, (a:ℝ) * (if a + 1 ≤ t then (1:ℝ) else 0)) =
      (t:ℝ) * ((t:ℝ) - 1) := by
  have h : (range n).filter (fun a => a + 1 ≤ t) = range t := by
    ext a; simp only [mem_filter, mem_range]; omega
  have h1 : ∀ a ∈ range n,
      (a:ℝ) * (if a + 1 ≤ t then (1:ℝ) else 0) = (if a + 1 ≤ t then (a:ℝ) else 0) := by
    intro a _; split_ifs <;> ring
  rw [Finset.sum_congr rfl h1, ← Finset.sum_filter, h]
  exact two_mul_sum_range t

lemma rowLen_le {N m j : ℕ} (hm : 0 < m) : m * rowLen N m j ≤ N + m := by
  rcases Nat.eq_zero_or_pos (rowLen N m j) with h0 | hpos
  · rw [h0]; omega
  · have hinj : Set.InjOn (fun p : ℕ => p / m)
        ↑((range N).filter (fun p => p % m = j)) := by
      intro a ha b hb hab
      simp only [mem_coe, mem_filter, mem_range] at ha hb
      have hab' : a / m = b / m := hab
      have h1 : a = b := by
        calc a = m * (a / m) + a % m := (Nat.div_add_mod _ _).symm
          _ = m * (b / m) + b % m := by rw [hab', ha.2, hb.2]
          _ = b := Nat.div_add_mod _ _
      exact h1
    have himg : ((range N).filter (fun p => p % m = j)).image (fun p => p / m) =
        range (rowLen N m j) := by
      refine Finset.eq_of_subset_of_card_le ?_ ?_
      · intro y hy
        rw [mem_image] at hy
        obtain ⟨p, hp, rfl⟩ := hy
        rw [mem_range]
        rw [← (mem_filter.mp hp).2]
        exact div_lt_rowLen hm (by simpa using (mem_filter.mp hp).1)
      · rw [Finset.card_image_of_injOn hinj, rowLen, card_range]
    have hlast : rowLen N m j - 1 ∈ ((range N).filter (fun p => p % m = j)).image
        (fun p => p / m) := by
      rw [himg]
      exact mem_range.mpr (by omega)
    rw [mem_image] at hlast
    obtain ⟨p, hp, hpv⟩ := hlast
    rw [mem_filter, mem_range] at hp
    have hpe : p = m * (rowLen N m j - 1) + j := by
      rw [← hpv, ← hp.2]
      exact (Nat.div_add_mod p m).symm
    have hrow : rowLen N m j = (rowLen N m j - 1) + 1 := (Nat.sub_add_cancel hpos).symm
    have hmul : m * (rowLen N m j - 1) = p - j := by
      rw [hpe, Nat.add_sub_cancel]
    calc m * rowLen N m j = m * ((rowLen N m j - 1) + 1) := by congr 1
      _ = m * (rowLen N m j - 1) + m := by ring
      _ = (p - j) + m := by rw [hmul]
      _ ≤ N + m := by omega

lemma sum_rowLen {N d : ℕ} (hd : 0 < d) : ∑ j ∈ range d, rowLen N d j = N := by
  have h : (∑ j ∈ range d, rowLen N d j)
      = ∑ j ∈ range d, ((range N).filter (fun p => p % d = j)).card := rfl
  rw [h, ← Finset.card_eq_sum_card_fiberwise (s := range N) (t := range d)
    (f := fun p => p % d) (fun p hp => mem_range.mpr (Nat.mod_lt _ hd))]
  simp

lemma sum_rowLen_sq_le {n d : ℕ} (hd : 0 < d) :
    (∑ j ∈ range d, (rowLen n d j : ℝ) * (rowLen n d j : ℝ)) ≤ ((n:ℝ) / d + 1) * n := by
  have hd' : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd
  have hb : ∀ j, (rowLen n d j : ℝ) ≤ (n:ℝ) / d + 1 := by
    intro j
    have h := rowLen_le (N := n) (m := d) (j := j) hd
    have h2 : (d:ℝ) * (rowLen n d j : ℝ) ≤ (n:ℝ) + d := by exact_mod_cast h
    have he : (n:ℝ) / d + 1 = ((n:ℝ) + d) / d := by field_simp
    rw [he, le_div_iff₀ hd']
    linarith
  calc (∑ j ∈ range d, (rowLen n d j : ℝ) * (rowLen n d j : ℝ))
      ≤ ∑ j ∈ range d, (rowLen n d j : ℝ) * ((n:ℝ) / d + 1) := by
        refine Finset.sum_le_sum fun j _ => ?_
        exact mul_le_mul_of_nonneg_left (hb j) (Nat.cast_nonneg _)
    _ = ((n:ℝ) / d + 1) * ∑ j ∈ range d, (rowLen n d j : ℝ) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
    _ = ((n:ℝ) / d + 1) * n := by
        rw [← Nat.cast_sum, sum_rowLen hd]

lemma sum_rowLen_mul_pred_le {n d : ℕ} (hd : 0 < d) :
    (∑ j ∈ range d, (rowLen n d j : ℝ) * ((rowLen n d j : ℝ) - 1)) ≤ (n:ℝ) * n / d := by
  have h1 : (∑ j ∈ range d, (rowLen n d j : ℝ) * ((rowLen n d j : ℝ) - 1))
      = (∑ j ∈ range d, (rowLen n d j : ℝ) * (rowLen n d j : ℝ))
        - (∑ j ∈ range d, (rowLen n d j : ℝ)) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have h2 : (∑ j ∈ range d, (rowLen n d j : ℝ)) = (n:ℝ) := by
    rw [← Nat.cast_sum, sum_rowLen hd]
  have h3 := sum_rowLen_sq_le (n := n) (d := d) hd
  rw [h1, h2]
  have : ((n:ℝ) / d + 1) * n - n = (n:ℝ) * n / d := by field_simp; ring
  linarith

end Part23

section Moments

variable (P : TopParams)

lemma expU_refLoad (hargs : P.Args) (j : ℕ) :
    expU (fun π : Equiv.Perm (Fin P.n) => (P.refLoad π j : ℝ)) =
      (P.d : ℝ) * (rowLen P.n P.d j : ℝ) / (P.n : ℝ) := by
  have hd : 0 < P.d := Pd_pos P hargs
  have hdn : P.d ≤ P.n := Pd_le_n P hargs
  have hn : 0 < P.n := Pn_pos P hargs
  have hfun : (fun π : Equiv.Perm (Fin P.n) => (P.refLoad π j : ℝ)) =
      fun π => ∑ i : Fin P.n, (if (i.val < P.d ∧ (π i).val % P.d = j) then (1:ℝ) else 0) := by
    funext π
    have hT : P.refLoad π j = (rowImage P.n P.d π j (range P.d)).card := rfl
    rw [hT, rowImage_card_eq_sum hd π j (range P.d), Nat.cast_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [mem_range]
    split_ifs <;> simp
  rw [hfun, expU_sum_finset]
  have hterm : ∀ i : Fin P.n, expU (fun π : Equiv.Perm (Fin P.n) =>
      (if (i.val < P.d ∧ (π i).val % P.d = j) then (1:ℝ) else 0)) =
      if i.val < P.d then (rowLen P.n P.d j : ℝ) / (P.n : ℝ) else 0 := by
    intro i
    by_cases hi : i.val < P.d
    · rw [if_pos hi]
      have hfun2 : (fun π : Equiv.Perm (Fin P.n) =>
          (if (i.val < P.d ∧ (π i).val % P.d = j) then (1:ℝ) else 0)) =
          fun π => (if π i ∈ rowSet P.n P.d j then (1:ℝ) else 0) := by
        funext π
        simp only [hi, true_and]
        congr 1
        exact propext (mem_rowSet (N := P.n) (d := P.d) (j := j) (p := π i)).symm
      rw [hfun2, expU_indicator, prU_pos_mem hn i (rowSet P.n P.d j), card_rowSet]
    · rw [if_neg hi]
      have h0 : (fun π : Equiv.Perm (Fin P.n) =>
          (if (i.val < P.d ∧ (π i).val % P.d = j) then (1:ℝ) else 0)) = fun _ => (0:ℝ) := by
        funext π
        rw [if_neg]
        intro h
        exact hi h.1
      rw [h0, expU_const]
  rw [Finset.sum_congr rfl fun i _ => hterm i]
  rw [← Finset.sum_filter, Finset.sum_const, card_fin_filter_lt hdn, nsmul_eq_mul]
  ring

lemma sum_prU_le_expU_refLoad (hargs : P.Args) (j : ℕ) :
    ∑ a ∈ range P.n, prU (fun π : Equiv.Perm (Fin P.n) => a + 1 ≤ P.refLoad π j) =
      expU (fun π : Equiv.Perm (Fin P.n) => (P.refLoad π j : ℝ)) := by
  have hdn : P.d ≤ P.n := Pd_le_n P hargs
  have hfun : ∀ a, prU (fun π : Equiv.Perm (Fin P.n) => a + 1 ≤ P.refLoad π j)
      = expU (fun π : Equiv.Perm (Fin P.n) =>
          (if a + 1 ≤ P.refLoad π j then (1:ℝ) else 0)) :=
    fun a => (expU_indicator _).symm
  rw [Finset.sum_congr rfl fun a _ => hfun a, ← expU_sum_finset]
  congr 1
  funext π
  rw [sum_indicator_le' (le_trans (refLoad_le P hargs π j) hdn)]

end Moments

/-- The indicator that position `i` sits in row `j` of the reference placement. -/
def rowInd (P : TopParams) (j : ℕ) (π : Equiv.Perm (Fin P.n)) (i : Fin P.n) : ℝ :=
  if (i.val < P.d ∧ (π i).val % P.d = j) then 1 else 0

section Moment2

variable (P : TopParams)

lemma expU_refLoad_pred_le (hargs : P.Args) (j : ℕ) :
    expU (fun π : Equiv.Perm (Fin P.n) =>
        (P.refLoad π j : ℝ) * ((P.refLoad π j : ℝ) - 1)) ≤
      (P.d : ℝ) * ((P.d : ℝ) - 1) *
        ((rowLen P.n P.d j : ℝ) * ((rowLen P.n P.d j : ℝ) - 1)) /
        ((P.n : ℝ) * ((P.n : ℝ) - 1)) := by
  have hd : 0 < P.d := Pd_pos P hargs
  have hn : 0 < P.n := Pn_pos P hargs
  have hn2 : 2 ≤ P.n := Pn_two P hargs
  set C : ℝ := (rowLen P.n P.d j : ℝ) * ((rowLen P.n P.d j : ℝ) - 1) /
    ((P.n : ℝ) * ((P.n : ℝ) - 1)) with hC
  have hpt : ∀ π : Equiv.Perm (Fin P.n),
      (P.refLoad π j : ℝ) * ((P.refLoad π j : ℝ) - 1) =
      ∑ i1 : Fin P.n, ∑ i2 ∈ (univ : Finset (Fin P.n)).erase i1,
        (rowInd P j π i1) * (rowInd P j π i2) := by
    intro π
    have hT : (P.refLoad π j : ℝ) = ∑ i : Fin P.n, rowInd P j π i := by
      have hT' : P.refLoad π j = (rowImage P.n P.d π j (range P.d)).card := rfl
      rw [hT', rowImage_card_eq_sum hd π j (range P.d), Nat.cast_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [rowInd, mem_range]
      split_ifs <;> simp
    have hcc : ∀ i : Fin P.n, rowInd P j π i * rowInd P j π i = rowInd P j π i := by
      intro i
      simp only [rowInd]
      split_ifs <;> ring
    have hstep : ∀ i1 : Fin P.n,
        (∑ i2 ∈ (univ : Finset (Fin P.n)).erase i1, rowInd P j π i1 * rowInd P j π i2)
        = rowInd P j π i1 * (∑ i2 : Fin P.n, rowInd P j π i2) - rowInd P j π i1 := by
      intro i1
      rw [Finset.sum_erase_eq_sub (Finset.mem_univ i1), ← Finset.mul_sum, hcc i1]
    rw [hT, Finset.sum_congr rfl fun i1 _ => hstep i1, Finset.sum_sub_distrib,
      ← Finset.sum_mul]
    ring
  rw [show (fun π : Equiv.Perm (Fin P.n) =>
      (P.refLoad π j : ℝ) * ((P.refLoad π j : ℝ) - 1)) =
      fun π => ∑ i1 : Fin P.n, ∑ i2 ∈ (univ : Finset (Fin P.n)).erase i1,
        (rowInd P j π i1) * (rowInd P j π i2) from funext hpt]
  rw [expU_sum_finset]
  have hinner : ∀ i1 : Fin P.n, expU (fun π : Equiv.Perm (Fin P.n) =>
      ∑ i2 ∈ (univ : Finset (Fin P.n)).erase i1, (rowInd P j π i1) * (rowInd P j π i2)) =
      ∑ i2 ∈ (univ : Finset (Fin P.n)).erase i1,
        expU (fun π : Equiv.Perm (Fin P.n) => (rowInd P j π i1) * (rowInd P j π i2)) :=
    fun i1 => expU_sum_finset _ _
  rw [Finset.sum_congr rfl fun i1 _ => hinner i1]
  have hpair : ∀ i1 i2 : Fin P.n, i2 ≠ i1 →
      expU (fun π : Equiv.Perm (Fin P.n) => (rowInd P j π i1) * (rowInd P j π i2)) =
      if (i1.val < P.d ∧ i2.val < P.d) then C else 0 := by
    intro i1 i2 hne
    by_cases h1 : i1.val < P.d
    · by_cases h2 : i2.val < P.d
      · rw [if_pos ⟨h1, h2⟩]
        have hfun : (fun π : Equiv.Perm (Fin P.n) =>
            (rowInd P j π i1) * (rowInd P j π i2)) =
            fun π => (if (π i1 ∈ rowSet P.n P.d j ∧ π i2 ∈ rowSet P.n P.d j) then (1:ℝ) else 0) := by
          funext π
          by_cases e1 : (π i1).val % P.d = j <;>
            by_cases e2 : (π i2).val % P.d = j <;>
            simp [rowInd, h1, h2, e1, e2, mem_rowSet]
        rw [hfun, expU_indicator, prU_pair_mem (n := P.n) hn2 (Ne.symm hne) (rowSet P.n P.d j),
          card_rowSet]
      · rw [if_neg (fun h => h2 h.2)]
        have h0 : (fun π : Equiv.Perm (Fin P.n) => (rowInd P j π i1) * (rowInd P j π i2))
            = fun _ => (0:ℝ) := by
          funext π
          simp [rowInd, h1, h2]
        rw [h0, expU_const]
    · rw [if_neg (fun h => h1 h.1)]
      have h0 : (fun π : Equiv.Perm (Fin P.n) => (rowInd P j π i1) * (rowInd P j π i2))
          = fun _ => (0:ℝ) := by
        funext π
        simp [rowInd, h1]
      rw [h0, expU_const]
  rw [Finset.sum_congr rfl fun i1 _ => Finset.sum_congr rfl fun i2 hi2 =>
    hpair i1 i2 (Finset.ne_of_mem_erase hi2)]
  have hinner2 : ∀ i1 : Fin P.n, (∑ i2 ∈ (univ : Finset (Fin P.n)).erase i1,
      (if (i1.val < P.d ∧ i2.val < P.d) then C else 0)) =
      if i1.val < P.d then ((P.d : ℝ) - 1) * C else 0 := by
    intro i1
    by_cases hi : i1.val < P.d
    · rw [if_pos hi]
      have hstep : ∀ i2 ∈ (univ : Finset (Fin P.n)).erase i1,
          (if (i1.val < P.d ∧ i2.val < P.d) then C else 0) =
          C * (if i2.val < P.d then (1:ℝ) else 0) := by
        intro i2 _
        by_cases e : i2.val < P.d <;> simp [hi, e]
      rw [Finset.sum_congr rfl hstep, ← Finset.mul_sum]
      have hcnt : (∑ i2 ∈ (univ : Finset (Fin P.n)).erase i1,
          (if i2.val < P.d then (1:ℝ) else 0)) = ((P.d : ℝ) - 1) := by
        rw [Finset.sum_boole]
        have hc : ((univ : Finset (Fin P.n)).erase i1).filter (fun i2 => i2.val < P.d)
            = (univ.filter fun i2 : Fin P.n => i2.val < P.d).erase i1 := by
          ext x
          simp only [mem_filter, mem_erase, mem_univ, true_and]
          tauto
        rw [hc, Finset.card_erase_of_mem (mem_filter.mpr ⟨mem_univ i1, hi⟩),
          card_fin_filter_lt (Pd_le_n P hargs)]
        push_cast [Nat.cast_sub (by have := Pd_pos P hargs; omega : 1 ≤ P.d)]
        ring
      rw [hcnt]
      ring
    · rw [if_neg hi]
      refine Finset.sum_eq_zero fun i2 _ => ?_
      rw [if_neg (fun h => hi h.1)]
  rw [Finset.sum_congr rfl fun i1 _ => hinner2 i1]
  have hstep2 : ∀ i1 : Fin P.n,
      (if i1.val < P.d then ((P.d : ℝ) - 1) * C else 0) =
      ((P.d : ℝ) - 1) * C * (if i1.val < P.d then (1:ℝ) else 0) := by
    intro i1
    by_cases e : i1.val < P.d <;> simp [e]
  rw [Finset.sum_congr rfl fun i1 _ => hstep2 i1, ← Finset.mul_sum]
  have hcnt2 : (∑ i1 : Fin P.n, (if i1.val < P.d then (1:ℝ) else 0)) = (P.d : ℝ) := by
    rw [← Finset.sum_filter, Finset.sum_const, card_fin_filter_lt (Pd_le_n P hargs),
      nsmul_eq_mul, mul_one]
  rw [hcnt2, hC]
  apply le_of_eq
  ring
end Moment2

lemma expU_mul_const {α : Type} [Fintype α] (c : ℝ) (f : α → ℝ) :
    expU (fun a => c * f a) = c * expU f := by
  unfold expU
  rw [← Finset.mul_sum]
  ring

section Assembly

variable (P : TopParams)

lemma q_sum_eq (hargs : P.Args) : ∑ a ∈ range P.n, P.q (a + 1) = P.d := by
  have hd : 0 < P.d := Pd_pos P hargs
  have hdn : P.d ≤ P.n := Pd_le_n P hargs
  calc ∑ a ∈ range P.n, P.q (a + 1)
      = ∑ a ∈ range P.n, ∑ j ∈ range P.d,
          prU (fun π : Equiv.Perm (Fin P.n) => a + 1 ≤ P.refLoad π j) := rfl
    _ = ∑ j ∈ range P.d, ∑ a ∈ range P.n,
          prU (fun π : Equiv.Perm (Fin P.n) => a + 1 ≤ P.refLoad π j) := Finset.sum_comm
    _ = ∑ j ∈ range P.d, expU (fun π : Equiv.Perm (Fin P.n) => (P.refLoad π j : ℝ)) := by
        exact Finset.sum_congr rfl fun j _ => sum_prU_le_expU_refLoad P hargs j
    _ = expU (fun π : Equiv.Perm (Fin P.n) => ∑ j ∈ range P.d, (P.refLoad π j : ℝ)) := by
        rw [expU_sum_finset]
    _ = expU (fun _ : Equiv.Perm (Fin P.n) => (P.d : ℝ)) := by
        congr 1
        funext π
        have hsr : ∑ j ∈ range P.d, P.refLoad π j = P.d := sum_refLoad hd hdn π
        rw [← Nat.cast_sum, hsr]
    _ = P.d := expU_const _

lemma sum_mul_prU_eq_expU_pred (hargs : P.Args) (j : ℕ) :
    ∑ a ∈ range P.n, (a:ℝ) * prU (fun π : Equiv.Perm (Fin P.n) => a + 1 ≤ P.refLoad π j)
      = (1/2) * expU (fun π : Equiv.Perm (Fin P.n) =>
          (P.refLoad π j : ℝ) * ((P.refLoad π j : ℝ) - 1)) := by
  have hdn : P.d ≤ P.n := Pd_le_n P hargs
  have hfun : ∀ a : ℕ, (a:ℝ) * prU (fun π : Equiv.Perm (Fin P.n) => a + 1 ≤ P.refLoad π j)
      = expU (fun π : Equiv.Perm (Fin P.n) =>
          (if a + 1 ≤ P.refLoad π j then (a:ℝ) else 0)) := by
    intro a
    rw [show (fun π : Equiv.Perm (Fin P.n) =>
        (if a + 1 ≤ P.refLoad π j then (a:ℝ) else 0))
        = fun π => (a:ℝ) * (if a + 1 ≤ P.refLoad π j then (1:ℝ) else 0) from by
      funext π; by_cases h : a + 1 ≤ P.refLoad π j <;> simp [h]]
    rw [expU_mul_const, expU_indicator]
  rw [Finset.sum_congr rfl fun a _ => hfun a, ← expU_sum_finset]
  have hfun2 : (fun π : Equiv.Perm (Fin P.n) => ∑ a ∈ range P.n,
      (if a + 1 ≤ P.refLoad π j then (a:ℝ) else 0))
      = fun π => (1/2) * ((P.refLoad π j : ℝ) * ((P.refLoad π j : ℝ) - 1)) := by
    funext π
    have h2 := sum_indicator_mul_two (n := P.n) (t := P.refLoad π j)
      (le_trans (refLoad_le P hargs π j) hdn)
    have h3 : (∑ a ∈ range P.n, (if a + 1 ≤ P.refLoad π j then (a:ℝ) else 0))
        = ∑ a ∈ range P.n, (a:ℝ) * (if a + 1 ≤ P.refLoad π j then (1:ℝ) else 0) := by
      refine Finset.sum_congr rfl fun a _ => ?_
      by_cases h : a + 1 ≤ P.refLoad π j <;> simp [h]
    rw [h3]
    linarith
  rw [hfun2, expU_mul_const]

lemma q_moment_le (hargs : P.Args) : ∑ a ∈ range P.n, (a:ℝ) * P.q (a + 1) ≤ P.d := by
  have hd : 0 < P.d := Pd_pos P hargs
  have hdn : P.d ≤ P.n := Pd_le_n P hargs
  have hn : 0 < P.n := Pn_pos P hargs
  have hn2 : 2 ≤ P.n := Pn_two P hargs
  have hd1 : (0:ℝ) < (P.d : ℝ) := by exact_mod_cast hd
  have hn1 : (1:ℝ) < (P.n : ℝ) := by exact_mod_cast (by omega : 1 < P.n)
  have hnne : ((P.n : ℝ) * ((P.n : ℝ) - 1)) ≠ 0 := by
    have : (0:ℝ) < (P.n : ℝ) * ((P.n : ℝ) - 1) := by nlinarith
    exact ne_of_gt this
  have hdne : (P.d : ℝ) ≠ 0 := ne_of_gt hd1
  have hsplit : ∑ a ∈ range P.n, (a:ℝ) * P.q (a + 1)
      = ∑ j ∈ range P.d, ∑ a ∈ range P.n,
          (a:ℝ) * prU (fun π : Equiv.Perm (Fin P.n) => a + 1 ≤ P.refLoad π j) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [show P.q (a + 1) = ∑ j ∈ range P.d, prU (fun π : Equiv.Perm (Fin P.n) => a + 1 ≤ P.refLoad π j) from rfl, Finset.mul_sum]
  have hstep : ∑ j ∈ range P.d, ∑ a ∈ range P.n,
        (a:ℝ) * prU (fun π : Equiv.Perm (Fin P.n) => a + 1 ≤ P.refLoad π j)
      = ∑ j ∈ range P.d, (1/2) * expU (fun π : Equiv.Perm (Fin P.n) =>
          (P.refLoad π j : ℝ) * ((P.refLoad π j : ℝ) - 1)) :=
    Finset.sum_congr rfl fun j _ => sum_mul_prU_eq_expU_pred P hargs j
  rw [hsplit, hstep, ← Finset.mul_sum]
  have hfac : ∀ j ∈ range P.d, expU (fun π : Equiv.Perm (Fin P.n) =>
        (P.refLoad π j : ℝ) * ((P.refLoad π j : ℝ) - 1)) ≤
      ((P.d : ℝ) * ((P.d : ℝ) - 1) / ((P.n : ℝ) * ((P.n : ℝ) - 1))) *
        ((rowLen P.n P.d j : ℝ) * ((rowLen P.n P.d j : ℝ) - 1)) := by
    intro j _
    refine le_trans (expU_refLoad_pred_le P hargs j) ?_
    rw [div_mul_eq_mul_div]
  have hcoef : (0:ℝ) ≤ (P.d : ℝ) * ((P.d : ℝ) - 1) / ((P.n : ℝ) * ((P.n : ℝ) - 1)) := by
    apply div_nonneg
    · have : (1:ℝ) ≤ (P.d : ℝ) := by exact_mod_cast (by omega : 1 ≤ P.d)
      nlinarith
    · have : (0:ℝ) < (P.n : ℝ) * ((P.n : ℝ) - 1) := by nlinarith
      exact le_of_lt this
  have hsum_bound : ∑ j ∈ range P.d, expU (fun π : Equiv.Perm (Fin P.n) =>
        (P.refLoad π j : ℝ) * ((P.refLoad π j : ℝ) - 1)) ≤
      ((P.d : ℝ) * ((P.d : ℝ) - 1) / ((P.n : ℝ) * ((P.n : ℝ) - 1))) *
        ((P.n : ℝ) * (P.n : ℝ) / (P.d : ℝ)) := by
    refine le_trans (Finset.sum_le_sum hfac) ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (sum_rowLen_mul_pred_le (n := P.n) (d := P.d) hd) hcoef
  have hfinal : (1/2 : ℝ) * (((P.d : ℝ) * ((P.d : ℝ) - 1) / ((P.n : ℝ) * ((P.n : ℝ) - 1))) *
        ((P.n : ℝ) * (P.n : ℝ) / (P.d : ℝ))) ≤ P.d := by
    have h1 : ((P.d : ℝ) * ((P.d : ℝ) - 1) / ((P.n : ℝ) * ((P.n : ℝ) - 1))) *
        ((P.n : ℝ) * (P.n : ℝ) / (P.d : ℝ)) = (P.d - 1) * (P.n) / (P.n - 1) := by
      field_simp
    rw [h1]
    have h3 : (0:ℝ) < (P.n:ℝ) - 1 := by linarith
    have h5 : (1/2 : ℝ) * ((P.d - 1) * (P.n) / (P.n - 1)) = ((1/2 : ℝ) * ((P.d - 1) * (P.n))) / (P.n - 1) := by ring
    rw [h5, div_le_iff₀ h3]
    have h4 : ((P.d : ℝ) - 1) * (P.n : ℝ) ≤ P.d * ((P.n : ℝ) - 1) * 2 := by
      have h6 : (P.d : ℝ) ≤ P.n := by exact_mod_cast hdn
      nlinarith
    linarith
  have := mul_le_mul_of_nonneg_left hsum_bound (by norm_num : (0:ℝ) ≤ 1/2)
  linarith

end Assembly

section Final

variable (P : TopParams)

lemma q_tsum_eq (hargs : P.Args) :
    (∑' a : ℕ, ENNReal.ofReal (P.q (a + 1))) = (P.d : ℝ≥0∞) := by
  have hdn : P.d ≤ P.n := Pd_le_n P hargs
  have hzero : ∀ a ∉ range P.n, ENNReal.ofReal (P.q (a + 1)) = 0 := by
    intro a ha
    rw [Finset.mem_range, not_lt] at ha
    rw [q_zero_of_gt P hargs (by omega), ENNReal.ofReal_zero]
  rw [tsum_eq_sum hzero]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => q_nonneg P (a + 1)), q_sum_eq P hargs,
    ENNReal.ofReal_natCast]

lemma entropy_bound (hargs : P.Args) :
    entropy (fun a : ℕ => P.q (a + 1) / (P.d : ℝ)) ≤ ENNReal.ofReal (lg (2 * Real.exp 1)) := by
  have hd : 0 < P.d := Pd_pos P hargs
  have hdn : P.d ≤ P.n := Pd_le_n P hargs
  have hn : 0 < P.n := Pn_pos P hargs
  have hn2 : 2 ≤ P.n := Pn_two P hargs
  set w : ℕ → ℝ := fun a => P.q (a + 1) / (P.d : ℝ) with hw
  have hw_nonneg : ∀ a, 0 ≤ w a := fun a => div_nonneg (q_nonneg P (a + 1)) (Nat.cast_nonneg _)
  have hw_zero : ∀ a ∉ range P.n, w a = 0 := by
    intro a ha
    rw [Finset.mem_range, not_lt] at ha
    rw [hw]
    change P.q (a + 1) / (P.d : ℝ) = 0
    rw [q_zero_of_gt P hargs (by omega), zero_div]
  have hw_sum : ∑ a ∈ range P.n, w a = 1 := by
    rw [hw, ← Finset.sum_div, q_sum_eq P hargs]
    exact div_self (by exact_mod_cast (ne_of_gt hd))
  have hw_mean : ∑ a ∈ range P.n, (a:ℝ) * w a ≤ 1 := by
    rw [hw]
    simp only
    have hsplit : ∑ a ∈ range P.n, (a:ℝ) * (P.q (a + 1) / (P.d : ℝ))
        = (∑ a ∈ range P.n, (a:ℝ) * P.q (a + 1)) / (P.d : ℝ) := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun a _ => by ring
    rw [hsplit, div_le_one (by exact_mod_cast hd)]
    exact q_moment_le P hargs
  -- the PMF
  have hsum1 : ∑ a ∈ range P.n, ENNReal.ofReal (w a) = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => hw_nonneg a), hw_sum, ENNReal.ofReal_one]
  have hzero1 : ∀ a ∉ range P.n, ENNReal.ofReal (w a) = 0 := by
    intro a ha; rw [hw_zero a ha, ENNReal.ofReal_zero]
  set T : PMF ℕ := PMF.ofFinset (fun a => ENNReal.ofReal (w a)) (range P.n) hsum1 hzero1 with hT
  have hT_apply : ∀ a : ℕ, T a = ENNReal.ofReal (w a) := fun a => rfl
  have hT_toReal : ∀ a : ℕ, (T a).toReal = w a := by
    intro a; rw [hT_apply, ENNReal.toReal_ofReal (hw_nonneg a)]
  have hterm_zero : ∀ k ∉ range P.n, (k : ℝ≥0∞) * T k = 0 := by
    intro k hk
    rw [hT_apply, hw_zero k hk, ENNReal.ofReal_zero, mul_zero]
  have hterm_ne_top : ∀ k ∈ range P.n, (k : ℝ≥0∞) * T k ≠ ⊤ :=
    fun k _ => ENNReal.mul_ne_top (ENNReal.natCast_ne_top k) (T.apply_ne_top k)
  have hmean_fin : (∑' k : ℕ, (k : ℝ≥0∞) * T k) ≠ ⊤ := by
    rw [tsum_eq_sum hterm_zero]
    exact ENNReal.sum_ne_top.mpr hterm_ne_top
  have hmean_eq : (∑' k : ℕ, (k : ℝ≥0∞) * T k).toReal = ∑ a ∈ range P.n, (a:ℝ) * w a := by
    rw [tsum_eq_sum hterm_zero, ENNReal.toReal_sum hterm_ne_top]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, hT_toReal]
  have hmain := lemma_4_5 T hmean_fin
  have hentropy_eq : entropy (fun a : ℕ => w a) = entropy (fun k : ℕ => (T k).toReal) := by
    congr 1
    funext a
    exact (hT_toReal a).symm
  rw [hw, hentropy_eq]
  refine le_trans hmain ?_
  apply ENNReal.ofReal_le_ofReal
  rw [hmean_eq]
  have hmean_nonneg : 0 ≤ ∑ a ∈ range P.n, (a:ℝ) * w a :=
    Finset.sum_nonneg fun a _ => mul_nonneg (Nat.cast_nonneg _) (hw_nonneg a)
  have hpos : (0:ℝ) < Real.exp 1 * (1 + ∑ a ∈ range P.n, (a:ℝ) * w a) := by
    have := Real.exp_pos 1
    nlinarith
  have hle : Real.exp 1 * (1 + ∑ a ∈ range P.n, (a:ℝ) * w a) ≤ Real.exp 1 * (1 + 1) := by
    have h1 := hw_mean
    nlinarith [Real.exp_pos 1]
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1:ℝ) < 2) hpos hle
  simpa [lg, mul_comm, show (1:ℝ) + 1 = 2 from by norm_num] using hlog

end Final

/-! ## Part 1: across words -/

section Part1

variable (P : TopParams)

/-- The uniqueness clause of Proposition 2.1 (Pinsketch): light vectors are determined by
their syndrome. -/
lemma pin_unique {N t : ℕ} (hN : 1 ≤ N) (ht : t ≤ N)
    {F : Type} [Field F] [Algebra (ZMod 2) F] (w : ℕ) (hw : w = ⌈lg ((N : ℝ) + 1)⌉₊)
    (b : Module.Basis (Fin w) (ZMod 2) F) (ι : ℕ → F)
    (h0 : ∀ v < N, ι v ≠ 0) (hinj : Set.InjOn ι (Set.Iio N))
    (x x' : Fin N → ZMod 2)
    (hx : (univ.filter fun i => x i = 1).card ≤ t)
    (hx' : (univ.filter fun i => x' i = 1).card ≤ t)
    (hp : pin ι t x = pin ι t x') : x = x' := by
  obtain ⟨progDec, K, cW, p, hK, hcW, H⟩ := proposition_2_1
  exact (H N t hN ht F w hw b ι h0 hinj).2.2.2.1 x x' hx hx' hp

/-- The Pinsketch power sums of the indicator vector of a finset. -/
lemma pin_indicator {N t : ℕ} {F : Type} [Field F] [Fintype F] [Algebra (ZMod 2) F] (ι : ℕ → F)
    (S : Finset ℕ) (hS : S ⊆ range N) (j : Fin t) :
    pin ι t (fun i : Fin N => if i.val ∈ S then 1 else 0) j =
      TopParams.power ι (2 * j.val + 1) S := by
  show pinPower ι (2 * j.val + 1) (fun i : Fin N => if i.val ∈ S then 1 else 0) = _
  unfold pinPower TopParams.power
  rw [Finset.sum_fin_eq_sum_range]
  have h1 : ∀ v ∈ range N, (if h : v < N then (fun i : Fin N => if i.val ∈ S then (1 : ZMod 2) else 0) ⟨v, h⟩ • ι (⟨v, h⟩ : Fin N).val ^ (2 * j.val + 1) else 0) =
      (if v ∈ S then ι v ^ (2 * j.val + 1) else 0) := by
    intro v hv
    rw [dif_pos (mem_range.mp hv)]
    by_cases h : v ∈ S <;> simp [h]
  rw [Finset.sum_congr rfl h1, ← Finset.sum_filter]
  congr 1
  ext v
  simp only [mem_filter, mem_range]
  constructor
  · rintro ⟨_, hv⟩; exact hv
  · intro hv; exact ⟨by simpa using hS hv, hv⟩

lemma card_indicator {N : ℕ} (S : Finset ℕ) (hS : S ⊆ range N) :
    (univ.filter fun i : Fin N => (if i.val ∈ S then (1 : ZMod 2) else 0) = 1).card = S.card := by
  have himg : (univ.filter fun i : Fin N => (if i.val ∈ S then (1 : ZMod 2) else 0) = 1).image
      (fun i => i.val) = S := by
    ext v
    simp only [mem_image, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨i, hi, rfl⟩
      by_cases h : i.val ∈ S
      · exact h
      · simp [h] at hi
    · intro hv
      refine ⟨⟨v, by simpa using hS hv⟩, ?_, rfl⟩
      simp [hv]
  have hinj : Set.InjOn (fun i : Fin N => i.val)
      ↑(univ.filter fun i : Fin N => (if i.val ∈ S then (1 : ZMod 2) else 0) = 1) :=
    fun a _ b _ hab => Fin.ext hab
  rw [← Finset.card_image_of_injOn hinj, himg]

lemma pin_unique_sets {N t : ℕ} (hN : 1 ≤ N) (ht : t ≤ N)
    {F : Type} [Field F] [Fintype F] [Algebra (ZMod 2) F] (w : ℕ) (hw : w = ⌈lg ((N : ℝ) + 1)⌉₊)
    (b : Module.Basis (Fin w) (ZMod 2) F) (ι : ℕ → F)
    (h0 : ∀ v < N, ι v ≠ 0) (hinj : Set.InjOn ι (Set.Iio N))
    (S T : Finset ℕ) (hS : S ⊆ range N) (hT : T ⊆ range N)
    (hSc : S.card ≤ t) (hTc : T.card ≤ t)
    (hp : ∀ j : Fin t, TopParams.power ι (2 * j.val + 1) S = TopParams.power ι (2 * j.val + 1) T) : S = T := by
  set x : Fin N → ZMod 2 := fun i => if i.val ∈ S then 1 else 0 with hx
  set x' : Fin N → ZMod 2 := fun i => if i.val ∈ T then 1 else 0 with hx'
  have hp' : pin ι t x = pin ι t x' := by
    funext j
    rw [hx, hx', pin_indicator ι S hS j, pin_indicator ι T hT j]
    exact hp j
  have hxx : x = x' := by
    refine pin_unique hN ht w hw b ι h0 hinj x x' ?_ ?_ hp'
    · rw [hx]; exact le_trans (le_of_eq (card_indicator S hS)) hSc
    · rw [hx']; exact le_trans (le_of_eq (card_indicator T hT)) hTc
  ext v
  by_cases hvN : v < N
  · have h1 : x ⟨v, hvN⟩ = x' ⟨v, hvN⟩ := by rw [hxx]
    constructor
    · intro hv
      have h2 : x ⟨v, hvN⟩ = 1 := by simp [hx, hv]
      rw [h2] at h1
      by_contra hcon
      simp [hx', hcon] at h1
    · intro hv
      have h2 : x' ⟨v, hvN⟩ = 1 := by simp [hx', hv]
      rw [← h1] at h2
      by_contra hcon
      simp [hx, hcon] at h2
  · have h1 : v ∉ S := fun h => hvN (mem_range.mp (hS h))
    have h2 : v ∉ T := fun h => hvN (mem_range.mp (hT h))
    simp [h1, h2]

end Part1

section Part1b

lemma exists_superset {n d : ℕ} {x : Finset ℕ} (hx : x ⊆ range n) (hxd : x.card ≤ d)
    (hdn : d ≤ n) : ∃ X : Finset ℕ, x ⊆ X ∧ X ⊆ range n ∧ X.card = d := by
  classical
  set x' : Finset (Fin n) := univ.filter (fun i : Fin n => i.val ∈ x) with hx'
  have hx'card : x'.card = x.card := by
    have himg : x'.image (fun i : Fin n => i.val) = x := by
      ext v
      simp only [hx', mem_image, mem_filter, mem_univ, true_and]
      exact ⟨fun ⟨i, hi, hv⟩ => hv ▸ hi, fun hv =>
        ⟨⟨v, by simpa using hx hv⟩, hv, rfl⟩⟩
    have hinj : Set.InjOn (fun i : Fin n => i.val) ↑x' := fun a _ b _ hab => Fin.ext hab
    rw [← Finset.card_image_of_injOn hinj, himg]
  obtain ⟨X', hx'sub, hX'card⟩ := Finset.exists_superset_card_eq (s := x') (n := d)
    (by rw [hx'card]; exact hxd) (by simpa using hdn)
  refine ⟨X'.image (fun i : Fin n => i.val), ?_, ?_, ?_⟩
  · intro v hv
    have hv' : (⟨v, by simpa using hx hv⟩ : Fin n) ∈ x' := by
      simp only [hx', mem_filter, mem_univ, true_and]; exact hv
    exact mem_image.mpr ⟨_, hx'sub hv', rfl⟩
  · intro v hv
    obtain ⟨i, -, rfl⟩ := mem_image.mp hv
    exact mem_range.mpr i.isLt
  · have hinj : Set.InjOn (fun i : Fin n => i.val) ↑X' := fun a _ b _ hab => Fin.ext hab
    rw [Finset.card_image_of_injOn hinj]; exact hX'card

lemma subtypeCongr_apply_of {α : Type} {p q : α → Prop} [DecidablePred p] [DecidablePred q]
    (e : {x // p x} ≃ {x // q x}) (f : {x // ¬p x} ≃ {x // ¬q x}) {a : α} (h : p a) :
    Equiv.subtypeCongr e f a = e ⟨a, h⟩ := by
  rw [Equiv.subtypeCongr]
  simp only [Equiv.trans_apply, Equiv.sumCompl_symm_apply_of_pos h]
  rfl

lemma subtypeCongr_apply_of_not {α : Type} {p q : α → Prop} [DecidablePred p] [DecidablePred q]
    (e : {x // p x} ≃ {x // q x}) (f : {x // ¬p x} ≃ {x // ¬q x}) {a : α} (h : ¬p a) :
    Equiv.subtypeCongr e f a = f ⟨a, h⟩ := by
  rw [Equiv.subtypeCongr]
  simp only [Equiv.trans_apply, Equiv.sumCompl_symm_apply_of_neg h]
  rfl

lemma exists_perm_range {n d : ℕ} (hdn : d ≤ n) (X : Finset ℕ) (hX : X ⊆ range n)
    (hXc : X.card = d) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i : Fin n, ((σ i).val ∈ X ↔ i.val < d) := by
  classical
  set U : Finset (Fin n) := univ.filter (fun i : Fin n => i.val < d) with hU
  set V : Finset (Fin n) := univ.filter (fun i : Fin n => i.val ∈ X) with hV
  have hUc : U.card = d := card_fin_filter_lt hdn
  have hVc : V.card = d := by
    have himg : V.image (fun i : Fin n => i.val) = X := by
      ext v
      simp only [hV, mem_image, mem_filter, mem_univ, true_and]
      exact ⟨fun ⟨i, hi, hv⟩ => hv ▸ hi, fun hv =>
        ⟨⟨v, by simpa using hX hv⟩, hv, rfl⟩⟩
    have hinj : Set.InjOn (fun i : Fin n => i.val) ↑V := fun a _ b _ hab => Fin.ext hab
    rw [← Finset.card_image_of_injOn hinj, himg]; exact hXc
  have he : {i // i ∈ U} ≃ {i // i ∈ V} :=
    Fintype.equivOfCardEq (by rw [Fintype.card_coe, Fintype.card_coe, hUc, hVc])
  have hf : {i // ¬ i ∈ U} ≃ {i // ¬ i ∈ V} := by
    refine Fintype.equivOfCardEq ?_
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, Fintype.card_coe,
      Fintype.card_coe, hUc, hVc]
  refine ⟨Equiv.subtypeCongr he hf, fun i => ?_⟩
  have hmemV : ∀ z : Fin n, (z ∈ V ↔ z.val ∈ X) := by
    intro z; simp [hV]
  by_cases hi : i.val < d
  · have hiU : i ∈ U := by simp [hU, hi]
    rw [subtypeCongr_apply_of he hf hiU]
    exact ⟨fun _ => hi, fun _ => (hmemV _).mp (he ⟨i, hiU⟩).2⟩
  · have hiU : ¬ i ∈ U := by simp [hU, hi]
    rw [subtypeCongr_apply_of_not he hf hiU]
    exact ⟨fun hcon => False.elim ((hf ⟨i, hiU⟩).2 ((hmemV _).mpr hcon)),
      fun hcon => absurd hcon hi⟩

end Part1b

section Concrete

variable (P : TopParams) {F : Type} [Field F] [Fintype F] [Algebra (ZMod 2) F]

/-- The top-level code, in concrete form. -/
def codeP (b : Module.Basis (Fin P.w) (ZMod 2) F) (ι : ℕ → F) (α : Fin P.B → Fˣ)
    (S : Finset ℕ) (s : Fin P.ell) : ZMod 2 :=
  b.repr ((α (P.wordIdx s) : F) * TopParams.power ι (2 * (P.wordIdx s).val + 1) S) (P.bitIdx s)

/-- The row prefix, in concrete form. -/
def truePrefixP (b : Module.Basis (Fin P.w) (ZMod 2) F) (ι : ℕ → F) (α : Fin P.B → Fˣ)
    (S : Finset ℕ) (a : ℕ) : List (ZMod 2) :=
  ((List.finRange P.ell).take a).map
    (fun s => b.repr ((α (P.wordIdx s) : F) *
      TopParams.power ι (2 * (P.wordIdx s).val + 1) S) (P.bitIdx s))

/-- The exact prediction, in concrete form. -/
def exactPredP (b : Module.Basis (Fin P.w) (ZMod 2) F) (ι : ℕ → F)
    (lr : Equiv.Perm (Fin P.n) × (Fin P.d → (Fin P.B → Fˣ)))
    (x J : Finset ℕ) (s : Fin P.ell) (j : Fin P.d) : Option (ZMod 2) :=
  P.predictTop b ι j.val (lr.2 j)
    (truePrefixP P b ι (lr.2 j) (rowImage P.n P.d lr.1 j.val x) s.val)

/-- `U_s`, in concrete form. -/
def UP (b : Module.Basis (Fin P.w) (ZMod 2) F) (ι : ℕ → F)
    (lr : Equiv.Perm (Fin P.n) × (Fin P.d → (Fin P.B → Fˣ)))
    (x J : Finset ℕ) (s : Fin P.ell) : ℕ :=
  (univ.filter fun j : Fin P.d => exactPredP P b ι lr x J s j = none).card

lemma codeP_eq (b : Module.Basis (Fin P.w) (ZMod 2) F) (ι : ℕ → F) (j : Fin P.d)
    (α : Fin P.B → Fˣ) (S : Finset ℕ) (s : Fin P.ell) :
    (P.scheme b ι).code j α S s = codeP P b ι α S s := rfl

lemma truePrefixP_eq (b : Module.Basis (Fin P.w) (ZMod 2) F) (ι : ℕ → F) (j : Fin P.d)
    (α : Fin P.B → Fˣ) (S : Finset ℕ) (a : ℕ) :
    (P.scheme b ι).truePrefix j α S a = truePrefixP P b ι α S a := rfl

lemma exactPredP_eq (b : Module.Basis (Fin P.w) (ZMod 2) F) (ι : ℕ → F)
    (lr : Equiv.Perm (Fin P.n) × (Fin P.d → (Fin P.B → Fˣ)))
    (x J : Finset ℕ) (s : Fin P.ell) (j : Fin P.d) :
    (P.scheme b ι).exactPred lr x J s j = exactPredP P b ι lr x J s j := rfl

lemma UP_eq (b : Module.Basis (Fin P.w) (ZMod 2) F) (ι : ℕ → F)
    (lr : Equiv.Perm (Fin P.n) × (Fin P.d → (Fin P.B → Fˣ)))
    (x J : Finset ℕ) (s : Fin P.ell) :
    (P.scheme b ι).U lr x J s = UP P b ι lr x J s := rfl

/-- A prefix bit of the concrete prefix. -/
lemma truePrefixP_getD (b : Module.Basis (Fin P.w) (ZMod 2) F) (ι : ℕ → F)
    (α : Fin P.B → Fˣ) (S : Finset ℕ) {a q : ℕ} (ha : a ≤ P.ell) (hq : q < a) :
    (truePrefixP P b ι α S a).getD q 0 = codeP P b ι α S ⟨q, lt_of_lt_of_le hq ha⟩ := by
  simp only [truePrefixP]
  have hlen : (((List.finRange P.ell).take a).map
      (fun s => b.repr ((α (P.wordIdx s) : F) *
        TopParams.power ι (2 * (P.wordIdx s).val + 1) S) (P.bitIdx s))).length = a := by
    rw [List.length_map, List.length_take, List.length_finRange]
    omega
  rw [List.getD_eq_getElem _ _ (by rw [hlen]; exact hq), List.getElem_map]
  have h2 : q < ((List.finRange P.ell).take a).length := by
    rw [List.length_take, List.length_finRange]; omega
  rw [List.getElem_take]
  have h3 : q < (List.finRange P.ell).length := by
    rw [List.length_finRange]; omega
  rw [List.getElem_finRange]
  congr 2

/-- Membership in the candidate filter. -/
lemma cand_mem (b : Module.Basis (Fin P.w) (ZMod 2) F) (ι : ℕ → F)
    (j : Fin P.d) (α : Fin P.B → Fˣ) (z : List (ZMod 2)) (i : ℕ)
    {C : Finset ℕ} (h : P.cand b ι j.val α z i = some C) :
    C ⊆ range (rowLen P.n P.d j.val) ∧ C.card ≤ i ∧
      ∀ a : Fin P.B, a.val < i →
        TopParams.power ι (2 * a.val + 1) C = ((α a)⁻¹ : Fˣ) * P.wordOf b z a.val := by
  have h1 : C ∈ (range (rowLen P.n P.d j.val)).powerset.filter (fun S =>
      S.card ≤ i ∧ ∀ a : Fin P.B, a.val < i →
        TopParams.power ι (2 * a.val + 1) S = ((α a)⁻¹ : Fˣ) * P.wordOf b z a.val) := by
    unfold TopParams.cand at h
    rw [List.head?_eq_some_iff] at h
    obtain ⟨ys, hys⟩ := h
    rw [← Finset.mem_toList, hys]
    exact List.mem_cons_self ..
  rw [Finset.mem_filter, Finset.mem_powerset] at h1
  exact h1

end Concrete

section WordIdx

variable (P : TopParams)

lemma w_pos (hargs : P.Args) : 0 < P.w := by
  have hd : 0 < P.d := Pd_pos P hargs
  have hdn : P.d ≤ P.n := Pd_le_n P hargs
  have hN : 1 ≤ P.N := by
    rw [TopParams.N]
    apply Nat.ceil_pos.mpr
    have h1 : (1:ℝ) ≤ (P.n : ℝ) / (P.d : ℝ) := by
      rw [le_div_iff₀ (by exact_mod_cast hd)]
      have : (1:ℝ) * (P.d:ℝ) = (P.d:ℝ) := by ring
      rw [this]
      exact_mod_cast hdn
    linarith
  rw [TopParams.w]
  apply Nat.ceil_pos.mpr
  have h2 : (1:ℝ) < (P.N : ℝ) + 1 := by
    have : (1:ℝ) ≤ (P.N : ℝ) := by exact_mod_cast hN
    linarith
  exact Real.logb_pos (by norm_num) h2

lemma wordIdx_mul_add {a' k : ℕ} (hk : k < P.w) (h : a' * P.w + k < P.ell)
    (hA : a' < P.B) : P.wordIdx ⟨a' * P.w + k, h⟩ = ⟨a', hA⟩ := by
  apply Fin.ext
  show (a' * P.w + k) / P.w = a'
  rw [show a' * P.w + k = P.w * a' + k by ring,
    Nat.mul_add_div (by omega : 0 < P.w), Nat.div_eq_of_lt hk, Nat.add_zero]

lemma bitIdx_mul_add {a' k : ℕ} (hk : k < P.w) (h : a' * P.w + k < P.ell)
    (hk' : k < P.w) : P.bitIdx ⟨a' * P.w + k, h⟩ = ⟨k, hk'⟩ := by
  apply Fin.ext
  show (a' * P.w + k) % P.w = k
  rw [show a' * P.w + k = k + P.w * a' by ring, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt hk]

end WordIdx

section WordOf

variable (P : TopParams) {F : Type} [Field F] [Fintype F] [Algebra (ZMod 2) F]

lemma wordOf_truePrefix (b : Module.Basis (Fin P.w) (ZMod 2) F) (ι : ℕ → F)
    (α : Fin P.B → Fˣ) (S : Finset ℕ) {a a' : ℕ} (hA : a' < P.B)
    (ha : (a' + 1) * P.w ≤ a) (haell : a ≤ P.ell) :
    P.wordOf b (truePrefixP P b ι α S a) a' =
      (α ⟨a', hA⟩ : F) * TopParams.power ι (2 * a' + 1) S := by
  unfold TopParams.wordOf
  have h1 : ∀ k : Fin P.w, (truePrefixP P b ι α S a).getD (a' * P.w + k.val) 0 =
      b.repr ((α ⟨a', hA⟩ : F) * TopParams.power ι (2 * a' + 1) S) k := by
    intro k
    have hklt : a' * P.w + k.val < a := by
      have hk := k.isLt
      nlinarith
    rw [truePrefixP_getD P b ι α S haell hklt]
    simp only [codeP]
    rw [wordIdx_mul_add (P := P) k.isLt (by omega) hA,
      bitIdx_mul_add (P := P) k.isLt (by omega) k.isLt]
  rw [Finset.sum_congr rfl fun k _ => by rw [h1 k]]
  exact b.sum_repr ((α ⟨a', hA⟩ : F) * TopParams.power ι (2 * a' + 1) S)

end WordOf

lemma rowLen_le_n {N m j : ℕ} : rowLen N m j ≤ N := by
  rw [rowLen]
  exact le_trans (Finset.card_filter_le _ _) (by simp)

section Predict

variable (P : TopParams) {F : Type} [Field F] [Fintype F] [Algebra (ZMod 2) F]

lemma N_pos (hargs : P.Args) : 1 ≤ P.N := by
  have hd : 0 < P.d := Pd_pos P hargs
  have hdn : P.d ≤ P.n := Pd_le_n P hargs
  rw [TopParams.N]
  apply Nat.ceil_pos.mpr
  exact div_pos (by exact_mod_cast (Pn_pos P hargs)) (by exact_mod_cast hd)

lemma div_lt_N (hargs : P.Args) {p : ℕ} (hp : p < P.n) : p / P.d < P.N := by
  have hd : 0 < P.d := Pd_pos P hargs
  rw [Nat.div_lt_iff_lt_mul hd]
  rw [TopParams.N]
  have h1 : (P.n : ℝ) / (P.d : ℝ) ≤ (⌈(P.n : ℝ) / (P.d : ℝ)⌉₊ : ℝ) := Nat.le_ceil _
  have h2 : (P.n : ℝ) ≤ (⌈(P.n : ℝ) / (P.d : ℝ)⌉₊ : ℝ) * P.d := by
    have h3 := mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg (α := ℝ) P.d)
    rw [div_mul_cancel₀] at h3
    · exact h3
    · exact ne_of_gt (by exact_mod_cast hd)
  have h3 : (p : ℝ) < (⌈(P.n : ℝ) / (P.d : ℝ)⌉₊ : ℝ) * P.d := by
    have : (p : ℝ) < (P.n : ℝ) := by exact_mod_cast hp
    linarith
  exact_mod_cast h3

lemma rowLen_le_N (hargs : P.Args) (j : ℕ) : rowLen P.n P.d j ≤ P.N := by
  have hd : 0 < P.d := Pd_pos P hargs
  have hinj : Set.InjOn (fun p : ℕ => p / P.d)
      ↑((range P.n).filter (fun p => p % P.d = j)) := by
    intro a ha b hb hab
    simp only [mem_coe, mem_filter, mem_range] at ha hb
    have hab' : a / P.d = b / P.d := hab
    calc a = P.d * (a / P.d) + a % P.d := (Nat.div_add_mod _ _).symm
      _ = P.d * (b / P.d) + b % P.d := by rw [hab', ha.2, hb.2]
      _ = b := Nat.div_add_mod _ _
  have himg : ((range P.n).filter (fun p => p % P.d = j)).image (fun p => p / P.d) ⊆
      range P.N := by
    intro y hy
    rw [mem_image] at hy
    obtain ⟨p, hp, rfl⟩ := hy
    rw [mem_range]
    exact div_lt_N P hargs (by simpa using (mem_filter.mp hp).1)
  calc rowLen P.n P.d j = ((range P.n).filter (fun p => p % P.d = j)).card := rfl
    _ = (((range P.n).filter (fun p => p % P.d = j)).image (fun p => p / P.d)).card :=
        (Finset.card_image_of_injOn hinj).symm
    _ ≤ (range P.N).card := Finset.card_le_card himg
    _ = P.N := card_range _



lemma prU_mul_right {n : ℕ} (τ : Equiv.Perm (Fin n)) (Q : Equiv.Perm (Fin n) → Prop) :
    prU (fun π => Q (π * τ)) = prU Q := by
  have h := prU_equiv (Equiv.mulRight τ) Q
  simpa [Equiv.mulRight] using h

/-- If the row has at most `s.val / w` nonzeros, the top-layer prediction from the true prefix is
not `⊥`. -/
lemma predictTop_some (hargs : P.Args) (b : Module.Basis (Fin P.w) (ZMod 2) F) (ι : ℕ → F)
    (hι : P.IsAddress ι) (π : Equiv.Perm (Fin P.n))
    (α : Fin P.d → (Fin P.B → Fˣ)) (x : Finset ℕ) (hx : x ⊆ range P.n)
    (s : Fin P.ell) (j : Fin P.d)
    (hR : (rowImage P.n P.d π j.val x).card ≤ s.val / P.w) :
    P.predictTop b ι j.val (α j)
      (truePrefixP P b ι (α j) (rowImage P.n P.d π j.val x) s.val) ≠ none := by
  have hw : 0 < P.w := w_pos P hargs
  have hd : 0 < P.d := Pd_pos P hargs
  set R := rowImage P.n P.d π j.val x with hRdef
  set A := s.val / P.w with hAdef
  set k := s.val % P.w with hkdef
  have hklt : k < P.w := by rw [hkdef]; exact Nat.mod_lt _ hw
  have hsval : s.val = A * P.w + k := by
    rw [hAdef, hkdef, Nat.mul_comm]
    exact (Nat.div_add_mod s.val P.w).symm
  have hAB : A < P.B := by
    have hs : A * P.w + k < P.B * P.w := by rw [← hsval]; exact s.isLt
    have h1 : A * P.w < P.B * P.w := by omega
    exact (Nat.mul_lt_mul_right hw).mp h1
  -- membership of the true support in the candidate filter
  have hRmem : R ∈ (range (rowLen P.n P.d j.val)).powerset.filter (fun S =>
      S.card ≤ A ∧ ∀ a : Fin P.B, a.val < A →
        TopParams.power ι (2 * a.val + 1) S = ((α j a)⁻¹ : Fˣ) * P.wordOf b
          (truePrefixP P b ι (α j) R s.val) a.val) := by
    rw [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨rowImage_subset_range_rowLen (N := P.n) (m := P.d) (j := j.val) hd π x,
      by rw [hRdef]; exact hR, ?_⟩
    intro a' ha'
    have hle : (a'.val + 1) * P.w ≤ s.val := by
      have h1 : a'.val + 1 ≤ A := ha'
      calc (a'.val + 1) * P.w ≤ A * P.w := by nlinarith [hw]
        _ ≤ A * P.w + k := Nat.le_add_right _ _
        _ = s.val := hsval.symm
    have h1 := wordOf_truePrefix (P := P) b ι (α j) R (lt_trans ha' hAB) hle (le_of_lt s.isLt)
    rw [h1]
    rw [show (⟨a'.val, lt_trans ha' hAB⟩ : Fin P.B) = a' from Fin.ext rfl]
    rw [← mul_assoc]
    simp only [Units.val_inv_eq_inv_val]
    rw [inv_mul_cancel₀ (Units.ne_zero (α j a')), one_mul]
  have hne : (range (rowLen P.n P.d j.val)).powerset.filter (fun S =>
      S.card ≤ A ∧ ∀ a : Fin P.B, a.val < A →
        TopParams.power ι (2 * a.val + 1) S = ((α j a)⁻¹ : Fˣ) * P.wordOf b
          (truePrefixP P b ι (α j) R s.val) a.val) ≠ ∅ := by
    intro h; rw [h] at hRmem; exact absurd hRmem (by simp)
  obtain ⟨C, hC⟩ : ∃ C, P.cand b ι j.val (α j) (truePrefixP P b ι (α j) R s.val) A = some C := by
    unfold TopParams.cand
    cases h : ((range (rowLen P.n P.d j.val)).powerset.filter (fun S =>
        S.card ≤ A ∧ ∀ a : Fin P.B, a.val < A →
          TopParams.power ι (2 * a.val + 1) S = ((α j a)⁻¹ : Fˣ) * P.wordOf b
            (truePrefixP P b ι (α j) R s.val) a.val)).toList with
    | nil =>
        exfalso
        apply hne
        have hcard : ((range (rowLen P.n P.d j.val)).powerset.filter (fun S =>
            S.card ≤ A ∧ ∀ a : Fin P.B, a.val < A →
              TopParams.power ι (2 * a.val + 1) S = ((α j a)⁻¹ : Fˣ) * P.wordOf b
                (truePrefixP P b ι (α j) R s.val) a.val)).card = 0 := by
          have := Finset.length_toList (s := ((range (rowLen P.n P.d j.val)).powerset.filter (fun S =>
              S.card ≤ A ∧ ∀ a : Fin P.B, a.val < A →
                TopParams.power ι (2 * a.val + 1) S = ((α j a)⁻¹ : Fˣ) * P.wordOf b
                  (truePrefixP P b ι (α j) R s.val) a.val)))
          rw [h] at this
          simpa using this.symm
        exact Finset.card_eq_zero.mp hcard
    | cons a l => exact ⟨a, rfl⟩
  -- `C` equals the true support
  have hCmem := cand_mem P b ι j (α j) (truePrefixP P b ι (α j) R s.val) A hC
  have hCeq : C = R := by
    obtain ⟨hCsub, hCcard, hCpow⟩ := hCmem
    have hCn : C ⊆ range P.N := fun v hv => by
      have := hCsub hv
      rw [mem_range] at this ⊢
      exact lt_of_lt_of_le this (rowLen_le_N P hargs j.val)
    have hRn : R ⊆ range P.N := fun v hv => by
      have := rowImage_subset_range_rowLen (N := P.n) (m := P.d) (j := j.val) hd π x hv
      rw [mem_range] at this ⊢
      exact lt_of_lt_of_le this (rowLen_le_N P hargs j.val)
    have hRpow : ∀ a : Fin P.B, a.val < A →
        TopParams.power ι (2 * a.val + 1) R =
          ((α j a)⁻¹ : Fˣ) * P.wordOf b (truePrefixP P b ι (α j) R s.val) a.val := by
      intro a' ha'
      have hle : (a'.val + 1) * P.w ≤ s.val := by
        have h1 : a'.val + 1 ≤ A := ha'
        calc (a'.val + 1) * P.w ≤ A * P.w := by nlinarith [hw]
          _ ≤ A * P.w + k := Nat.le_add_right _ _
          _ = s.val := hsval.symm
      have h1 := wordOf_truePrefix (P := P) b ι (α j) R (lt_trans ha' hAB) hle (le_of_lt s.isLt)
      rw [h1]
      rw [show (⟨a'.val, lt_trans ha' hAB⟩ : Fin P.B) = a' from Fin.ext rfl]
      rw [← mul_assoc]
      simp only [Units.val_inv_eq_inv_val]
      rw [inv_mul_cancel₀ (Units.ne_zero (α j a')), one_mul]
    have hBP : P.B ≤ P.N := min_le_left _ _
    refine pin_unique_sets (N := P.N) (t := A) (N_pos P hargs) (by omega) P.w rfl b ι
      hι.1 hι.2 C R hCn hRn hCcard ?_ ?_
    · rw [hRdef]; exact hR
    · intro a'
      have hPB : a'.val < P.B := lt_of_lt_of_le a'.isLt (le_of_lt hAB)
      rw [hCpow ⟨a'.val, hPB⟩ a'.isLt, hRpow ⟨a'.val, hPB⟩ a'.isLt]
  -- the check passes
  have hzlen : (truePrefixP P b ι (α j) R s.val).length = s.val := by
    simp only [truePrefixP, List.length_map, List.length_take, List.length_finRange]
    omega
  have hkey : P.predictTop b ι j.val (α j) (truePrefixP P b ι (α j) R s.val)
      = (P.cand b ι j.val (α j) (truePrefixP P b ι (α j) R s.val) A).bind (fun C =>
          let bits := fun k' => b.repr ((α j ⟨A, hAB⟩) * TopParams.power ι (2 * A + 1) C) k'
          if ∀ k' : Fin P.w, k'.val < k → bits k' = (truePrefixP P b ι (α j) R s.val).getD (A * P.w + k'.val) 0
          then some (bits ⟨k, hklt⟩) else none) := by
    rw [TopParams.predictTop, dif_pos (by rw [hzlen]; exact s.isLt)]
    simp only [hzlen]
    rfl
  rw [hkey, hC, hCeq]
  simp only [Option.bind_some]
  rw [if_pos]
  · exact Option.some_ne_none _
  · intro k' hklt'
    have hk' : k'.val < P.w := k'.isLt
    have hq : A * P.w + k'.val < s.val := by
      rw [hsval]
      omega
    have hA' : A < P.B := hAB
    have hgetD := truePrefixP_getD (P := P) b ι (α j) R (le_of_lt s.isLt) hq
    rw [hgetD]
    simp only [codeP]
    rw [wordIdx_mul_add (P := P) hk' (by omega) hA',
      bitIdx_mul_add (P := P) hk' (by omega) hk']

end Predict

section UPBound

variable (P : TopParams) {F : Type} [Field F] [Fintype F] [Algebra (ZMod 2) F]

lemma UP_le (hargs : P.Args) (b : Module.Basis (Fin P.w) (ZMod 2) F) (ι : ℕ → F)
    (hι : P.IsAddress ι) (x : Finset ℕ) (hx : x ⊆ range P.n) (s : Fin P.ell)
    (lr : Equiv.Perm (Fin P.n) × (Fin P.d → (Fin P.B → Fˣ))) :
    UP P b ι lr x ∅ s ≤ (univ.filter fun j : Fin P.d =>
      (P.wordIdx s).val + 1 ≤ (rowImage P.n P.d lr.1 j.val x).card).card := by
  unfold UP
  refine Finset.card_le_card ?_
  intro j hj
  simp only [mem_filter, mem_univ, true_and] at hj ⊢
  by_contra hcon
  rw [not_le] at hcon
  have hAe : (P.wordIdx s).val = s.val / P.w := rfl
  exact (predictTop_some P hargs b ι hι lr.1 lr.2 x hx s j (by omega)) hj

end UPBound

section MainProof

variable (P : TopParams) {F : Type} [Field F] [Fintype F] [Algebra (ZMod 2) F]

lemma perm_rowImage (n d : ℕ) (X : Finset ℕ) (σ : Equiv.Perm (Fin n))
    (hσ : ∀ i : Fin n, ((σ i).val ∈ X ↔ i.val < d))
    (π : Equiv.Perm (Fin n)) (j : Fin d) :
    rowImage n d (π * σ⁻¹) j.val X = rowImage n d π j.val (range d) := by
  ext y
  rw [mem_rowImage, mem_rowImage]
  constructor
  · rintro ⟨i, hiX, hmod, hdiv⟩
    refine ⟨σ⁻¹ i, ?_, ?_, ?_⟩
    · rw [mem_range]
      exact (hσ (σ⁻¹ i)).mp (by simpa using hiX)
    · simpa using hmod
    · simpa using hdiv
  · rintro ⟨u, hu, hmod, hdiv⟩
    refine ⟨σ u, ?_, ?_, ?_⟩
    · exact (hσ u).mpr (mem_range.mp hu)
    · simpa using hmod
    · simpa using hdiv

end MainProof

/-- Lemma 6.1 (Across words), PDF p.28 (printed p.27). Source word `a` is `a + 1` here. -/
theorem lemma_6_1 (P : TopParams) (hargs : P.Args) (F : Type) [Field F] [Fintype F]
    [Algebra (ZMod 2) F] (b : Module.Basis (Fin P.w) (ZMod 2) F) (ι : ℕ → F) (hι : P.IsAddress ι)
    (x : Finset ℕ) (hx : x ⊆ range P.n) (hxd : x.card ≤ P.d) :
    (∀ s : Fin P.ell,
      expU (fun lr : (P.scheme b ι).LocalSeed => ((P.scheme b ι).U lr x ∅ s : ℝ)) ≤
        P.q ((P.wordIdx s).val + 1)) ∧
    (∑' a : ℕ, ENNReal.ofReal (P.q (a + 1))) = (P.d : ℝ≥0∞) ∧
    entropy (fun a : ℕ => P.q (a + 1) / (P.d : ℝ)) ≤
      ENNReal.ofReal (lg (2 * Real.exp 1)) := by
  refine ⟨?_, q_tsum_eq P hargs, entropy_bound P hargs⟩
  intro s
  have hargs' := hargs
  have hd : 0 < P.d := Pd_pos P hargs
  have hdn : P.d ≤ P.n := Pd_le_n P hargs
  obtain ⟨X, hxX, hXsub, hXcard⟩ := exists_superset hx hxd hdn
  change expU (fun lr : Equiv.Perm (Fin P.n) × (Fin P.d → (Fin P.B → Fˣ)) =>
    (UP P b ι lr x ∅ s : ℝ)) ≤ P.q ((P.wordIdx s).val + 1)
  have h1 : expU (fun lr : Equiv.Perm (Fin P.n) × (Fin P.d → (Fin P.B → Fˣ)) =>
        (UP P b ι lr x ∅ s : ℝ)) ≤
      expU (fun lr : Equiv.Perm (Fin P.n) × (Fin P.d → (Fin P.B → Fˣ)) =>
        ((univ.filter fun j : Fin P.d => (P.wordIdx s).val + 1 ≤
          (rowImage P.n P.d lr.1 j.val x).card).card : ℝ)) := by
    refine expU_le fun lr => ?_
    exact_mod_cast UP_le P hargs b ι hι x hx s lr
  have h2 : expU (fun lr : Equiv.Perm (Fin P.n) × (Fin P.d → (Fin P.B → Fˣ)) =>
        ((univ.filter fun j : Fin P.d => (P.wordIdx s).val + 1 ≤
          (rowImage P.n P.d lr.1 j.val x).card).card : ℝ)) ≤
      expU (fun lr : Equiv.Perm (Fin P.n) × (Fin P.d → (Fin P.B → Fˣ)) =>
        ((univ.filter fun j : Fin P.d => (P.wordIdx s).val + 1 ≤
          (rowImage P.n P.d lr.1 j.val X).card).card : ℝ)) := by
    refine expU_le fun lr => ?_
    have hcard : (univ.filter fun j : Fin P.d => (P.wordIdx s).val + 1 ≤
        (rowImage P.n P.d lr.1 j.val x).card).card ≤
        (univ.filter fun j : Fin P.d => (P.wordIdx s).val + 1 ≤
          (rowImage P.n P.d lr.1 j.val X).card).card := by
      refine Finset.card_le_card ?_
      intro j hj
      simp only [mem_filter, mem_univ, true_and] at hj ⊢
      exact le_trans hj (rowImage_card_le lr.1 j.val hxX)
    exact_mod_cast hcard
  obtain ⟨σ, hσ⟩ := exists_perm_range hdn X hXsub hXcard
  have hrel : ∀ j : Fin P.d, prU (fun π : Equiv.Perm (Fin P.n) =>
        (P.wordIdx s).val + 1 ≤ (rowImage P.n P.d π j.val X).card) =
      prU (fun π : Equiv.Perm (Fin P.n) =>
        (P.wordIdx s).val + 1 ≤ (rowImage P.n P.d π j.val (range P.d)).card) := by
    intro j
    rw [← prU_mul_right (σ⁻¹) (fun π : Equiv.Perm (Fin P.n) =>
      (P.wordIdx s).val + 1 ≤ (rowImage P.n P.d π j.val X).card)]
    congr 1
    ext π
    rw [perm_rowImage P.n P.d X σ hσ π j]
  set G : Equiv.Perm (Fin P.n) → ℝ := fun π =>
    ((univ.filter fun j : Fin P.d => (P.wordIdx s).val + 1 ≤
      (rowImage P.n P.d π j.val X).card).card : ℝ) with hG
  have hsum : expU (fun lr : Equiv.Perm (Fin P.n) × (Fin P.d → (Fin P.B → Fˣ)) =>
        ((univ.filter fun j : Fin P.d => (P.wordIdx s).val + 1 ≤
          (rowImage P.n P.d lr.1 j.val X).card).card : ℝ)) =
      ∑ j : Fin P.d, prU (fun π : Equiv.Perm (Fin P.n) =>
        (P.wordIdx s).val + 1 ≤ (rowImage P.n P.d π j.val X).card) := by
    rw [show (fun lr : Equiv.Perm (Fin P.n) × (Fin P.d → (Fin P.B → Fˣ)) =>
        ((univ.filter fun j : Fin P.d => (P.wordIdx s).val + 1 ≤
          (rowImage P.n P.d lr.1 j.val X).card).card : ℝ)) = fun lr => G lr.1 from rfl]
    rw [expU_fst_prod]
    have hcard : G = fun π : Equiv.Perm (Fin P.n) => ∑ j : Fin P.d,
        (if (P.wordIdx s).val + 1 ≤ (rowImage P.n P.d π j.val X).card then (1:ℝ) else 0) := by
      funext π
      rw [hG]
      exact (Finset.sum_boole _ _).symm
    rw [hcard, expU_sum_finset]
    exact Finset.sum_congr rfl fun j _ => expU_indicator _
  calc expU (fun lr : Equiv.Perm (Fin P.n) × (Fin P.d → (Fin P.B → Fˣ)) =>
        (UP P b ι lr x ∅ s : ℝ))
      ≤ expU (fun lr : Equiv.Perm (Fin P.n) × (Fin P.d → (Fin P.B → Fˣ)) =>
        ((univ.filter fun j : Fin P.d => (P.wordIdx s).val + 1 ≤
          (rowImage P.n P.d lr.1 j.val x).card).card : ℝ)) := h1
    _ ≤ expU (fun lr : Equiv.Perm (Fin P.n) × (Fin P.d → (Fin P.B → Fˣ)) =>
        ((univ.filter fun j : Fin P.d => (P.wordIdx s).val + 1 ≤
          (rowImage P.n P.d lr.1 j.val X).card).card : ℝ)) := h2
    _ = ∑ j : Fin P.d, prU (fun π : Equiv.Perm (Fin P.n) =>
        (P.wordIdx s).val + 1 ≤ (rowImage P.n P.d π j.val X).card) := hsum
    _ = ∑ j : Fin P.d, prU (fun π : Equiv.Perm (Fin P.n) =>
        (P.wordIdx s).val + 1 ≤ (rowImage P.n P.d π j.val (range P.d)).card) := by
        exact Finset.sum_congr rfl fun j _ => hrel j
    _ = P.q ((P.wordIdx s).val + 1) := by
        rw [TopParams.q, Finset.sum_fin_eq_sum_range]
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [dif_pos (Finset.mem_range.mp hj)]
        rfl

end LinearSetReconciliation327.Main

open LinearSetReconciliation327.Main in
/-- Lemma 6.1 (Across words) — submission wrapper matching the target statement. -/
theorem solution (P : TopParams) (hargs : P.Args) (F : Type) [Field F] [Fintype F]
    [Algebra (ZMod 2) F] (b : Module.Basis (Fin P.w) (ZMod 2) F) (ι : ℕ → F) (hι : P.IsAddress ι)
    (x : Finset ℕ) (hx : x ⊆ range P.n) (hxd : x.card ≤ P.d) :
    (∀ s : Fin P.ell,
      expU (fun lr : (P.scheme b ι).LocalSeed => ((P.scheme b ι).U lr x ∅ s : ℝ)) ≤
        P.q ((P.wordIdx s).val + 1)) ∧
    (∑' a : ℕ, ENNReal.ofReal (P.q (a + 1))) = (P.d : ℝ≥0∞) ∧
    entropy (fun a : ℕ => P.q (a + 1) / (P.d : ℝ)) ≤
      ENNReal.ofReal (lg (2 * Real.exp 1)) :=
  LinearSetReconciliation327.Main.lemma_6_1 P hargs F b ι hι x hx hxd