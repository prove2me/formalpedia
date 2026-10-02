-- Prove2me | solution 1 for MooreFoelner.card_Rf_sub_two_le_three_mul_wordLength
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-02T08:42:22.628466+00:00
-- url     : https://prove2.me/submissions/f02d12a6-68f8-4ada-9510-f4c5eb4d1e72

import Theorems.Thm_MooreFoelner_closure_x0_x1_eq_top
import Theorems.Thm_MooreFoelner_bijOn_Lf_Rf_and_diagramMul
import Theorems.Thm_MooreFoelner_isReducedDiagram_iff
import Theorems.Thm_MooreFoelner_existsUnique_isReducedDiagram_diagramEquiv
import Theorems.Thm_MooreFoelner_isTree_treeAct_and_isPartialAction
import Definitions.Def_CannonFloydParry
import Definitions.Def_MooreFoelner
import Definitions.Def_MooreTrees
import Definitions.Def_ThompsonAmenability
import Mathlib

section
namespace MooreFoelner

open Classical CannonFloydParry

end MooreFoelner
end

section
/-!
# Moore 2013, group GenTrees: #7, #17, #18, #27
-/

namespace MooreFoelner.Dev.GenTrees

open Classical MooreFoelner CannonFloydParry
open scoped symmDiff

section Folner

variable {G : Type*} [Group G]

end Folner

section Seqs

/-- The infinite sequence `s⁀y`. -/
def appS (s : Seq) (y : ℕ → Bool) : ℕ → Bool :=
  fun n => if h : n < s.length then s.get ⟨n, h⟩ else y (n - s.length)

/-- `x` with its first `k` digits removed. -/
def shift (x : ℕ → Bool) (k : ℕ) : ℕ → Bool := fun n => x (n + k)

lemma isInitialPart_appS (s : Seq) (y : ℕ → Bool) : IsInitialPart s (appS s y) := by
  intro i h; simp [appS, h]

lemma appS_shift {s : Seq} {x : ℕ → Bool} (h : IsInitialPart s x) :
    appS s (shift x s.length) = x := by
  funext n; unfold appS shift
  split_ifs with hn
  · exact h n hn
  · congr 1; omega

lemma shift_appS (s : Seq) (y : ℕ → Bool) : shift (appS s y) s.length = y := by
  funext n; simp [appS, shift]

@[simp] lemma appS_nil (y : ℕ → Bool) : appS [] y = y := by funext n; simp [appS]

@[simp] lemma shift_zero (x : ℕ → Bool) : shift x 0 = x := by funext n; simp [shift]

lemma isInitialPart_of_prefix {a b : Seq} {x : ℕ → Bool} (hab : a <+: b)
    (hb : IsInitialPart b x) : IsInitialPart a x := by
  intro i hi
  obtain ⟨c, rfl⟩ := hab
  have := hb i (by simp; omega)
  simpa [List.getElem_append_left hi] using this

lemma isInitialPart_comparable {a b : Seq} {x : ℕ → Bool} (ha : IsInitialPart a x)
    (hb : IsInitialPart b x) : a <+: b ∨ b <+: a := by
  have key : ∀ a b : Seq, IsInitialPart a x → IsInitialPart b x → a.length ≤ b.length →
      a <+: b := by
    intro a b ha hb hle
    rw [List.prefix_iff_eq_take]
    apply List.ext_getElem (by simp; omega)
    intro n h1 h2
    have := ha n h1
    have := hb n (by omega)
    simp_all
  rcases le_total a.length b.length with h | h
  · exact Or.inl (key a b ha hb h)
  · exact Or.inr (key b a hb ha h)

end Seqs

section Trees

lemma tree_prefix_eq {T : Finset Seq} (hT : IsTree T) {a b : Seq} (ha : a ∈ T) (hb : b ∈ T)
    (hab : a <+: b) : a = b := by
  obtain ⟨t, _, huniq⟩ := hT (appS b fun _ => false)
  have hb' := huniq b ⟨hb, isInitialPart_appS _ _⟩
  have ha' := huniq a ⟨ha, isInitialPart_of_prefix hab (isInitialPart_appS _ _)⟩
  rw [ha', hb']

lemma tree_comparable_eq {T : Finset Seq} (hT : IsTree T) {a b : Seq} (ha : a ∈ T) (hb : b ∈ T)
    (hab : a <+: b ∨ b <+: a) : a = b := by
  rcases hab with h | h
  · exact tree_prefix_eq hT ha hb h
  · exact (tree_prefix_eq hT hb ha h).symm

lemma tree_exists_initialPart {T : Finset Seq} (hT : IsTree T) (x : ℕ → Bool) :
    ∃ t ∈ T, IsInitialPart t x := by
  obtain ⟨t, ⟨ht, hx⟩, _⟩ := hT x
  exact ⟨t, ht, hx⟩

lemma tree_nonempty {T : Finset Seq} (hT : IsTree T) : T.Nonempty := by
  obtain ⟨t, ht, _⟩ := tree_exists_initialPart hT (fun _ => false)
  exact ⟨t, ht⟩

end Trees

section Sorted

lemma mem_sorted {T : Finset Seq} {a : Seq} : a ∈ sorted T ↔ a ∈ T := by
  unfold sorted; simp [List.mem_mergeSort]

lemma length_sorted (T : Finset Seq) : (sorted T).length = T.card := by
  unfold sorted; simp

lemma nodup_sorted (T : Finset Seq) : (sorted T).Nodup :=
  (List.mergeSort_perm _ _).nodup_iff.mpr (Finset.nodup_toList T)

lemma get_mem_sorted (T : Finset Seq) (i : Fin (sorted T).length) : (sorted T).get i ∈ T :=
  mem_sorted.mp (List.get_mem _ _)

lemma exists_index_of_mem {T : Finset Seq} {a : Seq} (ha : a ∈ T) :
    ∃ i : Fin (sorted T).length, (sorted T).get i = a :=
  List.get_of_mem (mem_sorted.mpr ha)

lemma sorted_index_unique {T : Finset Seq} {i j : Fin (sorted T).length}
    (h : (sorted T).get i = (sorted T).get j) : i = j :=
  (nodup_sorted T).get_inj_iff.mp h

end Sorted

section DiagramMap

lemma find_finRange_eq {n : ℕ} (p : Fin n → Bool) (i : Fin n) (hi : p i = true)
    (huniq : ∀ j, p j = true → j = i) : (List.finRange n).find? p = some i := by
  cases h : (List.finRange n).find? p with
  | none =>
    rw [List.find?_eq_none] at h
    exact absurd hi (by simpa using h i (List.mem_finRange i))
  | some j =>
    have := List.find?_some h
    rw [huniq j this]

lemma diagramMap_eq {L R : Finset Seq} (hL : IsTree L)
    (x : ℕ → Bool) (i : ℕ) (hiL : i < (sorted L).length) (hiR : i < (sorted R).length)
    (hx : IsInitialPart ((sorted L).get ⟨i, hiL⟩) x) :
    diagramMap L R x = appS ((sorted R).get ⟨i, hiR⟩) (shift x ((sorted L).get ⟨i, hiL⟩).length) := by
  unfold diagramMap
  simp only
  rw [find_finRange_eq _ ⟨i, hiL⟩ (by simpa using hx)]
  · simp only [List.getElem?_eq_getElem hiR]
    funext n
    simp [appS, shift]
  · intro j hj
    have hj' : IsInitialPart ((sorted L).get j) x := by simpa using hj
    exact sorted_index_unique (tree_comparable_eq hL (get_mem_sorted L _) (get_mem_sorted L _)
      (isInitialPart_comparable hj' hx))

lemma exists_index_initialPart {L : Finset Seq} (hL : IsTree L) (x : ℕ → Bool) :
    ∃ i : Fin (sorted L).length, IsInitialPart ((sorted L).get i) x := by
  obtain ⟨t, ht, hx⟩ := tree_exists_initialPart hL x
  obtain ⟨i, rfl⟩ := exists_index_of_mem ht
  exact ⟨i, hx⟩

end DiagramMap

section DiagramAct

lemma diagramAct_eq {L R : Finset Seq} (hL : IsTree L) (t : Seq) (i : ℕ)
    (hiL : i < (sorted L).length) (hiR : i < (sorted R).length)
    (ht : (sorted L).get ⟨i, hiL⟩ <+: t) :
    diagramAct L R t = some ((sorted R).get ⟨i, hiR⟩ ++ t.drop ((sorted L).get ⟨i, hiL⟩).length) := by
  unfold diagramAct
  simp only
  rw [find_finRange_eq _ ⟨i, hiL⟩ (by simpa using ht)]
  · simp [List.getElem?_eq_getElem hiR]
  · intro j hj
    have hj' : (sorted L).get j <+: t := by simpa using hj
    exact sorted_index_unique (tree_comparable_eq hL (get_mem_sorted L _) (get_mem_sorted L _)
      (List.prefix_or_prefix_of_prefix hj' ht))

lemma diagramAct_some {L R : Finset Seq} {t t' : Seq} (h : diagramAct L R t = some t') :
    ∃ (i : ℕ) (hiL : i < (sorted L).length) (hiR : i < (sorted R).length),
      (sorted L).get ⟨i, hiL⟩ <+: t ∧
        t' = (sorted R).get ⟨i, hiR⟩ ++ t.drop ((sorted L).get ⟨i, hiL⟩).length := by
  unfold diagramAct at h
  simp only at h
  split at h
  · rename_i j hj
    have hp := List.find?_some hj
    simp only [decide_eq_true_eq] at hp
    rcases hT : (sorted R)[j.1]? with _ | r
    · rw [hT] at h; simp at h
    · rw [hT] at h
      simp only [Option.map_some, Option.some.injEq] at h
      obtain ⟨hjR, hr⟩ := List.getElem?_eq_some_iff.mp hT
      exact ⟨j.1, j.2, hjR, hp, by rw [← h, ← hr]; rfl⟩
  · simp at h

lemma diagramAct_isSome_iff {L R : Finset Seq} (hL : IsTree L) (hcard : L.card = R.card)
    (t : Seq) : (diagramAct L R t).isSome ↔ ∃ s ∈ L, s <+: t := by
  constructor
  · intro h
    obtain ⟨t', ht'⟩ := Option.isSome_iff_exists.mp h
    obtain ⟨i, hiL, _, hp, _⟩ := diagramAct_some ht'
    exact ⟨_, get_mem_sorted L _, hp⟩
  · rintro ⟨s, hs, hst⟩
    obtain ⟨⟨i, hiL⟩, rfl⟩ := exists_index_of_mem hs
    have hiR : i < (sorted R).length := by rw [length_sorted, ← hcard, ← length_sorted]; exact hiL
    rw [diagramAct_eq hL t i hiL hiR hst]; rfl

end DiagramAct

section Five

/-- The reduced diagram of `f`. -/
noncomputable def DD (f : MooreF) : Finset Seq × Finset Seq := (Lf (toMap f), Rf (toMap f))

lemma reduced_DD (f : MooreF) : IsReducedDiagram (Lf (toMap f)) (Rf (toMap f)) :=
  (bijOn_Lf_Rf_and_diagramMul).2.2.2.2.2.1.mapsTo (Set.mem_univ f)

lemma isTree_Lf (f : MooreF) : IsTree (Lf (toMap f)) := (reduced_DD f).1.1
lemma isTree_Rf (f : MooreF) : IsTree (Rf (toMap f)) := (reduced_DD f).1.2.1
lemma card_Lf_Rf (f : MooreF) : (Lf (toMap f)).card = (Rf (toMap f)).card := (reduced_DD f).1.2.2

lemma describes_DD (f : MooreF) : Describes (Lf (toMap f)) (Rf (toMap f)) (toMap f) :=
  (bijOn_Lf_Rf_and_diagramMul).2.2.2.2.2.2.1 f

lemma DD_mul (f g : MooreF) : DD (f * g) = diagramMul (DD f) (DD g) :=
  (bijOn_Lf_Rf_and_diagramMul).2.2.2.2.2.2.2 f g

lemma reduced_DD' (f : MooreF) : IsReducedDiagram (DD f).1 (DD f).2 := reduced_DD f

lemma DD_one : DD 1 = (trivialTree, trivialTree) := by
  obtain ⟨_, hassoc, htriv, hid, hinv, _⟩ := bijOn_Lf_Rf_and_diagramMul
  set E := DD 1
  have hE : IsReducedDiagram E.1 E.2 := reduced_DD' 1
  have h1 : diagramMul E E = E := by rw [← DD_mul, mul_one]
  have hEi := hinv E hE
  have h2 : diagramMul (diagramMul E E) (E.2, E.1) = diagramMul E (diagramMul E (E.2, E.1)) :=
    hassoc E E (E.2, E.1) hE hE hEi.1
  rw [h1, hEi.2.1, (hid E hE).2] at h2
  exact h2.symm

lemma DD_inv (f : MooreF) : DD f⁻¹ = (Rf (toMap f), Lf (toMap f)) := by
  obtain ⟨_, hassoc, htriv, hid, hinv, _⟩ := bijOn_Lf_Rf_and_diagramMul
  set P := DD f
  set Q := DD f⁻¹
  have hP : IsReducedDiagram P.1 P.2 := reduced_DD' f
  have hQ : IsReducedDiagram Q.1 Q.2 := reduced_DD' f⁻¹
  have hPQ : diagramMul P Q = (trivialTree, trivialTree) := by
    rw [← DD_mul, mul_inv_cancel, DD_one]
  have hPi := hinv P hP
  have h := hassoc (P.2, P.1) P Q hPi.1 hP hQ
  rw [hPi.2.2, hPQ, (hid Q hQ).1, (hid _ hPi.1).2] at h
  exact h

lemma Lf_inv (f : MooreF) : Lf (toMap f⁻¹) = Rf (toMap f) := congrArg Prod.fst (DD_inv f)
lemma Rf_inv (f : MooreF) : Rf (toMap f⁻¹) = Lf (toMap f) := congrArg Prod.snd (DD_inv f)
lemma Rf_one : Rf (toMap 1) = trivialTree := congrArg Prod.snd DD_one

end Five

section PartialAction

lemma treeAct_singleton_iff (t t' : Seq) (f : MooreF) :
    treeAct {t} f = some {t'} ↔ seqAct t f = some t' := by
  unfold treeAct
  split_ifs with h
  · have hs : (seqAct t f).isSome := h t (Finset.mem_singleton_self t)
    obtain ⟨t'', ht''⟩ := Option.isSome_iff_exists.mp hs
    have himg : (({t} : Finset Seq).attach.image fun s => (seqAct s.1 f).get (h s.1 s.2)) = {t''} := by
      ext a
      simp only [Finset.mem_image, Finset.mem_attach, true_and, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨s, hs⟩, rfl⟩
        rw [Finset.mem_singleton] at hs; subst hs
        simp [ht'']
      · rintro rfl
        exact ⟨⟨t, Finset.mem_singleton_self t⟩, by simp [ht'']⟩
    rw [himg, ht'']
    simp
  · constructor
    · intro h'; simp at h'
    · intro h'
      exact absurd (fun s hs => by rw [Finset.mem_singleton] at hs; subst hs; simp [h']) h

lemma seqAct_inv_iff (t t' : Seq) (g : MooreF) : seqAct t g = some t' ↔ seqAct t' g⁻¹ = some t := by
  rw [← treeAct_singleton_iff, ← treeAct_singleton_iff]
  exact isTree_treeAct_and_isPartialAction.2.inv g {t} {t'}

lemma seqAct_mul {t t' t'' : Seq} {g h : MooreF} (h1 : seqAct t g = some t')
    (h2 : seqAct t' h = some t'') : seqAct t (g * h) = some t'' := by
  rw [← treeAct_singleton_iff] at h1 h2 ⊢
  exact isTree_treeAct_and_isPartialAction.2.mul g h _ _ _ h1 h2

lemma seqAct_isSome_iff (t : Seq) (f : MooreF) :
    (seqAct t f).isSome ↔ ∃ s ∈ Lf (toMap f), s <+: t :=
  diagramAct_isSome_iff (isTree_Lf f) (card_Lf_Rf f) t

/-- Every extension of an element of `R_f` is in the range of `f`. -/
lemma exists_seqAct_eq_of_Rf {f : MooreF} {r : Seq} (hr : r ∈ Rf (toMap f)) (w : Seq) :
    ∃ a, seqAct a f = some (r ++ w) := by
  obtain ⟨⟨i, hiR⟩, rfl⟩ := exists_index_of_mem hr
  have hiL : i < (sorted (Lf (toMap f))).length := by
    rw [length_sorted, card_Lf_Rf, ← length_sorted]; exact hiR
  refine ⟨(sorted (Lf (toMap f))).get ⟨i, hiL⟩ ++ w, ?_⟩
  unfold seqAct
  rw [diagramAct_eq (isTree_Lf f) _ i hiL hiR (List.prefix_append _ _)]
  simp

end PartialAction

section StrictSort

variable {α : Type*}

theorem pairwise_merge_strict (le : α → α → Bool) (lt : α → α → Prop)
    (hle : ∀ a b, le a b = true ↔ lt a b) (trans : ∀ a b c, lt a b → lt b c → lt a c)
    (tri : ∀ a b, a ≠ b → lt a b ∨ lt b a) :
    ∀ (l₁ l₂ : List α), l₁.Pairwise lt → l₂.Pairwise lt → (∀ a ∈ l₁, ∀ b ∈ l₂, a ≠ b) →
      (List.merge l₁ l₂ le).Pairwise lt := by
  intro l₁
  induction l₁ with
  | nil => intro l₂ _ h₂ _; simpa [List.merge] using h₂
  | cons x l₁ ih₁ =>
    intro l₂
    induction l₂ with
    | nil => intro h₁ _ _; simpa [List.merge] using h₁
    | cons y l₂ ih₂ =>
      intro h₁ h₂ hd
      simp only [List.merge]
      split <;> rename_i h
      · apply List.Pairwise.cons
        · intro z m
          rw [List.mem_merge, List.mem_cons] at m
          rcases m with (m|rfl|m)
          · exact List.rel_of_pairwise_cons h₁ m
          · exact (hle _ _).mp h
          · exact trans _ _ _ ((hle _ _).mp h) (List.rel_of_pairwise_cons h₂ m)
        · exact ih₁ _ h₁.tail h₂ (fun a ha b hb => hd a (List.mem_cons_of_mem _ ha) b hb)
      · have hyx : lt y x := by
          rcases tri x y (hd x List.mem_cons_self y List.mem_cons_self) with h' | h'
          · exact absurd ((hle _ _).mpr h') h
          · exact h'
        apply List.Pairwise.cons
        · intro z m
          rw [List.mem_merge, List.mem_cons] at m
          rcases m with (⟨rfl|m⟩|m)
          · exact hyx
          · exact trans _ _ _ hyx (List.rel_of_pairwise_cons h₁ m)
          · exact List.rel_of_pairwise_cons h₂ m
        · exact ih₂ h₁ h₂.tail (fun a ha b hb => hd a ha b (List.mem_cons_of_mem _ hb))

theorem pairwise_mergeSort_strict (le : α → α → Bool) (lt : α → α → Prop)
    (hle : ∀ a b, le a b = true ↔ lt a b) (trans : ∀ a b c, lt a b → lt b c → lt a c)
    (tri : ∀ a b, a ≠ b → lt a b ∨ lt b a) :
    (l : List α) → l.Nodup → (l.mergeSort le).Pairwise lt
  | [], _ => by simp
  | [a], _ => by simp
  | a :: b :: xs, hnd => by
    rw [List.mergeSort]
    have : (List.MergeSort.Internal.splitInTwo ⟨a :: b :: xs, rfl⟩).1.1.length <
        xs.length + 1 + 1 := by simp [List.MergeSort.Internal.splitInTwo_fst]; omega
    have : (List.MergeSort.Internal.splitInTwo ⟨a :: b :: xs, rfl⟩).2.1.length <
        xs.length + 1 + 1 := by simp [List.MergeSort.Internal.splitInTwo_snd]; omega
    apply pairwise_merge_strict le lt hle trans tri
    · apply pairwise_mergeSort_strict le lt hle trans tri
      simp only [List.MergeSort.Internal.splitInTwo_fst]
      exact hnd.sublist (List.take_sublist _ _)
    · apply pairwise_mergeSort_strict le lt hle trans tri
      simp only [List.MergeSort.Internal.splitInTwo_snd]
      exact hnd.sublist (List.drop_sublist _ _)
    · intro x hx y hy hxy
      subst hxy
      rw [List.mem_mergeSort] at hx hy
      simp only [List.MergeSort.Internal.splitInTwo_fst,
        List.MergeSort.Internal.splitInTwo_snd] at hx hy
      exact List.disjoint_take_drop hnd (le_refl _) hx hy
termination_by l => l.length

end StrictSort

section SortedOrder

lemma lexLt_trans (a b c : Seq) (h1 : LexLt a b) (h2 : LexLt b c) : LexLt a c :=
  show a < c from lt_trans (show a < b from h1) (show b < c from h2)

lemma lexLt_irrefl (a : Seq) : ¬ LexLt a a := lt_irrefl a

lemma lexLt_tri (a b : Seq) (h : a ≠ b) : LexLt a b ∨ LexLt b a := lt_or_gt_of_ne h

lemma sorted_pairwise (T : Finset Seq) : (sorted T).Pairwise LexLt :=
  pairwise_mergeSort_strict _ LexLt (fun _ _ => decide_eq_true_iff) lexLt_trans lexLt_tri _
    (Finset.nodup_toList T)

lemma sorted_eq {T : Finset Seq} {l : List Seq} (hl : l.Pairwise LexLt)
    (hmem : ∀ a, a ∈ l ↔ a ∈ T) : sorted T = l := by
  have hnd : l.Nodup := hl.imp (fun {a b} (h : LexLt a b) (e : a = b) => lexLt_irrefl b (e ▸ h))
  apply List.Perm.eq_of_pairwise (le := LexLt)
    (fun a b _ _ h1 h2 => absurd (lexLt_trans _ _ _ h1 h2) (lexLt_irrefl a))
    (sorted_pairwise T) hl
  exact (List.perm_ext_iff_of_nodup (nodup_sorted T) hnd).mpr (fun a => by rw [mem_sorted, hmem])

end SortedOrder

section Val

/-- The `n`th term of the binary expansion. -/
noncomputable def term (x : ℕ → Bool) (n : ℕ) : ℝ := if x n then (1/2 : ℝ) ^ (n + 1) else 0

lemma term_nonneg (x : ℕ → Bool) (n : ℕ) : 0 ≤ term x n := by
  unfold term; split_ifs <;> positivity

lemma term_le (x : ℕ → Bool) (n : ℕ) : term x n ≤ (1/2 : ℝ) ^ (n + 1) := by
  unfold term; split_ifs <;> [exact le_rfl; positivity]

lemma summable_geom : Summable (fun n : ℕ => (1/2 : ℝ) ^ (n + 1)) := by
  simp_rw [pow_succ]
  exact (summable_geometric_two).mul_right _

lemma tsum_geom : ∑' n : ℕ, (1/2 : ℝ) ^ (n + 1) = 1 := by
  simp_rw [pow_succ]
  rw [tsum_mul_right, tsum_geometric_two]; norm_num

lemma summable_term (x : ℕ → Bool) : Summable (term x) :=
  Summable.of_nonneg_of_le (term_nonneg x) (term_le x) summable_geom

/-- The real number `0.x₀x₁x₂…`. -/
noncomputable def val (x : ℕ → Bool) : ℝ := ∑' n, term x n

lemma val_nonneg (x : ℕ → Bool) : 0 ≤ val x := tsum_nonneg (term_nonneg x)

lemma val_le_one (x : ℕ → Bool) : val x ≤ 1 := by
  rw [← tsum_geom]
  exact Summable.tsum_le_tsum (term_le x) (summable_term x) summable_geom

lemma term_shift (x : ℕ → Bool) (k n : ℕ) :
    term x (n + k) = (1/2 : ℝ) ^ k * term (shift x k) n := by
  unfold term shift
  split_ifs <;> [ring; ring]

lemma val_split (x : ℕ → Bool) (k : ℕ) :
    val x = ∑ n ∈ Finset.range k, term x n + (1/2 : ℝ) ^ k * val (shift x k) := by
  unfold val
  rw [← (summable_term x).sum_add_tsum_nat_add k]
  congr 1
  simp_rw [term_shift x k]
  rw [tsum_mul_left]

lemma sum_term_appS (s : Seq) (y : ℕ → Bool) :
    ∑ n ∈ Finset.range s.length, term (appS s y) n = seqVal s := by
  unfold seqVal
  rw [Finset.sum_range]
  apply Finset.sum_congr rfl
  intro i _
  simp [term, appS, i.2]

lemma val_appS (s : Seq) (y : ℕ → Bool) :
    val (appS s y) = seqVal s + (1/2 : ℝ) ^ s.length * val y := by
  rw [val_split _ s.length, sum_term_appS, shift_appS]

lemma val_of_initialPart {s : Seq} {x : ℕ → Bool} (h : IsInitialPart s x) :
    val x = seqVal s + (1/2 : ℝ) ^ s.length * val (shift x s.length) := by
  conv_lhs => rw [← appS_shift h]
  exact val_appS _ _

lemma val_eq_one {y : ℕ → Bool} (h : val y = 1) (n : ℕ) : y n = true := by
  by_contra hn
  simp only [Bool.not_eq_true] at hn
  have hs : Summable (fun m => (1/2 : ℝ) ^ (m + 1) - term y m) := summable_geom.sub (summable_term y)
  have h1 : ∑' m, ((1/2 : ℝ) ^ (m + 1) - term y m) = 0 := by
    rw [summable_geom.tsum_sub (summable_term y), tsum_geom]; unfold val at h; linarith
  have h2 : (1/2 : ℝ) ^ (n + 1) - term y n ≤ ∑' m, ((1/2 : ℝ) ^ (m + 1) - term y m) :=
    hs.le_tsum n (fun j _ => by linarith [term_le y j])
  have h3 : term y n = 0 := by simp [term, hn]
  rw [h3, h1] at h2
  have : (0 : ℝ) < (1/2) ^ (n + 1) := by positivity
  linarith

lemma val_eq_zero {y : ℕ → Bool} (h : val y = 0) (n : ℕ) : y n = false := by
  by_contra hn
  simp only [Bool.not_eq_false] at hn
  have h2 : term y n ≤ val y := (summable_term y).le_tsum n (fun j _ => term_nonneg y j)
  have h3 : term y n = (1/2 : ℝ) ^ (n + 1) := by simp [term, hn]
  have : (0 : ℝ) < (1/2) ^ (n + 1) := by positivity
  linarith

lemma eq_of_val_eq {a b : ℕ → Bool} (hv : val a = val b) (hne : a ≠ b) :
    ∃ p c, (∀ n, p < n → a n = c) ∧ (∀ n, p < n → b n = !c) := by
  have hex : ∃ n, a n ≠ b n := by
    by_contra h; push Not at h; exact hne (funext h)
  set p := Nat.find hex with hpdef
  have hp : a p ≠ b p := Nat.find_spec hex
  have hlt : ∀ n < p, a n = b n := fun n hn => not_not.mp (Nat.find_min hex hn)
  have hS : ∑ n ∈ Finset.range p, term a n = ∑ n ∈ Finset.range p, term b n :=
    Finset.sum_congr rfl (fun n hn => by unfold term; rw [hlt n (Finset.mem_range.mp hn)])
  have ha := val_split a (p + 1)
  have hb := val_split b (p + 1)
  rw [Finset.sum_range_succ] at ha hb
  have hpos : (0 : ℝ) < (1/2) ^ (p + 1) := by positivity
  have va0 := val_nonneg (shift a (p + 1))
  have va1 := val_le_one (shift a (p + 1))
  have vb0 := val_nonneg (shift b (p + 1))
  have vb1 := val_le_one (shift b (p + 1))
  have hsh : ∀ (x : ℕ → Bool) (n : ℕ), p < n → x n = shift x (p + 1) (n - (p + 1)) := by
    intro x n hn; unfold shift; congr 1; omega
  rcases hap : a p <;> rcases hbp : b p
  · exact absurd (hap.trans hbp.symm) hp
  · -- a p = false, b p = true
    have hta : term a p = 0 := by simp [term, hap]
    have htb : term b p = (1/2) ^ (p + 1) := by simp [term, hbp]
    rw [hta] at ha; rw [htb] at hb
    have e1 : val (shift a (p + 1)) = 1 := by nlinarith
    have e2 : val (shift b (p + 1)) = 0 := by nlinarith
    exact ⟨p, true, fun n hn => by rw [hsh a n hn]; exact val_eq_one e1 _,
      fun n hn => by rw [hsh b n hn]; exact val_eq_zero e2 _⟩
  · have hta : term a p = (1/2) ^ (p + 1) := by simp [term, hap]
    have htb : term b p = 0 := by simp [term, hbp]
    rw [hta] at ha; rw [htb] at hb
    have e1 : val (shift a (p + 1)) = 0 := by nlinarith
    have e2 : val (shift b (p + 1)) = 1 := by nlinarith
    exact ⟨p, false, fun n hn => by rw [hsh a n hn]; exact val_eq_zero e1 _,
      fun n hn => by rw [hsh b n hn]; exact val_eq_one e2 _⟩
  · exact absurd (hap.trans hbp.symm) hp

/-- `0.x₀x₁…` as a point of `[0,1]`. -/
noncomputable def valUI (x : ℕ → Bool) : UI := ⟨val x, val_nonneg x, val_le_one x⟩

lemma describes_val {L R : Finset Seq} {h : UI ≃o UI} (hD : Describes L R h) (x : ℕ → Bool) :
    (h (valUI x) : ℝ) = val (diagramMap L R x) := by
  obtain ⟨⟨i, hiL⟩, hx⟩ := exists_index_initialPart hD.1.1 x
  have hiR : i < (sorted R).length := by
    rw [length_sorted, ← hD.1.2.2, ← length_sorted]; exact hiL
  rw [diagramMap_eq hD.1.1 x i hiL hiR hx, val_appS]
  have hv := val_of_initialPart hx
  set s := (sorted L).get ⟨i, hiL⟩
  set t := (sorted R).get ⟨i, hiR⟩
  have v0 := val_nonneg (shift x s.length)
  have v1 := val_le_one (shift x s.length)
  have hp : (0 : ℝ) < (1/2) ^ s.length := by positivity
  have h1 : seqVal s ≤ (valUI x : ℝ) := by
    show seqVal s ≤ val x
    rw [hv]; nlinarith
  have h2 : (valUI x : ℝ) ≤ seqVal s + (1/2 : ℝ) ^ s.length := by
    show val x ≤ _
    rw [hv]; nlinarith
  rw [hD.2 i hiL hiR (valUI x) h1 h2]
  have e : (valUI x : ℝ) - seqVal s = (1/2 : ℝ) ^ s.length * val (shift x s.length) := by
    show val x - _ = _
    rw [hv]; ring
  rw [e, zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_natCast, zpow_natCast]
  congr 1
  rw [one_div_pow, one_div_pow]
  field_simp
  ring

lemma diagramEquiv_of_describes {L R L' R' : Finset Seq} {h : UI ≃o UI} (hD : Describes L R h)
    (hD' : Describes L' R' h) : DiagramEquiv L R L' R' := by
  intro x
  by_contra hne
  have hv : val (diagramMap L R x) = val (diagramMap L' R' x) := by
    rw [← describes_val hD, ← describes_val hD']
  obtain ⟨p, c, hpa, hpb⟩ := eq_of_val_eq hv hne
  obtain ⟨⟨i, hiL⟩, hx⟩ := exists_index_initialPart hD.1.1 x
  have hiR : i < (sorted R).length := by
    rw [length_sorted, ← hD.1.2.2, ← length_sorted]; exact hiL
  obtain ⟨⟨j, hjL⟩, hx'⟩ := exists_index_initialPart hD'.1.1 x
  have hjR : j < (sorted R').length := by
    rw [length_sorted, ← hD'.1.2.2, ← length_sorted]; exact hjL
  rw [diagramMap_eq hD.1.1 x i hiL hiR hx] at hpa
  rw [diagramMap_eq hD'.1.1 x j hjL hjR hx'] at hpb
  set s := (sorted L).get ⟨i, hiL⟩
  set t := (sorted R).get ⟨i, hiR⟩
  set s' := (sorted L').get ⟨j, hjL⟩
  set t' := (sorted R').get ⟨j, hjR⟩
  set m := p + s.length + s'.length + t.length + t'.length + 1
  have e1 := hpa (m - s.length + t.length) (by omega)
  have e2 := hpb (m - s'.length + t'.length) (by omega)
  simp only [appS, shift] at e1 e2
  rw [dif_neg (by omega)] at e1 e2
  have q1 : m - s.length + t.length - t.length + s.length = m := by omega
  have q2 : m - s'.length + t'.length - t'.length + s'.length = m := by omega
  rw [q1] at e1; rw [q2] at e2
  rw [e1] at e2
  cases c <;> simp at e2

end Val

section Concrete

lemma isInitialPart_nil (x : ℕ → Bool) : IsInitialPart [] x := fun _ h => absurd h (Nat.not_lt_zero _)

lemma isInitialPart_cons_iff (b : Bool) (s : Seq) (x : ℕ → Bool) :
    IsInitialPart (b :: s) x ↔ x 0 = b ∧ IsInitialPart s (shift x 1) := by
  constructor
  · intro h
    refine ⟨(h 0 (by simp)).symm, fun i hi => ?_⟩
    have := h (i + 1) (by simp; omega)
    simpa [shift] using this
  · rintro ⟨h0, h⟩ i hi
    rcases i with _ | i
    · simp [h0]
    · have := h i (by simp at hi; omega)
      simpa [shift] using this

@[simp] lemma seqVal_nil : seqVal [] = 0 := by simp [seqVal]

@[simp] lemma seqVal_cons (b : Bool) (s : Seq) :
    seqVal (b :: s) = (if b then 1/2 else 0) + (1/2) * seqVal s := by
  unfold seqVal
  change (∑ i : Fin (s.length + 1), _) = _
  rw [Fin.sum_univ_succ, Finset.mul_sum]
  congr 1
  · simp
  · apply Finset.sum_congr rfl
    intro i _
    simp only [List.length_cons, Fin.val_succ, List.get_eq_getElem, List.getElem_cons_succ]
    split_ifs <;> ring

lemma bits_00 : bits "00" = [false, false] := rfl
lemma bits_01 : bits "01" = [false, true] := rfl
lemma bits_1 : bits "1" = [true] := rfl
lemma bits_0 : bits "0" = [false] := rfl
lemma bits_10 : bits "10" = [true, false] := rfl
lemma bits_11 : bits "11" = [true, true] := rfl
lemma bits_100 : bits "100" = [true, false, false] := rfl
lemma bits_101 : bits "101" = [true, false, true] := rfl
lemma bits_110 : bits "110" = [true, true, false] := rfl
lemma bits_111 : bits "111" = [true, true, true] := rfl

/-- A tree given by an explicit list of leaves, checked digit by digit. -/
lemma isTree_of_check (T : Finset Seq)
    (h : ∀ x : ℕ → Bool, ∃ t ∈ T, IsInitialPart t x ∧ ∀ t' ∈ T, IsInitialPart t' x → t' = t) :
    IsTree T := fun x => by
  obtain ⟨t, ht, hx, hu⟩ := h x
  exact ⟨t, ⟨ht, hx⟩, fun t' ⟨h1, h2⟩ => hu t' h1 h2⟩

noncomputable def x0L : Finset Seq := {bits "00", bits "01", bits "1"}
noncomputable def x0R : Finset Seq := {bits "0", bits "10", bits "11"}
noncomputable def x1L : Finset Seq := {bits "0", bits "100", bits "101", bits "11"}
noncomputable def x1R : Finset Seq := {bits "0", bits "10", bits "110", bits "111"}

lemma isTree_x0L : IsTree x0L := by
  apply isTree_of_check
  intro x
  simp only [x0L, bits_00, bits_01, bits_1, Finset.mem_insert, Finset.mem_singleton,
    forall_eq_or_imp, forall_eq, exists_eq_or_imp, exists_eq_left,
    isInitialPart_cons_iff, isInitialPart_nil, shift]
  rcases x 0 <;> rcases x 1 <;> simp

lemma isTree_x0R : IsTree x0R := by
  apply isTree_of_check
  intro x
  simp only [x0R, bits_0, bits_10, bits_11, Finset.mem_insert, Finset.mem_singleton,
    forall_eq_or_imp, forall_eq, exists_eq_or_imp, exists_eq_left,
    isInitialPart_cons_iff, isInitialPart_nil, shift]
  rcases x 0 <;> rcases x 1 <;> simp

lemma isTree_x1L : IsTree x1L := by
  apply isTree_of_check
  intro x
  simp only [x1L, bits_0, bits_100, bits_101, bits_11, Finset.mem_insert, Finset.mem_singleton,
    forall_eq_or_imp, forall_eq, exists_eq_or_imp, exists_eq_left,
    isInitialPart_cons_iff, isInitialPart_nil, shift]
  rcases x 0 <;> rcases x 1 <;> rcases x 2 <;> simp

lemma isTree_x1R : IsTree x1R := by
  apply isTree_of_check
  intro x
  simp only [x1R, bits_0, bits_10, bits_110, bits_111, Finset.mem_insert, Finset.mem_singleton,
    forall_eq_or_imp, forall_eq, exists_eq_or_imp, exists_eq_left,
    isInitialPart_cons_iff, isInitialPart_nil, shift]
  rcases x 0 <;> rcases x 1 <;> rcases x 2 <;> simp

lemma sorted_x0L : sorted x0L = [[false, false], [false, true], [true]] := by
  apply sorted_eq
  · show List.Pairwise (· < ·) _; decide
  · intro a; simp [x0L, bits_00, bits_01, bits_1]

lemma sorted_x0R : sorted x0R = [[false], [true, false], [true, true]] := by
  apply sorted_eq
  · show List.Pairwise (· < ·) _; decide
  · intro a; simp [x0R, bits_0, bits_10, bits_11]

lemma sorted_x1L : sorted x1L = [[false], [true, false, false], [true, false, true], [true, true]] := by
  apply sorted_eq
  · show List.Pairwise (· < ·) _; decide
  · intro a; simp [x1L, bits_0, bits_100, bits_101, bits_11]

lemma sorted_x1R : sorted x1R = [[false], [true, false], [true, true, false], [true, true, true]] := by
  apply sorted_eq
  · show List.Pairwise (· < ·) _; decide
  · intro a; simp [x1R, bits_0, bits_10, bits_110, bits_111]

lemma card_x0L : x0L.card = 3 := by rw [← length_sorted, sorted_x0L]; rfl
lemma card_x0R : x0R.card = 3 := by rw [← length_sorted, sorted_x0R]; rfl
lemma card_x1L : x1L.card = 4 := by rw [← length_sorted, sorted_x1L]; rfl
lemma card_x1R : x1R.card = 4 := by rw [← length_sorted, sorted_x1R]; rfl

lemma treeDiagram_x0 : IsTreeDiagram x0L x0R :=
  ⟨isTree_x0L, isTree_x0R, by rw [card_x0L, card_x0R]⟩
lemma treeDiagram_x1 : IsTreeDiagram x1L x1R :=
  ⟨isTree_x1L, isTree_x1R, by rw [card_x1L, card_x1R]⟩

end Concrete

section GMap

/-! ### The element `g_u`: `x₀` acting inside the dyadic interval of `u` -/

noncomputable def g4 (a l : ℝ) : ℝ → ℝ := fun y => if y ≤ a + l then (y + a + l) / 2 else y
noncomputable def g3 (a l : ℝ) : ℝ → ℝ := fun y => if y ≤ a + l / 2 then y + l / 4 else g4 a l y
noncomputable def g2 (a l : ℝ) : ℝ → ℝ := fun y => if y ≤ a + l / 4 then 2 * y - a else g3 a l y
noncomputable def gFun (a l : ℝ) : ℝ → ℝ := fun y => if y ≤ a then y else g2 a l y

lemma strictMono_gFun {a l : ℝ} (hl : 0 < l) : StrictMono (gFun a l) := by
  have h4 : StrictMono (g4 a l) :=
    strictMono_glue (c := a + l) (fun x _ y _ h => by linarith) (fun x _ y _ h => h)
      (by ring)
  have h3 : StrictMono (g3 a l) :=
    strictMono_glue (c := a + l / 2) (fun x _ y _ h => by linarith) (fun x _ y _ h => h4 h)
      (by unfold g4; rw [if_pos (by linarith)]; ring)
  have h2 : StrictMono (g2 a l) :=
    strictMono_glue (c := a + l / 4) (fun x _ y _ h => by linarith) (fun x _ y _ h => h3 h)
      (by unfold g3; rw [if_pos (by linarith)]; ring)
  exact strictMono_glue (c := a) (fun x _ y _ h => h) (fun x _ y _ h => h2 h)
    (by unfold g2; rw [if_pos (by linarith)]; ring)

noncomputable def gInv (a l : ℝ) : ℝ → ℝ := fun z =>
  if z ≤ a then z
  else if z ≤ a + l / 2 then (z + a) / 2
  else if z ≤ a + 3 * l / 4 then z - l / 4
  else if z ≤ a + l then 2 * z - a - l
  else z

lemma gFun_gInv {a l : ℝ} (hl : 0 < l) (z : ℝ) : gFun a l (gInv a l z) = z := by
  unfold gFun g2 g3 g4 gInv
  split_ifs <;> linarith

lemma gFun_of_le {a l y : ℝ} (_hl : 0 < l) (h : y ≤ a) : gFun a l y = y := by
  unfold gFun; rw [if_pos h]

lemma gFun_of_mem1 {a l y : ℝ} (_hl : 0 < l) (h0 : a ≤ y) (h1 : y ≤ a + l / 4) :
    gFun a l y = 2 * y - a := by
  unfold gFun g2 g3 g4; split_ifs <;> linarith

lemma gFun_of_mem2 {a l y : ℝ} (hl : 0 < l) (h0 : a + l / 4 ≤ y) (h1 : y ≤ a + l / 2) :
    gFun a l y = y + l / 4 := by
  unfold gFun g2 g3 g4; split_ifs <;> linarith

lemma gFun_of_mem3 {a l y : ℝ} (hl : 0 < l) (h0 : a + l / 2 ≤ y) (h1 : y ≤ a + l) :
    gFun a l y = (y + a + l) / 2 := by
  unfold gFun g2 g3 g4; split_ifs <;> linarith

lemma gFun_of_ge {a l y : ℝ} (hl : 0 < l) (h : a + l ≤ y) : gFun a l y = y := by
  unfold gFun g2 g3 g4; split_ifs <;> linarith

noncomputable def lineG (a l : ℝ) (hl : 0 < l) : ℝ ≃o ℝ :=
  StrictMono.orderIsoOfSurjective (gFun a l) (strictMono_gFun hl) (fun z => ⟨gInv a l z, gFun_gInv hl z⟩)

/-- `g` as an order isomorphism of `[0,1]`. -/
noncomputable def gUI (a l : ℝ) (hl : 0 < l) (ha : 0 ≤ a) (hal : a + l ≤ 1) : UI ≃o UI :=
  CannonFloydParry.restrict (lineG a l hl) (fun x hx => gFun_of_le hl (by linarith))
    (fun x hx => gFun_of_ge hl (by linarith))

lemma gUI_apply {a l : ℝ} (hl : 0 < l) (ha : 0 ≤ a) (hal : a + l ≤ 1) (z : UI) :
    (gUI a l hl ha hal z : ℝ) = gFun a l z := rfl

lemma isDyadic_add {x y : ℝ} (hx : IsDyadic x) (hy : IsDyadic y) : IsDyadic (x + y) := by
  obtain ⟨m, k, rfl⟩ := hx
  obtain ⟨m', k', rfl⟩ := hy
  refine ⟨m * 2 ^ k' + m' * 2 ^ k, k + k', ?_⟩
  push_cast
  field_simp
  ring

lemma isDyadic_half_pow (n : ℕ) : IsDyadic ((1/2 : ℝ) ^ n) :=
  ⟨1, n, by rw [one_div_pow]; push_cast; ring⟩

lemma isDyadic_seqVal (u : Seq) : IsDyadic (seqVal u) := by
  induction u with
  | nil => exact ⟨0, 0, by simp⟩
  | cons b s ih =>
    rw [seqVal_cons]
    obtain ⟨m, k, hm⟩ := ih
    refine isDyadic_add ?_ ⟨m, k + 1, by rw [hm, pow_succ]; field_simp⟩
    split_ifs
    · exact ⟨1, 1, by norm_num⟩
    · exact ⟨0, 0, by norm_num⟩

lemma isThompson_gUI {a l : ℝ} (hl : 0 < l) (ha : 0 ≤ a) (hal : a + l ≤ 1)
    (hda : IsDyadic a) (hdl : ∀ n : ℕ, IsDyadic (l / 2 ^ n)) : IsThompson (gUI a l hl ha hal) := by
  refine ⟨{a, a + l / 4, a + l / 2, a + l}, ?_, ?_⟩
  · intro b hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hda
    · exact isDyadic_add hda (by have := hdl 2; norm_num at this; exact this)
    · exact isDyadic_add hda (by have := hdl 1; norm_num at this; exact this)
    · exact isDyadic_add hda (by have := hdl 0; norm_num at this; exact this)
  · intro x y hxy hB
    have hnot : ∀ b ∈ ({a, a + l / 4, a + l / 2, a + l} : Finset ℝ), b ≤ (x : ℝ) ∨ (y : ℝ) ≤ b := by
      intro b hb
      by_contra h
      push Not at h
      have : b ∈ Set.Ioo (x : ℝ) (y : ℝ) ∩ (({a, a + l / 4, a + l / 2, a + l} : Finset ℝ) : Set ℝ) :=
        ⟨⟨h.1, h.2⟩, hb⟩
      rw [hB] at this; exact this
    have b1 := hnot a (by simp)
    have b2 := hnot (a + l / 4) (by simp)
    have b3 := hnot (a + l / 2) (by simp)
    have b4 := hnot (a + l) (by simp)
    simp only [gUI_apply]
    rcases b1 with b1 | b1
    · rcases b2 with b2 | b2
      · rcases b3 with b3 | b3
        · rcases b4 with b4 | b4
          · exact ⟨0, 0, fun z hz => by rw [gFun_of_ge hl (by linarith [hz.1])]; simp⟩
          · exact ⟨-1, (a + l) / 2, fun z hz => by
              rw [gFun_of_mem3 hl (by linarith [hz.1]) (by linarith [hz.2])]
              rw [zpow_neg, zpow_one]; ring⟩
        · exact ⟨0, l / 4, fun z hz => by
            rw [gFun_of_mem2 hl (by linarith [hz.1]) (by linarith [hz.2])]; simp⟩
      · exact ⟨1, -a, fun z hz => by
          rw [gFun_of_mem1 hl (by linarith [hz.1]) (by linarith [hz.2])]; simp; ring⟩
    · exact ⟨0, 0, fun z hz => by rw [gFun_of_le hl (by linarith [hz.2])]; simp⟩

lemma seqVal_add_le_one (u : Seq) : seqVal u + (1/2 : ℝ) ^ u.length ≤ 1 := by
  have h := val_appS u (fun _ => true)
  have h1 : val (fun _ => true) = 1 := by unfold val term; simp only [if_true]; exact tsum_geom
  rw [h1, mul_one] at h
  rw [← h]; exact val_le_one _

lemma seqVal_nonneg (u : Seq) : 0 ≤ seqVal u := by
  have h := val_appS u (fun _ => false)
  have h1 : val (fun _ => false) = 0 := by unfold val term; simp
  rw [h1, mul_zero, add_zero] at h
  rw [← h]; exact val_nonneg _

/-- `g_u`: the identity off the dyadic interval of `u`, and a copy of `x₀` on it. -/
noncomputable def gU (u : Seq) : MooreF :=
  MulOpposite.op ⟨gUI (seqVal u) ((1/2 : ℝ) ^ u.length) (by positivity) (seqVal_nonneg u)
    (seqVal_add_le_one u),
    mem_F_of_isThompson (isThompson_gUI _ _ _ (isDyadic_seqVal u) (fun n => by
      have : (1/2 : ℝ) ^ u.length / 2 ^ n = (1/2) ^ (u.length + n) := by
        rw [pow_add, one_div_pow (2:ℝ) n, mul_one_div]
      rw [this]; exact isDyadic_half_pow _))⟩

lemma toMap_gU_apply (u : Seq) (z : UI) :
    (toMap (gU u) z : ℝ) = gFun (seqVal u) ((1/2 : ℝ) ^ u.length) z := rfl

end GMap

section Concrete2

lemma toMap_gU_nil (z : UI) : (toMap (gU []) z : ℝ) = gFun 0 1 z := by
  rw [toMap_gU_apply]; simp

lemma toMap_gU_one (z : UI) : (toMap (gU [true]) z : ℝ) = gFun (1/2) (1/2) z := by
  rw [toMap_gU_apply]; simp

/-- `x₀`'s diagram describes `g_⟨⟩`. -/
lemma describes_x0_gU : Describes x0L x0R (toMap (gU [])) := by
  refine ⟨treeDiagram_x0, ?_⟩
  rw [sorted_x0L, sorted_x0R]
  intro i hL hR x h1 h2
  have hx0 := x.2.1
  have hx1 := x.2.2
  rw [toMap_gU_nil]
  rcases i with _ | _ | _ | i
  · simp [seqVal_cons] at h1 h2 ⊢
    norm_num at h1 h2 ⊢
    rw [gFun_of_mem1 one_pos (by linarith) (by linarith)]; ring
  · simp [seqVal_cons] at h1 h2 ⊢
    norm_num at h1 h2 ⊢
    rw [gFun_of_mem2 one_pos (by linarith) (by linarith)]; ring
  · simp [seqVal_cons] at h1 h2 ⊢
    norm_num at h1 h2 ⊢
    rw [gFun_of_mem3 one_pos (by linarith) (by linarith)]; ring
  · exfalso; simp at hL; omega

/-- `x₁`'s diagram describes `g_⟨1⟩`. -/
lemma describes_x1_gU : Describes x1L x1R (toMap (gU [true])) := by
  refine ⟨treeDiagram_x1, ?_⟩
  rw [sorted_x1L, sorted_x1R]
  intro i hL hR x h1 h2
  have hx0 := x.2.1
  have hx1 := x.2.2
  rw [toMap_gU_one]
  have hl : (0 : ℝ) < 1/2 := by norm_num
  rcases i with _ | _ | _ | _ | i
  · simp [seqVal_cons] at h1 h2 ⊢
    norm_num at h1 h2 ⊢
    rw [gFun_of_le hl (by linarith)]
  · simp [seqVal_cons] at h1 h2 ⊢
    norm_num at h1 h2 ⊢
    rw [gFun_of_mem1 hl (by linarith) (by linarith)]; ring
  · simp [seqVal_cons] at h1 h2 ⊢
    norm_num at h1 h2 ⊢
    rw [gFun_of_mem2 hl (by linarith) (by linarith)]; ring
  · simp [seqVal_cons] at h1 h2 ⊢
    norm_num at h1 h2 ⊢
    rw [gFun_of_mem3 hl (by linarith) (by linarith)]; ring
  · exfalso; simp at hL; omega

lemma describes_toMap_ofDiagram {L R : Finset Seq} (h : ∃ f : F, Describes L R (f : UI ≃o UI)) :
    Describes L R (toMap (ofDiagram L R)) :=
  Classical.epsilon_spec (p := fun f : F => Describes L R (f : UI ≃o UI)) h

lemma describes_toMap_x0 : Describes x0L x0R (toMap x0) :=
  describes_toMap_ofDiagram ⟨MulOpposite.unop (gU []), describes_x0_gU⟩

lemma describes_toMap_x1 : Describes x1L x1R (toMap x1) :=
  describes_toMap_ofDiagram ⟨MulOpposite.unop (gU [true]), describes_x1_gU⟩

lemma reduced_x0 : IsReducedDiagram x0L x0R := by
  rw [isReducedDiagram_iff x0L x0R treeDiagram_x0]
  rintro ⟨i, hi, hi', h1, h2, h3, h4⟩
  have hl : (sorted x0L).length = 3 := by rw [sorted_x0L]; rfl
  rcases i with _ | _ | i
  · simp [sorted_x0R] at h4
  · simp [sorted_x0L] at h1
  · omega

lemma reduced_x1 : IsReducedDiagram x1L x1R := by
  rw [isReducedDiagram_iff x1L x1R treeDiagram_x1]
  rintro ⟨i, hi, hi', h1, h2, h3, h4⟩
  have hl : (sorted x1L).length = 4 := by rw [sorted_x1L]; rfl
  rcases i with _ | _ | _ | i
  · simp [sorted_x1L] at h3
  · simp [sorted_x1R] at h4
  · simp [sorted_x1L] at h1
  · omega

lemma DD_x0 : DD x0 = (x0L, x0R) :=
  ((existsUnique_isReducedDiagram_diagramEquiv x0L x0R treeDiagram_x0).unique
    ⟨reduced_DD x0, diagramEquiv_of_describes describes_toMap_x0 (describes_DD x0)⟩
    ⟨reduced_x0, fun _ => rfl⟩)

lemma DD_x1 : DD x1 = (x1L, x1R) :=
  ((existsUnique_isReducedDiagram_diagramEquiv x1L x1R treeDiagram_x1).unique
    ⟨reduced_DD x1, diagramEquiv_of_describes describes_toMap_x1 (describes_DD x1)⟩
    ⟨reduced_x1, fun _ => rfl⟩)

lemma Lf_x0 : Lf (toMap x0) = x0L := congrArg Prod.fst DD_x0
lemma Rf_x0 : Rf (toMap x0) = x0R := congrArg Prod.snd DD_x0
lemma Lf_x1 : Lf (toMap x1) = x1L := congrArg Prod.fst DD_x1
lemma Rf_x1 : Rf (toMap x1) = x1R := congrArg Prod.snd DD_x1

/-- `Γ` generates `F`, from the milestone that `x₀` and `x₁` do. -/
lemma closure_gens : Subgroup.closure (gens : Set MooreF) = ⊤ := by
  rw [eq_top_iff, ← closure_x0_x1_eq_top]
  apply Subgroup.closure_mono
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl <;> simp [gens]

lemma gens_symm : ∀ γ ∈ gens, γ⁻¹ ∈ gens := by
  intro γ hγ
  simp only [gens, Finset.mem_insert, Finset.mem_singleton] at hγ ⊢
  rcases hγ with rfl | rfl | rfl | rfl <;> simp

end Concrete2

section WordLength

lemma prefix_antisymm {a b : Seq} (h1 : a <+: b) (h2 : b <+: a) : a = b :=
  h1.eq_of_length (le_antisymm h1.length_le h2.length_le)

/-- Claim C: a tree all of whose elements extend elements of the tree `L` has at least as many
elements as `L`. -/
lemma card_le_of_extends {L A : Finset Seq} (hL : IsTree L) (hA : IsTree A)
    (h : ∀ a ∈ A, ∃ ℓ ∈ L, ℓ <+: a) : L.card ≤ A.card := by
  have hex : ∀ ℓ ∈ L, ∃ a ∈ A, ℓ <+: a := by
    intro ℓ hℓ
    obtain ⟨a, ha, hx⟩ := tree_exists_initialPart hA (appS ℓ fun _ => false)
    refine ⟨a, ha, ?_⟩
    rcases isInitialPart_comparable hx (isInitialPart_appS ℓ _) with h1 | h1
    · obtain ⟨ℓ', hℓ', h2⟩ := h a ha
      have := tree_prefix_eq hL hℓ' hℓ (h2.trans h1)
      subst this; exact h2
    · exact h1
  choose! g hg using hex
  refine Finset.card_le_card_of_injOn g (fun ℓ hℓ => (hg ℓ hℓ).1) ?_
  intro ℓ₁ h₁ ℓ₂ h₂ heq
  have p1 := (hg ℓ₁ h₁).2
  have p2 := (hg ℓ₂ h₂).2
  rw [heq] at p1
  exact tree_comparable_eq hL h₁ h₂ (List.prefix_or_prefix_of_prefix p1 p2)

lemma exists_join {R L : Finset Seq} (hR : IsTree R) (hL : IsTree L) :
    ∃ J : Finset Seq, IsTree J ∧ J.card + 1 ≤ R.card + L.card ∧
      ∀ j ∈ J, (∃ r ∈ R, r <+: j) ∧ (∃ ℓ ∈ L, ℓ <+: j) := by
  set J := R.filter (fun r => ∃ ℓ ∈ L, ℓ <+: r) ∪ L.filter (fun ℓ => ∃ r ∈ R, r <+: ℓ) with hJ
  refine ⟨J, ?_, ?_, ?_⟩
  · -- `J` is a tree
    intro x
    obtain ⟨r, hr, hxr⟩ := tree_exists_initialPart hR x
    obtain ⟨ℓ, hℓ, hxℓ⟩ := tree_exists_initialPart hL x
    have hRu : ∀ t ∈ R, IsInitialPart t x → t = r := fun t ht hx =>
      tree_comparable_eq hR ht hr (isInitialPart_comparable hx hxr)
    have hLu : ∀ t ∈ L, IsInitialPart t x → t = ℓ := fun t ht hx =>
      tree_comparable_eq hL ht hℓ (isInitialPart_comparable hx hxℓ)
    by_cases hlr : ℓ <+: r
    · refine ⟨r, ⟨Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hr, ℓ, hℓ, hlr⟩), hxr⟩, ?_⟩
      rintro t ⟨ht, hxt⟩
      rcases Finset.mem_union.mp ht with ht | ht
      · exact hRu t (Finset.mem_filter.mp ht).1 hxt
      · obtain ⟨htL, r', hr', hr't⟩ := Finset.mem_filter.mp ht
        have e1 := hLu t htL hxt
        subst e1
        have e2 := hRu r' hr' (isInitialPart_of_prefix hr't hxt)
        subst e2
        exact prefix_antisymm hr't hlr |>.symm
    · have hrl : r <+: ℓ := by
        rcases isInitialPart_comparable hxr hxℓ with h | h
        · exact h
        · exact absurd h hlr
      refine ⟨ℓ, ⟨Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hℓ, r, hr, hrl⟩), hxℓ⟩, ?_⟩
      rintro t ⟨ht, hxt⟩
      rcases Finset.mem_union.mp ht with ht | ht
      · obtain ⟨htR, ℓ', hℓ', hℓ't⟩ := Finset.mem_filter.mp ht
        have e1 := hRu t htR hxt
        subst e1
        have e2 := hLu ℓ' hℓ' (isInitialPart_of_prefix hℓ't hxt)
        subst e2
        exact absurd hℓ't hlr
      · exact hLu t (Finset.mem_filter.mp ht).1 hxt
  · -- the count
    set P := R.filter (fun r => ∃ ℓ ∈ L, r <+: ℓ ∧ r ≠ ℓ) with hP
    set L' := L.filter (fun ℓ => ∃ r ∈ P, r <+: ℓ) with hL'
    have hsub : J ⊆ (R \ P) ∪ L' := by
      intro j hj
      rcases Finset.mem_union.mp hj with hj | hj
      · obtain ⟨hjR, ℓ, hℓ, hℓj⟩ := Finset.mem_filter.mp hj
        refine Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hjR, fun hjP => ?_⟩)
        obtain ⟨_, ℓ', hℓ', hjℓ', hne⟩ := Finset.mem_filter.mp hjP
        have e := tree_prefix_eq hL hℓ hℓ' (hℓj.trans hjℓ')
        subst e
        exact hne (prefix_antisymm hjℓ' hℓj)
      · obtain ⟨hjL, r, hr, hrj⟩ := Finset.mem_filter.mp hj
        by_cases hrj' : r = j
        · subst hrj'
          refine Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hr, fun hjP => ?_⟩)
          obtain ⟨_, ℓ', hℓ', hjℓ', hne⟩ := Finset.mem_filter.mp hjP
          exact hne (tree_prefix_eq hL hjL hℓ' hjℓ')
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr
            ⟨hjL, r, Finset.mem_filter.mpr ⟨hr, j, hjL, hrj, hrj'⟩, hrj⟩)
    have h1 : J.card ≤ (R \ P).card + L'.card :=
      (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have h2 : (R \ P).card + P.card = R.card :=
      Finset.card_sdiff_add_card_eq_card (Finset.filter_subset _ _)
    have h3 : L'.card ≤ L.card := Finset.card_le_card (Finset.filter_subset _ _)
    have hLne : 0 < L.card := Finset.card_pos.mpr (tree_nonempty hL)
    by_cases hPe : P = ∅
    · have : L' = ∅ := by
        rw [hL', Finset.filter_eq_empty_iff]
        rintro ℓ - ⟨r, hr, -⟩
        rw [hPe] at hr; simp at hr
      have hL'0 : L'.card = 0 := by rw [this]; rfl
      have hP0 : P.card = 0 := by rw [hPe]; rfl
      omega
    · have : 0 < P.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hPe)
      omega
  · intro j hj
    rcases Finset.mem_union.mp hj with hj | hj
    · obtain ⟨hjR, h⟩ := Finset.mem_filter.mp hj
      exact ⟨⟨j, hjR, List.prefix_refl j⟩, h⟩
    · obtain ⟨hjL, h⟩ := Finset.mem_filter.mp hj
      exact ⟨h, ⟨j, hjL, List.prefix_refl j⟩⟩

lemma treeAct_eq_of_isSome (T : Finset Seq) (f : MooreF) (h : ∀ t ∈ T, (seqAct t f).isSome) :
    treeAct T f = some (T.attach.image fun t => (seqAct t.1 f).get (h t.1 t.2)) := by
  unfold treeAct; rw [dif_pos h]

lemma mem_image_seqAct {T : Finset Seq} {f : MooreF} {h : ∀ t ∈ T, (seqAct t f).isSome} {a : Seq}
    (ha : a ∈ T.attach.image fun t => (seqAct t.1 f).get (h t.1 t.2)) :
    ∃ t ∈ T, seqAct t f = some a := by
  obtain ⟨⟨t, ht⟩, -, rfl⟩ := Finset.mem_image.mp ha
  exact ⟨t, ht, by simp⟩

lemma card_Rf_mul_le (f γ : MooreF) :
    (Rf (toMap (f * γ))).card + 1 ≤ (Rf (toMap f)).card + (Lf (toMap γ)).card := by
  obtain ⟨J, hJ, hJcard, hJmem⟩ := exists_join (isTree_Rf f) (isTree_Lf γ)
  have hdom : ∀ j ∈ J, (seqAct j f⁻¹).isSome := by
    intro j hj
    obtain ⟨⟨r, hr, w, rfl⟩, -⟩ := hJmem j hj
    obtain ⟨a, ha⟩ := exists_seqAct_eq_of_Rf hr w
    rw [seqAct_inv_iff] at ha
    rw [ha]; rfl
  set A := J.attach.image fun t => (seqAct t.1 f⁻¹).get (hdom t.1 t.2)
  have hA : treeAct J f⁻¹ = some A := treeAct_eq_of_isSome J f⁻¹ hdom
  have hAtree : IsTree A := isTree_treeAct_and_isPartialAction.1 J A f⁻¹ hJ hA
  have hAcard : A.card ≤ J.card := Finset.card_image_le.trans (Finset.card_attach).le
  have hAdom : ∀ a ∈ A, ∃ ℓ ∈ Lf (toMap (f * γ)), ℓ <+: a := by
    intro a ha
    obtain ⟨t, ht, hta⟩ := mem_image_seqAct ha
    rw [seqAct_inv_iff, inv_inv] at hta
    obtain ⟨-, ℓ, hℓ, hℓt⟩ := hJmem t ht
    have hs : (seqAct t γ).isSome := (seqAct_isSome_iff t γ).mpr ⟨ℓ, hℓ, hℓt⟩
    obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp hs
    have := seqAct_mul hta hk
    exact (seqAct_isSome_iff a (f * γ)).mp (by rw [this]; rfl)
  have := card_le_of_extends (isTree_Lf (f * γ)) hAtree hAdom
  rw [← card_Lf_Rf]
  omega

lemma card_Lf_gens_le (γ : MooreF) (hγ : γ ∈ gens) : (Lf (toMap γ)).card ≤ 4 := by
  simp only [gens, Finset.mem_insert, Finset.mem_singleton] at hγ
  rcases hγ with rfl | rfl | rfl | rfl
  · rw [Lf_x0, card_x0L]; norm_num
  · rw [Lf_x1, card_x1L]
  · rw [Lf_inv, Rf_x0, card_x0R]; norm_num
  · rw [Lf_inv, Rf_x1, card_x1R]

lemma card_Rf_gens_mul_le (γ f : MooreF) (hγ : γ ∈ gens) :
    (Rf (toMap (γ * f))).card ≤ (Rf (toMap f)).card + 3 := by
  have h1 := card_Rf_mul_le f⁻¹ γ⁻¹
  have h2 := card_Lf_gens_le γ⁻¹ (gens_symm γ hγ)
  rw [← mul_inv_rev, Rf_inv, Rf_inv, card_Lf_Rf, card_Lf_Rf] at h1
  omega

lemma card_Rf_prod_le (w : List MooreF) (hw : ∀ γ ∈ w, γ ∈ gens) :
    (Rf (toMap w.prod)).card ≤ 1 + 3 * w.length := by
  induction w with
  | nil => simp [Rf_one, trivialTree]
  | cons γ w ih =>
    rw [List.prod_cons, List.length_cons]
    have := card_Rf_gens_mul_le γ w.prod (hw γ (by simp))
    have := ih (fun g hg => hw g (by simp [hg]))
    omega

lemma exists_word (f : MooreF) :
    ∃ w : List MooreF, w.length = wordLength gens f ∧ (∀ γ ∈ w, γ ∈ gens) ∧ w.prod = f := by
  have hmem : f ∈ (Subgroup.closure (gens : Set MooreF)).toSubmonoid := by
    rw [closure_gens]; exact Subgroup.mem_top f
  rw [Subgroup.closure_toSubmonoid] at hmem
  obtain ⟨l, hl, hprod⟩ := Submonoid.exists_list_of_mem_closure hmem
  have hne : {n | ∃ w : List MooreF, w.length = n ∧ (∀ γ ∈ w, γ ∈ gens) ∧ w.prod = f}.Nonempty := by
    refine ⟨l.length, l, rfl, fun γ hγ => ?_, hprod⟩
    rcases hl γ hγ with h | h
    · exact h
    · have := gens_symm _ (Set.mem_inv.mp h); rwa [inv_inv] at this
  exact Nat.sInf_mem hne

end WordLength

section LocalX0

end LocalX0

section Lemma41


end Lemma41

section Lemma42


end Lemma42

end MooreFoelner.Dev.GenTrees

namespace MooreFoelner

open Classical CannonFloydParry

end MooreFoelner
end

open MooreFoelner in
open Classical MooreFoelner CannonFloydParry in
open scoped symmDiff in
open Classical CannonFloydParry in
theorem solution (f : MooreF) :
    ((Rf (toMap f)).card : ℝ) - 2 ≤ 3 * wordLength gens f := by
  obtain ⟨w, hlen, hw, rfl⟩ := Dev.GenTrees.exists_word f
  have := Dev.GenTrees.card_Rf_prod_le w hw
  rw [← hlen]
  have : ((Rf (toMap w.prod)).card : ℝ) ≤ 1 + 3 * w.length := by exact_mod_cast this
  linarith
