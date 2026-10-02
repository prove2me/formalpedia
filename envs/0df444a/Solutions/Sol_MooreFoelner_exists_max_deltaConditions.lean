-- Prove2me | solution 1 for MooreFoelner.exists_max_deltaConditions
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-02T07:38:25.262372+00:00
-- url     : https://prove2.me/submissions/b95363c1-89ef-49c5-871b-58ae7899b093

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
# Moore §5: the operation `∂` (Lemmas 5.2, 5.4, 5.5)
-/

namespace MooreFoelner.Dev.Delta

open Classical CannonFloydParry MooreFoelner

/-! ## Prefixes and initial parts -/

/-- The infinite sequence extending `u` by zeros. -/
def ext (u : Seq) : ℕ → Bool := fun n => if h : n < u.length then u[n] else false

theorem ip_ext (u : Seq) : IsInitialPart u (ext u) := by
  intro i h
  simp [ext, h]

theorem ip_of_prefix {u v : Seq} {x : ℕ → Bool} (hv : IsInitialPart v x) (h : u <+: v) :
    IsInitialPart u x := by
  intro i hi
  have hl := h.length_le
  have := hv i (by omega)
  simp only [List.get_eq_getElem] at this ⊢
  rw [← this, h.getElem hi]

theorem ip_comparable {u v : Seq} {x : ℕ → Bool} (hu : IsInitialPart u x)
    (hv : IsInitialPart v x) : u <+: v ∨ v <+: u := by
  have key : ∀ {u v : Seq}, IsInitialPart u x → IsInitialPart v x → u.length ≤ v.length →
      u <+: v := by
    intro u v hu hv hle
    rw [List.prefix_iff_eq_take]
    apply List.ext_getElem (by simp; omega)
    intro i h1 h2
    have e1 := hu i h1
    have e2 := hv i (by omega)
    simp only [List.get_eq_getElem] at e1 e2
    rw [List.getElem_take, e1, e2]
  rcases le_total u.length v.length with h | h
  · exact Or.inl (key hu hv h)
  · exact Or.inr (key hv hu h)

/-! ## Trees -/

theorem tr_ip {T : Finset Seq} (hT : IsTree T) (x : ℕ → Bool) :
    ∃ t ∈ T, IsInitialPart t x := by
  obtain ⟨t, ⟨ht, hx⟩, -⟩ := hT x
  exact ⟨t, ht, hx⟩

theorem tr_unique {T : Finset Seq} (hT : IsTree T) {x : ℕ → Bool} {t t' : Seq} (ht : t ∈ T)
    (hx : IsInitialPart t x) (ht' : t' ∈ T) (hx' : IsInitialPart t' x) : t = t' := by
  obtain ⟨s, -, hs⟩ := hT x
  rw [hs t ⟨ht, hx⟩, hs t' ⟨ht', hx'⟩]

theorem tr_eq {T : Finset Seq} (hT : IsTree T) {u v : Seq} (hu : u ∈ T)
    (hv : v ∈ T) (h : u <+: v) : u = v :=
  tr_unique hT hu (ip_of_prefix (ip_ext v) h) hv (ip_ext v)

theorem tr_sib {T : Finset Seq} (hT : IsTree T) {p : Seq} {b : Bool}
    (h : ∃ t ∈ T, p ++ [b] <+: t) (c : Bool) : ∃ t ∈ T, p ++ [c] <+: t := by
  obtain ⟨t, ht, hpt⟩ := h
  obtain ⟨t', ht', hx⟩ := tr_ip hT (ext (p ++ [c]))
  rcases ip_comparable hx (ip_ext _) with h1 | h1
  · rw [List.prefix_concat_iff] at h1
    rcases h1 with h1 | h1
    · exact ⟨t', ht', h1 ▸ List.prefix_refl _⟩
    · have h2 : t' <+: t := h1.trans ((List.prefix_append p [b]).trans hpt)
      have := tr_eq hT ht' ht h2
      subst this
      have := h1.length_le
      have := hpt.length_le
      simp at *
      omega
  · exact ⟨t', ht', h1⟩

theorem exists_prefix_of_dominated {U T : Finset Seq} (hU : IsTree U) (hT : IsTree T)
    (hd : Dominated U T) {t : Seq} (ht : t ∈ T) : ∃ u ∈ U, u <+: t := by
  obtain ⟨u, hu, hx⟩ := tr_ip hU (ext t)
  rcases ip_comparable hx (ip_ext t) with h | h
  · exact ⟨u, hu, h⟩
  · obtain ⟨t', ht', hut'⟩ := hd u hu
    have := tr_eq hT ht ht' (h.trans hut')
    subst this
    exact ⟨u, hu, hut'⟩

theorem sum_card_filter_le (U T : Finset Seq) (hU : ∀ u ∈ U, ∀ u' ∈ U, u <+: u' → u = u') :
    ∑ u ∈ U, (T.filter (u <+: ·)).card ≤ T.card := by
  rw [← Finset.card_biUnion]
  · apply Finset.card_le_card
    intro t
    simp only [Finset.mem_biUnion, Finset.mem_filter]
    rintro ⟨_, _, ht, _⟩
    exact ht
  · intro u hu u' hu' hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro t ht ht'
    simp only [Finset.mem_filter] at ht ht'
    rcases List.prefix_or_prefix_of_prefix ht.2 ht'.2 with h | h
    · exact hne (hU u hu u' hu' h)
    · exact hne (hU u' hu' u hu h).symm

theorem eq_of_dominated_of_card_le {U V : Finset Seq} (hU : IsTree U) (hV : IsTree V)
    (hd : Dominated U V) (hc : V.card ≤ U.card) : U = V := by
  have hsub : U ⊆ V := by
    intro u hu
    by_contra hnot
    have h2 : 1 < (V.filter (u <+: ·)).card := by
      obtain ⟨v, hv, huv⟩ := hd u hu
      obtain ⟨r, rfl⟩ := huv
      cases r with
      | nil => simp at hv; exact absurd hv hnot
      | cons c r =>
        obtain ⟨v', hv', h'⟩ := tr_sib hV (p := u) (b := c) ⟨u ++ c :: r, hv, by simp⟩ (!c)
        apply Finset.one_lt_card.mpr
        refine ⟨u ++ c :: r, by simp [hv], v', ?_, ?_⟩
        · simp only [Finset.mem_filter]
          exact ⟨hv', (List.prefix_append _ _).trans h'⟩
        · intro heq
          rw [← heq] at h'
          simp at h'
    have : U.card < V.card := by
      calc U.card = ∑ u ∈ U, 1 := by simp
        _ < ∑ u ∈ U, (V.filter (u <+: ·)).card := by
            apply Finset.sum_lt_sum
            · intro u hu
              obtain ⟨v, hv, h⟩ := hd u hu
              exact Finset.card_pos.mpr ⟨v, by simp [hv, h]⟩
            · exact ⟨u, hu, h2⟩
        _ ≤ V.card := sum_card_filter_le U V (fun u hu u' hu' h => tr_eq hU hu hu' h)
    omega
  exact Finset.eq_of_subset_of_card_le hsub hc

/-! ## The first-difference relation -/

/-- `D b u v`: `u` and `v` first differ at a position where `u` has `b` and `v` has `!b`. -/
def D (b : Bool) (u v : Seq) : Prop := ∃ p, p ++ [b] <+: u ∧ p ++ [!b] <+: v

theorem not_D_nil_left (b : Bool) (v : Seq) : ¬ D b [] v := by
  rintro ⟨p, h, -⟩
  have := h.length_le
  simp at this

theorem not_D_nil_right (b : Bool) (u : Seq) : ¬ D b u [] := by
  rintro ⟨p, -, h⟩
  have := h.length_le
  simp at this

theorem D_cons (β a b : Bool) (u v : Seq) :
    D β (a :: u) (b :: v) ↔ (a = β ∧ b = !β) ∨ (a = b ∧ D β u v) := by
  constructor
  · rintro ⟨p, h1, h2⟩
    cases p with
    | nil =>
      simp only [List.nil_append, List.cons_prefix_cons] at h1 h2
      exact Or.inl ⟨h1.1.symm, h2.1.symm⟩
    | cons c p =>
      simp only [List.cons_append, List.cons_prefix_cons] at h1 h2
      exact Or.inr ⟨h1.1.symm.trans h2.1, p, h1.2, h2.2⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, p, h1, h2⟩)
    · exact ⟨[], by simp, by simp⟩
    · exact ⟨a :: p, by simpa using h1, by simpa using h2⟩

theorem lt_iff_D (u v : Seq) : u < v ↔ (u <+: v ∧ u ≠ v) ∨ D false u v := by
  induction u generalizing v with
  | nil =>
    cases v with
    | nil => simp [not_D_nil_left]
    | cons b v => simp [List.nil_lt_cons]
  | cons a u ih =>
    cases v with
    | nil => simp [List.not_lt_nil, not_D_nil_right]
    | cons b v =>
      rw [List.cons_lt_cons_iff, ih, D_cons]
      cases a <;> cases b <;> simp

theorem D_symm {b : Bool} {u v : Seq} : D b u v ↔ D (!b) v u := by
  constructor
  · rintro ⟨p, h1, h2⟩
    exact ⟨p, h2, by simpa using h1⟩
  · rintro ⟨p, h1, h2⟩
    exact ⟨p, by simpa using h2, h1⟩

theorem D_irrefl (b : Bool) (u : Seq) : ¬ D b u u := by
  rintro ⟨p, h1, h2⟩
  have := List.prefix_of_prefix_length_le h1 h2 (by simp)
  simp at this

theorem D_trans {b : Bool} {u v w : Seq} (h1 : D b u v) (h2 : D b v w) : D b u w := by
  obtain ⟨p, hp1, hp2⟩ := h1
  obtain ⟨q, hq1, hq2⟩ := h2
  rcases List.prefix_or_prefix_of_prefix hp2 hq1 with h | h
  · rw [List.prefix_concat_iff] at h
    rcases h with h | h
    · have := congrArg List.getLast? h
      simp at this
    · exact ⟨p, hp1, h.trans ((List.prefix_append q [!b]).trans hq2)⟩
  · rw [List.prefix_concat_iff] at h
    rcases h with h | h
    · have := congrArg List.getLast? h
      simp at this
    · exact ⟨q, h.trans ((List.prefix_append p [b]).trans hp1), hq2⟩

theorem D_asymm {b : Bool} {u v : Seq} (h1 : D b u v) (h2 : D b v u) : False :=
  D_irrefl b u (D_trans h1 h2)

theorem D_ne {b : Bool} {u v : Seq} (h : D b u v) : u ≠ v := by
  rintro rfl
  exact D_irrefl b u h

theorem lt_of_D {u v : Seq} (h : D false u v) : u < v := (lt_iff_D u v).2 (Or.inr h)

theorem D_of_lt {u v : Seq} (h : u < v) (hp : ¬ u <+: v) : D false u v := by
  rcases (lt_iff_D u v).1 h with h | h
  · exact absurd h.1 hp
  · exact h

theorem D_total (b : Bool) {u v : Seq} (h1 : ¬ u <+: v) (h2 : ¬ v <+: u) : D b u v ∨ D b v u := by
  have hne : u ≠ v := by rintro rfl; exact h1 (List.prefix_refl u)
  rcases lt_or_gt_of_ne hne with h | h
  · have := D_of_lt h h1
    cases b
    · exact Or.inl this
    · exact Or.inr (D_symm.2 this)
  · have := D_of_lt h h2
    cases b
    · exact Or.inr this
    · exact Or.inl (D_symm.2 this)

/-- If `x` is a prefix of `x'` and `x` is incomparable with `y`, `D b x' y` gives `D b x y`. -/
theorem D_of_D_left {b : Bool} {x x' y : Seq} (h : D b x' y) (hx : x <+: x') (h1 : ¬ x <+: y) :
    D b x y := by
  obtain ⟨p, hp1, hp2⟩ := h
  rcases List.prefix_or_prefix_of_prefix hp1 hx with h | h
  · exact ⟨p, h, hp2⟩
  · rw [List.prefix_concat_iff] at h
    rcases h with h | h
    · exact ⟨p, h ▸ List.prefix_refl _, hp2⟩
    · exact absurd (h.trans ((List.prefix_append p [!b]).trans hp2)) h1

theorem D_of_D_right {b : Bool} {x y y' : Seq} (h : D b x y') (hy : y <+: y') (h1 : ¬ y <+: x) :
    D b x y :=
  D_symm.2 (D_of_D_left (D_symm.1 h) hy h1)

/-- In a prefix-free set, two distinct elements are incomparable. -/
theorem D_total_of_tree {U : Finset Seq} (hU : IsTree U) (b : Bool) {u v : Seq} (hu : u ∈ U)
    (hv : v ∈ U) (hne : u ≠ v) : D b u v ∨ D b v u :=
  D_total b (fun h => hne (tr_eq hU hu hv h)) (fun h => hne (tr_eq hU hv hu h).symm)

theorem lt_iff_D_of_tree {U : Finset Seq} (hU : IsTree U) {u v : Seq} (hu : u ∈ U) (hv : v ∈ U) :
    u < v ↔ D false u v := by
  refine ⟨fun h => D_of_lt h (fun h' => ?_), lt_of_D⟩
  exact (ne_of_lt h) (tr_eq hU hu hv h')

/-! ## Constant sequences -/

theorem not_D_replicate (b : Bool) (n : ℕ) (z : Seq) : ¬ D b z (List.replicate n b) := by
  rintro ⟨p, -, h⟩
  rw [List.prefix_replicate_iff] at h
  have := h.2
  have hm : (!b) ∈ p ++ [!b] := by simp
  rw [this] at hm
  have := List.eq_of_mem_replicate hm
  cases b <;> simp at this

theorem D_replicate (b : Bool) (k : ℕ) :
    D b (List.replicate (k + 1) b) (List.replicate k b ++ [!b]) :=
  ⟨List.replicate k b, by rw [List.replicate_succ'],
    List.prefix_refl _⟩

theorem eq_replicate_of_prefix_concat {b : Bool} {q : Seq} {k : ℕ}
    (h : q ++ [!b] <+: List.replicate k b ++ [!b]) : q = List.replicate k b := by
  rw [List.prefix_concat_iff] at h
  rcases h with h | h
  · simpa using h
  · rw [List.prefix_replicate_iff] at h
    have hm : (!b) ∈ q ++ [!b] := by simp
    rw [h.2] at hm
    have := List.eq_of_mem_replicate hm
    cases b <;> simp at this

theorem exists_replicate_mem {U : Finset Seq} (hU : IsTree U) (b : Bool) :
    ∃ m, List.replicate m b ∈ U := by
  obtain ⟨t, ht, hx⟩ := tr_ip hU (fun _ => b)
  refine ⟨t.length, ?_⟩
  have : t = List.replicate t.length b := by
    rw [List.eq_replicate_iff]
    refine ⟨rfl, fun c hc => ?_⟩
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
    exact hx i hi
  rw [← this]
  exact ht

/-! ## Quotients `T/u` -/

theorem card_quot (T : Finset Seq) (u : Seq) :
    (quot T u).card = (T.filter (u <+: ·)).card := by
  unfold quot
  apply Finset.card_image_of_injOn
  intro s hs t ht h
  simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hs ht
  obtain ⟨s', rfl⟩ := hs.2
  obtain ⟨t', rfl⟩ := ht.2
  simp only [List.drop_left] at h
  rw [h]

theorem card_quot_mono (T : Finset Seq) {u v : Seq} (h : u <+: v) :
    (quot T v).card ≤ (quot T u).card := by
  rw [card_quot, card_quot]
  apply Finset.card_le_card
  intro t
  simp only [Finset.mem_filter]
  exact fun ⟨ht, hv⟩ => ⟨ht, h.trans hv⟩

theorem card_quot_pos (T : Finset Seq) {u : Seq} (h : ∃ t ∈ T, u <+: t) :
    1 ≤ (quot T u).card := by
  rw [card_quot]
  obtain ⟨t, ht, hut⟩ := h
  exact Finset.card_pos.mpr ⟨t, by simp [ht, hut]⟩

/-! ## Sorting -/

theorem pairwise_merge' {α : Type*} {le : α → α → Bool}
    (trans : ∀ a b c, le a b = true → le b c = true → le a c = true) (l₁ l₂ : List α)
    (total : ∀ a ∈ l₁, ∀ b ∈ l₂, (le a b || le b a) = true)
    (h₁ : l₁.Pairwise (fun a b => le a b = true)) (h₂ : l₂.Pairwise (fun a b => le a b = true)) :
    (List.merge l₁ l₂ le).Pairwise (fun a b => le a b = true) := by
  induction l₁ generalizing l₂ with
  | nil => simpa using h₂
  | cons x l₁ ih₁ =>
    induction l₂ with
    | nil => simpa using h₁
    | cons y l₂ ih₂ =>
      rw [List.cons_merge_cons]
      split <;> rename_i h
      · apply List.Pairwise.cons
        · intro z m
          rw [List.mem_merge, List.mem_cons] at m
          rcases m with (m|rfl|m)
          · exact List.rel_of_pairwise_cons h₁ m
          · exact h
          · exact trans _ _ _ h (List.rel_of_pairwise_cons h₂ m)
        · exact ih₁ _ (fun a ha b hb => total a (List.mem_cons_of_mem _ ha) b hb) h₁.tail h₂
      · have hyx : le y x = true := by
          have := total x List.mem_cons_self y List.mem_cons_self
          simp_all
        apply List.Pairwise.cons
        · intro z m
          rw [List.mem_merge, List.mem_cons] at m
          rcases m with (⟨rfl|m⟩|m)
          · exact hyx
          · exact trans _ _ _ hyx (List.rel_of_pairwise_cons h₁ m)
          · exact List.rel_of_pairwise_cons h₂ m
        · exact ih₂ (fun a ha b hb => total a ha b (List.mem_cons_of_mem _ hb)) h₂.tail

open List.MergeSort.Internal in
theorem pairwise_mergeSort' {α : Type*} {le : α → α → Bool}
    (trans : ∀ a b c, le a b = true → le b c = true → le a c = true)
    (total : ∀ a b, a ≠ b → (le a b || le b a) = true) :
    ∀ (l : List α), l.Nodup → (List.mergeSort l le).Pairwise (fun a b => le a b = true)
  | [], _ => by simp
  | [a], _ => by simp
  | a :: b :: xs, hnd => by
    rw [List.mergeSort]
    have : (splitInTwo ⟨a :: b :: xs, rfl⟩).1.1.length < xs.length + 1 + 1 := by
      simp [splitInTwo_fst]; omega
    have : (splitInTwo ⟨a :: b :: xs, rfl⟩).2.1.length < xs.length + 1 + 1 := by
      simp [splitInTwo_snd]; omega
    have hsplit := splitInTwo_fst_append_splitInTwo_snd
      (⟨a :: b :: xs, rfl⟩ : {l : List α // l.length = (a :: b :: xs).length})
    have hnd' : ((splitInTwo ⟨a :: b :: xs, rfl⟩).1.1 ++
        (splitInTwo ⟨a :: b :: xs, rfl⟩).2.1).Nodup := by
      rw [hsplit]; exact hnd
    rw [List.nodup_append] at hnd'
    apply pairwise_merge' trans
    · intro x hx y hy
      rw [List.mem_mergeSort] at hx hy
      exact total x y (hnd'.2.2 x hx y hy)
    · exact pairwise_mergeSort' trans total _ hnd'.1
    · exact pairwise_mergeSort' trans total _ hnd'.2.1
termination_by l => l.length

theorem decide_lexLt (u v : Seq) : decide (LexLt u v) = true ↔ u < v := by
  rw [decide_eq_true_iff]
  exact Iff.rfl

theorem sorted_pairwise (U : Finset Seq) : (sorted U).Pairwise (· < ·) := by
  have := pairwise_mergeSort' (le := fun u v => decide (LexLt u v))
    (fun a b c h1 h2 => (decide_lexLt a c).2
      (lt_trans ((decide_lexLt a b).1 h1) ((decide_lexLt b c).1 h2)))
    (fun a b hne => by
      rw [Bool.or_eq_true, decide_lexLt, decide_lexLt]
      exact lt_or_gt_of_ne hne) U.toList U.nodup_toList
  exact this.imp (fun h => (decide_lexLt _ _).1 h)

theorem mem_sorted {U : Finset Seq} {x : Seq} : x ∈ sorted U ↔ x ∈ U := by
  simp [sorted, List.mem_mergeSort]

/-! ## Lists sorted by a strict order -/

theorem head?_eq_some_iff_of_pairwise {α : Type*} {r : α → α → Prop}
    (hr : ∀ a b, r a b → ¬ r b a) {l : List α} (hl : l.Pairwise r) (c : α) :
    l.head? = some c ↔ c ∈ l ∧ ∀ y ∈ l, y ≠ c → r c y := by
  cases l with
  | nil => simp
  | cons a m =>
    simp only [List.head?_cons, Option.some.injEq, List.mem_cons]
    rw [List.pairwise_cons] at hl
    constructor
    · rintro rfl
      refine ⟨Or.inl rfl, fun y hy hne => ?_⟩
      rcases hy with rfl | hy
      · exact absurd rfl hne
      · exact hl.1 y hy
    · rintro ⟨hc, h⟩
      by_contra hne
      rcases hc with rfl | hc
      · exact hne rfl
      · exact hr _ _ (h a (Or.inl rfl) hne) (hl.1 c hc)

theorem getLast?_eq_some_iff_of_pairwise {α : Type*} {r : α → α → Prop}
    (hr : ∀ a b, r a b → ¬ r b a) {l : List α} (hl : l.Pairwise r) (c : α) :
    l.getLast? = some c ↔ c ∈ l ∧ ∀ y ∈ l, y ≠ c → r y c := by
  rw [← List.head?_reverse]
  have := head?_eq_some_iff_of_pairwise (r := fun a b => r b a) (fun a b h h' => hr _ _ h h')
    (List.pairwise_reverse.2 hl) c
  simpa using this

theorem mem_middle_iff {l : List Seq} (hl : l.Pairwise (· < ·)) (x : Seq) :
    x ∈ (l.drop 1).dropLast ↔ x ∈ l ∧ (∃ y ∈ l, y < x) ∧ (∃ y ∈ l, x < y) := by
  cases l with
  | nil => simp
  | cons a m =>
    simp only [List.drop_succ_cons, List.drop_zero]
    by_cases hm : m = []
    · subst hm
      simp only [List.dropLast_nil, List.not_mem_nil, false_iff]
      rintro ⟨hx, ⟨y, hy, hyx⟩, -⟩
      simp only [List.mem_singleton] at hx hy
      subst hx
      subst hy
      exact lt_irrefl _ hyx
    · obtain ⟨m', c, rfl⟩ : ∃ m' c, m = m' ++ [c] :=
        ⟨m.dropLast, m.getLast hm, (List.dropLast_append_getLast hm).symm⟩
      rw [List.dropLast_concat]
      rw [List.pairwise_cons, List.pairwise_append] at hl
      obtain ⟨ha, -, -, hc⟩ := hl
      simp only [List.mem_singleton, forall_eq] at hc
      have hac : a < c := ha c (by simp)
      constructor
      · intro hx
        exact ⟨by simp [hx], ⟨a, by simp, ha x (by simp [hx])⟩, ⟨c, by simp, hc x hx⟩⟩
      · rintro ⟨hx, ⟨y, hy, hyx⟩, ⟨z, hz, hxz⟩⟩
        simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hx hy hz
        rcases hx with rfl | hx | rfl
        · exfalso
          rcases hy with rfl | hy | rfl
          · exact lt_irrefl _ hyx
          · exact lt_asymm hyx (ha y (by simp [hy]))
          · exact lt_asymm hyx hac
        · exact hx
        · exfalso
          rcases hz with rfl | hz | rfl
          · exact lt_asymm hxz hac
          · exact lt_asymm hxz (hc z hz)
          · exact lt_irrefl _ hxz

theorem pairwise_iff_forall_lt {l : List Seq} (hl : l.Pairwise (· < ·)) (R : Seq → Seq → Prop) :
    l.Pairwise R ↔ ∀ x ∈ l, ∀ y ∈ l, x < y → R x y := by
  constructor
  · intro h x hx y hy hxy
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hy
    rw [List.pairwise_iff_getElem] at h hl
    rcases lt_trichotomy i j with hij | rfl | hij
    · exact h i j hi hj hij
    · exact absurd hxy (lt_irrefl _)
    · exact absurd hxy (lt_asymm (hl j i hj hi hij))
  · intro h
    exact hl.imp_of_mem (fun hx hy hxy => h _ hx _ hy hxy)

/-! ## Interior elements and the semantic form of the conditions -/

/-- `x` is an interior element of `U`: there are elements of `U` on both sides of it. -/
def IsInt (U : Finset Seq) (x : Seq) : Prop :=
  x ∈ U ∧ (∃ y ∈ U, D false y x) ∧ (∃ y ∈ U, D false x y)

theorem isInt_iff_b (U : Finset Seq) (b : Bool) (x : Seq) :
    IsInt U x ↔ x ∈ U ∧ (∃ y ∈ U, D b y x) ∧ (∃ y ∈ U, D b x y) := by
  cases b
  · rfl
  · simp only [IsInt]
    constructor
    · rintro ⟨h, ⟨y, hy, h1⟩, ⟨z, hz, h2⟩⟩
      exact ⟨h, ⟨z, hz, D_symm.1 h2⟩, ⟨y, hy, D_symm.1 h1⟩⟩
    · rintro ⟨h, ⟨y, hy, h1⟩, ⟨z, hz, h2⟩⟩
      exact ⟨h, ⟨z, hz, D_symm.1 h2⟩, ⟨y, hy, D_symm.1 h1⟩⟩

theorem interior_sublist (U : Finset Seq) : (interior U).Sublist (sorted U) :=
  (List.dropLast_sublist _).trans (List.drop_sublist _ _)

theorem interior_pairwise (U : Finset Seq) : (interior U).Pairwise (· < ·) :=
  (sorted_pairwise U).sublist (interior_sublist U)

theorem mem_interior_iff {U : Finset Seq} (hU : IsTree U) (x : Seq) :
    x ∈ interior U ↔ IsInt U x := by
  unfold interior IsInt
  rw [mem_middle_iff (sorted_pairwise U)]
  simp only [mem_sorted]
  constructor
  · rintro ⟨hx, ⟨y, hy, hyx⟩, ⟨z, hz, hxz⟩⟩
    exact ⟨hx, ⟨y, hy, (lt_iff_D_of_tree hU hy hx).1 hyx⟩,
      ⟨z, hz, (lt_iff_D_of_tree hU hx hz).1 hxz⟩⟩
  · rintro ⟨hx, ⟨y, hy, hyx⟩, ⟨z, hz, hxz⟩⟩
    exact ⟨hx, ⟨y, hy, lt_of_D hyx⟩, ⟨z, hz, lt_of_D hxz⟩⟩

/-- Condition 2 of Definition 5.1, in the direction `b` (`false`: increasing). -/
def Inc (b : Bool) (T U : Finset Seq) : Prop :=
  ∀ x y, IsInt U x → IsInt U y → D b x y → 2 * (quot T x).card ≤ (quot T y).card

/-- Condition 1 of Definition 5.1. -/
def Cond1 (U : Finset Seq) : Prop := ∀ b : Bool, ∃ u ∈ U, [b, !b] <+: u

/-- Condition 3 of Definition 5.1 at the end `b` (`false`: the left end), in structural form:
the extreme element `b^(k+1)` and its sibling `b^k (!b)` both lie in `U`. -/
def Cond3 (b : Bool) (U : Finset Seq) : Prop :=
  ∃ k, List.replicate (k + 1) b ∈ U ∧ List.replicate k b ++ [!b] ∈ U

/-- `c` is the first interior element of `U` in the direction `b`. -/
def First (b : Bool) (U : Finset Seq) (c : Seq) : Prop :=
  IsInt U c ∧ ∀ y, IsInt U y → y ≠ c → D b c y

/-- The semantic form of the defining conditions of `∂T`. -/
def Sem (T U : Finset Seq) : Prop :=
  Cond1 U ∧ (Inc false T U ∨ Inc true T U) ∧ Cond3 false U ∧ Cond3 true U

theorem cond1_iff (U : Finset Seq) :
    ((∃ u ∈ U, bits "01" <+: u) ∧ (∃ u ∈ U, bits "10" <+: u)) ↔ Cond1 U := by
  have h01 : bits "01" = [false, true] := rfl
  have h10 : bits "10" = [true, false] := rfl
  rw [h01, h10]
  constructor
  · rintro ⟨h1, h2⟩ b
    cases b
    exacts [h1, h2]
  · intro h
    exact ⟨h false, h true⟩

theorem opt_pairwise_iff (T U : Finset Seq) (R : ℕ → ℕ → Prop) :
    (∀ i j (hi : i < (interior U).length) (hj : j < (interior U).length), i < j →
      R (quot T ((interior U).get ⟨i, hi⟩)).card (quot T ((interior U).get ⟨j, hj⟩)).card) ↔
      (interior U).Pairwise (fun x y => R (quot T x).card (quot T y).card) := by
  rw [List.pairwise_iff_getElem]
  simp only [List.get_eq_getElem]

theorem opt1_iff {T U : Finset Seq} (hU : IsTree U) :
    (∀ i j (hi : i < (interior U).length) (hj : j < (interior U).length), i < j →
      2 * (quot T ((interior U).get ⟨i, hi⟩)).card ≤ (quot T ((interior U).get ⟨j, hj⟩)).card) ↔
    Inc false T U := by
  rw [opt_pairwise_iff T U (fun a b => 2 * a ≤ b), pairwise_iff_forall_lt (interior_pairwise U)]
  constructor
  · intro h x y hx hy hxy
    exact h x ((mem_interior_iff hU x).2 hx) y ((mem_interior_iff hU y).2 hy) (lt_of_D hxy)
  · intro h x hx y hy hxy
    have hx' := (mem_interior_iff hU x).1 hx
    have hy' := (mem_interior_iff hU y).1 hy
    exact h x y hx' hy' ((lt_iff_D_of_tree hU hx'.1 hy'.1).1 hxy)

theorem opt2_iff {T U : Finset Seq} (hU : IsTree U) :
    (∀ i j (hi : i < (interior U).length) (hj : j < (interior U).length), i < j →
      2 * (quot T ((interior U).get ⟨j, hj⟩)).card ≤ (quot T ((interior U).get ⟨i, hi⟩)).card) ↔
    Inc true T U := by
  rw [opt_pairwise_iff T U (fun a b => 2 * b ≤ a), pairwise_iff_forall_lt (interior_pairwise U)]
  constructor
  · intro h x y hx hy hxy
    exact h y ((mem_interior_iff hU y).2 hy) x ((mem_interior_iff hU x).2 hx)
      (lt_of_D (D_symm.1 hxy))
  · intro h x hx y hy hxy
    have hx' := (mem_interior_iff hU x).1 hx
    have hy' := (mem_interior_iff hU y).1 hy
    exact h y x hy' hx' (D_symm.1 ((lt_iff_D_of_tree hU hx'.1 hy'.1).1 hxy))

theorem head_iff {U : Finset Seq} (hU : IsTree U) :
    (interior U).head?.bind List.getLast? = some true ↔
      ∃ c, First false U c ∧ c.getLast? = some true := by
  rw [Option.bind_eq_some_iff]
  apply exists_congr
  intro c
  rw [head?_eq_some_iff_of_pairwise (fun a b h h' => lt_asymm h h') (interior_pairwise U)]
  apply and_congr _ Iff.rfl
  unfold First
  constructor
  · rintro ⟨hc, h⟩
    have hc' := (mem_interior_iff hU c).1 hc
    refine ⟨hc', fun y hy hne => ?_⟩
    exact (lt_iff_D_of_tree hU hc'.1 hy.1).1 (h y ((mem_interior_iff hU y).2 hy) hne)
  · rintro ⟨hc, h⟩
    exact ⟨(mem_interior_iff hU c).2 hc,
      fun y hy hne => lt_of_D (h y ((mem_interior_iff hU y).1 hy) hne)⟩

theorem last_iff {U : Finset Seq} (hU : IsTree U) :
    (interior U).getLast?.bind List.getLast? = some false ↔
      ∃ c, First true U c ∧ c.getLast? = some false := by
  rw [Option.bind_eq_some_iff]
  apply exists_congr
  intro c
  rw [getLast?_eq_some_iff_of_pairwise (fun a b h h' => lt_asymm h h') (interior_pairwise U)]
  apply and_congr _ Iff.rfl
  unfold First
  constructor
  · rintro ⟨hc, h⟩
    have hc' := (mem_interior_iff hU c).1 hc
    refine ⟨hc', fun y hy hne => ?_⟩
    exact D_symm.1 ((lt_iff_D_of_tree hU hy.1 hc'.1).1 (h y ((mem_interior_iff hU y).2 hy) hne))
  · rintro ⟨hc, h⟩
    exact ⟨(mem_interior_iff hU c).2 hc,
      fun y hy hne => lt_of_D (D_symm.1 (h y ((mem_interior_iff hU y).1 hy) hne))⟩

theorem replicate_prefix_replicate (b : Bool) {m n : ℕ} (h : m ≤ n) :
    List.replicate m b <+: List.replicate n b :=
  List.prefix_replicate_iff.2 ⟨by simp; omega, by simp⟩

theorem cond3_of_first {U : Finset Seq} (hU : IsTree U) {b : Bool} {c : Seq} (hc : First b U c)
    (hlast : c.getLast? = some (!b)) : Cond3 b U := by
  obtain ⟨hcI, hfirst⟩ := hc
  have hcU := hcI.1
  rw [List.getLast?_eq_some_iff] at hlast
  obtain ⟨p, rfl⟩ := hlast
  obtain ⟨a, haU, hpa⟩ := tr_sib hU ⟨p ++ [!b], hcU, List.prefix_refl _⟩ b
  have hDac : D b a (p ++ [!b]) := ⟨p, hpa, List.prefix_refl _⟩
  have ha_not : ¬ ∃ z ∈ U, D b z a := by
    rintro ⟨z, hz, hza⟩
    have hint : IsInt U a := (isInt_iff_b U b a).2 ⟨haU, ⟨z, hz, hza⟩, ⟨_, hcU, hDac⟩⟩
    exact D_asymm hDac (hfirst a hint (D_ne hDac))
  obtain ⟨m, hm⟩ := exists_replicate_mem hU b
  have ha : a = List.replicate m b := by
    by_contra hne
    rcases D_total_of_tree hU b haU hm hne with h | h
    · exact not_D_replicate b m a h
    · exact ha_not ⟨_, hm, h⟩
  subst ha
  obtain ⟨hlen, hpeq⟩ := List.prefix_replicate_iff.1 hpa
  simp only [List.length_append, List.length_singleton] at hlen hpeq
  rw [List.replicate_succ'] at hpeq
  have hp : p = List.replicate p.length b := List.append_inj_left' hpeq rfl
  set j := p.length with hj
  have hmj : m = j + 1 := by
    by_contra hne
    have hm2 : j + 2 ≤ m := by omega
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have hrep : List.replicate (m' + 1) b = List.replicate m' b ++ [b] := List.replicate_succ' ..
    have hpre : List.replicate m' b ++ [b] <+: List.replicate (m' + 1) b :=
      (show List.replicate m' b ++ [b] <+: List.replicate (m' + 1) b from
        hrep ▸ List.prefix_refl _)
    obtain ⟨c', hc'U, hc'⟩ := tr_sib hU ⟨_, hm, hpre⟩ (!b)
    have h1 : D b (List.replicate (m' + 1) b) c' := ⟨List.replicate m' b, hpre, hc'⟩
    have h2 : D b c' (p ++ [!b]) := by
      refine ⟨p, ?_, List.prefix_refl _⟩
      rw [hp, ← List.replicate_succ']
      exact (replicate_prefix_replicate b (by omega)).trans ((List.prefix_append _ _).trans hc')
    have hint : IsInt U c' :=
      (isInt_iff_b U b c').2 ⟨hc'U, ⟨_, hm, h1⟩, ⟨_, hcU, h2⟩⟩
    exact D_asymm h2 (hfirst c' hint (D_ne h2))
  refine ⟨j, hmj ▸ hm, ?_⟩
  rw [← hp]
  exact hcU

theorem first_of_cond3 {U : Finset Seq} (hU : IsTree U) (h1 : Cond1 U) {b : Bool}
    (h : Cond3 b U) : ∃ c, First b U c ∧ c.getLast? = some (!b) := by
  obtain ⟨k, hk1, hk2⟩ := h
  have hk : k ≠ 0 := by
    rintro rfl
    obtain ⟨u', hu', hpu'⟩ := h1 b
    have h' : [b] <+: u' := (List.prefix_append [b] [!b]).trans hpu'
    have := tr_eq hU hk1 hu' (by simpa using h')
    subst this
    have := hpu'.length_le
    simp at this
  refine ⟨List.replicate k b ++ [!b], ⟨?_, ?_⟩, by simp⟩
  · rw [isInt_iff_b U b]
    refine ⟨hk2, ⟨_, hk1, D_replicate b k⟩, ?_⟩
    obtain ⟨u, hu, hpu⟩ := h1 (!b)
    refine ⟨u, hu, ⟨[], ?_, ?_⟩⟩
    · obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
      simp [List.replicate_succ]
    · simpa using (List.prefix_append [!b] [!!b]).trans hpu
  · intro y hy hne
    rw [isInt_iff_b U b] at hy
    obtain ⟨hyU, ⟨z, hz, hzy⟩, -⟩ := hy
    have hne' : y ≠ List.replicate (k + 1) b := by
      rintro rfl
      exact not_D_replicate b (k + 1) z hzy
    rcases D_total_of_tree hU b hk2 hyU (Ne.symm hne) with h | h
    · exact h
    · exfalso
      obtain ⟨q, hq1, hq2⟩ := h
      have := eq_replicate_of_prefix_concat hq2
      subst this
      rw [← List.replicate_succ'] at hq1
      exact hne' (tr_eq hU hk1 hyU hq1).symm

theorem sem_iff {T U : Finset Seq} (hU : IsTree U) : DeltaConditions T U ↔ Sem T U := by
  unfold DeltaConditions Sem
  constructor
  · rintro ⟨h01, h10, h2, h3, h4⟩
    refine ⟨(cond1_iff U).1 ⟨h01, h10⟩, ?_, ?_, ?_⟩
    · rcases h2 with h | h
      exacts [Or.inl ((opt1_iff hU).1 h), Or.inr ((opt2_iff hU).1 h)]
    · obtain ⟨c, hc, hcl⟩ := (head_iff hU).1 h3
      exact cond3_of_first hU hc hcl
    · obtain ⟨c, hc, hcl⟩ := (last_iff hU).1 h4
      exact cond3_of_first hU hc hcl
  · rintro ⟨h1, h2, h3, h4⟩
    obtain ⟨h01, h10⟩ := (cond1_iff U).2 h1
    refine ⟨h01, h10, ?_, (head_iff hU).2 (first_of_cond3 hU h1 h3),
      (last_iff hU).2 (first_of_cond3 hU h1 h4)⟩
    rcases h2 with h | h
    exacts [Or.inl ((opt1_iff hU).2 h), Or.inr ((opt2_iff hU).2 h)]

/-! ## The join of two trees -/

/-- The join of two trees: at every point, the longer of the two leaves. -/
noncomputable def join (U V : Finset Seq) : Finset Seq :=
  U.filter (fun u => ∃ v ∈ V, v <+: u) ∪ V.filter (fun v => ∃ u ∈ U, u <+: v)

theorem mem_join {U V : Finset Seq} {x : Seq} :
    x ∈ join U V ↔ (x ∈ U ∧ ∃ v ∈ V, v <+: x) ∨ (x ∈ V ∧ ∃ u ∈ U, u <+: x) := by
  simp [join]

theorem join_comm (U V : Finset Seq) : join U V = join V U := by
  ext x
  rw [mem_join, mem_join]
  exact Or.comm

theorem join_isTree {U V : Finset Seq} (hU : IsTree U) (hV : IsTree V) : IsTree (join U V) := by
  intro x
  obtain ⟨u, hu, hux⟩ := tr_ip hU x
  obtain ⟨v, hv, hvx⟩ := tr_ip hV x
  -- any element of the join that is an initial part of `x`
  have hchar : ∀ j, j ∈ join U V → IsInitialPart j x →
      (j = u ∧ v <+: u) ∨ (j = v ∧ u <+: v) := by
    intro j hj hjx
    rcases mem_join.1 hj with ⟨hjU, v', hv', hv'j⟩ | ⟨hjV, u', hu', hu'j⟩
    · have := tr_unique hU hjU hjx hu hux
      subst this
      have := tr_unique hV hv' (ip_of_prefix hjx hv'j) hv hvx
      subst this
      exact Or.inl ⟨rfl, hv'j⟩
    · have := tr_unique hV hjV hjx hv hvx
      subst this
      have := tr_unique hU hu' (ip_of_prefix hjx hu'j) hu hux
      subst this
      exact Or.inr ⟨rfl, hu'j⟩
  by_cases huv : u <+: v
  · refine ⟨v, ⟨mem_join.2 (Or.inr ⟨hv, u, hu, huv⟩), hvx⟩, ?_⟩
    rintro j ⟨hj, hjx⟩
    rcases hchar j hj hjx with ⟨rfl, hvu⟩ | ⟨rfl, -⟩
    · exact huv.eq_of_length (le_antisymm huv.length_le hvu.length_le) ▸ rfl
    · rfl
  · have hvu : v <+: u := (ip_comparable hux hvx).resolve_left huv
    refine ⟨u, ⟨mem_join.2 (Or.inl ⟨hu, v, hv, hvu⟩), hux⟩, ?_⟩
    rintro j ⟨hj, hjx⟩
    rcases hchar j hj hjx with ⟨rfl, -⟩ | ⟨rfl, h⟩
    · rfl
    · exact absurd h huv

theorem dominated_join {U V : Finset Seq} (hU : IsTree U) (hV : IsTree V) :
    Dominated U (join U V) := by
  intro u hu
  obtain ⟨j, hj, hjx⟩ := tr_ip (join_isTree hU hV) (ext u)
  refine ⟨j, hj, ?_⟩
  rcases mem_join.1 hj with ⟨hjU, -⟩ | ⟨-, u', hu', hu'j⟩
  · rw [tr_unique hU hu (ip_ext u) hjU hjx]
  · rw [tr_unique hU hu (ip_ext u) hu' (ip_of_prefix hjx hu'j)]
    exact hu'j

theorem join_dominated {U V T : Finset Seq} (hUT : Dominated U T) (hVT : Dominated V T) :
    Dominated (join U V) T := by
  intro j hj
  rcases mem_join.1 hj with ⟨hjU, -⟩ | ⟨hjV, -⟩
  exacts [hUT j hjU, hVT j hjV]

theorem isInt_of_join {U V : Finset Seq} (hU : IsTree U) (hV : IsTree V) {x : Seq}
    (hx : IsInt (join U V) x) (hxU : x ∈ U) : IsInt U x := by
  have hJ := join_isTree hU hV
  obtain ⟨hxJ, ⟨y, hy, hyx⟩, ⟨z, hz, hxz⟩⟩ := hx
  refine ⟨hxU, ?_, ?_⟩
  · rcases mem_join.1 hy with ⟨hyU, -⟩ | ⟨-, u, hu, huy⟩
    · exact ⟨y, hyU, hyx⟩
    · refine ⟨u, hu, D_of_D_left hyx huy ?_⟩
      intro hux
      have := tr_eq hU hu hxU hux
      subst this
      exact D_ne hyx (tr_eq hJ hxJ hy huy).symm
  · rcases mem_join.1 hz with ⟨hzU, -⟩ | ⟨-, u, hu, huz⟩
    · exact ⟨z, hzU, hxz⟩
    · refine ⟨u, hu, D_of_D_right hxz huz ?_⟩
      intro hux
      have := tr_eq hU hu hxU hux
      subst this
      exact D_ne hxz (tr_eq hJ hxJ hz huz)

theorem cond1_of_dominated {U V : Finset Seq} (h : Cond1 U) (hd : Dominated U V) : Cond1 V := by
  intro b
  obtain ⟨u, hu, hbu⟩ := h b
  obtain ⟨v, hv, huv⟩ := hd u hu
  exact ⟨v, hv, hbu.trans huv⟩

theorem cond3_join_aux {U V : Finset Seq} {b : Bool} {k l : ℕ}
    (hk1 : List.replicate (k + 1) b ∈ U) (hk2 : List.replicate k b ++ [!b] ∈ U)
    (hl1 : List.replicate (l + 1) b ∈ V) (hl2 : List.replicate l b ++ [!b] ∈ V) (hlk : l ≤ k) :
    Cond3 b (join U V) := by
  refine ⟨k, mem_join.2 (Or.inl ⟨hk1, _, hl1, replicate_prefix_replicate b (by omega)⟩),
    mem_join.2 (Or.inl ⟨hk2, ?_⟩)⟩
  rcases Nat.lt_or_eq_of_le hlk with h | rfl
  · exact ⟨_, hl1, (replicate_prefix_replicate b h).trans (List.prefix_append _ _)⟩
  · exact ⟨_, hl2, List.prefix_refl _⟩

theorem cond3_join {U V : Finset Seq} {b : Bool} (hU : Cond3 b U) (hV : Cond3 b V) :
    Cond3 b (join U V) := by
  obtain ⟨k, hk1, hk2⟩ := hU
  obtain ⟨l, hl1, hl2⟩ := hV
  rcases le_total l k with h | h
  · exact cond3_join_aux hk1 hk2 hl1 hl2 h
  · rw [join_comm]
    exact cond3_join_aux hl1 hl2 hk1 hk2 h

/-- The mixed case of condition 2 for the join: `x` comes from `U` (extending `x' ∈ V`) and `y`
comes from `V`. This is where condition 3 is used. -/
theorem inc_join_mixed {T U V : Finset Seq} (hU : IsTree U) (hV : IsTree V)
    (h1U : Cond1 U) (h1V : Cond1 V) {b : Bool}
    (hIU : Inc b T U) (hIV : Inc b T V) (h3V : Cond3 b V)
    {x y : Seq} (hx : IsInt (join U V) x) (hy : IsInt (join U V) y) (hxy : D b x y)
    (hxU : x ∈ U) {x' : Seq} (hx'V : x' ∈ V) (hx'x : x' <+: x) (hyV : y ∈ V) :
    2 * (quot T x).card ≤ (quot T y).card := by
  have hJ := join_isTree hU hV
  have hxJ := hx.1
  have hyJ := hy.1
  have hxIU : IsInt U x := isInt_of_join hU hV hx hxU
  have hyIV : IsInt V y := isInt_of_join hV hU (join_comm U V ▸ hy) hyV
  have hx'y : x' ≠ y := by
    rintro rfl
    exact D_ne hxy (tr_eq hJ hyJ hxJ hx'x).symm
  have hD' : D b x' y := D_of_D_left hxy hx'x (fun h => hx'y (tr_eq hV hx'V hyV h))
  have hmono : (quot T x).card ≤ (quot T x').card := card_quot_mono T hx'x
  by_cases hx'I : IsInt V x'
  · have := hIV x' y hx'I hyIV hD'
    omega
  · have hno : ¬ ∃ z ∈ V, D b z x' := by
      rintro ⟨z, hz, hzx'⟩
      exact hx'I ((isInt_iff_b V b x').2 ⟨hx'V, ⟨z, hz, hzx'⟩, ⟨y, hyV, hD'⟩⟩)
    obtain ⟨k, hk1, hk2⟩ := h3V
    have hx'eq : x' = List.replicate (k + 1) b := by
      by_contra hne
      rcases D_total_of_tree hV b hx'V hk1 hne with h | h
      · exact not_D_replicate b (k + 1) x' h
      · exact hno ⟨_, hk1, h⟩
    subst hx'eq
    have hxk : List.replicate k b ++ [b] <+: x := by rwa [← List.replicate_succ']
    obtain ⟨w, hwU, hcw⟩ := tr_sib hU ⟨x, hxU, hxk⟩ (!b)
    have hk : k ≠ 0 := by
      rintro rfl
      obtain ⟨u', hu', hpu'⟩ := h1V b
      have h' : [b] <+: u' := (List.prefix_append [b] [!b]).trans hpu'
      have := tr_eq hV hk1 hu' (by simpa using h')
      subst this
      have := hpu'.length_le
      simp at this
    have hDxw : D b x w := ⟨List.replicate k b, hxk, hcw⟩
    have hwI : IsInt U w := by
      rw [isInt_iff_b U b]
      obtain ⟨u, hu, hpu⟩ := h1U (!b)
      refine ⟨hwU, ⟨x, hxU, hDxw⟩, ⟨u, hu, [], ?_, ?_⟩⟩
      · obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
        exact (by simp [List.replicate_succ] : [] ++ [b] <+: List.replicate (k' + 1) b ++ [!b]).trans
          hcw
      · simpa using (List.prefix_append [!b] [!!b]).trans hpu
    have h1 := hIU x w hxIU hwI hDxw
    have h2 : (quot T w).card ≤ (quot T (List.replicate k b ++ [!b])).card := card_quot_mono T hcw
    have h3 : (quot T (List.replicate k b ++ [!b])).card ≤ (quot T y).card := by
      by_cases hyc : y = List.replicate k b ++ [!b]
      · rw [hyc]
      · have hDcy : D b (List.replicate k b ++ [!b]) y := by
          rcases D_total_of_tree hV b hk2 hyV (Ne.symm hyc) with h | h
          · exact h
          · exfalso
            obtain ⟨q, hq1, hq2⟩ := h
            have := eq_replicate_of_prefix_concat hq2
            subst this
            rw [← List.replicate_succ'] at hq1
            exact hx'y (tr_eq hV hk1 hyV hq1)
        have hcI : IsInt V (List.replicate k b ++ [!b]) :=
          (isInt_iff_b V b _).2 ⟨hk2, ⟨_, hk1, D_replicate b k⟩, ⟨y, hyV, hDcy⟩⟩
        have := hIV _ y hcI hyIV hDcy
        omega
    omega

theorem inc_join {T U V : Finset Seq} (hU : IsTree U) (hV : IsTree V)
    (h1U : Cond1 U) (h1V : Cond1 V) {b : Bool}
    (hIU : Inc b T U) (hIV : Inc b T V) (h3U : Cond3 b U) (h3V : Cond3 b V) :
    Inc b T (join U V) := by
  intro x y hx hy hxy
  rcases mem_join.1 hx.1 with ⟨hxU, x', hx'V, hx'x⟩ | ⟨hxV, x', hx'U, hx'x⟩ <;>
  rcases mem_join.1 hy.1 with ⟨hyU, y', hy'V, hy'y⟩ | ⟨hyV, y', hy'U, hy'y⟩
  · exact hIU x y (isInt_of_join hU hV hx hxU) (isInt_of_join hU hV hy hyU) hxy
  · exact inc_join_mixed hU hV h1U h1V hIU hIV h3V hx hy hxy hxU hx'V hx'x hyV
  · rw [join_comm] at hx hy
    exact inc_join_mixed hV hU h1V h1U hIV hIU h3U hx hy hxy hxV hx'U hx'x hyU
  · rw [join_comm] at hx hy
    exact hIV x y (isInt_of_join hV hU hx hxV) (isInt_of_join hV hU hy hyV) hxy

/-! ## The orientation of condition 2 -/

theorem sum_lt_two_mul : ∀ (n : ℕ) (S : Finset Seq) (g : Seq → ℕ), S.card = n → S.Nonempty →
    (∀ x ∈ S, 1 ≤ g x) → (∀ x ∈ S, ∀ y ∈ S, x ≠ y → 2 * g x ≤ g y ∨ 2 * g y ≤ g x) →
    ∃ m ∈ S, ∑ x ∈ S, g x < 2 * g m
  | 0, S, _, hc, hne, _, _ => by
    rw [Finset.card_eq_zero] at hc
    subst hc
    simp at hne
  | n + 1, S, g, hc, hne, hpos, hdbl => by
    obtain ⟨m, hm, hmax⟩ := S.exists_max_image g hne
    refine ⟨m, hm, ?_⟩
    rw [← Finset.add_sum_erase S g hm]
    by_cases hS' : (S.erase m).Nonempty
    · obtain ⟨m', hm', hsum⟩ := sum_lt_two_mul n (S.erase m) g
        (by rw [Finset.card_erase_of_mem hm]; omega) hS'
        (fun x hx => hpos x (Finset.mem_of_mem_erase hx))
        (fun x hx y hy => hdbl x (Finset.mem_of_mem_erase hx) y (Finset.mem_of_mem_erase hy))
      have hm'ne : m' ≠ m := Finset.ne_of_mem_erase hm'
      have : 2 * g m' ≤ g m := by
        rcases hdbl m' (Finset.mem_of_mem_erase hm') m hm hm'ne with h | h
        · exact h
        · have := hmax m' (Finset.mem_of_mem_erase hm')
          have := hpos m hm
          omega
      omega
    · rw [Finset.not_nonempty_iff_eq_empty.1 hS', Finset.sum_empty]
      have := hpos m hm
      omega

theorem card_quot_le_sum {T U : Finset Seq} (hT : IsTree T) (hU : IsTree U)
    (hUT : Dominated U T) {p : Seq} (hp : ∃ u ∈ U, p <+: u) :
    (quot T p).card ≤ ∑ u ∈ U.filter (p <+: ·), (quot T u).card := by
  rw [card_quot]
  simp_rw [card_quot]
  calc (T.filter (p <+: ·)).card
      ≤ ((U.filter (p <+: ·)).biUnion (fun u => T.filter (u <+: ·))).card := by
        apply Finset.card_le_card
        intro t ht
        simp only [Finset.mem_filter] at ht
        obtain ⟨u, hu, hut⟩ := exists_prefix_of_dominated hU hT hUT ht.1
        simp only [Finset.mem_biUnion, Finset.mem_filter]
        refine ⟨u, ⟨hu, ?_⟩, ht.1, hut⟩
        rcases List.prefix_or_prefix_of_prefix ht.2 hut with h | h
        · exact h
        · obtain ⟨u0, hu0, hpu0⟩ := hp
          have := tr_eq hU hu hu0 (h.trans hpu0)
          subst this
          exact hpu0
    _ ≤ _ := Finset.card_biUnion_le

theorem orient {T U : Finset Seq} (hT : IsTree T) (hU : IsTree U) (hUT : Dominated U T)
    (h1 : Cond1 U) {b : Bool} (hI : Inc b T U) :
    (quot T [b, !b]).card < (quot T [!b, b]).card := by
  have hSI : ∀ x ∈ U.filter ([b, !b] <+: ·), IsInt U x := by
    intro x hx
    simp only [Finset.mem_filter] at hx
    rw [isInt_iff_b U b]
    obtain ⟨z, hz, hbz⟩ := tr_sib hU (p := [b]) (b := !b) ⟨x, hx.1, by simpa using hx.2⟩ b
    obtain ⟨u, hu, hbu⟩ := h1 (!b)
    refine ⟨hx.1, ⟨z, hz, [b], hbz, by simpa using hx.2⟩, ⟨u, hu, [], ?_, ?_⟩⟩
    · exact (by simp : [] ++ [b] <+: [b, !b]).trans hx.2
    · simpa using (List.prefix_append [!b] [!!b]).trans hbu
  have hne : (U.filter ([b, !b] <+: ·)).Nonempty := by
    obtain ⟨u, hu, hbu⟩ := h1 b
    exact ⟨u, by simp [hu, hbu]⟩
  obtain ⟨m, hm, hsum⟩ := sum_lt_two_mul _ (U.filter ([b, !b] <+: ·)) (fun x => (quot T x).card)
    rfl hne
    (fun x hx => card_quot_pos T (hUT x (Finset.mem_filter.1 hx).1))
    (fun x hx y hy hxy => by
      rcases D_total_of_tree hU b (Finset.mem_filter.1 hx).1 (Finset.mem_filter.1 hy).1 hxy
        with h | h
      · exact Or.inl (hI x y (hSI x hx) (hSI y hy) h)
      · exact Or.inr (hI y x (hSI y hy) (hSI x hx) h))
  have hle := card_quot_le_sum hT hU hUT (h1 b)
  obtain ⟨u, hu, hbu⟩ := h1 (!b)
  obtain ⟨z, hz, hbz⟩ := tr_sib hU (p := [!b]) (b := !!b) ⟨u, hu, by simpa using hbu⟩ (!b)
  have hmI := hSI m hm
  have hmb : [b, !b] <+: m := (Finset.mem_filter.1 hm).2
  have hDmu : D b m u :=
    ⟨[], (by simp : [] ++ [b] <+: [b, !b]).trans hmb,
      by simpa using (List.prefix_append [!b] [!!b]).trans hbu⟩
  have huI : IsInt U u := (isInt_iff_b U b u).2
    ⟨hu, ⟨m, hmI.1, hDmu⟩, ⟨z, hz, [!b], by simpa using hbu, hbz⟩⟩
  have h2 := hI m u hmI huI hDmu
  have h3 : (quot T u).card ≤ (quot T [!b, b]).card := by
    have := card_quot_mono T hbu
    simpa using this
  calc (quot T [b, !b]).card ≤ _ := hle
    _ < 2 * (quot T m).card := hsum
    _ ≤ (quot T u).card := h2
    _ ≤ _ := h3

theorem not_inc_false_inc_true {T U V : Finset Seq} (hT : IsTree T) (hU : IsTree U)
    (hV : IsTree V) (hUT : Dominated U T) (hVT : Dominated V T) (h1U : Cond1 U) (h1V : Cond1 V)
    (hIU : Inc false T U) (hIV : Inc true T V) : False := by
  have h1 := orient hT hU hUT h1U hIU
  have h2 := orient hT hV hVT h1V hIV
  simp only [Bool.not_false, Bool.not_true] at h1 h2
  omega

/-! ## Lemma 5.2 -/

/-- All prefixes of elements of `T`. -/
noncomputable def prefixes (T : Finset Seq) : Finset Seq := T.biUnion (fun t => t.inits.toFinset)

theorem subset_prefixes {U T : Finset Seq} (h : Dominated U T) : U ⊆ prefixes T := by
  intro u hu
  obtain ⟨t, ht, hut⟩ := h u hu
  simp only [prefixes, Finset.mem_biUnion, List.mem_toFinset, List.mem_inits]
  exact ⟨t, ht, hut⟩

theorem exists_max (T : Finset Seq) (hT : IsTree T)
    (h : ∃ U, IsTree U ∧ Dominated U T ∧ DeltaConditions T U) :
    ∃ U, IsTree U ∧ Dominated U T ∧ DeltaConditions T U ∧
      ∀ V, IsTree V → Dominated V T → DeltaConditions T V → Dominated V U := by
  let C := (prefixes T).powerset.filter (fun U => IsTree U ∧ Dominated U T ∧ DeltaConditions T U)
  have hC : C.Nonempty := by
    obtain ⟨U, hU⟩ := h
    exact ⟨U, Finset.mem_filter.2 ⟨Finset.mem_powerset.2 (subset_prefixes hU.2.1), hU⟩⟩
  obtain ⟨M, hM, hmax⟩ := C.exists_max_image Finset.card hC
  obtain ⟨-, hMt, hMT, hMD⟩ := Finset.mem_filter.1 hM
  refine ⟨M, hMt, hMT, hMD, fun V hV hVT hVD => ?_⟩
  obtain ⟨h1M, h2M, h3M, h4M⟩ := (sem_iff hMt).1 hMD
  obtain ⟨h1V, h2V, h3V, h4V⟩ := (sem_iff hV).1 hVD
  obtain ⟨b, hbM, hbV⟩ : ∃ b, Inc b T M ∧ Inc b T V := by
    rcases h2M with hM' | hM' <;> rcases h2V with hV' | hV'
    · exact ⟨false, hM', hV'⟩
    · exact (not_inc_false_inc_true hT hMt hV hMT hVT h1M h1V hM' hV').elim
    · exact (not_inc_false_inc_true hT hV hMt hVT hMT h1V h1M hV' hM').elim
    · exact ⟨true, hM', hV'⟩
  have hJ : IsTree (join M V) := join_isTree hMt hV
  have hJT : Dominated (join M V) T := join_dominated hMT hVT
  have hJD : DeltaConditions T (join M V) := by
    rw [sem_iff hJ]
    refine ⟨cond1_of_dominated h1M (dominated_join hMt hV), ?_, cond3_join h3M h3V,
      cond3_join h4M h4V⟩
    have hI := inc_join hMt hV h1M h1V hbM hbV (by cases b; exacts [h3M, h4M])
      (by cases b; exacts [h3V, h4V])
    cases b
    exacts [Or.inl hI, Or.inr hI]
  have hJC : join M V ∈ C :=
    Finset.mem_filter.2 ⟨Finset.mem_powerset.2 (subset_prefixes hJT), hJ, hJT, hJD⟩
  have hMJ : M = join M V :=
    eq_of_dominated_of_card_le hMt hJ (dominated_join hMt hV) (hmax _ hJC)
  rw [hMJ, join_comm]
  exact dominated_join hV hMt

/-! ## Lemma 5.4 -/

/-! ## The action on sequences -/

end MooreFoelner.Dev.Delta

namespace MooreFoelner

open Classical CannonFloydParry
open MooreFoelner.Dev.Delta

end MooreFoelner
end

open MooreFoelner in
open Classical CannonFloydParry MooreFoelner in
open Classical CannonFloydParry in
open MooreFoelner.Dev.Delta in
theorem solution (T : Finset Seq) (hT : IsTree T)
    (h : ∃ U, IsTree U ∧ Dominated U T ∧ DeltaConditions T U) :
    ∃ U, IsTree U ∧ Dominated U T ∧ DeltaConditions T U ∧
      ∀ V, IsTree V → Dominated V T → DeltaConditions T V → Dominated V U :=
  exists_max T hT h
