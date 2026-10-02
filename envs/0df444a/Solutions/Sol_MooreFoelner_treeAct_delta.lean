-- Prove2me | solution 1 for MooreFoelner.treeAct_delta
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-02T08:06:19.810982+00:00
-- url     : https://prove2.me/submissions/493fe3bf-926e-4d17-bc73-02f64de5666e

import Theorems.Thm_MooreFoelner_exists_max_deltaConditions
import Theorems.Thm_MooreFoelner_bijOn_Lf_Rf_and_diagramMul
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

theorem dominated_antisymm {U V : Finset Seq} (hU : IsTree U) (hV : IsTree V)
    (h1 : Dominated U V) (h2 : Dominated V U) : U = V := by
  have key : ∀ {U V : Finset Seq}, IsTree U → Dominated U V → Dominated V U → U ⊆ V := by
    intro U V hU h1 h2 u hu
    obtain ⟨v, hv, huv⟩ := h1 u hu
    obtain ⟨u', hu', hvu'⟩ := h2 v hv
    have := tr_eq hU hu hu' (huv.trans hvu')
    subst this
    have : u = v := huv.eq_of_length (le_antisymm huv.length_le hvu'.length_le)
    exact this ▸ hv
  exact Finset.Subset.antisymm (key hU h1 h2) (key hV h2 h1)

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

theorem D_mono {b : Bool} {u v u' v' : Seq} (h : D b u v) (hu : u <+: u') (hv : v <+: v') :
    D b u' v' := by
  obtain ⟨p, h1, h2⟩ := h
  exact ⟨p, h1.trans hu, h2.trans hv⟩

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

theorem sorted_perm (U : Finset Seq) : (sorted U).Perm U.toList := List.mergeSort_perm _ _

theorem sorted_nodup (U : Finset Seq) : (sorted U).Nodup :=
  (sorted_perm U).nodup_iff.2 U.nodup_toList

theorem length_sorted (U : Finset Seq) : (sorted U).length = U.card := by
  simp [sorted]

theorem nodup_of_pairwise_lt {l : List Seq} (hl : l.Pairwise (· < ·)) : l.Nodup :=
  hl.imp (fun h => ne_of_lt h)

theorem sorted_eq {U : Finset Seq} {l : List Seq} (hl : l.Pairwise (· < ·))
    (hmem : ∀ x, x ∈ l ↔ x ∈ U) : sorted U = l := by
  apply List.Perm.eq_of_pairwise (le := (· < ·))
    (fun a b _ _ h1 h2 => absurd (lt_trans h1 h2) (lt_irrefl a)) (sorted_pairwise U) hl
  rw [List.perm_ext_iff_of_nodup (sorted_nodup U) (nodup_of_pairwise_lt hl)]
  intro x
  rw [mem_sorted, hmem]

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

theorem mem_of_mem_interior {U : Finset Seq} {x : Seq} (h : x ∈ interior U) : x ∈ U :=
  mem_sorted.1 ((interior_sublist U).subset h)

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

/-- Condition 1 of Definition 5.1. -/
def Cond1 (U : Finset Seq) : Prop := ∀ b : Bool, ∃ u ∈ U, [b, !b] <+: u

/-- Condition 3 of Definition 5.1 at the end `b` (`false`: the left end), in structural form:
the extreme element `b^(k+1)` and its sibling `b^k (!b)` both lie in `U`. -/
def Cond3 (b : Bool) (U : Finset Seq) : Prop :=
  ∃ k, List.replicate (k + 1) b ∈ U ∧ List.replicate k b ++ [!b] ∈ U

/-- `c` is the first interior element of `U` in the direction `b`. -/
def First (b : Bool) (U : Finset Seq) (c : Seq) : Prop :=
  IsInt U c ∧ ∀ y, IsInt U y → y ≠ c → D b c y

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

/-! ## The join of two trees -/

/-! ## The orientation of condition 2 -/

/-! ## Lemma 5.2 -/

/-! ## Lemma 5.4 -/

/-! ## The action on sequences -/

theorem append_lt_append_left (p x y : Seq) : p ++ x < p ++ y ↔ x < y := by
  induction p with
  | nil => simp
  | cons a p ih =>
    rw [List.cons_append, List.cons_append, List.cons_lt_cons_iff, ih]
    simp

theorem incomp_append_lt {a b : Seq} (h1 : ¬ a <+: b) (h2 : ¬ b <+: a) (x y : Seq) :
    a ++ x < b ++ y ↔ a < b := by
  rcases D_total false h1 h2 with h | h
  · exact ⟨fun _ => lt_of_D h,
      fun _ => lt_of_D (D_mono h (List.prefix_append a x) (List.prefix_append b y))⟩
  · have hba := lt_of_D h
    have hba' := lt_of_D (D_mono h (List.prefix_append b y) (List.prefix_append a x))
    exact ⟨fun h' => absurd hba' (not_lt.2 h'.le), fun h' => absurd hba (not_lt.2 h'.le)⟩

theorem getElem_lt_iff {l : List Seq} (hl : l.Pairwise (· < ·)) {i j : ℕ} (hi : i < l.length)
    (hj : j < l.length) : l[i] < l[j] ↔ i < j := by
  rw [List.pairwise_iff_getElem] at hl
  constructor
  · intro h
    rcases lt_trichotomy i j with hij | rfl | hij
    · exact hij
    · exact absurd h (lt_irrefl _)
    · exact absurd h (lt_asymm (hl j i hj hi hij))
  · intro hij
    exact hl i j hi hj hij

theorem diagramAct_eq_some_iff {L R : Finset Seq} (hL : IsTree L) (hlen : L.card = R.card)
    (t t' : Seq) :
    diagramAct L R t = some t' ↔ ∃ (i : ℕ) (hi : i < (sorted L).length)
      (hi' : i < (sorted R).length),
      (sorted L)[i] <+: t ∧ t' = (sorted R)[i] ++ t.drop (sorted L)[i].length := by
  have huniq : ∀ i j : Fin (sorted L).length, (sorted L).get i <+: t →
      (sorted L).get j <+: t → i = j := by
    intro i j hi hj
    have hmi : (sorted L).get i ∈ L := mem_sorted.1 (List.get_mem _ _)
    have hmj : (sorted L).get j ∈ L := mem_sorted.1 (List.get_mem _ _)
    have heq : (sorted L).get i = (sorted L).get j := by
      rcases List.prefix_or_prefix_of_prefix hi hj with h | h
      · exact tr_eq hL hmi hmj h
      · exact (tr_eq hL hmj hmi h).symm
    exact (sorted_nodup L).get_inj_iff.1 heq
  have hlen' : (sorted L).length = (sorted R).length := by
    rw [length_sorted, length_sorted, hlen]
  unfold diagramAct
  dsimp only
  constructor
  · intro h
    split at h
    · rename_i i hfind
      have hp := List.find?_some hfind
      simp only [decide_eq_true_eq] at hp
      refine ⟨i.1, i.2, hlen' ▸ i.2, hp, ?_⟩
      rw [List.getElem?_eq_getElem (hlen' ▸ i.2)] at h
      simp only [Option.map_some, Option.some.injEq] at h
      exact h.symm
    · simp at h
  · rintro ⟨i, hi, hi', hp, rfl⟩
    split
    · rename_i j hfind
      have hpj := List.find?_some hfind
      simp only [decide_eq_true_eq] at hpj
      have := huniq j ⟨i, hi⟩ hpj hp
      subst this
      simp [List.getElem?_eq_getElem hi']
    · rename_i hfind
      rw [List.find?_eq_none] at hfind
      exact absurd (by simpa using hp) (hfind ⟨i, hi⟩ (List.mem_finRange _))

/-- `Lf`, `Rf` form a tree diagram (the §2 milestone `bijOn_Lf_Rf_and_diagramMul`). -/
theorem lf_rf (g : MooreF) : IsTreeDiagram (Lf (toMap g)) (Rf (toMap g)) :=
  (MooreFoelner.bijOn_Lf_Rf_and_diagramMul.2.2.2.2.2.2.1 g).1

theorem seqAct_eq_some_iff (g : MooreF) (t t' : Seq) :
    seqAct t g = some t' ↔ ∃ (i : ℕ) (hi : i < (sorted (Lf (toMap g))).length)
      (hi' : i < (sorted (Rf (toMap g))).length),
      (sorted (Lf (toMap g)))[i] <+: t ∧
        t' = (sorted (Rf (toMap g)))[i] ++ t.drop (sorted (Lf (toMap g)))[i].length :=
  diagramAct_eq_some_iff (lf_rf g).1 (lf_rf g).2.2 t t'

theorem seqAct_append {g : MooreF} {u u' : Seq} (h : seqAct u g = some u') (s : Seq) :
    seqAct (u ++ s) g = some (u' ++ s) := by
  obtain ⟨i, hi, hi', hp, rfl⟩ := (seqAct_eq_some_iff g u u').1 h
  refine (seqAct_eq_some_iff g _ _).2 ⟨i, hi, hi', hp.trans (List.prefix_append u s), ?_⟩
  rw [List.drop_append_of_le_length hp.length_le, List.append_assoc]

theorem seqAct_lt {g : MooreF} {u v u' v' : Seq} (hu : seqAct u g = some u')
    (hv : seqAct v g = some v') : u < v ↔ u' < v' := by
  obtain ⟨i, hi, hi', hpi, rfl⟩ := (seqAct_eq_some_iff g u u').1 hu
  obtain ⟨j, hj, hj', hpj, rfl⟩ := (seqAct_eq_some_iff g v v').1 hv
  obtain ⟨x, rfl⟩ := hpi
  obtain ⟨y, rfl⟩ := hpj
  simp only [List.drop_left]
  have hL := (lf_rf g).1
  have hR := (lf_rf g).2.1
  by_cases hij : i = j
  · subst hij
    rw [append_lt_append_left, append_lt_append_left]
  · have hne : ∀ {W : Finset Seq}, IsTree W → ∀ (hi : i < (sorted W).length)
        (hj : j < (sorted W).length),
        ¬ (sorted W)[i] <+: (sorted W)[j] ∧ ¬ (sorted W)[j] <+: (sorted W)[i] := by
      intro W hW hi hj
      have hmi : (sorted W)[i] ∈ W := mem_sorted.1 (List.getElem_mem _)
      have hmj : (sorted W)[j] ∈ W := mem_sorted.1 (List.getElem_mem _)
      have hneq : (sorted W)[i] ≠ (sorted W)[j] := fun h =>
        hij (((sorted_nodup W).getElem_inj_iff).1 h)
      exact ⟨fun h => hneq (tr_eq hW hmi hmj h), fun h => hneq (tr_eq hW hmj hmi h).symm⟩
    obtain ⟨hL1, hL2⟩ := hne hL hi hj
    obtain ⟨hR1, hR2⟩ := hne hR hi' hj'
    rw [incomp_append_lt hL1 hL2, incomp_append_lt hR1 hR2,
      getElem_lt_iff (sorted_pairwise _), getElem_lt_iff (sorted_pairwise _)]

theorem treeAct_eq_some_of {A : Finset Seq} {g : MooreF} (φ : Seq → Seq)
    (h : ∀ t ∈ A, seqAct t g = some (φ t)) : treeAct A g = some (A.image φ) := by
  unfold treeAct
  have hdef : ∀ t ∈ A, (seqAct t g).isSome := fun t ht => by rw [h t ht]; rfl
  rw [dif_pos hdef]
  congr 1
  ext y
  simp only [Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists]
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, ht, by simp [h t ht]⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, ht, by simp [h t ht]⟩

theorem treeAct_some {A B : Finset Seq} {g : MooreF} (h : treeAct A g = some B) :
    (∀ a ∈ A, ∃ b ∈ B, seqAct a g = some b) ∧ (∀ b ∈ B, ∃ a ∈ A, seqAct a g = some b) := by
  unfold treeAct at h
  split_ifs at h with hdef
  simp only [Option.some.injEq] at h
  subst h
  constructor
  · intro a ha
    exact ⟨_, Finset.mem_image.2 ⟨⟨a, ha⟩, Finset.mem_attach _ _, rfl⟩, (Option.some_get _).symm⟩
  · intro b hb
    obtain ⟨⟨a, ha⟩, -, rfl⟩ := Finset.mem_image.1 hb
    exact ⟨a, ha, (Option.some_get _).symm⟩

theorem treeAct_singleton {g : MooreF} {t t' : Seq} :
    treeAct {t} g = some {t'} ↔ seqAct t g = some t' := by
  constructor
  · intro h
    obtain ⟨b, hb, hb'⟩ := (treeAct_some h).1 t (Finset.mem_singleton_self t)
    rw [Finset.mem_singleton] at hb
    rw [hb'] at *
    rw [hb]
  · intro h
    rw [treeAct_eq_some_of (fun _ => t') (fun s hs => by rw [Finset.mem_singleton.1 hs]; exact h)]
    simp

theorem seqAct_inv {g : MooreF} {t t' : Seq} (h : seqAct t g = some t') :
    seqAct t' g⁻¹ = some t := by
  rw [← treeAct_singleton] at h ⊢
  exact ((MooreFoelner.isTree_treeAct_and_isPartialAction).2.inv g {t} {t'}).1 h

theorem seqAct_inj {g : MooreF} {a b c : Seq} (ha : seqAct a g = some c)
    (hb : seqAct b g = some c) : a = b := by
  have := seqAct_inv ha
  rw [seqAct_inv hb] at this
  exact (Option.some.inj this).symm

/-- The image of `t` under `g` (junk when undefined). -/
noncomputable def img (g : MooreF) (t : Seq) : Seq := (seqAct t g).getD []

theorem img_eq {g : MooreF} {t t' : Seq} (h : seqAct t g = some t') : img g t = t' := by
  simp [img, h]

theorem card_le_two {W : Finset Seq} (hW : IsTree W) {b : Bool} (h1 : [b] ∈ W) (h2 : [!b] ∈ W) :
    W.card ≤ 2 := by
  have hsub : W ⊆ {[b], [!b]} := by
    intro w hw
    cases w with
    | nil =>
      have := tr_eq hW hw h1 (List.nil_prefix)
      simp at this
    | cons c w =>
      have hc : [c] <+: c :: w := by simp
      have hmem : [c] ∈ W := by
        cases b <;> cases c <;> simp_all
      have := tr_eq hW hmem hw hc
      rw [← this]
      cases b <;> cases c <;> simp
  calc W.card ≤ ({[b], [!b]} : Finset Seq).card := Finset.card_le_card hsub
    _ ≤ 2 := Finset.card_le_two

theorem cond1_of_cond3 {W : Finset Seq} (hW : IsTree W) (h3 : 3 ≤ W.card) (hL : Cond3 false W)
    (hR : Cond3 true W) : Cond1 W := by
  have key : ∀ b : Bool, Cond3 b W → ∃ u ∈ W, [b, !b] <+: u := by
    intro b ⟨k, hk1, hk2⟩
    have hk : k ≠ 0 := by
      rintro rfl
      have := card_le_two hW (b := b) (by simpa using hk1) (by simpa using hk2)
      omega
    obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
    obtain ⟨u, hu, hpu⟩ := tr_sib hW (p := [b]) (b := b)
      ⟨_, hk1, by simp [List.replicate_succ]⟩ (!b)
    exact ⟨u, hu, by simpa using hpu⟩
  intro b
  cases b
  · exact key false hL
  · exact key true hR

theorem three_le_card {U : Finset Seq} (h3 : (interior U).head?.bind List.getLast? = some true) :
    3 ≤ U.card := by
  obtain ⟨c, hc, -⟩ := Option.bind_eq_some_iff.1 h3
  have hne : interior U ≠ [] := by
    intro h
    rw [h] at hc
    simp at hc
  have hlen : (interior U).length ≠ 0 := by simpa using hne
  unfold interior at hlen
  rw [← length_sorted]
  simp at hlen
  omega

/-- The forward half of Lemma 5.5: if `g` acts properly on a tree `U` satisfying the defining
conditions for `∂T`, then `U · g` satisfies the defining conditions for `∂(T · g)`. -/
theorem fwd {T U : Finset Seq} (hT : IsTree T) (hU : IsTree U) (hUT : Dominated U T)
    (hD : DeltaConditions T U) {g : MooreF} (hg : ActsProperlyOn g U) :
    treeAct T g = some (T.image (img g)) ∧ treeAct U g = some (U.image (img g)) ∧
      IsTree (T.image (img g)) ∧ IsTree (U.image (img g)) ∧
      Dominated (U.image (img g)) (T.image (img g)) ∧
      DeltaConditions (T.image (img g)) (U.image (img g)) := by
  have hUact : ∀ u ∈ U, seqAct u g = some (img g u) ∧ (img g u).getLast? = u.getLast? := by
    intro u hu
    obtain ⟨t', h1, h2⟩ := hg u hu
    rw [img_eq h1]
    exact ⟨h1, h2⟩
  have hext : ∀ u ∈ U, ∀ s, seqAct (u ++ s) g = some (img g u ++ s) :=
    fun u hu s => seqAct_append (hUact u hu).1 s
  have hTact : ∀ t ∈ T, seqAct t g = some (img g t) := by
    intro t ht
    obtain ⟨u, hu, s, rfl⟩ := exists_prefix_of_dominated hU hT hUT ht
    rw [hext u hu s, img_eq (hext u hu s)]
  have hTT := treeAct_eq_some_of (img g) hTact
  have hUU := treeAct_eq_some_of (img g) (fun u hu => (hUact u hu).1)
  have hT' := (MooreFoelner.isTree_treeAct_and_isPartialAction).1 _ _ _ hT hTT
  have hU' := (MooreFoelner.isTree_treeAct_and_isPartialAction).1 _ _ _ hU hUU
  refine ⟨hTT, hUU, hT', hU', ?_, ?_⟩
  · intro y hy
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hy
    obtain ⟨t, ht, s, rfl⟩ := hUT u hu
    exact ⟨img g (u ++ s), Finset.mem_image.2 ⟨_, ht, rfl⟩,
      by rw [img_eq (hext u hu s)]; exact List.prefix_append _ _⟩
  -- injectivity and order
  have hinjT : Set.InjOn (img g) T := by
    intro a ha b hb hab
    exact seqAct_inj (hTact a ha) (hab ▸ hTact b hb)
  have hinjU : Set.InjOn (img g) U := by
    intro a ha b hb hab
    exact seqAct_inj (hUact a ha).1 (hab ▸ (hUact b hb).1)
  have hsorted : sorted (U.image (img g)) = (sorted U).map (img g) := by
    apply sorted_eq
    · rw [List.pairwise_map]
      exact (sorted_pairwise U).imp_of_mem (fun ha hb hab =>
        (seqAct_lt (hUact _ (mem_sorted.1 ha)).1 (hUact _ (mem_sorted.1 hb)).1).1 hab)
    · intro x
      simp [mem_sorted]
  have hint : interior (U.image (img g)) = (interior U).map (img g) := by
    unfold interior
    rw [hsorted, List.map_dropLast, List.map_drop]
  -- the quotients
  have hquot : ∀ u ∈ U, (quot (T.image (img g)) (img g u)).card = (quot T u).card := by
    intro u hu
    rw [card_quot, card_quot]
    have hfilter : (T.image (img g)).filter (img g u <+: ·) =
        (T.filter (u <+: ·)).image (img g) := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨⟨t, ht, rfl⟩, hpre⟩
        refine ⟨t, ⟨ht, ?_⟩, rfl⟩
        obtain ⟨u', hu', s, rfl⟩ := exists_prefix_of_dominated hU hT hUT ht
        rw [img_eq (hext u' hu' s)] at hpre
        have hu'U' : img g u' ∈ U.image (img g) := Finset.mem_image.2 ⟨u', hu', rfl⟩
        have huU' : img g u ∈ U.image (img g) := Finset.mem_image.2 ⟨u, hu, rfl⟩
        have heq : img g u = img g u' := by
          rcases List.prefix_or_prefix_of_prefix hpre (List.prefix_append (img g u') s) with h | h
          · exact tr_eq hU' huU' hu'U' h
          · exact (tr_eq hU' hu'U' huU' h).symm
        rw [hinjU hu hu' heq]
        exact List.prefix_append _ _
      · rintro ⟨t, ⟨ht, s, rfl⟩, rfl⟩
        refine ⟨⟨u ++ s, ht, rfl⟩, ?_⟩
        rw [img_eq (hext u hu s)]
        exact List.prefix_append _ _
    rw [hfilter, Finset.card_image_of_injOn (hinjT.mono (Finset.filter_subset _ _))]
  have hcard : (U.image (img g)).card = U.card := Finset.card_image_of_injOn hinjU
  obtain ⟨-, -, h2, h3, h4⟩ := hD
  have hint_mem : ∀ {x}, x ∈ interior U → x ∈ U := fun hx => mem_of_mem_interior hx
  -- conditions 2 and 3
  have h2' : (∀ i j (hi : i < (interior (U.image (img g))).length)
      (hj : j < (interior (U.image (img g))).length), i < j →
      2 * (quot (T.image (img g)) ((interior (U.image (img g))).get ⟨i, hi⟩)).card ≤
        (quot (T.image (img g)) ((interior (U.image (img g))).get ⟨j, hj⟩)).card) ∨
    (∀ i j (hi : i < (interior (U.image (img g))).length)
      (hj : j < (interior (U.image (img g))).length), i < j →
      2 * (quot (T.image (img g)) ((interior (U.image (img g))).get ⟨j, hj⟩)).card ≤
        (quot (T.image (img g)) ((interior (U.image (img g))).get ⟨i, hi⟩)).card) := by
    rw [hint]
    rcases h2 with h | h
    · left
      intro i j hi hj hij
      simp only [List.get_eq_getElem, List.getElem_map]
      rw [hquot _ (hint_mem (List.getElem_mem _)), hquot _ (hint_mem (List.getElem_mem _))]
      have := h i j (by simpa using hi) (by simpa using hj) hij
      simpa using this
    · right
      intro i j hi hj hij
      simp only [List.get_eq_getElem, List.getElem_map]
      rw [hquot _ (hint_mem (List.getElem_mem _)), hquot _ (hint_mem (List.getElem_mem _))]
      have := h i j (by simpa using hi) (by simpa using hj) hij
      simpa using this
  have h3' : (interior (U.image (img g))).head?.bind List.getLast? = some true := by
    rw [hint]
    obtain ⟨c, hc, hcl⟩ := Option.bind_eq_some_iff.1 h3
    refine Option.bind_eq_some_iff.2 ⟨img g c, by rw [List.head?_map, hc]; rfl, ?_⟩
    rw [(hUact c (hint_mem (List.mem_of_mem_head? hc))).2]
    exact hcl
  have h4' : (interior (U.image (img g))).getLast?.bind List.getLast? = some false := by
    rw [hint]
    obtain ⟨c, hc, hcl⟩ := Option.bind_eq_some_iff.1 h4
    refine Option.bind_eq_some_iff.2 ⟨img g c, by rw [List.getLast?_map, hc]; rfl, ?_⟩
    rw [(hUact c (hint_mem (List.mem_of_getLast? hc))).2]
    exact hcl
  -- condition 1
  have h1' : Cond1 (U.image (img g)) := by
    have h3c := three_le_card h3
    obtain ⟨c, hc, hcl⟩ := (head_iff hU').1 h3'
    obtain ⟨d, hd, hdl⟩ := (last_iff hU').1 h4'
    exact cond1_of_cond3 hU' (by omega) (cond3_of_first hU' hc hcl) (cond3_of_first hU' hd hdl)
  obtain ⟨h01, h10⟩ := (cond1_iff _).2 h1'
  exact ⟨h01, h10, h2', h3', h4'⟩

theorem delta_spec {T : Finset Seq} (hT : IsTree T)
    (h : ∃ U, IsTree U ∧ Dominated U T ∧ DeltaConditions T U) :
    IsTree (delta T) ∧ Dominated (delta T) T ∧ DeltaConditions T (delta T) ∧
      ∀ V, IsTree V → Dominated V T → DeltaConditions T V → Dominated V (delta T) := by
  have h' := MooreFoelner.exists_max_deltaConditions T hT h
  rw [delta, dif_pos h']
  exact Classical.choose_spec h'

theorem delta_triv {T : Finset Seq}
    (h : ¬ ∃ U, IsTree U ∧ Dominated U T ∧ DeltaConditions T U) : delta T = trivialTree := by
  rw [delta, dif_neg]
  rintro ⟨U, hU, hUT, hUD, -⟩
  exact h ⟨U, hU, hUT, hUD⟩

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
theorem solution (g : MooreF) (T : Finset Seq) (hT : IsTree T)
    (hg : ActsProperlyOn g (delta T)) :
    ∃ T', treeAct T g = some T' ∧ IsTree T' ∧ treeAct (delta T) g = some (delta T') := by
  have hPA := (MooreFoelner.isTree_treeAct_and_isPartialAction).2
  by_cases hc : ∃ U, IsTree U ∧ Dominated U T ∧ DeltaConditions T U
  · obtain ⟨hU, hUT, hUD, hUmax⟩ := delta_spec hT hc
    obtain ⟨hTT, hUU, hT', hU', hU'T', hU'D⟩ := fwd hT hU hUT hUD hg
    refine ⟨T.image (img g), hTT, hT', ?_⟩
    rw [hUU]
    congr 1
    obtain ⟨hV, hVT', hVD, hVmax⟩ :=
      delta_spec hT' ⟨_, hU', hU'T', hU'D⟩
    have hU'V := hVmax _ hU' hU'T' hU'D
    -- `g⁻¹` acts properly on `∂(T · g)`
    have hginv : ActsProperlyOn g⁻¹ (delta (T.image (img g))) := by
      intro v hv
      obtain ⟨u', hu', s, rfl⟩ := exists_prefix_of_dominated hU' hV hU'V hv
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hu'
      obtain ⟨t', h1, h2⟩ := hg u hu
      rw [img_eq h1]
      refine ⟨u ++ s, seqAct_append (seqAct_inv h1) s, ?_⟩
      by_cases hs : s = []
      · subst hs
        simpa using h2.symm
      · rw [List.getLast?_append_of_ne_nil _ hs, List.getLast?_append_of_ne_nil _ hs]
    obtain ⟨hTT2, hVV, -, hV'', hV''T2, hV''D⟩ := fwd hT' hV hVT' hVD hginv
    have hback : (T.image (img g)).image (img g⁻¹) = T := by
      have := (hPA.inv g _ _).1 hTT
      rw [hTT2] at this
      exact Option.some.inj this
    rw [hback] at hV''T2 hV''D
    have hV''U := hUmax _ hV'' hV''T2 hV''D
    have hVg : treeAct ((delta (T.image (img g))).image (img g⁻¹)) g =
        some (delta (T.image (img g))) := by
      have := (hPA.inv g⁻¹ _ _).1 hVV
      rwa [inv_inv] at this
    have hVU' : Dominated (delta (T.image (img g))) ((delta T).image (img g)) := by
      intro v hv
      obtain ⟨v'', hv'', hv''v⟩ := (treeAct_some hVg).2 v hv
      obtain ⟨u, hu, s, rfl⟩ := hV''U v'' hv''
      have h1 := seqAct_append hv''v s
      obtain ⟨t', h2, -⟩ := hg _ hu
      rw [h1] at h2
      refine ⟨img g (v'' ++ s), Finset.mem_image.2 ⟨_, hu, rfl⟩, ?_⟩
      rw [img_eq h1]
      exact List.prefix_append _ _
    exact dominated_antisymm hU' hV hU'V hVU'
  · rw [delta_triv hc] at hg ⊢
    obtain ⟨t', h1, h2⟩ := hg [] (Finset.mem_singleton_self _)
    have ht' : t' = [] := by simpa using h2
    subst ht'
    have hid : ∀ t, seqAct t g = some t := fun t => by simpa using seqAct_append h1 t
    refine ⟨T, ?_, hT, ?_⟩
    · rw [treeAct_eq_some_of id (fun t _ => hid t), Finset.image_id]
    · rw [delta_triv hc, treeAct_eq_some_of id (fun t _ => hid t), Finset.image_id]
