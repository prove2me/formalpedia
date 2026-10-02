-- Prove2me | solution 1 for MooreFoelner.isMarginal_EBad
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-02T08:22:59.113989+00:00
-- url     : https://prove2.me/submissions/8bfa6505-7daf-4c6e-a65a-3d3ec8d36f27

import Theorems.Thm_MooreFoelner_isMarginal_union_subset_image
import Theorems.Thm_MooreFoelner_bijOn_Lf_Rf_and_diagramMul
import Theorems.Thm_MooreFoelner_isReducedDiagram_iff
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
# Moore 2013, §5 (pp. 14–18): the marginal sets of Lemmas 5.7, 5.10, 5.12, Lemma 5.9 and Lemma 5.13

Development for the prover group `Sec5Marg`.

* The reduced tree diagrams of `x₀`, `x₁`, `a`, `b`, `c`, `d` are identified with the diagrams
  that define them (via milestones #4 and #5 and an explicit check that the dyadic intervals of the
  domain tree tile `[0,1]`), which gives the action of each element on finite sequences.
* Lemma 5.12 uses, in place of Moore's `g = (U, R)` (whose diagram is not reduced: its last two
  leaves form a common caret), the element `elemG` with reduced diagram
  `U' = {length-4 sequences} \ {1110, 1111} ∪ {111}` → right comb with 15 leaves; trees with the
  leaf `111` are excluded through the sets where `x₁⁻¹` and `x₁⁻²` are undefined. `E**` is
  taken with `i ≤ 13` (Moore: `i ≤ 16`), which is what the 14 interior leaves of `U` need.
* Lemma 5.9, last clause: trees with `|T/01| = 0` lie in `ℰ` but satisfy `(2×)`, so `ℰ ⊄ ℰ*`;
  the proof checks that one generator step from a `(−)` tree never reaches such a tree.
* Moore's "`x₀` marginalizes `E₅` off `E₄ ∪ E`" is used in the form "`x₀` marginalizes `E₅ \ E₄`
  off `E₄ ∪ E`" (Definition 3.6 starts at `i = 0`); likewise for `E₇`.
-/

namespace MooreFoelner.Dev.Sec5Marg

open Classical CannonFloydParry MooreFoelner

/-! ### Sorting -/

theorem mergeSort_congr {α : Type*} {r s : α → α → Bool} :
    ∀ {l : List α}, l.Nodup → (∀ a ∈ l, ∀ b ∈ l, a ≠ b → r a b = s a b) →
      l.mergeSort r = l.mergeSort s
  | [], _, _ => by simp
  | [x], _, _ => by simp
  | a :: b :: l, hnd, h => by
    simp only [List.mergeSort, List.MergeSort.Internal.splitInTwo_fst,
      List.MergeSort.Internal.splitInTwo_snd]
    have h1 := hnd.sublist (List.take_sublist (((a :: b :: l).length + 1) / 2) (a :: b :: l))
    have h2 := hnd.sublist (List.drop_sublist (((a :: b :: l).length + 1) / 2) (a :: b :: l))
    rw [mergeSort_congr h1 (fun x hx y hy hxy => h x (List.mem_of_mem_take hx) y
      (List.mem_of_mem_take hy) hxy)]
    rw [mergeSort_congr h2 (fun x hx y hy hxy => h x (List.mem_of_mem_drop hx) y
      (List.mem_of_mem_drop hy) hxy)]
    have key : ∀ (xs ys : List α), (∀ x ∈ xs, ∀ y ∈ ys, r x y = s x y) →
        xs.merge ys r = xs.merge ys s := by
      intro xs ys hxy
      have := List.map_merge (f := id) (r := r) (s := s) (l := xs) (l' := ys) hxy
      simpa using this
    apply key
    intro x hx y hy
    rw [List.mem_mergeSort] at hx hy
    apply h x (List.mem_of_mem_take hx) y (List.mem_of_mem_drop hy)
    rintro rfl
    have := List.disjoint_take_drop hnd (le_refl (((a :: b :: l).length + 1) / 2))
    exact this hx hy
  termination_by l => l.length

theorem lexLt_iff (u v : Seq) : LexLt u v ↔ u < v := (List.lt_iff_lex_lt u v).symm

theorem lexLt_irrefl (u : Seq) : ¬ LexLt u u := by rw [lexLt_iff]; exact lt_irrefl u
theorem lexLt_trans {u v w : Seq} : LexLt u v → LexLt v w → LexLt u w := by
  simp only [lexLt_iff]; exact lt_trans
theorem lexLt_asymm {u v : Seq} : LexLt u v → ¬ LexLt v u := by
  simp only [lexLt_iff]; exact fun h h' => lt_asymm h h'
theorem lexLt_trichotomous (u v : Seq) : LexLt u v ∨ u = v ∨ LexLt v u := by
  simp only [lexLt_iff]; exact lt_trichotomy u v

theorem sorted_eq (T : Finset Seq) (l : List Seq) (hl : l.Pairwise LexLt) (hT : l.toFinset = T) :
    sorted T = l := by
  have hnd : T.toList.Nodup := Finset.nodup_toList T
  unfold sorted
  rw [mergeSort_congr (s := fun u v => decide (LexLt u v ∨ u = v)) hnd (by
    intro a _ b _ hab
    simp [hab])]
  have hp := List.pairwise_mergeSort (le := fun u v => decide (LexLt u v ∨ u = v))
    (by
      intro a b c hab hbc
      simp only [decide_eq_true_eq] at *
      rcases hab with hab | rfl
      · rcases hbc with hbc | rfl
        · exact Or.inl (lexLt_trans hab hbc)
        · exact Or.inl hab
      · exact hbc)
    (by
      intro a b
      rcases lexLt_trichotomous a b with h | h | h <;> simp [h]) T.toList
  have hperm := List.mergeSort_perm T.toList (fun u v => decide (LexLt u v ∨ u = v))
  have hnd2 := hperm.nodup_iff.mpr hnd
  have hp2 : (T.toList.mergeSort (fun u v => decide (LexLt u v ∨ u = v))).Pairwise LexLt := by
    have := hp.and hnd2
    refine this.imp ?_
    rintro a b ⟨h1, h2⟩
    simp only [decide_eq_true_eq] at h1
    rcases h1 with h1 | h1
    · exact h1
    · exact absurd h1 h2
  apply List.Perm.eq_of_pairwise (le := LexLt) _ hp2 hl
  · refine hperm.trans ?_
    rw [← hT]
    apply List.perm_of_nodup_nodup_toFinset_eq (Finset.nodup_toList _) _ (by simp)
    exact hl.imp (fun h h' => by subst h'; exact lexLt_irrefl _ h)
  · intro a b _ _ h1 h2
    exact absurd h2 (lexLt_asymm h1)

theorem length_sorted (T : Finset Seq) : (sorted T).length = T.card := by
  unfold sorted; simp

/-! ### Initial parts and trees -/

/-- The extension of a finite sequence by zeros. -/
def ext0 (u : Seq) : ℕ → Bool := fun n => u.getD n false

theorem isInitialPart_ext0_of_prefix {u v : Seq} (h : u <+: v) : IsInitialPart u (ext0 v) := by
  intro i hi
  obtain ⟨w, rfl⟩ := h
  simp [ext0, List.getD_eq_getElem?_getD, List.getElem?_append_left hi, List.getElem?_eq_getElem hi]

theorem isInitialPart_ext0 (u : Seq) : IsInitialPart u (ext0 u) :=
  isInitialPart_ext0_of_prefix (List.prefix_refl u)

theorem prefix_of_isInitialPart {u v : Seq} {x : ℕ → Bool} (hu : IsInitialPart u x)
    (hv : IsInitialPart v x) (hle : u.length ≤ v.length) : u <+: v := by
  rw [List.prefix_iff_eq_take]
  apply List.ext_getElem
  · simp; omega
  · intro n h1 h2
    simp only [List.getElem_take]
    have := hu n h1
    have h' := hv n (by omega)
    simp only [List.get_eq_getElem] at this h'
    rw [this, h']

theorem isInitialPart_of_prefix {u v : Seq} {x : ℕ → Bool} (h : u <+: v)
    (hv : IsInitialPart v x) : IsInitialPart u x := by
  intro i hi
  obtain ⟨w, rfl⟩ := h
  have := hv i (by simp; omega)
  simp only [List.get_eq_getElem, List.getElem_append_left hi] at this ⊢
  exact this

theorem IsTree.exists_mem {T : Finset Seq} (hT : IsTree T) (x : ℕ → Bool) :
    ∃ t ∈ T, IsInitialPart t x := by
  obtain ⟨t, ⟨h1, h2⟩, _⟩ := hT x
  exact ⟨t, h1, h2⟩

theorem IsTree.eq_of_prefix {T : Finset Seq} (hT : IsTree T) {u v : Seq} (hu : u ∈ T)
    (hv : v ∈ T) (h : u <+: v) : u = v := by
  obtain ⟨t, _, ht⟩ := hT (ext0 v)
  have h1 := ht u ⟨hu, isInitialPart_ext0_of_prefix h⟩
  have h2 := ht v ⟨hv, isInitialPart_ext0 v⟩
  rw [h1, h2]

/-- A list of sequences no two of which are comparable under `<+:`. -/
def Antichain (l : List Seq) : Prop := ∀ u ∈ l, ∀ v ∈ l, u <+: v → u = v

/-- If every leaf of the tree `T` extends an element of the antichain `l`, then every element of
`l` is extended by a leaf of `T`. -/
theorem IsTree.exists_extends {T : Finset Seq} (hT : IsTree T) {l : List Seq} (hl : Antichain l)
    (hdom : ∀ t ∈ T, ∃ u ∈ l, u <+: t) {w : Seq} (hw : w ∈ l) : ∃ t ∈ T, w <+: t := by
  obtain ⟨t, htT, ht⟩ := IsTree.exists_mem hT (ext0 w)
  obtain ⟨u, hul, hut⟩ := hdom t htT
  have hu := isInitialPart_of_prefix hut ht
  have hw' := isInitialPart_ext0 w
  rcases le_total u.length w.length with hle | hle
  · have := hl u hul w hw (prefix_of_isInitialPart hu hw' hle)
    subst this; exact ⟨t, htT, hut⟩
  · have := hl w hw u hul (prefix_of_isInitialPart hw' hu hle)
    subst this; exact ⟨t, htT, hut⟩

/-! ### Building concrete trees -/

/-- `l` lists the leaves of a tree in increasing lexicographic order. -/
def Good (l : List Seq) : Prop := l.Pairwise LexLt ∧ IsTree l.toFinset

/-- The tree with left subtree `l₁` and right subtree `l₂`. -/
def joinL (l₁ l₂ : List Seq) : List Seq := l₁.map (false :: ·) ++ l₂.map (true :: ·)

theorem good_leaf : Good [[]] := by
  refine ⟨by simp, ?_⟩
  intro x
  refine ⟨[], ⟨by simp, fun i hi => by simp at hi⟩, ?_⟩
  intro t ⟨ht, _⟩
  simpa using ht

theorem lexLt_cons_cons (a : Bool) (u v : Seq) : LexLt (a :: u) (a :: v) ↔ LexLt u v := by
  unfold LexLt
  constructor
  · intro h
    cases h with
    | cons h => exact h
    | rel h => exact absurd h (lt_irrefl a)
  · intro h; exact List.Lex.cons h

theorem isInitialPart_cons (b : Bool) (u : Seq) (x : ℕ → Bool) :
    IsInitialPart (b :: u) x ↔ x 0 = b ∧ IsInitialPart u (fun n => x (n+1)) := by
  constructor
  · intro h
    refine ⟨(h 0 (by simp)).symm, fun i hi => ?_⟩
    have := h (i+1) (by simp; omega)
    simpa using this
  · rintro ⟨h0, h⟩ i hi
    cases i with
    | zero => simpa using h0.symm
    | succ i =>
      have := h i (by simp at hi; omega)
      simpa using this

theorem good_join {l₁ l₂ : List Seq} (h₁ : Good l₁) (h₂ : Good l₂) : Good (joinL l₁ l₂) := by
  refine ⟨?_, ?_⟩
  · unfold joinL
    rw [List.pairwise_append]
    refine ⟨?_, ?_, ?_⟩
    · rw [List.pairwise_map]
      exact h₁.1.imp (fun h => (lexLt_cons_cons _ _ _).mpr h)
    · rw [List.pairwise_map]
      exact h₂.1.imp (fun h => (lexLt_cons_cons _ _ _).mpr h)
    · intro a ha b hb
      simp only [List.mem_map] at ha hb
      obtain ⟨u, _, rfl⟩ := ha
      obtain ⟨v, _, rfl⟩ := hb
      exact List.Lex.rel (by decide)
  · intro x
    have hmem : ∀ t, t ∈ (joinL l₁ l₂).toFinset ↔
        (∃ u ∈ l₁, t = false :: u) ∨ (∃ u ∈ l₂, t = true :: u) := by
      intro t; simp [joinL, eq_comm]
    cases hx : x 0
    · obtain ⟨t1, ⟨ht1, hi1⟩, hu1⟩ := h₁.2 (fun n => x (n+1))
      refine ⟨false :: t1, ⟨(hmem _).mpr (Or.inl ⟨t1, by simpa using ht1, rfl⟩),
        (isInitialPart_cons _ _ _).mpr ⟨hx, hi1⟩⟩, ?_⟩
      rintro t ⟨ht, hit⟩
      rcases (hmem t).mp ht with ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩
      · rw [isInitialPart_cons] at hit
        rw [hu1 u ⟨by simpa using hu, hit.2⟩]
      · rw [isInitialPart_cons, hx] at hit
        exact absurd hit.1 (by decide)
    · obtain ⟨t1, ⟨ht1, hi1⟩, hu1⟩ := h₂.2 (fun n => x (n+1))
      refine ⟨true :: t1, ⟨(hmem _).mpr (Or.inr ⟨t1, by simpa using ht1, rfl⟩),
        (isInitialPart_cons _ _ _).mpr ⟨hx, hi1⟩⟩, ?_⟩
      rintro t ⟨ht, hit⟩
      rcases (hmem t).mp ht with ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩
      · rw [isInitialPart_cons, hx] at hit
        exact absurd hit.1 (by decide)
      · rw [isInitialPart_cons] at hit
        rw [hu1 u ⟨by simpa using hu, hit.2⟩]

theorem Good.nodup {l : List Seq} (h : Good l) : l.Nodup :=
  h.1.imp (fun h h' => by subst h'; exact lexLt_irrefl _ h)

theorem Good.antichain {l : List Seq} (h : Good l) : Antichain l := by
  intro u hu v hv huv
  exact IsTree.eq_of_prefix h.2 (by simpa using hu) (by simpa using hv) huv

theorem Good.sorted {l : List Seq} (h : Good l) : MooreFoelner.sorted l.toFinset = l :=
  sorted_eq _ l h.1 rfl

/-! ### Dyadic values and coverage -/

theorem seqVal_nil : seqVal [] = 0 := by simp [seqVal]

theorem seqVal_cons (b : Bool) (u : Seq) :
    seqVal (b :: u) = (if b then 1/2 else 0) + seqVal u / 2 := by
  unfold seqVal
  erw [Fin.sum_univ_succ (n := u.length)]
  simp only [List.length_cons, Fin.val_zero, zero_add, pow_one, List.get_eq_getElem,
    Fin.val_succ, List.getElem_cons_zero, List.getElem_cons_succ]
  congr 1
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  split_ifs <;> ring

/-- The dyadic intervals of the elements of `l`, in order, tile `[a, 1]`. -/
def Covers : List Seq → ℝ → Prop
  | [], a => a = 1
  | u :: l, a => seqVal u = a ∧ Covers l (a + (1/2 : ℝ) ^ u.length)

theorem covers_exists : ∀ (l : List Seq) (a x : ℝ), Covers l a → a ≤ x → x ≤ 1 → l ≠ [] →
    ∃ i, ∃ h : i < l.length, seqVal l[i] ≤ x ∧ x ≤ seqVal l[i] + (1/2 : ℝ) ^ l[i].length
  | [], _, _, _, _, _, h => absurd rfl h
  | u :: l, a, x, hc, hax, hx1, _ => by
    obtain ⟨hu, hl⟩ := hc
    by_cases hx : x ≤ a + (1/2 : ℝ) ^ u.length
    · refine ⟨0, by simp, ?_, ?_⟩
      · simp only [List.getElem_cons_zero]; rw [hu]; exact hax
      · simp only [List.getElem_cons_zero]; rw [hu]; exact hx
    · push Not at hx
      cases l with
      | nil => simp only [Covers] at hl; linarith
      | cons v l =>
        obtain ⟨i, hi, h1, h2⟩ := covers_exists (v :: l) _ x hl hx.le hx1 (by simp)
        exact ⟨i + 1, by simp at hi ⊢; omega, by simpa using h1, by simpa using h2⟩

theorem describes_unique {L R : Finset Seq} (hcov : Covers (sorted L) 0) (hne : sorted L ≠ [])
    {f g : UI ≃o UI} (hf : Describes L R f) (hg : Describes L R g) : f = g := by
  apply DFunLike.ext f g
  intro x
  apply Subtype.ext
  obtain ⟨i, hi, h1, h2⟩ := covers_exists (sorted L) 0 x hcov x.2.1 x.2.2 hne
  have hR : i < (sorted R).length := by
    rw [length_sorted, ← hf.1.2.2, ← length_sorted]; exact hi
  rw [hf.2 i hi hR x h1 h2, hg.2 i hi hR x h1 h2]

/-! ### Reduced diagrams -/

/-- No common caret, as a Boolean check on the sorted leaf lists. -/
def noCaret : List Seq → List Seq → Bool
  | a :: a' :: l, b :: b' :: l' =>
    !(a.getLast? == some false && b.getLast? == some false && a'.getLast? == some true &&
      b'.getLast? == some true) && noCaret (a' :: l) (b' :: l')
  | _, _ => true

theorem noCaret_spec : ∀ (l l' : List Seq), noCaret l l' = true →
    ¬ ∃ (i : ℕ) (hi : i + 1 < l.length) (hi' : i + 1 < l'.length),
      l[i].getLast? = some false ∧ l'[i].getLast? = some false ∧
      l[i+1].getLast? = some true ∧ l'[i+1].getLast? = some true
  | a :: a' :: l, b :: b' :: l', h => by
    simp only [noCaret, Bool.and_eq_true, Bool.not_eq_true'] at h
    rintro ⟨i, hi, hi', h1, h2, h3, h4⟩
    cases i with
    | zero =>
      simp at h1 h2 h3 h4
      simp [h1, h2, h3, h4] at h
    | succ i =>
      apply noCaret_spec (a' :: l) (b' :: l') h.2
      exact ⟨i, by simp at hi ⊢; omega, by simp at hi' ⊢; omega, by simpa using h1,
        by simpa using h2, by simpa using h3, by simpa using h4⟩
  | [], _, _ => by simp
  | [_], _, _ => by simp
  | _ :: _ :: _, [], _ => by simp
  | _ :: _ :: _, [_], _ => by simp

theorem isReduced_of {lL lR : List Seq} (hL : Good lL) (hR : Good lR)
    (hlen : lL.length = lR.length) (hnc : noCaret lL lR = true) :
    IsReducedDiagram lL.toFinset lR.toFinset := by
  have htd : IsTreeDiagram lL.toFinset lR.toFinset := by
    refine ⟨hL.2, hR.2, ?_⟩
    rw [List.toFinset_card_of_nodup hL.nodup, List.toFinset_card_of_nodup hR.nodup, hlen]
  rw [isReducedDiagram_iff _ _ htd]
  simp only [List.get_eq_getElem]
  simp only [hL.sorted, hR.sorted]
  exact noCaret_spec _ _ hnc

theorem LR_ofDiagram {L R : Finset Seq} (hred : IsReducedDiagram L R)
    (hcov : Covers (sorted L) 0) (hne : sorted L ≠ []) :
    Lf (toMap (ofDiagram L R)) = L ∧ Rf (toMap (ofDiagram L R)) = R := by
  obtain ⟨-, -, -, -, -, hbij, hdesc, -⟩ := bijOn_Lf_Rf_and_diagramMul
  obtain ⟨g, -, hg⟩ := hbij.surjOn (show (L, R) ∈ {D : Finset Seq × Finset Seq |
    IsReducedDiagram D.1 D.2} from hred)
  simp only [Prod.mk.injEq] at hg
  have hdg : Describes L R (toMap g) := by
    have := hdesc g; rw [hg.1, hg.2] at this; exact this
  have hex : ∃ f : F, Describes L R (f : UI ≃o UI) := ⟨MulOpposite.unop g, hdg⟩
  have hspec := Classical.epsilon_spec hex
  have : toMap (ofDiagram L R) = toMap g := describes_unique hcov hne hspec hdg
  rw [this]; exact hg

/-! ### The action of a diagram on finite sequences -/

/-- The body of `diagramAct`, as a function of the two sorted lists. -/
noncomputable def dAct (S T : List Seq) (t : Seq) : Option Seq :=
  match (List.finRange S.length).find? (fun i => decide (S.get i <+: t)) with
  | some i => (T[i.1]?).map (· ++ t.drop (S.get i).length)
  | none => none

theorem diagramAct_eq_dAct (L R : Finset Seq) (t : Seq) :
    diagramAct L R t = dAct (sorted L) (sorted R) t := rfl

theorem dAct_spec (S T : List Seq) (hlen : S.length = T.length) (hanti : Antichain S)
    (hnd : S.Nodup) (t t' : Seq) :
    dAct S T t = some t' ↔ ∃ p ∈ S.zip T, ∃ s, t = p.1 ++ s ∧ t' = p.2 ++ s := by
  unfold dAct
  constructor
  · intro h
    split at h
    · rename_i i hi
      have hpi := List.find?_some hi
      simp only [decide_eq_true_eq, List.get_eq_getElem] at hpi
      have hiT : i.1 < T.length := hlen ▸ i.2
      simp only [List.getElem?_eq_getElem hiT, Option.map_some, Option.some.injEq] at h
      refine ⟨(S[i.1], T[i.1]'hiT), ?_, t.drop (S[i.1]).length, ?_, ?_⟩
      · rw [List.mem_iff_getElem]
        exact ⟨i.1, by simp only [List.length_zip, lt_min_iff]; exact ⟨i.2, hiT⟩, by simp⟩
      · obtain ⟨w, hw⟩ := hpi
        subst hw; simp
      · rw [← h]; simp
    · simp at h
  · rintro ⟨p, hp, s, rfl, rfl⟩
    rw [List.mem_iff_getElem] at hp
    obtain ⟨i, hi, rfl⟩ := hp
    simp only [List.length_zip, lt_min_iff] at hi
    simp only [List.getElem_zip]
    have hex : ∃ j ∈ List.finRange S.length, decide (S.get j <+: S[i] ++ s) = true :=
      ⟨⟨i, hi.1⟩, by simp, by simp⟩
    obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp (List.find?_isSome.mpr hex)
    rw [hj]
    have hpj := List.find?_some hj
    simp only [decide_eq_true_eq, List.get_eq_getElem] at hpj
    have hij : S[j.1] = S[i] := by
      rcases List.prefix_or_prefix_of_prefix hpj (List.prefix_append S[i] s) with h | h
      · exact hanti _ (List.getElem_mem _) _ (List.getElem_mem _) h
      · exact (hanti _ (List.getElem_mem _) _ (List.getElem_mem _) h).symm
    have hji : j.1 = i := (List.Nodup.getElem_inj_iff hnd).mp hij
    have hiT : j.1 < T.length := hlen ▸ j.2
    simp only [List.get_eq_getElem, List.getElem?_eq_getElem hiT, Option.map_some]
    simp only [List.drop_left, hji]

theorem seqAct_ofDiagram {lL lR : List Seq} (hL : Good lL) (hR : Good lR)
    (hlen : lL.length = lR.length) (hnc : noCaret lL lR = true) (hcov : Covers lL 0)
    (hne : lL ≠ []) (t t' : Seq) :
    seqAct t (ofDiagram lL.toFinset lR.toFinset) = some t' ↔
      ∃ p ∈ lL.zip lR, ∃ s, t = p.1 ++ s ∧ t' = p.2 ++ s := by
  have hred := isReduced_of hL hR hlen hnc
  obtain ⟨h1, h2⟩ := LR_ofDiagram hred (by rw [hL.sorted]; exact hcov) (by rw [hL.sorted]; exact hne)
  unfold seqAct
  rw [h1, h2, diagramAct_eq_dAct, hL.sorted, hR.sorted]
  exact dAct_spec lL lR hlen hL.antichain hL.nodup t t'

/-! ### The action on finite sets of sequences -/

theorem treeAct_some_iff (T T' : Finset Seq) (f : MooreF) :
    treeAct T f = some T' ↔ (∀ t ∈ T, ∃ t', seqAct t f = some t') ∧
      ∀ t', t' ∈ T' ↔ ∃ t ∈ T, seqAct t f = some t' := by
  unfold treeAct
  split_ifs with h
  · simp only [Option.some.injEq]
    constructor
    · rintro rfl
      refine ⟨fun t ht => Option.isSome_iff_exists.mp (h t ht), fun t' => ?_⟩
      simp only [Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists]
      constructor
      · rintro ⟨t, ht, rfl⟩; exact ⟨t, ht, by simp⟩
      · rintro ⟨t, ht, h'⟩; exact ⟨t, ht, by simp [h']⟩
    · rintro ⟨-, h2⟩
      ext t'
      rw [h2]
      simp only [Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists]
      constructor
      · rintro ⟨t, ht, rfl⟩; exact ⟨t, ht, by simp⟩
      · rintro ⟨t, ht, h'⟩; exact ⟨t, ht, by simp [h']⟩
  · simp only [false_iff, not_and]
    intro h1
    exact absurd (fun t ht => by obtain ⟨t', ht'⟩ := h1 t ht; simp [ht']) h

theorem seqAct_iff_treeAct (t t' : Seq) (f : MooreF) :
    seqAct t f = some t' ↔ treeAct {t} f = some {t'} := by
  rw [treeAct_some_iff]
  simp only [Finset.mem_singleton, forall_eq, exists_eq_left]
  constructor
  · intro h; exact ⟨⟨t', h⟩, fun y => by rw [h]; simp [eq_comm]⟩
  · rintro ⟨-, h⟩; exact (h t').mp rfl

theorem hPA : IsPartialAction treeAct := isTree_treeAct_and_isPartialAction.2

theorem isTree_of_treeAct {T T' : Finset Seq} {f : MooreF} (hT : IsTree T)
    (h : treeAct T f = some T') : IsTree T' :=
  isTree_treeAct_and_isPartialAction.1 T T' f hT h

theorem seqAct_inv (t t' : Seq) (f : MooreF) :
    seqAct t f = some t' ↔ seqAct t' f⁻¹ = some t := by
  rw [seqAct_iff_treeAct, seqAct_iff_treeAct]
  exact hPA.inv f _ _

theorem seqAct_inj {t₁ t₂ t' : Seq} {f : MooreF} (h1 : seqAct t₁ f = some t')
    (h2 : seqAct t₂ f = some t') : t₁ = t₂ := by
  rw [seqAct_inv] at h1 h2
  rw [h1] at h2; exact Option.some.inj h2

theorem card_quot (T : Finset Seq) (u : Seq) :
    (quot T u).card = (T.filter (u <+: ·)).card := by
  unfold quot
  apply Finset.card_image_of_injOn
  intro a ha b hb hab
  simp only [Finset.coe_filter, Set.mem_ofPred_eq] at ha hb
  obtain ⟨a', rfl⟩ := ha.2
  obtain ⟨b', rfl⟩ := hb.2
  simp only [List.drop_left] at hab
  rw [hab]

theorem card_filter_treeAct {T T' : Finset Seq} {f : MooreF} (h : treeAct T f = some T')
    (P Q : Seq → Prop) (hPQ : ∀ t ∈ T, ∀ t', seqAct t f = some t' → (P t ↔ Q t')) :
    (T'.filter Q).card = (T.filter P).card := by
  obtain ⟨hdef, hmem⟩ := (treeAct_some_iff T T' f).mp h
  have hφ : ∀ t ∈ T, seqAct t f = some ((seqAct t f).getD []) := by
    intro t ht
    obtain ⟨t', ht'⟩ := hdef t ht
    rw [ht']; rfl
  have : T'.filter Q = (T.filter P).image (fun t => (seqAct t f).getD []) := by
    ext t'
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨ht', hq⟩
      obtain ⟨t, ht, hs⟩ := (hmem t').mp ht'
      refine ⟨t, ⟨ht, (hPQ t ht t' hs).mpr hq⟩, ?_⟩
      rw [hs]; rfl
    · rintro ⟨t, ⟨ht, hp⟩, rfl⟩
      exact ⟨(hmem _).mpr ⟨t, ht, hφ t ht⟩, (hPQ t ht _ (hφ t ht)).mp hp⟩
  rw [this]
  apply Finset.card_image_of_injOn
  intro a ha b hb hab
  simp only [Finset.coe_filter, Set.mem_ofPred_eq] at ha hb
  have h1 := hφ a ha.1
  have h2 := hφ b hb.1
  simp only at hab
  rw [hab] at h1
  exact seqAct_inj h1 h2

/-! ### Marginal sets -/

section marginal
variable {G S : Type*} [Group G] {act : S → G → Option S}

theorem isMarginal_empty : IsMarginal act ∅ := ⟨0, IsKMarginal.zero⟩

theorem isMarginal_of_marginalizes {E I : Set S} {g : G} (hI : IsMarginal act I)
    (hg : Marginalizes act g E I) : IsMarginal act E := by
  obtain ⟨k, hk⟩ := hI
  have := IsKMarginal.succ (l := 1) (fun _ => E) (fun _ => I) (fun _ => g) (fun _ => hk)
    (fun _ => hg)
  rw [Set.iUnion_const] at this
  exact ⟨k + 1, this⟩

theorem isMarginal_union (hact : IsPartialAction act) {E F : Set S} (hE : IsMarginal act E)
    (hF : IsMarginal act F) : IsMarginal act (E ∪ F) := by
  have := (isMarginal_union_subset_image act hact).1 {E, F} (by
    intro X hX
    simp only [Finset.mem_insert, Finset.mem_singleton] at hX
    rcases hX with rfl | rfl <;> assumption)
  simpa using this

theorem isMarginal_subset (hact : IsPartialAction act) {E E' : Set S} (h : E' ⊆ E)
    (hE : IsMarginal act E) : IsMarginal act E' :=
  (isMarginal_union_subset_image act hact).2.1 E E' h hE

theorem act_step (hact : IsPartialAction act) {x y z : S} {g : G} {i : ℕ}
    (h1 : act x (g ^ i) = some y) (h2 : act x (g ^ (i + 1)) = some z) : act y g = some z := by
  have h3 := (hact.inv _ _ _).mp h1
  have := hact.mul _ _ _ _ _ h3 h2
  rwa [pow_succ, ← mul_assoc, inv_mul_cancel, one_mul] at this

/-- A set `E` is marginalized by `g` off `I` when one step of `g` from `E` or from an auxiliary
set `P` (outside `I`) lands in `P ∪ I`, and `E` is disjoint from `P ∪ I`. -/
theorem marginalizes_of_step (hact : IsPartialAction act) {g : G} {E I P : Set S}
    (hstep : ∀ x, (x ∈ E ∨ x ∈ P) → x ∉ I → ∀ y, act x g = some y → y ∈ P ∨ y ∈ I)
    (hdisj : ∀ x ∈ E, x ∉ P ∧ x ∉ I) : Marginalizes act g E I := by
  intro x hx k hk ⟨y, hyE, hy⟩
  by_contra hcon
  push Not at hcon
  have hdefd : ∀ i ≤ k, ∃ z, act x (g ^ i) = some z := by
    intro i hi
    rcases lt_or_eq_of_le hi with hi | rfl
    · have := (hcon i hi).1
      unfold actPow at this
      exact Option.ne_none_iff_exists'.mp this
    · exact ⟨y, hy⟩
  have key : ∀ i, 1 ≤ i → i ≤ k → ∃ z, act x (g ^ i) = some z ∧ (z ∈ P ∨ z ∈ I) := by
    intro i hi1 hik
    induction i with
    | zero => omega
    | succ i ih =>
      obtain ⟨w, hw⟩ := hdefd (i + 1) hik
      rcases Nat.eq_zero_or_pos i with rfl | hipos
      · have hx0 : x ∉ I := by
          intro hxI
          exact (hcon 0 hk).2 x hxI (by simp [actPow, hact.one])
        simp only [zero_add, pow_one] at hw ⊢
        exact ⟨w, hw, hstep x (Or.inl hx) hx0 w hw⟩
      · obtain ⟨z, hz, hzP⟩ := ih hipos (by omega)
        have hzI : z ∉ I := fun hzI => (hcon i (by omega)).2 z hzI hz
        have hzP' : z ∈ P := hzP.resolve_right hzI
        refine ⟨w, hw, hstep z (Or.inr hzP') hzI w (act_step hact hz hw)⟩
  obtain ⟨z, hz, hzP⟩ := key k hk le_rfl
  unfold actPow at hy
  rw [hy] at hz
  cases hz
  rcases hzP with h | h
  · exact (hdisj y hyE).1 h
  · exact (hdisj y hyE).2 h

end marginal

end MooreFoelner.Dev.Sec5Marg

namespace MooreFoelner.Dev.Sec5Marg

open Classical CannonFloydParry MooreFoelner

/-! ### Concrete elements -/

/-- `t ↦ t'` under an element whose reduced diagram is listed by `l`. -/
def ActsBy (e : MooreF) (l : List (Seq × Seq)) : Prop :=
  ∀ t t', seqAct t e = some t' ↔ ∃ p ∈ l, ∃ s, t = p.1 ++ s ∧ t' = p.2 ++ s

theorem actsBy_ofDiagram {lL lR : List Seq} (hL : Good lL) (hR : Good lR)
    (hlen : lL.length = lR.length) (hnc : noCaret lL lR = true) (hcov : Covers lL 0)
    (hne : lL ≠ []) : ActsBy (ofDiagram lL.toFinset lR.toFinset) (lL.zip lR) :=
  seqAct_ofDiagram hL hR hlen hnc hcov hne

theorem ActsBy.rel {e : MooreF} {l : List (Seq × Seq)} (he : ActsBy e l) {P Q : Seq → Prop}
    (h : ∀ p ∈ l, ∀ s, (P (p.1 ++ s) ↔ Q (p.2 ++ s))) {t t' : Seq}
    (ht : seqAct t e = some t') : P t ↔ Q t' := by
  obtain ⟨p, hp, s, rfl, rfl⟩ := (he t t').mp ht
  exact h p hp s

theorem ActsBy.dom {e : MooreF} {l : List (Seq × Seq)} (he : ActsBy e l) {t : Seq}
    (ht : ∃ t', seqAct t e = some t') : ∃ p ∈ l, p.1 <+: t := by
  obtain ⟨t', ht'⟩ := ht
  obtain ⟨p, hp, s, rfl, rfl⟩ := (he _ t').mp ht'
  exact ⟨p, hp, List.prefix_append _ _⟩

theorem ActsBy.def {e : MooreF} {l : List (Seq × Seq)} (he : ActsBy e l) {t : Seq}
    (ht : ∃ p ∈ l, p.1 <+: t) : ∃ t', seqAct t e = some t' := by
  obtain ⟨p, hp, s, rfl⟩ := ht
  exact ⟨p.2 ++ s, (he _ _).mpr ⟨p, hp, s, rfl, rfl⟩⟩

/-- In a tree on which `e` acts, every left leaf of `e` is extended. -/
theorem ActsBy.exists_extends {e : MooreF} {l : List (Seq × Seq)} (he : ActsBy e l)
    (hanti : Antichain (l.map Prod.fst)) {T T' : Finset Seq} (hT : IsTree T)
    (hTT : treeAct T e = some T') {w : Seq} (hw : w ∈ l.map Prod.fst) : ∃ t ∈ T, w <+: t := by
  apply IsTree.exists_extends hT hanti _ hw
  intro t ht
  obtain ⟨p, hp, hpt⟩ := he.dom (((treeAct_some_iff T T' e).mp hTT).1 t ht)
  exact ⟨p.1, List.mem_map_of_mem hp, hpt⟩

/-- Small trees. -/
def lf : List Seq := [[]]

/-! #### `x₀` -/

def x0L : List Seq := joinL (joinL lf lf) lf
def x0R : List Seq := joinL lf (joinL lf lf)

theorem x0_eq : x0 = ofDiagram x0L.toFinset x0R.toFinset := by
  unfold x0; congr 1

theorem actsBy_x0 : ActsBy x0 (x0L.zip x0R) := by
  rw [x0_eq]
  exact actsBy_ofDiagram (good_join (good_join good_leaf good_leaf) good_leaf)
    (good_join good_leaf (good_join good_leaf good_leaf)) rfl (by decide)
    (by simp [x0L, joinL, lf, Covers, seqVal_cons, seqVal_nil]; norm_num) (by decide)

/-! #### `x₁` -/

/-! #### `a`, `b` (Lemma 5.7) -/

def aL : List Seq := joinL (joinL (joinL lf (joinL lf lf)) lf) (joinL (joinL lf lf) lf)
def aR : List Seq := joinL (joinL (joinL lf lf) (joinL (joinL lf lf) lf)) (joinL lf lf)

theorem a_eq : elemA = ofDiagram aL.toFinset aR.toFinset := by
  unfold elemA; congr 1

theorem good_aL : Good aL :=
  good_join (good_join (good_join good_leaf (good_join good_leaf good_leaf)) good_leaf)
    (good_join (good_join good_leaf good_leaf) good_leaf)

theorem actsBy_a : ActsBy elemA (aL.zip aR) := by
  rw [a_eq]
  exact actsBy_ofDiagram good_aL
    (good_join (good_join (good_join good_leaf good_leaf)
      (good_join (good_join good_leaf good_leaf) good_leaf)) (good_join good_leaf good_leaf))
    rfl (by decide)
    (by simp [aL, joinL, lf, Covers, seqVal_cons, seqVal_nil]; norm_num) (by decide)

def bL : List Seq := joinL (joinL (joinL lf (joinL lf lf)) lf) (joinL lf lf)
def bR : List Seq := joinL (joinL (joinL lf lf) lf) (joinL (joinL lf lf) lf)

theorem b_eq : elemB = ofDiagram bL.toFinset bR.toFinset := by
  unfold elemB; congr 1

theorem good_bL : Good bL :=
  good_join (good_join (good_join good_leaf (good_join good_leaf good_leaf)) good_leaf)
    (good_join good_leaf good_leaf)

theorem actsBy_b : ActsBy elemB (bL.zip bR) := by
  rw [b_eq]
  exact actsBy_ofDiagram good_bL
    (good_join (good_join (good_join good_leaf good_leaf) good_leaf)
      (good_join (good_join good_leaf good_leaf) good_leaf))
    rfl (by decide)
    (by simp [bL, joinL, lf, Covers, seqVal_cons, seqVal_nil]; norm_num) (by decide)

/-! #### `c`, `d` (Lemma 5.10) -/

/-! #### The element `g` of Lemma 5.12 -/

end MooreFoelner.Dev.Sec5Marg

namespace MooreFoelner.Dev.Sec5Marg

open Classical CannonFloydParry MooreFoelner

/-! ### Counting leaves -/

/-- `|T/u|`, as the number of leaves of `T` extending `u`. -/
noncomputable def qc (T : Finset Seq) (u : Seq) : ℕ := (T.filter (u <+: ·)).card

/-- `|T/001|`. -/
noncomputable abbrev A1 (T : Finset Seq) : ℕ := qc T [false, false, true]
/-- `|T/01|`. -/
noncomputable abbrev A2 (T : Finset Seq) : ℕ := qc T [false, true]
/-- `|T/10|`. -/
noncomputable abbrev A3 (T : Finset Seq) : ℕ := qc T [true, false]

theorem quot_card (T : Finset Seq) (u : Seq) : (quot T u).card = qc T u := card_quot T u

theorem bits_001 : bits "001" = [false, false, true] := rfl
theorem bits_01 : bits "01" = [false, true] := rfl
theorem bits_10 : bits "10" = [true, false] := rfl

theorem tPlus_iff (T : Finset Seq) : TPlus T ↔ A1 T < A2 T ∧ A2 T < A3 T := by
  simp only [TPlus, quot_card, bits_001, bits_01, bits_10]

theorem tMinus_iff (T : Finset Seq) : TMinus T ↔ A2 T < A1 T ∧ A3 T < A2 T := by
  simp only [TMinus, quot_card, bits_001, bits_01, bits_10, gt_iff_lt]

theorem mem_EBad (T : Finset Seq) : T ∈ EBad ↔ IsTree T ∧ ¬ TPlus T ∧ ¬ TMinus T := Iff.rfl

theorem card_filter_le_of {T : Finset Seq} {P Q : Seq → Prop} {_ : DecidablePred P}
    {_ : DecidablePred Q} (h : ∀ t ∈ T, P t → Q t) :
    (T.filter P).card ≤ (T.filter Q).card := by
  apply Finset.card_le_card
  intro t ht
  simp only [Finset.mem_filter] at ht ⊢
  exact ⟨ht.1, h t ht.1 ht.2⟩

theorem card_filter_lt_of {T : Finset Seq} {P Q : Seq → Prop} {_ : DecidablePred P}
    {_ : DecidablePred Q} (h : ∀ t ∈ T, P t → Q t)
    (hex : ∃ t ∈ T, Q t ∧ ¬ P t) : (T.filter P).card < (T.filter Q).card := by
  apply Finset.card_lt_card
  refine ⟨fun t ht => ?_, fun hsub => ?_⟩
  · simp only [Finset.mem_filter] at ht ⊢
    exact ⟨ht.1, h t ht.1 ht.2⟩
  · obtain ⟨t, ht, hq, hp⟩ := hex
    have := hsub (Finset.mem_filter.mpr ⟨ht, hq⟩)
    exact hp (Finset.mem_filter.mp this).2

theorem prefix_cases {u v t : Seq} (hu : u <+: t) (hv : v <+: t) : u <+: v ∨ v <+: u :=
  List.prefix_or_prefix_of_prefix hu hv

/-! ### Effect of the elements on the counts -/

theorem ActsBy.qc_eq {e : MooreF} {l : List (Seq × Seq)} (he : ActsBy e l) {T T' : Finset Seq}
    (h : treeAct T e = some T') (u v : Seq)
    (hl : ∀ p ∈ l, ∀ s, (u <+: p.1 ++ s ↔ v <+: p.2 ++ s)) : qc T' v = qc T u :=
  by unfold qc; convert card_filter_treeAct h (u <+: ·) (v <+: ·) (fun _ _ _ ht => he.rel hl ht)
       using 2 <;> ext <;> simp

theorem ActsBy.qc_eq_filter {e : MooreF} {l : List (Seq × Seq)} (he : ActsBy e l)
    {T T' : Finset Seq} (h : treeAct T e = some T') (P : Seq → Prop) (v : Seq)
    (hl : ∀ p ∈ l, ∀ s, (P (p.1 ++ s) ↔ v <+: p.2 ++ s)) : qc T' v = (T.filter P).card :=
  by unfold qc; convert card_filter_treeAct h P (v <+: ·) (fun _ _ _ ht => he.rel hl ht)
       using 2; ext; simp

section counts0
variable {T T' : Finset Seq}

theorem x0_counts (h : treeAct T x0 = some T') : A2 T' = A1 T ∧ A3 T' = A2 T :=
  ⟨actsBy_x0.qc_eq h _ _ (by simp [x0L, x0R, joinL, lf]),
    actsBy_x0.qc_eq h _ _ (by simp [x0L, x0R, joinL, lf])⟩

end counts0

theorem ActsBy.ext_of {e : MooreF} {lL lR : List Seq} (he : ActsBy e (lL.zip lR)) (hL : Good lL)
    (hlen : lL.length = lR.length) {T T' : Finset Seq} (hT : IsTree T)
    (h : treeAct T e = some T') {w : Seq} (hw : w ∈ lL) : ∃ t ∈ T, w <+: t := by
  have hm : (lL.zip lR).map Prod.fst = lL := List.map_fst_zip (by omega)
  exact he.exists_extends (by rw [hm]; exact hL.antichain) hT h (by rw [hm]; exact hw)

theorem not_both_prefix {u v t : Seq} (hu : u <+: t) (hv : v <+: t) (h : u.length = v.length)
    (hne : u ≠ v) : False := by
  rcases prefix_cases hu hv with h' | h'
  · exact hne (h'.eq_of_length h)
  · exact hne (h'.eq_of_length h.symm).symm

section counts
variable {T T' : Finset Seq}

theorem a_counts (hT : IsTree T) (h : treeAct T elemA = some T') :
    A1 T' < A1 T ∧ A2 T < A2 T' ∧ A3 T' < A3 T := by
  obtain ⟨t1, ht1, h1⟩ := actsBy_a.ext_of good_aL rfl hT h (w := [false, false, true, true])
    (by simp [aL, joinL, lf])
  obtain ⟨t2, ht2, h2⟩ := actsBy_a.ext_of good_aL rfl hT h (w := [true, false, false])
    (by simp [aL, joinL, lf])
  refine ⟨?_, ?_, ?_⟩
  · show qc T' [false, false, true] < qc T [false, false, true]
    rw [actsBy_a.qc_eq h [false, false, true, false] _ (by simp [aL, aR, joinL, lf])]
    simp only [qc]
    apply card_filter_lt_of
    · intro t _ ht; exact List.IsPrefix.trans (by simp) ht
    · exact ⟨t1, ht1, List.IsPrefix.trans (by simp) h1,
        fun h' => not_both_prefix h' h1 rfl (by simp)⟩
  · show qc T [false, true] < qc T' [false, true]
    rw [actsBy_a.qc_eq_filter h (fun t => [false, false, true, true] <+: t ∨ [false, true] <+: t ∨
      [true, false, false] <+: t) _ (by simp [aL, aR, joinL, lf])]
    simp only [qc]
    apply card_filter_lt_of
    · intro t _ ht; exact Or.inr (Or.inl ht)
    · exact ⟨t1, ht1, Or.inl h1, fun h' => not_both_prefix (u := [false, true])
        (v := [false, false]) h' (List.IsPrefix.trans (by simp) h1) rfl (by simp)⟩
  · show qc T' [true, false] < qc T [true, false]
    rw [actsBy_a.qc_eq h [true, false, true] _ (by simp [aL, aR, joinL, lf])]
    simp only [qc]
    apply card_filter_lt_of
    · intro t _ ht; exact List.IsPrefix.trans (by simp) ht
    · exact ⟨t2, ht2, List.IsPrefix.trans (by simp) h2,
        fun h' => not_both_prefix h' h2 rfl (by simp)⟩

theorem b_counts (hT : IsTree T) (h : treeAct T elemB = some T') :
    A1 T' < A1 T ∧ A2 T' < A1 T ∧ A2 T ≤ A3 T' ∧ A3 T < A3 T' := by
  obtain ⟨t1, ht1, h1⟩ := actsBy_b.ext_of good_bL rfl hT h (w := [false, false, true, true])
    (by simp [bL, joinL, lf])
  obtain ⟨t2, ht2, h2⟩ := actsBy_b.ext_of good_bL rfl hT h (w := [false, false, true, false])
    (by simp [bL, joinL, lf])
  obtain ⟨t3, ht3, h3⟩ := actsBy_b.ext_of good_bL rfl hT h (w := [false, true])
    (by simp [bL, joinL, lf])
  have e3 := actsBy_b.qc_eq_filter h (fun t => [false, true] <+: t ∨ [true, false] <+: t)
    [true, false] (by simp [bL, bR, joinL, lf])
  refine ⟨?_, ?_, ?_, ?_⟩
  · show qc T' [false, false, true] < qc T [false, false, true]
    rw [actsBy_b.qc_eq h [false, false, true, false] _ (by simp [bL, bR, joinL, lf])]
    simp only [qc]
    apply card_filter_lt_of
    · intro t _ ht; exact List.IsPrefix.trans (by simp) ht
    · exact ⟨t1, ht1, List.IsPrefix.trans (by simp) h1,
        fun h' => not_both_prefix h' h1 rfl (by simp)⟩
  · show qc T' [false, true] < qc T [false, false, true]
    rw [actsBy_b.qc_eq h [false, false, true, true] _ (by simp [bL, bR, joinL, lf])]
    simp only [qc]
    apply card_filter_lt_of
    · intro t _ ht; exact List.IsPrefix.trans (by simp) ht
    · exact ⟨t2, ht2, List.IsPrefix.trans (by simp) h2,
        fun h' => not_both_prefix h' h2 rfl (by simp)⟩
  · show qc T [false, true] ≤ qc T' [true, false]
    rw [e3]
    simp only [qc]
    apply card_filter_le_of
    intro t _ ht; exact Or.inl ht
  · show qc T [true, false] < qc T' [true, false]
    rw [e3]
    simp only [qc]
    apply card_filter_lt_of
    · intro t _ ht; exact Or.inr ht
    · exact ⟨t3, ht3, Or.inl h3, fun h' => not_both_prefix h' h3 rfl (by simp)⟩

end counts

/-! ### Lemma 5.7 -/

/-- `𝒯⁻`. -/
def SMinus : Set (Finset Seq) := {T | IsTree T ∧ A2 T < A1 T ∧ A3 T < A2 T}
/-- `E_max = E_a ∪ E_b`. -/
def Emax : Set (Finset Seq) := {T | IsTree T ∧ A1 T ≤ A2 T ∧ A3 T ≤ A2 T}
def Eb : Set (Finset Seq) := {T | IsTree T ∧ A1 T < A2 T ∧ A3 T < A2 T}
def Ea : Set (Finset Seq) := Emax \ Eb
def SR : Set (Finset Seq) := {T | IsTree T ∧ A1 T < A3 T ∧ A2 T < A3 T}
def E1 : Set (Finset Seq) := {T | IsTree T ∧ A2 T < A1 T ∧ A2 T = A3 T}
def E2 : Set (Finset Seq) := {T | IsTree T ∧ A2 T < A1 T ∧ A2 T < A3 T}
def E3 : Set (Finset Seq) := {T | IsTree T ∧ A1 T = A2 T ∧ A2 T < A3 T}

theorem marg_Ea : Marginalizes treeAct elemA Ea ∅ := by
  apply marginalizes_of_step hPA (P := Eb)
  · intro x hx _ y hy
    have hxT : IsTree x := by
      rcases hx with hx | hx
      · exact hx.1.1
      · exact hx.1
    have hxm : A1 x ≤ A2 x ∧ A3 x ≤ A2 x := by
      rcases hx with hx | hx
      · exact hx.1.2
      · exact ⟨hx.2.1.le, hx.2.2.le⟩
    obtain ⟨c1, c2, c3⟩ := a_counts hxT hy
    left
    exact ⟨isTree_of_treeAct hxT hy, by omega, by omega⟩
  · intro x hx
    exact ⟨hx.2, fun h => h⟩

theorem marg_Eb : Marginalizes treeAct elemB Eb ∅ := by
  apply marginalizes_of_step hPA (P := SR)
  · intro x hx _ y hy
    have hxT : IsTree x := by
      rcases hx with hx | hx
      · exact hx.1
      · exact hx.1
    obtain ⟨c1, c2, c3, c4⟩ := b_counts hxT hy
    left
    refine ⟨isTree_of_treeAct hxT hy, ?_, ?_⟩
    · rcases hx with hx | hx
      · have := hx.2; omega
      · have := hx.2; omega
    · rcases hx with hx | hx
      · have := hx.2; omega
      · have := hx.2; omega
  · intro x hx
    refine ⟨fun h => ?_, fun h => h⟩
    have := hx.2; have := h.2; omega

theorem marg_E12 : Marginalizes treeAct x0 (E1 ∪ E2) Emax := by
  apply marginalizes_of_step hPA (P := SMinus)
  · intro x hx hxI y hy
    have hxT : IsTree x := by
      rcases hx with (hx | hx) | hx
      · exact hx.1
      · exact hx.1
      · exact hx.1
    have hx' : A2 x < A1 x := by
      rcases hx with (hx | hx) | hx
      · exact hx.2.1
      · exact hx.2.1
      · exact hx.2.1
    obtain ⟨c1, c2⟩ := x0_counts hy
    have hyT := isTree_of_treeAct hxT hy
    by_cases hc : A2 y < A1 y
    · left; exact ⟨hyT, hc, by omega⟩
    · right; exact ⟨hyT, by omega, by omega⟩
  · intro x hx
    rcases hx with hx | hx
    · refine ⟨fun h => ?_, fun h => ?_⟩
      · have := hx.2; have := h.2; omega
      · have := hx.2; have := h.2; omega
    · refine ⟨fun h => ?_, fun h => ?_⟩
      · have := hx.2; have := h.2; omega
      · have := hx.2; have := h.2; omega

theorem marg_E3 : Marginalizes treeAct x0 E3 Emax := by
  apply marginalizes_of_step hPA (P := SMinus ∪ E1)
  · intro x hx hxI y hy
    have hxT : IsTree x := by
      rcases hx with hx | hx | hx
      · exact hx.1
      · exact hx.1
      · exact hx.1
    have hx' : A2 x ≤ A1 x := by
      rcases hx with hx | hx | hx
      · have := hx.2; omega
      · have := hx.2; omega
      · have := hx.2; omega
    obtain ⟨c1, c2⟩ := x0_counts hy
    have hyT := isTree_of_treeAct hxT hy
    have hle : A3 y ≤ A2 y := by omega
    by_cases hc : A2 y < A1 y
    · left
      rcases lt_or_eq_of_le hle with h' | h'
      · left; exact ⟨hyT, hc, h'⟩
      · right; exact ⟨hyT, hc, h'.symm⟩
    · right; exact ⟨hyT, by omega, hle⟩
  · intro x hx
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rcases h with h | h
      · have := hx.2; have := h.2; omega
      · have := hx.2; have := h.2; omega
    · have := hx.2; have := h.2; omega

theorem EBad_subset : EBad ⊆ Ea ∪ Eb ∪ (E1 ∪ E2) ∪ E3 := by
  intro T hT
  rw [mem_EBad, tPlus_iff, tMinus_iff] at hT
  obtain ⟨hT, h1, h2⟩ := hT
  by_cases hm : A1 T ≤ A2 T ∧ A3 T ≤ A2 T
  · by_cases hb : A1 T < A2 T ∧ A3 T < A2 T
    · left; left; right; exact ⟨hT, hb⟩
    · left; left; left; exact ⟨⟨hT, hm⟩, fun h => hb h.2⟩
  · rcases Nat.lt_or_ge (A2 T) (A1 T) with ha | ha
    · rcases Nat.lt_or_ge (A2 T) (A3 T) with hc | hc
      · left; right; right; exact ⟨hT, ha, hc⟩
      · rcases lt_or_eq_of_le hc with hc | hc
        · exact absurd ⟨ha, hc⟩ h2
        · left; right; left; exact ⟨hT, ha, hc.symm⟩
    · rcases lt_or_eq_of_le ha with ha | ha
      · have hc : A2 T < A3 T := by omega
        exact absurd ⟨ha, hc⟩ h1
      · right; exact ⟨hT, ha, by omega⟩

theorem isMarginal_EBad' : IsMarginal treeAct EBad := by
  have hEa := isMarginal_of_marginalizes isMarginal_empty marg_Ea
  have hEb := isMarginal_of_marginalizes isMarginal_empty marg_Eb
  have hEmax : IsMarginal treeAct Emax := by
    apply isMarginal_subset hPA _ (isMarginal_union hPA hEa hEb)
    intro T hT
    by_cases hb : T ∈ Eb
    · exact Or.inr hb
    · exact Or.inl ⟨hT, hb⟩
  have hE12 := isMarginal_of_marginalizes hEmax marg_E12
  have hE3 := isMarginal_of_marginalizes hEmax marg_E3
  exact isMarginal_subset hPA EBad_subset
    (isMarginal_union hPA (isMarginal_union hPA (isMarginal_union hPA hEa hEb) hE12) hE3)

/-! ### Lemma 5.9 -/

/-! ### Lemma 5.10 -/

section counts2
variable {T T' : Finset Seq}

end counts2


end MooreFoelner.Dev.Sec5Marg

namespace MooreFoelner.Dev.Sec5Marg

open Classical CannonFloydParry MooreFoelner

/-! ### Lemma 5.12 -/

end MooreFoelner.Dev.Sec5Marg

namespace MooreFoelner.Dev.Sec5Marg
open Classical CannonFloydParry MooreFoelner

end MooreFoelner.Dev.Sec5Marg

namespace MooreFoelner

open Classical CannonFloydParry

end MooreFoelner
end

open MooreFoelner in
open Classical CannonFloydParry MooreFoelner in
open Classical CannonFloydParry MooreFoelner in
open Classical CannonFloydParry MooreFoelner in
open Classical CannonFloydParry MooreFoelner in
open Classical CannonFloydParry MooreFoelner in
open Classical CannonFloydParry in
theorem solution : IsMarginal treeAct EBad := Dev.Sec5Marg.isMarginal_EBad'
