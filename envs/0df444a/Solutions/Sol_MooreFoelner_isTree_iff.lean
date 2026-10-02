-- Prove2me | solution 1 for MooreFoelner.isTree_iff
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-02T02:44:37.008517+00:00
-- url     : https://prove2.me/submissions/2c095af7-861c-4055-9539-5490dcf76e80

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
# Moore 2013, §2: trees, the partial action of `F` on trees, reduced diagrams (TreesBasic)

Targets: `isTree_iff` (#1), `isTree_treeAct_and_isPartialAction` (#2),
`isReducedDiagram_treeAct` (#6).
-/

namespace MooreFoelner.Dev.TreesBasic

open Classical CannonFloydParry MooreFoelner

/-! ### Infinite sequences and prefixes -/

/-- `u⁀y`. -/
def app (u : Seq) (y : ℕ → Bool) : ℕ → Bool :=
  fun n => if h : n < u.length then u.get ⟨n, h⟩ else y (n - u.length)

/-- The tail of `x` after its first `k` digits. -/
def shift (x : ℕ → Bool) (k : ℕ) : ℕ → Bool := fun n => x (n + k)

/-- The first `n` digits of `x`. -/
def pre (x : ℕ → Bool) (n : ℕ) : Seq := List.ofFn (fun i : Fin n => x i)

@[simp] lemma length_pre (x : ℕ → Bool) (n : ℕ) : (pre x n).length = n := by simp [pre]

lemma isInitialPart_pre (x : ℕ → Bool) (n : ℕ) : IsInitialPart (pre x n) x := by
  intro i hi
  simp [pre]

lemma isInitialPart_app (u : Seq) (y : ℕ → Bool) : IsInitialPart u (app u y) := by
  intro i hi
  simp [app, hi]

lemma ip_mono {u v : Seq} {x : ℕ → Bool} (huv : u <+: v) (hv : IsInitialPart v x) :
    IsInitialPart u x := by
  intro i hi
  have hi' : i < v.length := lt_of_lt_of_le hi huv.length_le
  have := hv i hi'
  rw [← this]
  simp only [List.get_eq_getElem]
  exact huv.getElem hi

lemma ip_prefix {u v : Seq} {x : ℕ → Bool} (hu : IsInitialPart u x)
    (hv : IsInitialPart v x) (hl : u.length ≤ v.length) : u <+: v := by
  rw [List.prefix_iff_eq_take]
  apply List.ext_get (by simp [hl])
  intro n h1 h2
  have h3 : n < v.length := by simp at h2; omega
  simp only [List.get_eq_getElem, List.getElem_take]
  have e1 := hu n h1
  have e2 := hv n h3
  simp only [List.get_eq_getElem] at e1 e2
  rw [e1, e2]

lemma ip_comparable {u v : Seq} {x : ℕ → Bool} (hu : IsInitialPart u x)
    (hv : IsInitialPart v x) : u <+: v ∨ v <+: u := by
  rcases le_total u.length v.length with h | h
  · exact Or.inl (ip_prefix hu hv h)
  · exact Or.inr (ip_prefix hv hu h)

@[simp] lemma shift_app (u : Seq) (y : ℕ → Bool) : shift (app u y) u.length = y := by
  funext n
  simp [shift, app]

lemma pre_succ (x : ℕ → Bool) (n : ℕ) : pre x (n + 1) = pre x n ++ [x n] := by
  simp only [pre]
  rw [List.ofFn_succ_last]
  simp

/-! ### Trees -/

section Trees

variable {T : Finset Seq}

lemma tree_exists (hT : IsTree T) (x : ℕ → Bool) : ∃ t ∈ T, IsInitialPart t x := by
  obtain ⟨t, ⟨ht, hx⟩, -⟩ := hT x
  exact ⟨t, ht, hx⟩

lemma tree_unique (hT : IsTree T) {x : ℕ → Bool} {t t' : Seq} (ht : t ∈ T) (ht' : t' ∈ T)
    (hx : IsInitialPart t x) (hx' : IsInitialPart t' x) : t = t' :=
  (hT x).unique ⟨ht, hx⟩ ⟨ht', hx'⟩

lemma tree_eq_of_prefix (hT : IsTree T) {s s' : Seq} (hs : s ∈ T) (hs' : s' ∈ T)
    (h : s <+: s') : s = s' :=
  tree_unique hT hs hs' (ip_mono h (isInitialPart_app s' (fun _ => false)))
    (isInitialPart_app s' (fun _ => false))

lemma tree_nonempty (hT : IsTree T) : T.Nonempty := by
  obtain ⟨t, ht, -⟩ := tree_exists hT (fun _ => false)
  exact ⟨t, ht⟩

/-- Every sequence either extends an element of the tree or is a proper prefix of one. -/
lemma tree_cases (hT : IsTree T) (u : Seq) :
    (∃ s ∈ T, s <+: u) ∨ ∃ s ∈ T, u <+: s ∧ u ≠ s := by
  obtain ⟨s, hs, hx⟩ := tree_exists hT (app u (fun _ => false))
  rcases ip_comparable hx (isInitialPart_app u (fun _ => false)) with h | h
  · exact Or.inl ⟨s, hs, h⟩
  · by_cases hus : u = s
    · exact Or.inl ⟨s, hs, hus ▸ List.prefix_refl u⟩
    · exact Or.inr ⟨s, hs, h, hus⟩

lemma tree_sibling (hT : IsTree T) (u : Seq) (b : Bool) (h : ∃ t ∈ T, (u ++ [b]) <+: t) :
    ∃ t ∈ T, (u ++ [!b]) <+: t := by
  obtain ⟨t, ht, hut⟩ := h
  rcases tree_cases hT (u ++ [!b]) with ⟨s, hs, hsu⟩ | ⟨s, hs, hsu, -⟩
  · rcases List.prefix_concat_iff.mp hsu with e | e
    · exact ⟨s, hs, e ▸ List.prefix_refl _⟩
    · have hst : s <+: t := e.trans ((List.prefix_append u [b]).trans hut)
      have := tree_eq_of_prefix hT hs ht hst
      subst this
      have h1 := e.length_le
      have h2 := hut.length_le
      simp at h2
      omega
  · exact ⟨s, hs, hsu⟩

/-- The backward direction of `isTree_iff`. -/
lemma isTree_of_conditions (T : Finset Seq) (hne : T.Nonempty)
    (hanti : ∀ u ∈ T, ∀ v ∈ T, u <+: v → u = v)
    (hsib : ∀ u : Seq, (∃ t ∈ T, (u ++ [false]) <+: t) ↔ (∃ t ∈ T, (u ++ [true]) <+: t)) :
    IsTree T := by
  intro x
  have key : ∀ k n, T.sup List.length - n ≤ k → (∃ t ∈ T, pre x n <+: t) →
      ∃ t ∈ T, IsInitialPart t x := by
    intro k
    induction k with
    | zero =>
      rintro n hn ⟨t, ht, hpt⟩
      have hle : t.length ≤ T.sup List.length := Finset.le_sup (f := List.length) ht
      have h1 := hpt.length_le
      simp only [length_pre] at h1
      have : (pre x n).length = t.length := by simp only [length_pre]; omega
      refine ⟨t, ht, ?_⟩
      rw [← hpt.eq_of_length this]
      exact isInitialPart_pre x n
    | succ k ih =>
      rintro n hn ⟨t, ht, hpt⟩
      by_cases heq : pre x n = t
      · exact ⟨t, ht, heq ▸ isInitialPart_pre x n⟩
      · have hle : t.length ≤ T.sup List.length := Finset.le_sup (f := List.length) ht
        have hlt : n < t.length := by
          have h1 := hpt.length_le
          simp only [length_pre] at h1
          rcases lt_or_eq_of_le h1 with h | h
          · exact h
          · exact absurd (hpt.eq_of_length (by simpa using h)) heq
        apply ih (n + 1) (by omega)
        have hext : (pre x n ++ [t[n]]) <+: t := by
          have : pre x n = t.take n := by
            have := List.prefix_iff_eq_take.mp hpt
            simpa using this
          rw [this, List.take_concat_get']
          exact List.take_prefix _ _
        rw [pre_succ]
        cases hxn : x n <;> cases htn : t[n]
        · exact ⟨t, ht, htn ▸ hext⟩
        · exact (hsib _).mpr ⟨t, ht, htn ▸ hext⟩
        · exact (hsib _).mp ⟨t, ht, htn ▸ hext⟩
        · exact ⟨t, ht, htn ▸ hext⟩
  obtain ⟨t0, ht0⟩ := hne
  obtain ⟨t, ht, hx⟩ := key _ 0 le_rfl ⟨t0, ht0, by simp [pre]⟩
  refine ⟨t, ⟨ht, hx⟩, ?_⟩
  rintro t' ⟨ht', hx'⟩
  rcases ip_comparable hx' hx with h | h
  · exact hanti _ ht' _ ht h
  · exact (hanti _ ht _ ht' h).symm

/-- The forward direction of `isTree_iff`. -/
lemma conditions_of_isTree {T : Finset Seq} (hT : IsTree T) :
    T.Nonempty ∧ (∀ u ∈ T, ∀ v ∈ T, u <+: v → u = v) ∧
      ∀ u : Seq, (∃ t ∈ T, (u ++ [false]) <+: t) ↔ (∃ t ∈ T, (u ++ [true]) <+: t) :=
  ⟨tree_nonempty hT, fun _ hu _ hv h => tree_eq_of_prefix hT hu hv h,
    fun u => ⟨fun h => tree_sibling hT u false h, fun h => tree_sibling hT u true h⟩⟩

end Trees

/-! ### `sorted` -/

section Sorted

end Sorted

/-! ### Dyadic intervals -/

section Real

/-! ### Affine maps between dyadic intervals -/

end Real

/-! ### Tree diagrams: the maps they define -/

section Diagrams

variable {L R : Finset Seq}

end Diagrams

/-! ### Describing diagrams through a pairing of leaves -/

section Pairing

variable {L R : Finset Seq}

end Pairing

/-! ### The reduced diagram of an element of `F` -/

section Reduced

end Reduced

end MooreFoelner.Dev.TreesBasic

namespace MooreFoelner

open Classical CannonFloydParry

end MooreFoelner
end

open MooreFoelner in
open Classical CannonFloydParry MooreFoelner in
open Classical CannonFloydParry in
theorem solution (T : Finset Seq) :
    IsTree T ↔ T.Nonempty ∧ (∀ u ∈ T, ∀ v ∈ T, u <+: v → u = v) ∧
      ∀ u : Seq, (∃ t ∈ T, (u ++ [false]) <+: t) ↔ (∃ t ∈ T, (u ++ [true]) <+: t) :=
  ⟨Dev.TreesBasic.conditions_of_isTree,
    fun ⟨h1, h2, h3⟩ => Dev.TreesBasic.isTree_of_conditions T h1 h2 h3⟩
