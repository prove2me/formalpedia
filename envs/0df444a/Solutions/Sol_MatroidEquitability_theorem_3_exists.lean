-- Prove2me | solution 1 for MatroidEquitability.theorem_3_exists
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T19:20:39.043429+00:00
-- url     : https://prove2.me/submissions/cd02c306-0dd6-4f08-92d4-7ad092c05435

import Mathlib
import Definitions.Def_MatroidEquitability_IsExchangeable

section
namespace MatroidEquitability.Dev.Tri

open Matroid in
/-- Triangular exchange lemma (Schrijver 39.13 in triangular form): if `x i ∈ B`, `y i ∉ B` and the
exchange graph of `B` restricted to these pairs is lower triangular with nonzero diagonal
(`B - x i + y j` is a base iff `j ≤ i`, at least for `i < j` it is not), then `B △ ({x i} ∪ {y i})` is a base. -/
theorem triangular_base {α : Type*} (M : Matroid α) [M.Finite] (B : Set α) (hB : M.IsBase B)
    (n : ℕ) (x y : Fin n → α) (hxB : ∀ i, x i ∈ B) (hyB : ∀ i, y i ∈ M.E \ B)
    (hxi : Function.Injective x) (hyi : Function.Injective y)
    (hdiag : ∀ i, M.IsBase (insert (y i) (B \ {x i})))
    (hoff : ∀ i j, i < j → ¬ M.IsBase (insert (y j) (B \ {x i}))) :
    M.IsBase ((B \ Set.range x) ∪ Set.range y) := by
  classical
  set J := (B \ Set.range x) ∪ Set.range y with hJ
  have hBfin : B.Finite := hB.finite
  -- membership in fundamental circuit iff exchange is a base
  have hmem : ∀ i j, x i ∈ M.fundCircuit (y j) B ↔ M.IsBase (insert (y j) (B \ {x i})) := by
    intro i j
    have hyj := hyB j
    have hne : x i ≠ y j := fun h => hyj.2 (h ▸ hxB i)
    have hcl : y j ∈ M.closure B := by rw [hB.closure_eq]; exact hyj.1
    rw [hB.indep.mem_fundCircuit_iff hcl hyj.2]
    have heq : insert (y j) B \ {x i} = insert (y j) (B \ {x i}) := by
      rw [Set.insert_sdiff_of_notMem _ (by simpa using hne.symm)]
    rw [heq]
    constructor
    · intro hI
      obtain ⟨B', hB', hIB'⟩ := hI.exists_isBase_superset
      have hc : (insert (y j) (B \ {x i})).ncard = B.ncard := by
        rw [Set.ncard_insert_of_notMem (by simp [hyj.2]) (hBfin.sdiff), Set.ncard_sdiff_singleton_of_mem (hxB i)]
        have : 0 < B.ncard := Set.ncard_pos hBfin |>.2 ⟨_, hxB i⟩
        omega
      have hc' : B'.ncard = B.ncard := hB'.ncard_eq_ncard_of_isBase hB
      have := Set.eq_of_subset_of_ncard_le hIB' (by omega) hB'.finite
      rw [this]; exact hB'
    · exact fun h => h.indep
  -- each x k is in the closure of J, by downward induction
  have hcirc : ∀ j, M.IsCircuit (M.fundCircuit (y j) B) := fun j =>
    hB.fundCircuit_isCircuit (hyB j).1 (hyB j).2
  have hJE : J ⊆ M.E := by
    rintro e (⟨h, _⟩ | ⟨i, rfl⟩)
    · exact hB.subset_ground h
    · exact (hyB i).1
  have key : ∀ d : ℕ, ∀ k : Fin n, n - k.val = d → x k ∈ M.closure J := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro k hk
      have hxk : x k ∈ M.fundCircuit (y k) B := (hmem k k).2 (hdiag k)
      have hsub : M.fundCircuit (y k) B \ {x k} ⊆ M.closure J := by
        intro e he
        have hC := M.fundCircuit_subset_insert (y k) B he.1
        have hne : e ≠ x k := he.2
        by_cases hey : e = y k
        · subst hey
          exact M.mem_closure_of_mem (Or.inr ⟨k, rfl⟩) hJE
        · have heB : e ∈ B := by
            rcases hC with h | h
            · exact absurd h hey
            · exact h
          by_cases hr : e ∈ Set.range x
          · obtain ⟨m, rfl⟩ := hr
            have hmk : m ≠ k := fun h => hne (by rw [h])
            have hlt : k < m := by
              rcases lt_or_gt_of_ne hmk with h | h
              · exact absurd ((hmem m k).1 he.1) (hoff m k h)
              · exact h
            exact ih (n - m.val) (by have := m.2; have : k.val < m.val := hlt; omega) m rfl
          · exact M.mem_closure_of_mem (Or.inl ⟨heB, hr⟩) hJE
      have h1 := (hcirc k).mem_closure_sdiff_singleton_of_mem hxk
      have h2 : M.closure (M.fundCircuit (y k) B \ {x k}) ⊆ M.closure J := by
        exact M.closure_subset_closure_of_subset_closure hsub
      exact h2 h1
  have hBcl : B ⊆ M.closure J := by
    intro e heB
    by_cases hr : e ∈ Set.range x
    · obtain ⟨m, rfl⟩ := hr
      exact key _ m rfl
    · exact M.mem_closure_of_mem (Or.inl ⟨heB, hr⟩) hJE
  have hspan : M.Spanning J := by
    rw [spanning_iff_closure_eq hJE]
    apply Set.Subset.antisymm (M.closure_subset_ground _)
    rw [← hB.closure_eq]
    exact M.closure_subset_closure_of_subset_closure hBcl
  obtain ⟨B', hB', hB'J⟩ := hspan.exists_isBase_subset
  have hJfin : J.Finite := (hBfin.sdiff).union (Set.finite_range y)
  have hdisj : Disjoint (B \ Set.range x) (Set.range y) := by
    rw [Set.disjoint_left]
    rintro e ⟨heB, _⟩ ⟨i, rfl⟩
    exact (hyB i).2 heB
  have hcard : J.ncard = B.ncard := by
    have h1 := Set.ncard_sdiff_add_ncard_of_subset (show Set.range x ⊆ B from by rintro _ ⟨i, rfl⟩; exact hxB i) hBfin
    rw [hJ, Set.ncard_union_eq hdisj hBfin.sdiff (Set.finite_range y),
      Set.ncard_range_of_injective hyi]
    rw [Set.ncard_range_of_injective hxi] at h1
    omega
  have := Set.eq_of_subset_of_ncard_le hB'J (by rw [hB'.ncard_eq_ncard_of_isBase hB, hcard]) hJfin
  rw [← this]; exact hB'

end MatroidEquitability.Dev.Tri
end

section
set_option autoImplicit false

open scoped symmDiff

namespace MatroidEquitability.Dev.T3a

open Relation

variable {α : Type*}

/-- exchange digraph between the bases `P` and `Q` -/
def Edge (M : Matroid α) (P Q : Set α) (a b : α) : Prop :=
  (a ∈ P ∧ b ∈ Q ∧ M.IsBase (insert b (P \ {a}))) ∨
    (a ∈ Q ∧ b ∈ P ∧ M.IsBase (insert b (Q \ {a})))

theorem Edge.swap {M : Matroid α} {P Q : Set α} {a b : α} :
    Edge M P Q a b ↔ Edge M Q P a b := or_comm

/-- `Reach R t n u`: there is a walk of length `n` from `t` to `u`. -/
def Reach (R : α → α → Prop) (t : α) : ℕ → α → Prop
  | 0, u => u = t
  | n + 1, u => ∃ w, Reach R t n w ∧ R w u

/-- shortest walk length -/
def Short (R : α → α → Prop) (t : α) (n : ℕ) (u : α) : Prop :=
  Reach R t n u ∧ ∀ m < n, ¬ Reach R t m u

theorem reach_of_rtg {R : α → α → Prop} {t u : α} (h : ReflTransGen R t u) :
    ∃ n, Reach R t n u := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | tail _ hbc ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, _, hn, hbc⟩

theorem exists_short {R : α → α → Prop} {t u : α} {n : ℕ} (h : Reach R t n u) :
    ∃ m ≤ n, Short R t m u := by
  classical
  have hex : ∃ m, Reach R t m u := ⟨n, h⟩
  refine ⟨Nat.find hex, Nat.find_min' hex h, Nat.find_spec hex, fun m hm => Nat.find_min hex hm⟩

theorem short_pred {R : α → α → Prop} {t u : α} {n : ℕ} (h : Short R t (n + 1) u) :
    ∃ w, Short R t n w ∧ R w u := by
  obtain ⟨w, hw, hwu⟩ := h.1
  obtain ⟨m, hm, hs⟩ := exists_short hw
  have : ¬ m < n := by
    intro hlt
    exact h.2 (m + 1) (by omega) ⟨w, hs.1, hwu⟩
  have hmn : m = n := by omega
  subst hmn
  exact ⟨w, hs, hwu⟩

theorem short_path {R : α → α → Prop} {t : α} :
    ∀ (n : ℕ) (u : α), Short R t n u →
      ∃ v : ℕ → α, v n = u ∧ (∀ i ≤ n, Short R t i (v i)) ∧ ∀ i < n, R (v i) (v (i + 1)) := by
  intro n
  induction n with
  | zero =>
    intro u hu
    exact ⟨fun _ => u, rfl, fun i hi => by
      have : i = 0 := by omega
      subst this; exact hu, fun i hi => by omega⟩
  | succ n ih =>
    intro u hu
    obtain ⟨w, hw, hwu⟩ := short_pred hu
    obtain ⟨v, hvn, hvs, hvR⟩ := ih w hw
    refine ⟨fun i => if i = n + 1 then u else v i, by simp, ?_, ?_⟩
    · intro i hi
      by_cases h : i = n + 1
      · subst h; simpa using hu
      · simpa [h] using hvs i (by omega)
    · intro i hi
      by_cases h : i = n
      · subst h; simpa [hvn] using hwu
      · have h1 : i ≠ n + 1 := by omega
        have h2 : i + 1 ≠ n + 1 := by omega
        simpa [h, h1, h2] using hvR i (by omega)

theorem symmDiff_eq_of_union {P R1 R2 : Set α} (h1 : R1 ⊆ P) (h2 : Disjoint R2 P) :
    symmDiff P (R1 ∪ R2) = (P \ R1) ∪ R2 := by
  ext u
  simp only [Set.symmDiff_def, Set.mem_union, Set.mem_sdiff]
  rw [Set.disjoint_left] at h2
  constructor
  · rintro ((⟨hp, hn⟩ | ⟨hx, hnp⟩))
    · exact Or.inl ⟨hp, fun h => hn (Or.inl h)⟩
    · rcases hx with hx | hx
      · exact absurd (h1 hx) hnp
      · exact Or.inr hx
  · rintro (⟨hp, hn⟩ | hx)
    · exact Or.inl ⟨hp, fun h => h.elim hn (fun h' => h2 h' hp)⟩
    · exact Or.inr ⟨Or.inr hx, h2 hx⟩

/-- Lemma 3.2 (with the minimal cycle chosen by shortest paths). -/
theorem exchangeable_of_cycle (M : Matroid α) [M.Finite] (P Q W : Set α) (hP : M.IsBase P)
    (hQ : M.IsBase Q) (hPQ : Disjoint P Q) (t : α) (htP : t ∈ P) (htW : t ∈ W)
    (hW : W ⊆ P ∪ Q) (y0 : α) (hy0W : y0 ∈ W) (hy0 : Edge M P Q y0 t)
    (hreach : ReflTransGen (fun u v => u ∈ W ∧ v ∈ W ∧ Edge M P Q u v) t y0) :
    ∃ X, t ∈ X ∧ X ⊆ W ∧ M.IsBase (symmDiff P X) ∧ M.IsBase (symmDiff Q X) := by
  classical
  set R : α → α → Prop := fun u v => u ∈ W ∧ v ∈ W ∧ Edge M P Q u v with hR
  have hreachW : ∀ n u, Reach R t n u → u ∈ W := by
    intro n u h
    cases n with
    | zero => simp only [Reach] at h; subst h; exact htW
    | succ n => obtain ⟨w, _, hw⟩ := h; exact hw.2.1
  -- the minimal closing length
  have hex : ∃ n, ∃ y, Edge M P Q y t ∧ y ∈ W ∧ Reach R t n y := by
    obtain ⟨n, hn⟩ := reach_of_rtg hreach
    exact ⟨n, y0, hy0, hy0W, hn⟩
  set p := Nat.find hex with hp
  obtain ⟨y, hyt, hyW, hyr⟩ := Nat.find_spec hex
  have hmin : ∀ m < p, ∀ y', Edge M P Q y' t → y' ∈ W → ¬ Reach R t m y' := by
    intro m hm y' h1 h2 h3
    exact Nat.find_min hex hm ⟨y', h1, h2, h3⟩
  have hys : Short R t p y := ⟨hyr, fun m hm hr => hmin m hm y hyt hyW hr⟩
  obtain ⟨v, hvp, hvs, hvR⟩ := short_path p y hys
  have hv0 : v 0 = t := (hvs 0 (by omega)).1
  have hvW : ∀ i ≤ p, v i ∈ W := fun i hi => hreachW i _ (hvs i hi).1
  have hvinj : ∀ i j, i ≤ p → j ≤ p → v i = v j → i = j := by
    intro i j hi hj h
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · exact (hvs j hj).2 i hlt (h ▸ (hvs i hi).1)
    · exact (hvs i hi).2 j hlt (h ▸ (hvs j hj).1)
  -- chordless
  have hchord : ∀ i j, i ≤ p → j ≤ p → i + 1 < j → ¬ Edge M P Q (v i) (v j) := by
    intro i j hi hj hij he
    exact (hvs j hj).2 (i + 1) hij ⟨v i, (hvs i hi).1, hvW i hi, hvW j hj, he⟩
  have hback : ∀ i, i < p → ¬ Edge M P Q (v i) t := by
    intro i hi he
    exact hmin i hi (v i) he (hvW i (by omega)) (hvs i (by omega)).1
  have hvPQ : ∀ i ≤ p, v i ∈ P ∪ Q := fun i hi => hW (hvW i hi)
  have hedgeR : ∀ i < p, Edge M P Q (v i) (v (i + 1)) := fun i hi => (hvR i hi).2.2
  -- sides
  have hside : ∀ i ≤ p, (i % 2 = 0 → v i ∈ P) ∧ (i % 2 = 1 → v i ∈ Q) := by
    intro i
    induction i with
    | zero => intro _; exact ⟨fun _ => hv0 ▸ htP, fun h => by omega⟩
    | succ i ih =>
      intro hi
      obtain ⟨h1, h2⟩ := ih (by omega)
      have he := hedgeR i (by omega)
      rcases Nat.mod_two_eq_zero_or_one i with h | h
      · have hvi := h1 h
        have : v (i + 1) ∈ Q := by
          rcases he with ⟨_, hb, _⟩ | ⟨ha, _, _⟩
          · exact hb
          · exact absurd ha (Set.disjoint_left.1 hPQ hvi)
        exact ⟨fun h' => by omega, fun _ => this⟩
      · have hvi := h2 h
        have : v (i + 1) ∈ P := by
          rcases he with ⟨ha, _, _⟩ | ⟨_, hb, _⟩
          · exact absurd ha (Set.disjoint_right.1 hPQ hvi)
          · exact hb
        exact ⟨fun _ => this, fun h' => by omega⟩
  have hvP : ∀ i ≤ p, i % 2 = 0 → v i ∈ P := fun i hi h => (hside i hi).1 h
  have hvQ : ∀ i ≤ p, i % 2 = 1 → v i ∈ Q := fun i hi h => (hside i hi).2 h
  have hpodd : p % 2 = 1 := by
    by_contra hne
    have h0 : p % 2 = 0 := by omega
    have hyP : v p ∈ P := hvP p le_rfl h0
    rw [hvp] at hyP
    rcases hyt with ⟨_, hb, _⟩ | ⟨ha, _, _⟩
    · exact Set.disjoint_left.1 hPQ htP hb
    · exact Set.disjoint_left.1 hPQ hyP ha
  obtain ⟨k, hk⟩ : ∃ k, p + 1 = 2 * k := ⟨(p + 1) / 2, by omega⟩
  have hk1 : 1 ≤ k := by omega
  -- first application of triangular lemma, to P
  let x : Fin k → α := fun i => v (2 * i.val)
  let y' : Fin k → α := fun i => v (2 * i.val + 1)
  have hxP : ∀ i, x i ∈ P := fun i => hvP _ (by have := i.2; omega) (by omega)
  have hyQ : ∀ i, y' i ∈ Q := fun i => hvQ _ (by have := i.2; omega) (by omega)
  have hdiagP : ∀ i, M.IsBase (insert (y' i) (P \ {x i})) := by
    intro i
    have he := hedgeR (2 * i.val) (by have := i.2; omega)
    rcases he with ⟨_, _, h⟩ | ⟨ha, _, _⟩
    · exact h
    · exact absurd (hxP i) (Set.disjoint_right.1 hPQ ha)
  have h1 := Tri.triangular_base M P hP k x y' hxP
    (fun i => ⟨(hdiagP i).subset_ground (Set.mem_insert _ _),
      Set.disjoint_right.1 hPQ (hyQ i)⟩)
    (fun i j h => by
      have := hvinj _ _ (by have := i.2; omega) (by have := j.2; omega) h
      exact Fin.ext (by simpa [Fin.ext_iff] using (by omega : i.val = j.val)))
    (fun i j h => by
      have := hvinj _ _ (by have := i.2; omega) (by have := j.2; omega) h
      exact Fin.ext (by omega))
    hdiagP
    (fun i j hij hb => by
      have hi := i.2
      have hj := j.2
      have hij' : i.val < j.val := hij
      have hbase : Edge M P Q (v (2 * i.val)) (v (2 * j.val + 1)) := Or.inl ⟨hxP i, hyQ j, hb⟩
      exact hchord (2 * i.val) (2 * j.val + 1) (by omega) (by omega) (by omega) hbase)
  -- second application, to Q
  let idx : ℕ → ℕ := fun i => if 2 * i + 2 ≤ p then 2 * i + 2 else 0
  let x2 : Fin k → α := fun i => v (2 * i.val + 1)
  let y2 : Fin k → α := fun i => v (idx i.val)
  have hidx_le : ∀ i : Fin k, idx i.val ≤ p := by
    intro i; simp only [idx]; split_ifs <;> omega
  have hidx_par : ∀ i : Fin k, idx i.val % 2 = 0 := by
    intro i; simp only [idx]; split_ifs <;> omega
  have hx2Q : ∀ i, x2 i ∈ Q := fun i => hvQ _ (by have := i.2; omega) (by omega)
  have hy2P : ∀ i, y2 i ∈ P := fun i => hvP _ (hidx_le i) (hidx_par i)
  have hdiagQ : ∀ i, M.IsBase (insert (y2 i) (Q \ {x2 i})) := by
    intro i
    have hi := i.2
    have he : Edge M P Q (x2 i) (y2 i) := by
      by_cases hc : 2 * i.val + 2 ≤ p
      · have : idx i.val = 2 * i.val + 2 := by simp [idx, hc]
        simp only [y2, this, x2]
        exact hedgeR _ (by omega)
      · have : idx i.val = 0 := by simp [idx, hc]
        have hp' : 2 * i.val + 1 = p := by omega
        simp only [y2, this, x2, hv0, hp', hvp]
        exact hyt
    rcases he with ⟨ha, _, _⟩ | ⟨_, _, h⟩
    · exact absurd ha (Set.disjoint_right.1 hPQ (hx2Q i))
    · exact h
  have h2 := Tri.triangular_base M Q hQ k x2 y2 hx2Q
    (fun i => ⟨(hdiagQ i).subset_ground (Set.mem_insert _ _),
      Set.disjoint_left.1 hPQ (hy2P i)⟩)
    (fun i j h => by
      have := hvinj _ _ (by have := i.2; omega) (by have := j.2; omega) h
      exact Fin.ext (by omega))
    (fun i j h => by
      have := hvinj _ _ (hidx_le i) (hidx_le j) h
      have hi := i.2
      have hj := j.2
      apply Fin.ext
      simp only [idx] at this
      split_ifs at this <;> omega)
    hdiagQ
    (fun i j hij hb => by
      have hi := i.2
      have hj := j.2
      have hij' : i.val < j.val := hij
      have hbase : Edge M P Q (v (2 * i.val + 1)) (v (idx j.val)) := Or.inr ⟨hx2Q i, hy2P j, hb⟩
      by_cases hc : 2 * j.val + 2 ≤ p
      · have : idx j.val = 2 * j.val + 2 := by simp [idx, hc]
        rw [this] at hbase
        exact hchord (2 * i.val + 1) (2 * j.val + 2) (by omega) (by omega) (by omega) hbase
      · have : idx j.val = 0 := by simp [idx, hc]
        rw [this, hv0] at hbase
        exact hback (2 * i.val + 1) (by omega) hbase)
  -- the set X
  refine ⟨{u | ∃ i ≤ p, v i = u}, ⟨0, by omega, hv0⟩, ?_, ?_, ?_⟩
  · rintro u ⟨i, hi, rfl⟩; exact hvW i hi
  · have hX : {u | ∃ i ≤ p, v i = u} = Set.range x ∪ Set.range y' := by
      ext u
      constructor
      · rintro ⟨i, hi, rfl⟩
        rcases Nat.mod_two_eq_zero_or_one i with h | h
        · left; exact ⟨⟨i / 2, by omega⟩, by simp only [x]; congr 1; omega⟩
        · right; exact ⟨⟨i / 2, by omega⟩, by simp only [y']; congr 1; omega⟩
      · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
        · exact ⟨2 * i.val, by have := i.2; omega, rfl⟩
        · exact ⟨2 * i.val + 1, by have := i.2; omega, rfl⟩
    rw [hX, symmDiff_eq_of_union (by rintro _ ⟨i, rfl⟩; exact hxP i)
      (by
        rw [Set.disjoint_left]
        rintro _ ⟨i, rfl⟩
        exact Set.disjoint_right.1 hPQ (hyQ i))]
    exact h1
  · have hX : {u | ∃ i ≤ p, v i = u} = Set.range x2 ∪ Set.range y2 := by
      ext u
      constructor
      · rintro ⟨i, hi, rfl⟩
        rcases Nat.mod_two_eq_zero_or_one i with h | h
        · right
          by_cases h0 : i = 0
          · subst h0
            refine ⟨⟨k - 1, by omega⟩, ?_⟩
            have : ¬ (2 * (k - 1) + 2 ≤ p) := by omega
            simp only [y2, idx, this, if_false]
          · refine ⟨⟨i / 2 - 1, by omega⟩, ?_⟩
            have : 2 * (i / 2 - 1) + 2 ≤ p := by omega
            simp only [y2, idx, this, if_true]
            congr 1; omega
        · left; exact ⟨⟨i / 2, by omega⟩, by simp only [x2]; congr 1; omega⟩
      · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
        · exact ⟨2 * i.val + 1, by have := i.2; omega, rfl⟩
        · exact ⟨idx i.val, hidx_le i, rfl⟩
    rw [hX, symmDiff_eq_of_union (by rintro _ ⟨i, rfl⟩; exact hx2Q i)
      (by
        rw [Set.disjoint_left]
        rintro _ ⟨i, rfl⟩
        exact Set.disjoint_left.1 hPQ (hy2P i))]
    exact h2

end MatroidEquitability.Dev.T3a
end

section
set_option autoImplicit false

namespace MatroidEquitability.Dev.T3b

open MatroidEquitability.Dev.T3a

variable {α : Type*}

/-- Observation 2.3: `e` lies in the closure of its in-neighbours in the exchange graph of `B`. -/
theorem mem_closure_inneighbors (M : Matroid α) {B : Set α} (hB : M.IsBase B) {e : α}
    (heE : e ∈ M.E) (heB : e ∉ B) :
    e ∈ M.closure {a | a ∈ B ∧ M.IsBase (insert e (B \ {a}))} := by
  have hC := hB.fundCircuit_isCircuit heE heB
  have hecl : e ∈ M.closure B := by rwa [hB.closure_eq]
  refine M.closure_subset_closure ?_
    (hC.mem_closure_sdiff_singleton_of_mem (M.mem_fundCircuit e B))
  intro f ⟨hfC, hfe⟩
  have hfe' : f ≠ e := hfe
  have hfB : f ∈ B := by
    have := M.fundCircuit_subset_insert e B hfC
    rcases this with h | h
    · exact absurd h hfe'
    · exact h
  refine ⟨hfB, ?_⟩
  have hind := (hB.indep.mem_fundCircuit_iff hecl heB).1 hfC
  have := hB.exchange_isBase_of_indep' hfB heB hind
  rwa [← Set.insert_sdiff_singleton_comm hfe'.symm] at this

theorem ncard_le_of_subset_closure (M : Matroid α) [M.Finite] {I X : Set α} (hI : M.Indep I)
    (h : I ⊆ M.closure X) (hXE : X ⊆ M.E) : I.ncard ≤ X.ncard := by
  have h1 : I.encard ≤ X.encard :=
    (hI.encard_le_eRk_of_subset h).trans ((M.eRk_closure_eq X).le.trans (M.eRk_le_encard X))
  have hIf : I.Finite := M.ground_finite.subset hI.subset_ground
  have hXf : X.Finite := M.ground_finite.subset hXE
  rw [← hIf.cast_ncard_eq, ← hXf.cast_ncard_eq] at h1
  exact_mod_cast h1

/-- Claims 3.3 and 3.4 of the proof of Theorem 1.4 (paper's `B₁ = D`, `B₂ = B`). -/
theorem exists_t (M : Matroid α) [M.Finite] (B D K : Set α) (hB : M.IsBase B) (hD : M.IsBase D)
    (hBD : Disjoint B D) (hcard : (K ∩ D).ncard < (K ∩ B).ncard) :
    ∃ t ∈ D \ K, ∃ x ∈ K ∩ B, ∃ y ∈ K ∩ B, Edge M B D x t ∧ Edge M B D t y := by
  classical
  have hBf : B.Finite := M.ground_finite.subset hB.subset_ground
  have hDf : D.Finite := M.ground_finite.subset hD.subset_ground
  have hBc : B.ncard = D.ncard := hB.ncard_eq_ncard_of_isBase hD
  have hB1 : (B ∩ K).ncard + (B \ K).ncard = B.ncard :=
    Set.ncard_inter_add_ncard_diff_eq_ncard B K hBf
  have hD1 : (D ∩ K).ncard + (D \ K).ncard = D.ncard :=
    Set.ncard_inter_add_ncard_diff_eq_ncard D K hDf
  rw [Set.inter_comm K D] at hcard
  rw [Set.inter_comm K B] at hcard
  have hlt : (B \ K).ncard < (D \ K).ncard := by omega
  have hH2 : M.Indep (B \ K) := hB.indep.subset Set.diff_subset
  have hH1 : M.Indep (D \ K) := hD.indep.subset Set.diff_subset
  -- T: elements of H1 outside the closure of H2
  have hTne : ∃ t ∈ D \ K, M.Indep (insert t (B \ K)) := by
    have hfin1 : (D \ K).Finite := hDf.subset Set.diff_subset
    have hfin2 : (B \ K).Finite := hBf.subset Set.diff_subset
    have : (B \ K).encard < (D \ K).encard := by
      rw [← hfin1.cast_ncard_eq, ← hfin2.cast_ncard_eq]; exact_mod_cast hlt
    obtain ⟨e, he, hi⟩ := hH2.exists_insert_of_encard_lt hH1 this
    exact ⟨e, he.1, hi⟩
  -- Claim 3.3
  have c33 : ∀ t ∈ D \ K, M.Indep (insert t (B \ K)) →
      ∃ x ∈ K ∩ B, M.IsBase (insert t (B \ {x})) := by
    intro t ht hti
    have htB : t ∉ B := fun h => Set.disjoint_right.1 hBD ht.1 h
    have htnot : t ∉ B \ K := fun h => htB h.1
    have hcl := mem_closure_inneighbors M hB (hD.subset_ground ht.1) htB
    by_contra hno
    push_neg at hno
    have hsub : {a | a ∈ B ∧ M.IsBase (insert t (B \ {a}))} ⊆ B \ K := by
      intro a ⟨haB, hab⟩
      refine ⟨haB, fun haK => hno a ⟨haK, haB⟩ hab⟩
    have := M.closure_subset_closure hsub hcl
    exact ((hH2.notMem_closure_iff_of_notMem htnot (hD.subset_ground ht.1)).2 hti) this
  -- Claim 3.4
  have c34 : ∃ t ∈ D \ K, M.Indep (insert t (B \ K)) ∧ ∃ y ∈ K ∩ B,
      M.IsBase (insert y (D \ {t})) := by
    by_contra hno
    push_neg at hno
    have hK1E : K ∩ D ⊆ M.E := fun a ha => hD.subset_ground ha.2
    have hH2E : B \ K ⊆ M.E := fun a ha => hB.subset_ground ha.1
    have hXE : (K ∩ D) ∪ (B \ K) ⊆ M.E := Set.union_subset hK1E hH2E
    have hK2 : ∀ y ∈ K ∩ B, y ∈ M.closure ((K ∩ D) ∪ (B \ K)) := by
      intro y hy
      have hyD : y ∉ D := fun h => Set.disjoint_left.1 hBD hy.2 h
      have hcl := mem_closure_inneighbors M hD (hB.subset_ground hy.2) hyD
      have hsub : {a | a ∈ D ∧ M.IsBase (insert y (D \ {a}))} ⊆
          M.closure ((K ∩ D) ∪ (B \ K)) := by
        intro a ⟨haD, hab⟩
        by_cases haK : a ∈ K
        · exact M.subset_closure _ hXE (Or.inl ⟨haK, haD⟩)
        · by_cases hai : M.Indep (insert a (B \ K))
          · exact absurd hab (hno a ⟨haD, haK⟩ hai y hy)
          · have haB : a ∉ B \ K := fun h => Set.disjoint_left.1 hBD h.1 haD
            have : a ∈ M.closure (B \ K) := by
              by_contra hn
              exact hai ((hH2.notMem_closure_iff_of_notMem haB (hD.subset_ground haD)).1 hn)
            exact M.closure_subset_closure Set.subset_union_right this
      have := M.closure_subset_closure_of_subset_closure hsub
      exact this hcl
    have hBsub : B ⊆ M.closure ((K ∩ D) ∪ (B \ K)) := by
      intro b hb
      by_cases hbK : b ∈ K
      · exact hK2 b ⟨hbK, hb⟩
      · exact M.subset_closure _ hXE (Or.inr ⟨hb, hbK⟩)
    have h1 := ncard_le_of_subset_closure M hB.indep hBsub hXE
    have h2 : ((K ∩ D) ∪ (B \ K)).ncard ≤ (K ∩ D).ncard + (B \ K).ncard :=
      Set.ncard_union_le _ _
    have hKD : (K ∩ D).ncard = (D ∩ K).ncard := by rw [Set.inter_comm]
    omega
  obtain ⟨t, ht, hti, y, hy, hty⟩ := c34
  obtain ⟨x, hx, hxt⟩ := c33 t ht hti
  refine ⟨t, ht, x, hx, y, hy, Or.inl ⟨hx.2, ht.1, hxt⟩, Or.inr ⟨ht.1, hy.2, hty⟩⟩

/-- Averaging over strong components. -/
theorem exists_class (S B D : Set α) (hSf : S.Finite) (Rs : α → α → Prop)
    (hrefl : ∀ a ∈ S, Rs a a) (htrans : ∀ a b c, Rs a b → Rs b c → Rs a c)
    (hcard : (S ∩ D).ncard < (S ∩ B).ncard) :
    ∃ u ∈ S, ((fun v => v ∈ S ∧ Rs u v ∧ Rs v u) ∩ D : Set α).ncard <
      ((fun v => v ∈ S ∧ Rs u v ∧ Rs v u) ∩ B : Set α).ncard := by
  by_contra hno
  push_neg at hno
  set Cl : α → Set α := fun u => {v | v ∈ S ∧ Rs u v ∧ Rs v u} with hCl
  have hno' : ∀ u ∈ S, (Cl u ∩ B).ncard ≤ (Cl u ∩ D).ncard := hno
  have key : ∀ n, ∀ F : Set α, F.ncard = n → F ⊆ S → (∀ a ∈ F, Cl a ⊆ F) →
      (F ∩ B).ncard ≤ (F ∩ D).ncard := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro F hFn hFS hFcl
      have hFf : F.Finite := hSf.subset hFS
      by_cases hFe : F = ∅
      · subst hFe; simp
      obtain ⟨a, haF⟩ := Set.nonempty_iff_ne_empty.2 hFe
      have haS := hFS haF
      have haCl : a ∈ Cl a := ⟨haS, hrefl a haS, hrefl a haS⟩
      have hClF : Cl a ⊆ F := hFcl a haF
      -- the remainder is a union of classes
      have hrem : ∀ b ∈ F \ Cl a, Cl b ⊆ F \ Cl a := by
        intro b ⟨hbF, hbn⟩ c hc
        refine ⟨hFcl b hbF hc, fun hca => hbn ?_⟩
        obtain ⟨hcS, hbc, hcb⟩ := hc
        obtain ⟨_, hac, hca'⟩ := hca
        exact ⟨hFS hbF, htrans _ _ _ hac hcb, htrans _ _ _ hbc hca'⟩
      have hlt : (F \ Cl a).ncard < n := by
        rw [← hFn]
        exact Set.ncard_lt_ncard ⟨Set.diff_subset, fun h => by
          have := h haF; exact this.2 haCl⟩ hFf
      have := ih _ hlt (F \ Cl a) rfl (Set.diff_subset.trans hFS) hrem
      have hB' := Set.ncard_inter_add_ncard_diff_eq_ncard (F ∩ B) (Cl a) (hFf.subset Set.inter_subset_left)
      have hD' := Set.ncard_inter_add_ncard_diff_eq_ncard (F ∩ D) (Cl a) (hFf.subset Set.inter_subset_left)
      have e1 : (F ∩ B) ∩ Cl a = Cl a ∩ B := by
        ext z; simp only [Set.mem_inter_iff]; constructor
        · rintro ⟨⟨_, hb⟩, hc⟩; exact ⟨hc, hb⟩
        · rintro ⟨hc, hb⟩; exact ⟨⟨hClF hc, hb⟩, hc⟩
      have e2 : (F ∩ D) ∩ Cl a = Cl a ∩ D := by
        ext z; simp only [Set.mem_inter_iff]; constructor
        · rintro ⟨⟨_, hb⟩, hc⟩; exact ⟨hc, hb⟩
        · rintro ⟨hc, hb⟩; exact ⟨⟨hClF hc, hb⟩, hc⟩
      have e3 : (F ∩ B) \ Cl a = (F \ Cl a) ∩ B := by
        ext z; simp only [Set.mem_inter_iff, Set.mem_sdiff]; tauto
      have e4 : (F ∩ D) \ Cl a = (F \ Cl a) ∩ D := by
        ext z; simp only [Set.mem_inter_iff, Set.mem_sdiff]; tauto
      rw [e1, e3] at hB'
      rw [e2, e4] at hD'
      have := hno' a haS
      omega
  have := key _ S rfl subset_rfl (fun a ha v hv => hv.1)
  omega

end MatroidEquitability.Dev.T3b
end

section
set_option autoImplicit false

namespace MatroidEquitability

open MatroidEquitability.Dev.T3a MatroidEquitability.Dev.T3b Relation

theorem chk_theorem_3_exists {α : Type*} (M : Matroid α) [M.Finite] (B D S : Set α)
    (hB : M.IsBase B) (hD : M.IsBase D) (hBD : Disjoint B D) (hS : S ⊆ M.E)
    (hcard : (D ∩ S).ncard < (B ∩ S).ncard) :
    ∃ t ∈ D \ S, ∃ X, IsExchangeable M B D t S X := by
  classical
  set Rs : α → α → Prop := ReflTransGen (fun u v => u ∈ S ∧ v ∈ S ∧ Edge M B D u v) with hRs
  have hSf : S.Finite := M.ground_finite.subset hS
  -- classes: restrict to S ∩ (B ∪ D)
  set S' : Set α := S ∩ (B ∪ D) with hS'
  have hS'f : S'.Finite := hSf.subset Set.inter_subset_left
  have hc1 : (S' ∩ D).ncard = (D ∩ S).ncard := by
    congr 1; ext z; simp only [hS', Set.mem_inter_iff, Set.mem_union]; tauto
  have hc2 : (S' ∩ B).ncard = (B ∩ S).ncard := by
    congr 1; ext z; simp only [hS', Set.mem_inter_iff, Set.mem_union]; tauto
  have hcard' : (S' ∩ D).ncard < (S' ∩ B).ncard := by omega
  have hedgeU : ∀ a b, Edge M B D a b → a ∈ B ∪ D ∧ b ∈ B ∪ D := by
    rintro a b (⟨h1, h2, _⟩ | ⟨h1, h2, _⟩)
    · exact ⟨Or.inl h1, Or.inr h2⟩
    · exact ⟨Or.inr h1, Or.inl h2⟩
  have hRsS : ∀ a b, Rs a b → a = b ∨ (a ∈ S ∧ b ∈ S) := by
    intro a b h
    induction h with
    | refl => exact Or.inl rfl
    | tail _ hbc ih =>
      rename_i b c
      rcases ih with rfl | ⟨ha, hb⟩
      · exact Or.inr ⟨hbc.1, hbc.2.1⟩
      · exact Or.inr ⟨ha, hbc.2.1⟩
  obtain ⟨u, huS, hu⟩ := exists_class S' B D hS'f Rs (fun a _ => ReflTransGen.refl)
    (fun a b c h1 h2 => ReflTransGen.trans h1 h2) hcard'
  set K : Set α := {v | v ∈ S' ∧ Rs u v ∧ Rs v u} with hK
  have hKS : K ⊆ S := fun v hv => hv.1.1
  have hKconn : ∀ a ∈ K, ∀ b ∈ K, Rs a b := fun a ha b hb => ha.2.2.trans hb.2.1
  have hKcl : ∀ a ∈ K, ∀ b ∈ S', Rs a b → Rs b a → b ∈ K :=
    fun a ha b hb h1 h2 => ⟨hb, ha.2.1.trans h1, h2.trans ha.2.2⟩
  have hKc : (K ∩ D).ncard < (K ∩ B).ncard := hu
  obtain ⟨t, ht, x, hx, y, hy, hxt, hty⟩ := exists_t M B D K hB hD hBD hKc
  have hxS : x ∈ S := hKS hx.1
  have hyS : y ∈ S := hKS hy.1
  have htS : t ∉ S := by
    intro htS
    have htS' : t ∈ S' := ⟨htS, Or.inr ht.1⟩
    have h1 : Rs x t := ReflTransGen.single ⟨hxS, htS, hxt⟩
    have h2 : Rs t y := ReflTransGen.single ⟨htS, hyS, hty⟩
    have h3 : Rs y x := hKconn y hy.1 x hx.1
    exact ht.2 (hKcl x hx.1 t htS' h1 (h2.trans h3))
  -- the cycle
  set W : Set α := insert t S' with hW
  have hWsub : W ⊆ D ∪ B := by
    intro z hz
    rcases hz with rfl | hz
    · exact Or.inl ht.1
    · rcases hz.2 with h | h
      · exact Or.inr h
      · exact Or.inl h
  have hmono : ReflTransGen (fun u v => u ∈ W ∧ v ∈ W ∧ Edge M D B u v) y x := by
    have := hKconn y hy.1 x hx.1
    refine ReflTransGen.mono (fun a b h => ?_) y x this
    obtain ⟨ha, hb, he⟩ := h
    have := hedgeU a b he
    exact ⟨Or.inr ⟨ha, this.1⟩, Or.inr ⟨hb, this.2⟩, Edge.swap.1 he⟩
  have hty' : Edge M D B t y := Edge.swap.1 hty
  have hxt' : Edge M D B x t := Edge.swap.1 hxt
  have hyW : y ∈ W := Or.inr ⟨hyS, Or.inl hy.2⟩
  have hxW : x ∈ W := Or.inr ⟨hxS, Or.inl hx.2⟩
  have hreach : ReflTransGen (fun u v => u ∈ W ∧ v ∈ W ∧ Edge M D B u v) t x :=
    ReflTransGen.head ⟨Or.inl rfl, hyW, hty'⟩ hmono
  obtain ⟨X, htX, hXW, hX1, hX2⟩ := exchangeable_of_cycle M D B W hD hB hBD.symm t ht.1
    (Or.inl rfl) hWsub x hxW hxt' hreach
  refine ⟨t, ⟨ht.1, htS⟩, X, ⟨Or.inr ht.1, htS⟩, ?_, htX, ?_, hX2, hX1⟩
  · intro z hz
    rcases hWsub (hXW hz) with h | h
    · exact Or.inr h
    · exact Or.inl h
  · intro z hz
    rcases hXW hz with rfl | hz'
    · exact Or.inl rfl
    · exact Or.inr hz'.1

end MatroidEquitability

end

theorem solution : type_of% @MatroidEquitability.chk_theorem_3_exists := @MatroidEquitability.chk_theorem_3_exists
