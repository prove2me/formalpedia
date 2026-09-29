-- Prove2me | solution 1 for HarelTarjan.Compressed.lemma5_sizeC
-- status  : ACCEPTED   (prove)
-- author  : @walker
-- created : 2026-09-28T04:30:15.955595+00:00
-- url     : https://prove2.me/submissions/e3f15a8d-ae1d-4398-a2d8-33d38595b246

import Mathlib
import Definitions.Def_HarelTarjan_Compressed_RootedTree
import Definitions.Def_HarelTarjan_Compressed_HeavyPath
import Definitions.Def_HarelTarjan_Compressed_CompressedTree

open HarelTarjan.Compressed

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Helper lemmas for `HarelTarjan.Compressed.lemma5_sizeC` -/

/-- The root is a fixed point of every iterate of the parent map. -/
lemma p2m_iterate_root (T : RootedTree V) (j : ℕ) : T.parent^[j] T.root = T.root := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply, T.parent_root, ih]

/-- Below the root there are no cycles: `p^[k] v ≠ v` for `v ≠ r` and `k ≥ 1`. -/
lemma p2m_iterate_ne_self (T : RootedTree V) {v : V} (hv : v ≠ T.root) {k : ℕ}
    (hk : 1 ≤ k) : T.parent^[k] v ≠ v := by
  intro h
  have hspec : T.parent^[depth T v] v = T.root := Nat.find_spec (T.reaches v)
  have hdpos : 0 < depth T v := by
    by_contra hc
    have h0 : depth T v = 0 := by omega
    rw [h0] at hspec
    exact hv (by simpa using hspec)
  rcases lt_or_ge k (depth T v) with hlt | hge
  · have h1 : T.parent^[depth T v] v = T.parent^[depth T v - k] (T.parent^[k] v) := by
      conv_lhs => rw [← Nat.sub_add_cancel (le_of_lt hlt)]
      rw [Function.iterate_add_apply]
    have h2 : T.parent^[depth T v - k] v = T.root := by
      have h3 := h1
      simp only [h] at h3
      exact h3.symm.trans hspec
    exact (Nat.find_min (T.reaches v) (Nat.sub_lt hdpos (by omega))) h2
  · have h1 : T.parent^[k] v = T.parent^[k - depth T v] (T.parent^[depth T v] v) := by
      conv_lhs => rw [← Nat.sub_add_cancel hge]
      rw [Function.iterate_add_apply]
    have h2 : T.parent^[k] v = T.root := by
      rw [h1, hspec, p2m_iterate_root]
    exact hv (h.symm.trans h2)

/-- `¬ IsHeavy v` implies `v` is an apex. -/
lemma p2m_isApex_of_not_isHeavy (T : RootedTree V) {v : V} (h : ¬ IsHeavy T v) :
    IsApex T v := by
  have hle : apexSteps T v ≤ 0 :=
    Nat.find_min' (exists_not_isHeavy_iterate T v) (by simpa using h)
  have hz : apexSteps T v = 0 := by omega
  show apex T v = v
  rw [apex, hz]
  rfl

/-- An apex is not the lower endpoint of a heavy edge. -/
lemma p2m_not_isHeavy_of_isApex (T : RootedTree V) {v : V} (h : IsApex T v) :
    ¬ IsHeavy T v := by
  have hv : T.parent^[apexSteps T v] v = v := h
  have hspec : ¬ IsHeavy T (T.parent^[apexSteps T v] v) :=
    Nat.find_spec (exists_not_isHeavy_iterate T v)
  rwa [hv] at hspec

lemma p2m_isApex_iff_not_isHeavy (T : RootedTree V) (v : V) :
    IsApex T v ↔ ¬ IsHeavy T v :=
  ⟨p2m_not_isHeavy_of_isApex T, p2m_isApex_of_not_isHeavy T⟩

lemma p2m_isApex_root (T : RootedTree V) : IsApex T T.root := by
  apply p2m_isApex_of_not_isHeavy
  intro h
  exact h.1 rfl

lemma p2m_isApex_apex (T : RootedTree V) (w : V) : IsApex T (apex T w) := by
  apply p2m_isApex_of_not_isHeavy
  have hspec : ¬ IsHeavy T (T.parent^[apexSteps T w] w) :=
    Nat.find_spec (exists_not_isHeavy_iterate T w)
  rwa [← apex] at hspec

lemma p2m_isAncestor_refl (T : RootedTree V) (v : V) : IsAncestor T v v := ⟨0, rfl⟩

lemma p2m_isAncestor_trans (T : RootedTree V) {a b c : V} (hab : IsAncestor T a b)
    (hbc : IsAncestor T b c) : IsAncestor T a c := by
  obtain ⟨i, hi⟩ := hab
  obtain ⟨j, hj⟩ := hbc
  exact ⟨i + j, by rw [Function.iterate_add_apply, hj, hi]⟩

/-- `apex w` is an ancestor of `w`. -/
lemma p2m_isAncestor_apex (T : RootedTree V) (w : V) : IsAncestor T (apex T w) w :=
  ⟨apexSteps T w, rfl⟩

/-- `p_C w` is an ancestor of `w` in `T`. -/
lemma p2m_isAncestor_pC (T : RootedTree V) (w : V) : IsAncestor T (pC T w) w := by
  by_cases hw : w = T.root
  · subst hw
    exact ⟨0, by simp [pC]⟩
  · obtain ⟨i, hi⟩ := p2m_isAncestor_apex T (T.parent w)
    refine ⟨i + 1, ?_⟩
    rw [Function.iterate_succ_apply, pC, if_neg hw]
    exact hi

/-- Every `C`-descendant is a `T`-descendant. -/
lemma p2m_isAncestor_iterate_pC (T : RootedTree V) :
    ∀ n (u : V), IsAncestor T ((pC T)^[n] u) u := by
  intro n
  induction n with
  | zero =>
    intro u
    exact p2m_isAncestor_refl T u
  | succ j ih =>
    intro u
    rw [Function.iterate_succ_apply]
    exact p2m_isAncestor_trans T (ih (pC T u)) (p2m_isAncestor_pC T u)

lemma p2m_isAncestor_of_isAncestorC' (T : RootedTree V) {v u : V}
    (h : IsAncestorC T v u) : IsAncestor T v u := by
  obtain ⟨n, hn⟩ := h
  rw [← hn]
  exact p2m_isAncestor_iterate_pC T n u

/-- If `a` is an apex and an ancestor of `w`, then `a` is an ancestor of `apex w`.

The point is that the two are comparable along the path from `w` to the root, and an apex
cannot sit strictly inside a heavy path. -/
lemma p2m_iterate_apex_eq (T : RootedTree V) {a w : V} (ha : IsApex T a) {i : ℕ}
    (hi : T.parent^[i] w = a) :
    T.parent^[i - apexSteps T w] (apex T w) = a := by
  by_cases hle : apexSteps T w ≤ i
  · have h1 : T.parent^[i - apexSteps T w] (T.parent^[apexSteps T w] w) = T.parent^[i] w := by
      rw [← Function.iterate_add_apply, Nat.sub_add_cancel hle]
    rw [apex, h1, hi]
  · exfalso
    have hlt : i < apexSteps T w := Nat.not_le.mp hle
    have hnn : ¬ ¬ IsHeavy T (T.parent^[i] w) :=
      Nat.find_min (exists_not_isHeavy_iterate T w) hlt
    have hh : IsHeavy T (T.parent^[i] w) := not_not.mp hnn
    rw [hi] at hh
    exact ((p2m_isApex_iff_not_isHeavy T a).mp ha) hh

/-- Step-count version of the key lemma. -/
lemma p2m_isAncestorC_of_isAncestor (T : RootedTree V) :
    ∀ n (w a : V), IsApex T a → T.parent^[n] w = a → IsAncestorC T a w := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro w a ha hn
    by_cases haw : a = w
    · subst haw
      exact ⟨0, rfl⟩
    · have hwroot : w ≠ T.root := by
        intro hwr
        exact haw (by rw [← hn, hwr]; exact p2m_iterate_root T n)
      have hn0 : n ≠ 0 := by
        rintro rfl
        exact haw hn.symm
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
      rw [Function.iterate_succ_apply] at hn
      have hstep : T.parent^[m - apexSteps T (T.parent w)] (apex T (T.parent w)) = a :=
        p2m_iterate_apex_eq T ha hn
      have hlt : m - apexSteps T (T.parent w) < m + 1 :=
        lt_of_le_of_lt (Nat.sub_le m _) (Nat.lt_succ_self m)
      obtain ⟨j, hj⟩ := ih _ hlt (apex T (T.parent w)) a ha hstep
      refine ⟨j + 1, ?_⟩
      rw [Function.iterate_succ_apply, pC, if_neg hwroot]
      exact hj

lemma p2m_isAncestorC_of_isAncestor' (T : RootedTree V) {a w : V} (ha : IsApex T a)
    (h : IsAncestor T a w) : IsAncestorC T a w := by
  obtain ⟨n, hn⟩ := h
  exact p2m_isAncestorC_of_isAncestor T n w a ha hn

theorem solution {V : Type*} [Fintype V] [DecidableEq V] (T : RootedTree V) (v : V) :
    (IsApex T v → sizeC T v = size T v) ∧ (¬ IsApex T v → sizeC T v = 1) := by
  classical
  constructor
  · intro hv
    have hset : Finset.univ.filter (fun u => IsAncestorC T v u) =
        Finset.univ.filter (fun u => IsAncestor T v u) := by
      apply Finset.filter_congr
      intro u _
      exact ⟨fun h => p2m_isAncestor_of_isAncestorC' T h,
        fun h => p2m_isAncestorC_of_isAncestor' T hv h⟩
    simp only [sizeC, size, hset]
  · intro hv
    have hset : Finset.univ.filter (fun u => IsAncestorC T v u) = {v} := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · rintro ⟨i, hi⟩
        cases i with
        | zero => simpa using hi
        | succ j =>
          rw [Function.iterate_succ_apply'] at hi
          have hvapex : IsApex T v := by
            have hw : pC T ((pC T)^[j] u) = v := hi
            rw [pC] at hw
            by_cases hroot : (pC T)^[j] u = T.root
            · rw [if_pos hroot] at hw
              rw [← hw]
              exact p2m_isApex_root T
            · rw [if_neg hroot] at hw
              rw [← hw]
              exact p2m_isApex_apex T (T.parent ((pC T)^[j] u))
          exact absurd hvapex hv
      · intro hu
        subst hu
        exact ⟨0, rfl⟩
    simp only [sizeC, hset, Finset.card_singleton]
