-- Prove2me | solution 1 for HarelTarjan.Compressed.lemma8_rank_count
-- status  : ACCEPTED   (prove)
-- author  : @walker
-- created : 2026-09-28T06:08:09.594987+00:00
-- url     : https://prove2.me/submissions/9f192b73-5628-44ee-83cf-a2b0635234c7

import Mathlib
import Definitions.Def_HarelTarjan_Compressed_RootedTree
import Definitions.Def_HarelTarjan_Compressed_HeavyPath
import Definitions.Def_HarelTarjan_Compressed_CompressedTree

open HarelTarjan.Compressed

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Shared infrastructure of the heavy-path decomposition

Self-contained re-derivation of the facts used below: the heavy-path decomposition, Lemma 5
(`size_C` agrees with `size_T` at apices; a non-apex is a leaf of `C`) and Lemma 6 (sizes at
least double along every edge of `C`). -/

/-- The root is a fixed point of every iterate of the parent map. -/
lemma p2m_iterate_root (T : RootedTree V) (j : ℕ) : T.parent^[j] T.root = T.root := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply, T.parent_root, ih]

/-- The root is a fixed point of every iterate of `p_C`. -/
lemma p2m_iterate_root_pC (T : RootedTree V) (j : ℕ) : (pC T)^[j] T.root = T.root := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply', ih, pC, if_pos rfl]

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

/-- If `a` is an apex and an ancestor of `w`, then `a` is an ancestor of `apex w`. -/
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

/-- **Lemma 5**. For an apex `size_C` agrees with `size_T`; any non-apex is a leaf of `C`. -/
theorem p2m_lemma5_sizeC (T : RootedTree V) (v : V) :
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

/-- `size_T` is monotone in the ancestor order. -/
lemma p2m_size_mono (T : RootedTree V) {a w : V} (h : IsAncestor T a w) :
    size T w ≤ size T a := by
  classical
  have hcard : (Finset.univ.filter (fun u => IsAncestor T w u)).card ≤
      (Finset.univ.filter (fun u => IsAncestor T a u)).card := by
    apply Finset.card_le_card
    intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
    exact p2m_isAncestor_trans T h hu
  simpa only [size] using hcard

/-- A strict ancestor has at least two `T`-descendants. -/
lemma p2m_two_le_size_of_isAncestor_ne (T : RootedTree V) {a v : V}
    (h : IsAncestor T a v) (hne : a ≠ v) : 2 ≤ size T a := by
  classical
  have hcard : 2 ≤ (Finset.univ.filter (fun u => IsAncestor T a u)).card := by
    have hsub : ({a, v} : Finset V) ⊆ Finset.univ.filter (fun u => IsAncestor T a u) := by
      intro u hu
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases Finset.mem_insert.mp hu with hu1 | hu2
      · rw [hu1]
        exact p2m_isAncestor_refl T a
      · rw [Finset.mem_singleton] at hu2
        rw [hu2]
        exact h
    have h2 : ({a, v} : Finset V).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simpa [Finset.mem_singleton] using hne),
        Finset.card_singleton]
    calc 2 = ({a, v} : Finset V).card := h2.symm
      _ ≤ (Finset.univ.filter (fun u => IsAncestor T a u)).card := Finset.card_le_card hsub
  simpa only [size] using hcard

/-- **Lemma 6**. Every edge `v → p_C(v)` of `C` satisfies `2 · size_C(v) ≤ size_C(p_C(v))`. -/
theorem p2m_lemma6 (T : RootedTree V) {v : V} (hv : v ≠ T.root) :
    2 * sizeC T v ≤ sizeC T (pC T v) := by
  classical
  have hpCv : pC T v = apex T (T.parent v) := by rw [pC, if_neg hv]
  have hpCa : IsApex T (pC T v) := by
    rw [hpCv]
    exact p2m_isApex_apex T (T.parent v)
  have ha_eq : sizeC T (pC T v) = size T (pC T v) := (p2m_lemma5_sizeC T (pC T v)).1 hpCa
  by_cases ha : IsApex T v
  · have hv_eq : sizeC T v = size T v := (p2m_lemma5_sizeC T v).1 ha
    have hle : 2 * size T v ≤ size T (T.parent v) :=
      not_lt.mp (fun hlt => (p2m_not_isHeavy_of_isApex T ha) ⟨hv, hlt⟩)
    have hmono : size T (T.parent v) ≤ size T (apex T (T.parent v)) :=
      p2m_size_mono T (p2m_isAncestor_apex T (T.parent v))
    rw [hv_eq, ha_eq, hpCv]
    exact le_trans hle hmono
  · have hv_eq : sizeC T v = 1 := (p2m_lemma5_sizeC T v).2 ha
    have hne : pC T v ≠ v := fun h => ha (h ▸ hpCa)
    have hge : 2 ≤ size T (pC T v) :=
      p2m_two_le_size_of_isAncestor_ne T (p2m_isAncestor_pC T v) hne
    rw [hv_eq, ha_eq]
    simpa using hge

/-! ### New ingredients for `lemma8_rank_count` -/

/-- The `C`-subtree of `v`: the set of its descendants in `C`. -/
noncomputable def p2m_cSubtree (T : RootedTree V) (v : V) : Finset V := by
  classical
  exact Finset.univ.filter (fun u => IsAncestorC T v u)

lemma p2m_subtree_card (T : RootedTree V) (v : V) : (p2m_cSubtree T v).card = sizeC T v := rfl

lemma p2m_mem_cSubtree {T : RootedTree V} {v u : V} :
    u ∈ p2m_cSubtree T v ↔ IsAncestorC T v u := by
  simp [p2m_cSubtree]

lemma p2m_sizeC_pos (T : RootedTree V) (v : V) : 0 < sizeC T v := by
  rw [← p2m_subtree_card]
  exact Finset.card_pos.mpr ⟨v, p2m_mem_cSubtree.mpr ⟨0, rfl⟩⟩

/-- `size_C` never decreases when climbing the `C`-parent map. -/
lemma p2m_sizeC_le_pC (T : RootedTree V) (x : V) : sizeC T x ≤ sizeC T (pC T x) := by
  by_cases hx : x = T.root
  · rw [hx, pC, if_pos rfl]
  · have h := p2m_lemma6 T hx
    omega

/-- Monotonicity along the whole `C`-parent chain. -/
lemma p2m_sizeC_iterate_mono (T : RootedTree V) (x : V) (k : ℕ) :
    sizeC T x ≤ sizeC T ((pC T)^[k] x) := by
  induction k with
  | zero => simp
  | succ j ih =>
    calc sizeC T x ≤ sizeC T ((pC T)^[j] x) := ih
      _ ≤ sizeC T (pC T ((pC T)^[j] x)) := p2m_sizeC_le_pC T _
      _ = sizeC T ((pC T)^[j + 1] x) := by rw [Function.iterate_succ_apply']

/-- Sizes at least double when climbing **one or more** steps of `C`, provided we start below
the root. -/
lemma p2m_sizeC_double_iter (T : RootedTree V) (b : V) (hb : b ≠ T.root) {k : ℕ}
    (hk : 1 ≤ k) : 2 * sizeC T b ≤ sizeC T ((pC T)^[k] b) := by
  have h1 : 2 * sizeC T b ≤ sizeC T ((pC T)^[1] b) := by
    rw [Function.iterate_one]
    exact p2m_lemma6 T hb
  have h2 : sizeC T ((pC T)^[1] b) ≤ sizeC T ((pC T)^[k] b) := by
    have h := p2m_sizeC_iterate_mono T ((pC T)^[1] b) (k - 1)
    have hgoal : (pC T)^[k - 1] ((pC T)^[1] b) = (pC T)^[k] b := by
      rw [← Function.iterate_add_apply]
      congr 1
      omega
    rwa [hgoal] at h
  omega

/-- `size_C` growing by a factor `2` forces the rank to increase. -/
lemma p2m_rank_lt_of_two_mul_le (T : RootedTree V) {a b : V}
    (h : 2 * sizeC T b ≤ sizeC T a) : rank T b < rank T a := by
  have hpos : sizeC T b ≠ 0 := Nat.pos_iff_ne_zero.mp (p2m_sizeC_pos T b)
  have hpow : 2 ^ (rank T b + 1) ≤ sizeC T a :=
    calc 2 ^ (rank T b + 1) = 2 * 2 ^ rank T b := by rw [pow_succ']
      _ ≤ 2 * sizeC T b := Nat.mul_le_mul_left 2 (Nat.pow_log_le_self 2 hpos)
      _ ≤ sizeC T a := h
  have hle : rank T b + 1 ≤ rank T a := Nat.le_log_of_pow_le (by norm_num) hpow
  omega

/-- A proper `C`-ancestor has strictly greater rank. -/
lemma p2m_rank_lt_of_iterate (T : RootedTree V) {a b : V} {k : ℕ} (hk : 1 ≤ k)
    (h : (pC T)^[k] a = b) (hne : a ≠ b) : rank T a < rank T b := by
  have haroot : a ≠ T.root := by
    intro har
    have hfix : (pC T)^[k] a = a := by rw [har]; exact p2m_iterate_root_pC T k
    exact hne (hfix.symm.trans h)
  have hdbl := p2m_sizeC_double_iter T a haroot hk
  rw [h] at hdbl
  exact p2m_rank_lt_of_two_mul_le T hdbl

/-- Two distinct vertices of equal rank have disjoint `C`-subtrees. -/
lemma p2m_disjoint_cSubtree_of_rank_eq (T : RootedTree V) {a b : V} (hne : a ≠ b)
    (hrank : rank T a = rank T b) : Disjoint (p2m_cSubtree T a) (p2m_cSubtree T b) := by
  rw [Finset.disjoint_left]
  intro u hua hub
  obtain ⟨m, hm⟩ := p2m_mem_cSubtree.mp hua
  obtain ⟨n, hn⟩ := p2m_mem_cSubtree.mp hub
  rcases le_total m n with hmn | hnm
  · have hb : (pC T)^[n - m] a = b := by
      have h1 : (pC T)^[n] u = (pC T)^[n - m] ((pC T)^[m] u) := by
        conv_lhs => rw [← Nat.sub_add_cancel hmn]
        rw [Function.iterate_add_apply]
      rw [← hm, ← h1, hn]
    have hkpos : 1 ≤ n - m := by
      rcases Nat.eq_zero_or_pos (n - m) with h0 | hpos
      · exfalso
        exact hne (by rw [← hm, ← hn, show n = m by omega])
      · exact hpos
    exact absurd (p2m_rank_lt_of_iterate T hkpos hb hne) (by omega)
  · have ha : (pC T)^[m - n] b = a := by
      have h1 : (pC T)^[m] u = (pC T)^[m - n] ((pC T)^[n] u) := by
        conv_lhs => rw [← Nat.sub_add_cancel hnm]
        rw [Function.iterate_add_apply]
      rw [← hn, ← h1, hm]
    have hkpos : 1 ≤ m - n := by
      rcases Nat.eq_zero_or_pos (m - n) with h0 | hpos
      · exfalso
        exact hne (by rw [← hm, ← hn, show m = n by omega])
      · exact hpos
    exact absurd (p2m_rank_lt_of_iterate T (a := b) (b := a) hkpos ha hne.symm) (by omega)

/-- **Lemma 8** (Harel–Tarjan, §4, p. 344). At most `n / 2^i` vertices of `C` can have rank `i`,
stated without division as `#{v : rank(v) = i} · 2^i ≤ n`.

Every vertex of rank `i` has a `C`-subtree with at least `2^i` vertices; distinct vertices of the
same rank have disjoint subtrees (a proper `C`-ancestor has strictly larger rank, by Lemma 6),
and all these subtrees live inside the `n` vertices of `T`. -/
theorem solution {V : Type*} [Fintype V] [DecidableEq V] (T : RootedTree V) (i : ℕ) :
    (Finset.univ.filter (fun v => rank T v = i)).card * 2 ^ i ≤ Fintype.card V := by
  classical
  set R : Finset V := Finset.univ.filter (fun v => rank T v = i) with hR
  have hmem : ∀ v, v ∈ R ↔ rank T v = i := by
    intro v
    rw [hR]
    simp
  have hpair : (R : Set V).PairwiseDisjoint (p2m_cSubtree T) := by
    intro a ha b hb hab
    simpa only [Function.onFun] using p2m_disjoint_cSubtree_of_rank_eq T hab
      (((hmem a).mp ha).trans ((hmem b).mp hb).symm)
  have hcard : (R.biUnion (p2m_cSubtree T)).card = ∑ v ∈ R, (p2m_cSubtree T v).card :=
    Finset.card_biUnion hpair
  have hsum : ∑ v ∈ R, 2 ^ i ≤ ∑ v ∈ R, (p2m_cSubtree T v).card := by
    apply Finset.sum_le_sum
    intro v hv
    have hrank : rank T v = i := (hmem v).mp hv
    have hone : 2 ^ i ≤ sizeC T v := by
      rw [← hrank]
      exact Nat.pow_log_le_self 2 (Nat.pos_iff_ne_zero.mp (p2m_sizeC_pos T v))
    rwa [p2m_subtree_card]
  have hle : (R.biUnion (p2m_cSubtree T)).card ≤ Fintype.card V := by
    rw [← Finset.card_univ]
    exact Finset.card_le_card (fun _ _ => Finset.mem_univ _)
  calc R.card * 2 ^ i = ∑ v ∈ R, 2 ^ i := by
        rw [Finset.sum_const]
        simp
    _ ≤ ∑ v ∈ R, (p2m_cSubtree T v).card := hsum
    _ = (R.biUnion (p2m_cSubtree T)).card := hcard.symm
    _ ≤ Fintype.card V := hle
