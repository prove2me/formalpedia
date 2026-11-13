-- Prove2me | solution 1 for LocalLemmaHierarchy.Completeness.proposition_3_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T07:01:47.503982+00:00
-- url     : https://prove2.me/submissions/1d6a5799-e577-4992-8320-ef6018ed65d6

import Mathlib
import Definitions.Def_LocalLemmaHierarchy_Completeness_Representation
import Definitions.Def_LocalLemmaHierarchy_Completeness_Histories
import Definitions.Def_LocalLemmaHierarchy_Completeness_Memory

section
set_option autoImplicit false

open scoped ENNReal NNReal
open Filter Topology

namespace LocalLemmaHierarchy.Completeness.Dev.P33

open scoped Classical

variable {V T : Type} {R : PosLocalDeletionRep V T}

theorem endpointOf_append (s : V) (l1 l2 : List (Move R)) :
    Hist.endpointOf s (l1 ++ l2) = Hist.endpointOf (Hist.endpointOf s l1) l2 := by
  unfold Hist.endpointOf
  rw [List.getLast?_append]
  cases h2 : l2.getLast? <;> simp

theorem mem_deleted (ms : List (Move R)) (w : V) :
    w ∈ deleted R ms ↔ ∃ m ∈ ms, w ∈ departure R m := by
  induction ms with
  | nil => simp [deleted]
  | cons m ms ih =>
    have : deleted R (m :: ms) = departure R m ∪ deleted R ms := by simp [deleted]
    rw [this, Finset.mem_union, ih]
    simp

theorem deleted_mono {l l' : List (Move R)} (h : ∀ m ∈ l, m ∈ l') : deleted R l ⊆ deleted R l' := by
  intro w hw
  rw [mem_deleted] at hw ⊢
  obtain ⟨m, hm, hw⟩ := hw
  exact ⟨m, h m hm, hw⟩

theorem suffix_exact {h : Hist R} (he : IsExact R Set.univ h) (j : ℕ) :
    IsExact R Set.univ (h.suffix j) := by
  refine ⟨Set.mem_univ _, ?_⟩
  intro i hi
  set k := h.moves.length - j with hk
  have hi' : i < (h.moves.drop k).length := hi
  rw [List.length_drop] at hi'
  have hki : k + i < h.moves.length := by omega
  have hget : (h.suffix j).moves[i] = h.moves[k + i] := by
    simp only [Hist.suffix]
    rw [List.getElem_drop]
  have htake : h.moves.take (k + i) = h.moves.take k ++ (h.moves.drop k).take i := by
    rw [List.take_add]
  have hleg := he.2 (k + i) hki
  obtain ⟨h1, h2, h3, h4⟩ := hleg
  have hsub : deleted R ((h.suffix j).moves.take i) ⊆ deleted R (h.moves.take (k + i)) := by
    apply deleted_mono
    intro m hm
    rw [htake]
    exact List.mem_append_right _ hm
  have hend : Hist.endpointOf (h.suffix j).start ((h.suffix j).moves.take i)
      = Hist.endpointOf h.start (h.moves.take (k + i)) := by
    rw [htake, endpointOf_append]
    rfl
  show LegalExactStep R Set.univ (h.suffix j).start ((h.suffix j).moves.take i)
      ((h.suffix j).moves[i])
  rw [hget]
  refine ⟨by rw [hend]; exact h1, ?_, ?_, h4⟩
  · intro w hw
    have := h2 hw
    simp only [Set.mem_sdiff, Set.mem_univ, true_and, Finset.mem_coe] at this ⊢
    exact fun hh => this (hsub hh)
  · refine ⟨h3.1, Set.mem_sdiff_of_mem (Set.mem_univ _) ?_⟩
    intro hh
    have := h3.2
    simp only [Set.mem_sdiff, Set.mem_univ, true_and, Finset.mem_coe] at this
    exact this (hsub hh)

theorem append_exact {s : Hist R} (hs : IsExact R Set.univ s) (a : R.Opt s.endpoint) (u : V)
    (ha : Disjoint (R.A s.endpoint a) (deleted R s.moves))
    (hu : u ∈ R.D s.endpoint a \ insert s.endpoint (deleted R s.moves)) :
    IsExact R Set.univ (s.append ⟨s.endpoint, a, u⟩) := by
  refine ⟨hs.1, ?_⟩
  intro i hi
  have hi' : i < s.moves.length + 1 := by
    simpa [Hist.append] using hi
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi' with hlt | heq
  · have := hs.2 i hlt
    have e1 : (s.append ⟨s.endpoint, a, u⟩).moves.take i = s.moves.take i := by
      simp only [Hist.append]
      rw [List.take_append_of_le_length hlt.le]
    have e2 : (s.append ⟨s.endpoint, a, u⟩).moves[i] = s.moves[i] := by
      simp only [Hist.append]
      rw [List.getElem_append_left hlt]
    show LegalExactStep R Set.univ s.start ((s.append ⟨s.endpoint, a, u⟩).moves.take i)
      ((s.append ⟨s.endpoint, a, u⟩).moves[i])
    rw [e1, e2]
    exact this
  · subst heq
    have e1 : (s.append ⟨s.endpoint, a, u⟩).moves.take s.moves.length = s.moves := by
      simp [Hist.append]
    have e2 : (s.append ⟨s.endpoint, a, u⟩).moves[s.moves.length] = ⟨s.endpoint, a, u⟩ := by
      simp [Hist.append]
    show LegalExactStep R Set.univ s.start ((s.append ⟨s.endpoint, a, u⟩).moves.take s.moves.length)
      ((s.append ⟨s.endpoint, a, u⟩).moves[s.moves.length])
    rw [e1, e2]
    simp only [Finset.mem_sdiff, Finset.mem_insert, not_or] at hu
    refine ⟨rfl, ?_, ?_, hu.2.1⟩
    · intro w hw
      simp only [Set.mem_sdiff, Set.mem_univ, true_and, Finset.mem_coe]
      exact Finset.disjoint_left.mp ha hw
    · refine ⟨by simpa using hu.1, ?_⟩
      simp only [Set.mem_sdiff, Set.mem_univ, true_and, Finset.mem_coe]
      exact hu.2.2

theorem memStar_state {q : ℕ} {s : Hist R} (hs : IsMemState R q s) (a : R.Opt s.endpoint) (u : V)
    (ha : Disjoint (R.A s.endpoint a) (deleted R s.moves))
    (hu : u ∈ R.D s.endpoint a \ insert s.endpoint (deleted R s.moves)) :
    IsMemState R q (memStar q s a u) := by
  refine ⟨suffix_exact (append_exact hs.1 a u ha hu) q, ?_⟩
  show (((s.append ⟨s.endpoint, a, u⟩).moves).drop
      ((s.append ⟨s.endpoint, a, u⟩).moves.length - q)).length ≤ q
  simp only [Hist.append, List.length_drop, List.length_append, List.length_singleton]
  omega


section Analysis

variable {q : ℕ} {p : T → ℝ}

theorem coef_nonneg (hp : ∀ τ, 0 ≤ p τ) (v : V) (a : R.Opt v) :
    0 ≤ R.c v a * p (R.label v a) :=
  mul_nonneg (R.c_pos v a).le (hp _)

theorem memUpdate_mono (hp : ∀ τ, 0 ≤ p τ) {x y : Hist R → ℝ} {s : Hist R}
    (hs : IsMemState R q s)
    (hxy : ∀ t, IsMemState R q t → 0 ≤ x t ∧ x t ≤ y t ∧ y t < 1) :
    memUpdate R q p x s ≤ memUpdate R q p y s := by
  unfold memUpdate
  refine Finset.sum_le_sum fun a ha => ?_
  rw [Finset.mem_filter] at ha
  refine mul_le_mul_of_nonneg_left ?_ (coef_nonneg hp _ a)
  refine Finset.prod_le_prod (fun u hu => ?_) (fun u hu => ?_)
  · have h := hxy _ (memStar_state hs a u ha.2 hu)
    exact inv_nonneg.mpr (by linarith [h.2.1, h.2.2])
  · have h := hxy _ (memStar_state hs a u ha.2 hu)
    exact inv_anti₀ (by linarith [h.2.1, h.2.2]) (by linarith [h.2.1, h.2.2])

theorem memUpdate_nonneg (hp : ∀ τ, 0 ≤ p τ) {x : Hist R → ℝ} {s : Hist R}
    (hs : IsMemState R q s) (hx : ∀ t, IsMemState R q t → x t < 1) :
    0 ≤ memUpdate R q p x s := by
  unfold memUpdate
  refine Finset.sum_nonneg fun a ha => ?_
  rw [Finset.mem_filter] at ha
  refine mul_nonneg (coef_nonneg hp _ a) (Finset.prod_nonneg fun u hu => ?_)
  exact inv_nonneg.mpr (by linarith [hx _ (memStar_state hs a u ha.2 hu)])

theorem memUpdate_tendsto {f : ℕ → Hist R → ℝ} {g : Hist R → ℝ}
    (hfg : ∀ t, IsMemState R q t → Tendsto (fun n => f n t) atTop (𝓝 (g t)))
    (hg : ∀ t, IsMemState R q t → g t < 1) {s : Hist R} (hs : IsMemState R q s) :
    Tendsto (fun n => memUpdate R q p (f n) s) atTop (𝓝 (memUpdate R q p g s)) := by
  unfold memUpdate
  refine tendsto_finsetSum _ fun a ha => ?_
  rw [Finset.mem_filter] at ha
  refine Tendsto.const_mul _ (tendsto_finsetProd _ fun u hu => ?_)
  have hst := memStar_state hs a u ha.2 hu
  refine Tendsto.inv₀ (tendsto_const_nhds.sub (hfg _ hst)) ?_
  exact (by linarith [hg _ hst] : (1 : ℝ) - g _ ≠ 0) |> fun h => h

theorem iter_bounds (hp : ∀ τ, 0 ≤ p τ) {x : Hist R → ℝ} (hx : IsMemCertificate R q p x) :
    ∀ n, ∀ s, IsMemState R q s →
      0 ≤ memIter R q p n s ∧ memIter R q p n s ≤ memIter R q p (n + 1) s ∧
        memIter R q p n s ≤ x s := by
  have h1 : ∀ n, ∀ s, IsMemState R q s → 0 ≤ memIter R q p n s ∧ memIter R q p n s ≤ x s := by
    intro n
    induction n with
    | zero => intro s hs; exact ⟨le_rfl, (hx s hs).1⟩
    | succ n ih =>
      intro s hs
      refine ⟨memUpdate_nonneg hp hs fun t ht => lt_of_le_of_lt (ih t ht).2 (hx t ht).2.1, ?_⟩
      calc memIter R q p (n + 1) s = memUpdate R q p (memIter R q p n) s := rfl
        _ ≤ memUpdate R q p x s := memUpdate_mono hp hs fun t ht =>
            ⟨(ih t ht).1, (ih t ht).2, (hx t ht).2.1⟩
        _ ≤ x s := (hx s hs).2.2
  have h2 : ∀ n, ∀ s, IsMemState R q s → memIter R q p n s ≤ memIter R q p (n + 1) s := by
    intro n
    induction n with
    | zero => intro s hs; exact (h1 1 s hs).1
    | succ n ih =>
      intro s hs
      show memUpdate R q p (memIter R q p n) s ≤ memUpdate R q p (memIter R q p (n + 1)) s
      exact memUpdate_mono hp hs fun t ht =>
        ⟨(h1 n t ht).1, ih t ht, lt_of_le_of_lt (h1 (n + 1) t ht).2 (hx t ht).2.1⟩
  exact fun n s hs => ⟨(h1 n s hs).1, h2 n s hs, (h1 n s hs).2⟩

/-- Existence of the limit of the iteration at states, given a certificate. -/
theorem iter_tendsto (hp : ∀ τ, 0 ≤ p τ) {x : Hist R → ℝ} (hx : IsMemCertificate R q p x)
    {s : Hist R} (hs : IsMemState R q s) :
    ∃ l, Tendsto (fun n => memIter R q p n s) atTop (𝓝 l) := by
  have hmono : Monotone (fun n => memIter R q p n s) := by
    refine monotone_nat_of_le_succ fun n => ?_
    exact (iter_bounds hp hx n s hs).2.1
  have hbdd : BddAbove (Set.range fun n => memIter R q p n s) :=
    ⟨x s, by rintro _ ⟨n, rfl⟩; exact (iter_bounds hp hx n s hs).2.2⟩
  exact ⟨_, tendsto_atTop_ciSup hmono hbdd⟩

/-- Properties of any limit of the iteration at states, given a certificate. -/
theorem limit_props (hp : ∀ τ, 0 ≤ p τ) {x : Hist R → ℝ} (hx : IsMemCertificate R q p x)
    {L : Hist R → ℝ}
    (hL : ∀ s, IsMemState R q s → Tendsto (fun n => memIter R q p n s) atTop (𝓝 (L s)))
    {s : Hist R} (hs : IsMemState R q s) : 0 ≤ L s ∧ L s ≤ x s ∧ L s < 1 := by
  have h0 : 0 ≤ L s := ge_of_tendsto' (hL s hs) fun n => (iter_bounds hp hx n s hs).1
  have h1 : L s ≤ x s := le_of_tendsto' (hL s hs) fun n => (iter_bounds hp hx n s hs).2.2
  exact ⟨h0, h1, lt_of_le_of_lt h1 (hx s hs).2.1⟩

/-- A limit of the iteration with values below one is a fixed point. -/
theorem limit_fixed (hp : ∀ τ, 0 ≤ p τ) {L : Hist R → ℝ}
    (hL : ∀ s, IsMemState R q s → Tendsto (fun n => memIter R q p n s) atTop (𝓝 (L s)))
    (hL1 : ∀ s, IsMemState R q s → L s < 1) {s : Hist R} (hs : IsMemState R q s) :
    memUpdate R q p L s = L s := by
  have h1 := memUpdate_tendsto (p := p) hL hL1 hs
  have h2 : Tendsto (fun n => memUpdate R q p (memIter R q p n) s) atTop (𝓝 (L s)) :=
    (hL s hs).comp (tendsto_add_atTop_nat 1)
  exact tendsto_nhds_unique h1 h2

/-- The limit is below any fixed point with values in `[0,1)`. -/
theorem iter_le_fixed (hp : ∀ τ, 0 ≤ p τ) {y : Hist R → ℝ}
    (hy : ∀ s, IsMemState R q s → memUpdate R q p y s = y s ∧ 0 ≤ y s ∧ y s < 1) :
    ∀ n, ∀ s, IsMemState R q s → memIter R q p n s ≤ y s := by
  have hcert : IsMemCertificate R q p y := fun s hs =>
    ⟨(hy s hs).2.1, (hy s hs).2.2, (hy s hs).1.le⟩
  exact fun n s hs => (iter_bounds hp hcert n s hs).2.2

end Analysis

section Grouped

variable {q : ℕ} {p : T → ℝ}

theorem memUpdate_eq_grouped (P : GroupedPresentation R q p) {x : Hist R → ℝ} {y : P.Θ → ℝ}
    (hxy : ∀ t, IsMemState R q t → x t = y (P.type t)) {s : Hist R} (hs : IsMemState R q s) :
    memUpdate R q p x s = groupedUpdate P.rows y (P.type s) := by
  unfold groupedUpdate
  rw [← P.row_eq s hs]
  unfold memUpdate memRowData
  rw [Multiset.map_map, Finset.sum_eq_multiset_sum]
  congr 1
  apply Multiset.map_congr rfl
  intro a ha
  rw [Finset.mem_val, Finset.mem_filter] at ha
  simp only [Function.comp, Multiset.map_map]
  congr 1
  refine congrArg Multiset.prod (Multiset.map_congr rfl ?_)
  intro u hu
  rw [Finset.mem_val] at hu
  simp [hxy _ (memStar_state hs a u ha.2 hu)]

theorem iter_type_inv (hp : ∀ τ, 0 ≤ p τ) (P : GroupedPresentation R q p) :
    ∀ n, ∀ s s', IsMemState R q s → IsMemState R q s' → P.type s = P.type s' →
      memIter R q p n s = memIter R q p n s' := by
  intro n
  induction n with
  | zero => intros; rfl
  | succ n ih =>
    intro s s' hs hs' hty
    have key : ∀ t, IsMemState R q t →
        memIter R q p n t = (fun k => memIter R q p n (Classical.choose (P.type_surj k)))
          (P.type t) := by
      intro t ht
      have hc := Classical.choose_spec (P.type_surj (P.type t))
      exact ih _ _ ht hc.1 hc.2.symm
    show memUpdate R q p (memIter R q p n) s = memUpdate R q p (memIter R q p n) s'
    rw [memUpdate_eq_grouped P (y := fun k => memIter R q p n (Classical.choose (P.type_surj k)))
      key hs, memUpdate_eq_grouped P (y := fun k => memIter R q p n (Classical.choose (P.type_surj k)))
      key hs', hty]

end Grouped

end LocalLemmaHierarchy.Completeness.Dev.P33

namespace LocalLemmaHierarchy.Completeness

open Dev.P33 in
theorem chk_proposition_3_3 {V T : Type} (R : PosLocalDeletionRep V T) (q : ℕ) (p : T → ℝ)
    (hp : ∀ τ, 0 ≤ p τ) :
    ((∃ x : Hist R → ℝ, IsMemCertificate R q p x) ↔
      ((∀ n s, IsMemState R q s → 0 ≤ memIter R q p n s ∧ memIter R q p n s < 1) ∧
        ∃ L : Hist R → ℝ, ∀ s, IsMemState R q s →
          0 ≤ L s ∧ L s < 1 ∧ Tendsto (fun n => memIter R q p n s) atTop (𝓝 (L s)))) ∧
    (∀ L : Hist R → ℝ, (∃ x : Hist R → ℝ, IsMemCertificate R q p x) →
      (∀ s, IsMemState R q s → Tendsto (fun n => memIter R q p n s) atTop (𝓝 (L s))) →
      (∀ s, IsMemState R q s → memUpdate R q p L s = L s ∧ 0 ≤ L s ∧ L s < 1) ∧
      (∀ y : Hist R → ℝ,
        (∀ s, IsMemState R q s → memUpdate R q p y s = y s ∧ 0 ≤ y s ∧ y s < 1) →
        ∀ s, IsMemState R q s → L s ≤ y s) ∧
      (∀ x : Hist R → ℝ, IsMemCertificate R q p x → ∀ s, IsMemState R q s → L s ≤ x s)) ∧
    ∀ P : GroupedPresentation R q p,
      (∃ y : P.Θ → ℝ, P.IsCertificate y) ↔ ∃ x : Hist R → ℝ, IsMemCertificate R q p x := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rintro ⟨x, hx⟩
    refine ⟨fun n s hs => ⟨(iter_bounds hp hx n s hs).1,
      lt_of_le_of_lt (iter_bounds hp hx n s hs).2.2 (hx s hs).2.1⟩, ?_⟩
    have : ∀ s, ∃ l, IsMemState R q s → Tendsto (fun n => memIter R q p n s) atTop (𝓝 l) := by
      intro s
      by_cases hs : IsMemState R q s
      · obtain ⟨l, hl⟩ := iter_tendsto hp hx hs
        exact ⟨l, fun _ => hl⟩
      · exact ⟨0, fun h => absurd h hs⟩
    choose L hL using this
    exact ⟨L, fun s hs => by
      have := limit_props hp hx hL hs
      exact ⟨this.1, this.2.2, hL s hs⟩⟩
  · rintro ⟨-, L, hL⟩
    have hL1 : ∀ s, IsMemState R q s → L s < 1 := fun s hs => (hL s hs).2.1
    have hT := fun s hs => (hL s hs).2.2
    exact ⟨L, fun s hs => ⟨(hL s hs).1, (hL s hs).2.1,
      (limit_fixed hp hT hL1 hs).le⟩⟩
  · rintro L ⟨x, hx⟩ hT
    have hL1 : ∀ s, IsMemState R q s → L s < 1 := fun s hs => (limit_props hp hx hT hs).2.2
    refine ⟨fun s hs => ⟨limit_fixed hp hT hL1 hs, (limit_props hp hx hT hs).1, hL1 s hs⟩,
      ?_, fun x' hx' s hs => (limit_props hp hx' hT hs).2.1⟩
    intro y hy s hs
    exact le_of_tendsto' (hT s hs) fun n => iter_le_fixed hp hy n s hs
  · intro P
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨fun s => y (P.type s), fun s hs => ⟨(hy _).1, (hy _).2.1, ?_⟩⟩
      rw [memUpdate_eq_grouped P (fun t _ => rfl) hs]
      exact (hy _).2.2
    · rintro ⟨x, hx⟩
      have : ∀ s, ∃ l, IsMemState R q s → Tendsto (fun n => memIter R q p n s) atTop (𝓝 l) := by
        intro s
        by_cases hs : IsMemState R q s
        · obtain ⟨l, hl⟩ := iter_tendsto hp hx hs
          exact ⟨l, fun _ => hl⟩
        · exact ⟨0, fun h => absurd h hs⟩
      choose L hL using this
      have hL1 : ∀ s, IsMemState R q s → L s < 1 := fun s hs => (limit_props hp hx hL hs).2.2
      have hfix : ∀ s, IsMemState R q s → memUpdate R q p L s = L s :=
        fun s hs => limit_fixed hp hL hL1 hs
      have hinv : ∀ s s', IsMemState R q s → IsMemState R q s' → P.type s = P.type s' →
          L s = L s' := by
        intro s s' hs hs' hty
        exact tendsto_nhds_unique (hL s hs)
          ((hL s' hs').congr fun n => (iter_type_inv hp P n s s' hs hs' hty).symm)
      have hc := fun k => Classical.choose_spec (P.type_surj k)
      refine ⟨fun k => L (Classical.choose (P.type_surj k)), fun k => ?_⟩
      have hk := hc k
      have hxy : ∀ t, IsMemState R q t →
          L t = (fun k => L (Classical.choose (P.type_surj k))) (P.type t) := by
        intro t ht
        have h2 := hc (P.type t)
        exact hinv _ _ ht h2.1 h2.2.symm
      have hupd := memUpdate_eq_grouped P (x := L)
        (y := fun k => L (Classical.choose (P.type_surj k))) hxy hk.1
      rw [hfix _ hk.1, hk.2] at hupd
      have := limit_props hp hx hL hk.1
      exact ⟨this.1, this.2.2, hupd.symm.le⟩

end LocalLemmaHierarchy.Completeness
end

theorem solution : type_of% @LocalLemmaHierarchy.Completeness.chk_proposition_3_3 := @LocalLemmaHierarchy.Completeness.chk_proposition_3_3
