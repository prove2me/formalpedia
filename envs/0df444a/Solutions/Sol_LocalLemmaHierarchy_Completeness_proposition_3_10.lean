-- Prove2me | solution 1 for LocalLemmaHierarchy.Completeness.proposition_3_10
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T08:28:51.870429+00:00
-- url     : https://prove2.me/submissions/be1cc2b4-3b31-4614-b386-4343eea3f2ff

import Mathlib
import Definitions.Def_LocalLemmaHierarchy_Completeness_Representation
import Definitions.Def_LocalLemmaHierarchy_Completeness_Histories
import Definitions.Def_LocalLemmaHierarchy_Completeness_Memory
import Definitions.Def_LocalLemmaHierarchy_Completeness_Graph
import Theorems.Thm_LocalLemmaHierarchy_Completeness_proposition_2_4

section
set_option autoImplicit false

open scoped ENNReal NNReal

namespace LocalLemmaHierarchy.Completeness.Dev.MZ

open scoped Classical

variable {V : Type} (G : SimpleGraph V) [G.LocallyFinite] (o : NeighborOrders G)

theorem sum_helper {ι M : Type} [AddCommMonoid M] [Fintype ι] [Subsingleton ι] (a0 : ι)
    (s : Finset ι) (hs : a0 ∈ s) (f : ι → M) : ∑ a ∈ s, f a = f a0 :=
  Finset.sum_eq_single_of_mem a0 hs (fun b _ hb => absurd (Subsingleton.elim b a0) hb)

theorem indep_insert (J : Finset V) (v : V) :
    G.IsIndepSet (↑(insert v J) : Set V) ↔
      G.IsIndepSet (↑J : Set V) ∧ ∀ w ∈ J, v ≠ w → ¬ G.Adj v w := by
  rw [SimpleGraph.isIndepSet_iff, SimpleGraph.isIndepSet_iff, Finset.coe_insert,
    Set.pairwise_insert]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun w hw hne => (h2 w hw hne).1⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun w hw hne => ⟨h2 w hw hne, fun hh => h2 w hw hne hh.symm⟩⟩

theorem indep_split (U : Finset V) (v : V) (hv : v ∈ U) :
    indepPoly G U = indepPoly G (U.erase v) +
      MvPolynomial.X v * indepPoly G (U \ insert v (G.neighborFinset v)) := by
  unfold indepPoly
  rw [← Finset.sum_filter_add_sum_filter_not
    (U.powerset.filter (fun I : Finset V => G.IsIndepSet (I : Set V))) (fun I => v ∈ I)]
  have h1 : (U.powerset.filter (fun I : Finset V => G.IsIndepSet (I : Set V))).filter
      (fun I => ¬ v ∈ I) = (U.erase v).powerset.filter (fun I : Finset V => G.IsIndepSet (I : Set V)) := by
    ext I
    simp only [Finset.mem_filter, Finset.mem_powerset]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨fun w hw => Finset.mem_erase.2 ⟨fun e => h3 (e ▸ hw), h1 hw⟩, h2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨⟨fun w hw => (Finset.mem_erase.1 (h1 hw)).2, h2⟩, fun hh => ?_⟩
      exact (Finset.mem_erase.1 (h1 hh)).1 rfl
  have h2 : (U.powerset.filter (fun I : Finset V => G.IsIndepSet (I : Set V))).filter
      (fun I => v ∈ I) = ((U \ insert v (G.neighborFinset v)).powerset.filter
        (fun I : Finset V => G.IsIndepSet (I : Set V))).image (insert v) := by
    ext I
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_image]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨I.erase v, ⟨?_, ?_⟩, Finset.insert_erase h3⟩
      · have h2' := h2
        rw [← Finset.insert_erase h3, indep_insert] at h2'
        intro w hw
        obtain ⟨hne, hwI⟩ := Finset.mem_erase.1 hw
        simp only [Finset.mem_sdiff, Finset.mem_insert, not_or, SimpleGraph.mem_neighborFinset]
        exact ⟨h1 hwI, fun e => hne e, fun hadj => h2'.2 w hw (Ne.symm hne) hadj⟩
      · have h2' := h2
        rw [← Finset.insert_erase h3, indep_insert] at h2'
        exact h2'.1
    · rintro ⟨J, ⟨h1, h2⟩, rfl⟩
      have hvJ : v ∉ J := fun hh => by
        have := h1 hh
        simp at this
      refine ⟨⟨?_, ?_⟩, Finset.mem_insert_self _ _⟩
      · intro w hw
        rcases Finset.mem_insert.1 hw with rfl | hw
        · exact hv
        · exact (Finset.mem_sdiff.1 (h1 hw)).1
      · rw [indep_insert]
        refine ⟨h2, fun w hw _ hadj => ?_⟩
        have := (Finset.mem_sdiff.1 (h1 hw)).2
        simp only [Finset.mem_insert, SimpleGraph.mem_neighborFinset, not_or] at this
        exact this.2 hadj
  rw [h1, h2, Finset.sum_image, Finset.mul_sum, add_comm]
  · congr 1
    refine Finset.sum_congr rfl fun J hJ => ?_
    have hvJ : v ∉ J := by
      simp only [Finset.mem_filter, Finset.mem_powerset] at hJ
      intro hh
      have := hJ.1 hh
      simp at this
    rw [Finset.prod_insert hvJ]
  · intro I hI J hJ hIJ
    have hvI : v ∉ I := by
      simp only [Finset.coe_filter, Finset.mem_powerset, Set.mem_setOf_eq] at hI
      intro hh
      have := hI.1 hh
      simp at this
    have hvJ : v ∉ J := by
      simp only [Finset.coe_filter, Finset.mem_powerset, Set.mem_setOf_eq] at hJ
      intro hh
      have := hJ.1 hh
      simp at this
    rw [← Finset.erase_insert hvI, hIJ, Finset.erase_insert hvJ]

theorem indep_rep : IsRepresentationOf (indRep G o) (indepPoly G) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold indepPoly
    rw [Finset.powerset_empty, Finset.filter_singleton, if_pos (by simp [SimpleGraph.isIndepSet_iff])]
    simp
  · intro U
    unfold indepPoly
    rw [map_sum, Finset.sum_eq_single ∅]
    · simp
    · intro I hI hne
      rw [map_prod]
      obtain ⟨w, hw⟩ := Finset.nonempty_iff_ne_empty.2 hne
      exact Finset.prod_eq_zero hw (by simp)
    · intro h
      exfalso
      apply h
      simp
  · intro U v hv
    have hfil : Finset.univ.filter (fun a : (indRep G o).Opt v =>
        (indRep G o).A v a ⊆ U) = Finset.univ := by
      apply Finset.filter_true_of_mem
      intro a _
      show ({v} : Finset V) ⊆ U
      simpa using hv
    rw [hfil]
    have : Subsingleton ((indRep G o).Opt v) := inferInstanceAs (Subsingleton Unit)
    rw [indep_split G U v hv]
    congr 1
    refine Eq.symm ((sum_helper (ι := (indRep G o).Opt v) () _ (Finset.mem_univ _) _).trans ?_)
    show MvPolynomial.C (1 : ℝ) * MvPolynomial.X v *
      indepPoly G (U \ insert v (G.neighborFinset v)) = _
    rw [map_one, one_mul]

end LocalLemmaHierarchy.Completeness.Dev.MZ

namespace LocalLemmaHierarchy.Completeness

end LocalLemmaHierarchy.Completeness
end

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

end Analysis

section Grouped

variable {q : ℕ} {p : T → ℝ}

end Grouped

end LocalLemmaHierarchy.Completeness.Dev.P33

namespace LocalLemmaHierarchy.Completeness

end LocalLemmaHierarchy.Completeness
end

section
set_option autoImplicit false

namespace LocalLemmaHierarchy.Completeness.Dev.P310

/-- Value of the independence polynomial of the path on `k` vertices at `-t`. -/
noncomputable def aSeq (t : ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => 1 - t
  | (k + 2) => aSeq t (k + 1) - t * aSeq t k

theorem aSeq_succ_succ (t : ℝ) (k : ℕ) : aSeq t (k + 2) = aSeq t (k + 1) - t * aSeq t k := rfl

/-- The cycle value `Z_{C_{k+3}}(-t)`. -/
noncomputable def zCyc (t : ℝ) (k : ℕ) : ℝ := aSeq t (k + 2) - t * aSeq t k

/-- The claimed radius for the cycle `C_n`. -/
noncomputable def Rn (n : ℕ) : ℝ := 1 / (4 * Real.cos (Real.pi / (2 * n)) ^ 2)

theorem aSeq_quarter {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1 / 4) :
    ∀ k, 0 < aSeq t k ∧ aSeq t k < 2 * aSeq t (k + 1) := by
  intro k
  induction k with
  | zero => simp [aSeq]; linarith
  | succ k ih =>
    obtain ⟨h1', h2'⟩ := ih
    have hpos : 0 < aSeq t (k + 1) := by linarith
    have : aSeq t (k + 2) = aSeq t (k + 1) - t * aSeq t k := rfl
    have e : t * aSeq t k ≤ 1 / 4 * aSeq t k := mul_le_mul_of_nonneg_right h1 h1'.le
    constructor
    · exact hpos
    · rw [this]; nlinarith

theorem zCyc_quarter {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1 / 4) (k : ℕ) : 0 < zCyc t k := by
  obtain ⟨a1, a2⟩ := aSeq_quarter h0 h1 k
  obtain ⟨b1, b2⟩ := aSeq_quarter h0 h1 (k + 1)
  unfold zCyc
  rw [aSeq_succ_succ]
  have e : t * aSeq t k ≤ 1 / 4 * aSeq t k := mul_le_mul_of_nonneg_right h1 a1.le
  nlinarith

/-- trigonometric recurrence -/
theorem sin_rec (x φ : ℝ) : Real.sin (x + φ) = 2 * Real.cos φ * Real.sin x - Real.sin (x - φ) := by
  rw [Real.sin_add, Real.sin_sub]; ring

theorem aSeq_closed {φ : ℝ} (hc : Real.cos φ ≠ 0) (hs : Real.sin φ ≠ 0) (k : ℕ) :
    aSeq (1 / (4 * Real.cos φ ^ 2)) k * Real.sin φ =
      (1 / (2 * Real.cos φ)) ^ (k + 1) * Real.sin ((k + 2 : ℝ) * φ) ∧
    aSeq (1 / (4 * Real.cos φ ^ 2)) (k + 1) * Real.sin φ =
      (1 / (2 * Real.cos φ)) ^ (k + 2) * Real.sin ((k + 3 : ℝ) * φ) := by
  set c := Real.cos φ with hcdef
  have hs2 : Real.sin φ ^ 2 = 1 - c ^ 2 := by rw [hcdef]; nlinarith [Real.sin_sq_add_cos_sq φ]
  induction k with
  | zero =>
    constructor
    · simp only [aSeq, Nat.cast_zero, zero_add, pow_one]
      have : Real.sin (2 * φ) = 2 * Real.sin φ * c := Real.sin_two_mul φ
      rw [show (2:ℝ) * φ = 2 * φ from rfl, this]
      field_simp
    · simp only [aSeq, Nat.cast_zero, zero_add]
      have h3 : Real.sin (3 * φ) = 3 * Real.sin φ - 4 * Real.sin φ ^ 3 := Real.sin_three_mul φ
      rw [h3]
      have : Real.sin φ ^ 3 = Real.sin φ * (1 - c ^ 2) := by rw [pow_succ, hs2]; ring
      rw [this]
      field_simp
      ring
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨?_, ?_⟩
    · have := h2
      push_cast
      rw [show (k + 1 + 2 : ℝ) = k + 3 by ring]
      rw [pow_succ] at this ⊢
      linear_combination this
    · rw [aSeq_succ_succ]
      have hr := sin_rec ((k + 3 : ℝ) * φ) φ
      have e1 : (k + 3 : ℝ) * φ + φ = ((k + 1 : ℕ) + 3 : ℝ) * φ := by push_cast; ring
      have e2 : (k + 3 : ℝ) * φ - φ = (k + 2 : ℝ) * φ := by ring
      rw [e1, e2] at hr
      rw [show (k + 1 + 2 : ℕ) = k + 3 from rfl]
      have ht : 1 / (4 * c ^ 2) = (1 / (2 * c)) ^ 2 := by field_simp; norm_num
      have hsc : (1 / (2 * c)) * (2 * c) = 1 := by field_simp
      rw [ht]
      set s := 1 / (2 * c) with hsdef
      rw [ht] at h1 h2
      calc (aSeq (s ^ 2) (k + 1) - s ^ 2 * aSeq (s ^ 2) k) * Real.sin φ
          = aSeq (s ^ 2) (k + 1) * Real.sin φ - s ^ 2 * (aSeq (s ^ 2) k * Real.sin φ) := by ring
        _ = s ^ (k + 2) * Real.sin ((k + 3 : ℝ) * φ) - s ^ 2 * (s ^ (k + 1) * Real.sin ((k + 2 : ℝ) * φ)) := by
            rw [h2, h1]
        _ = s ^ (k + 3) * (2 * c * Real.sin ((k + 3 : ℝ) * φ) - Real.sin ((k + 2 : ℝ) * φ)) := by
            linear_combination (-(s ^ (k + 2) * Real.sin ((k + 3 : ℝ) * φ))) * hsc
        _ = _ := by rw [hr]

theorem zCyc_closed {φ : ℝ} (hc : Real.cos φ ≠ 0) (hs : Real.sin φ ≠ 0) (k : ℕ) :
    zCyc (1 / (4 * Real.cos φ ^ 2)) k =
      2 * (1 / (2 * Real.cos φ)) ^ (k + 3) * Real.cos ((k + 3 : ℝ) * φ) := by
  have h := aSeq_closed hc hs k
  have h' := aSeq_closed hc hs (k + 1)
  have e : zCyc (1 / (4 * Real.cos φ ^ 2)) k * Real.sin φ =
      (2 * (1 / (2 * Real.cos φ)) ^ (k + 3) * Real.cos ((k + 3 : ℝ) * φ)) * Real.sin φ := by
    unfold zCyc
    have h4 := h'.2
    have h1 := h.1
    set s := 1 / (2 * Real.cos φ) with hsdef
    have ht : 1 / (4 * Real.cos φ ^ 2) = s ^ 2 := by rw [hsdef]; field_simp; norm_num
    rw [ht] at h4 h1 ⊢
    have hr := sin_rec ((k + 3 : ℝ) * φ) φ
    have hr2 : Real.sin ((k + 3 : ℝ) * φ + φ) - Real.sin ((k + 3 : ℝ) * φ - φ) =
        2 * Real.cos ((k + 3 : ℝ) * φ) * Real.sin φ := by
      rw [Real.sin_add, Real.sin_sub]; ring
    have e1 : (k + 3 : ℝ) * φ + φ = ((k + 1 : ℕ) + 3 : ℝ) * φ := by push_cast; ring
    have e2 : (k + 3 : ℝ) * φ - φ = (k + 2 : ℝ) * φ := by ring
    rw [e1, e2] at hr2
    rw [show (k + 1 + 2 : ℕ) = k + 3 from rfl] at h4
    calc (aSeq (s ^ 2) (k + 2) - s ^ 2 * aSeq (s ^ 2) k) * Real.sin φ
        = aSeq (s ^ 2) (k + 2) * Real.sin φ - s ^ 2 * (aSeq (s ^ 2) k * Real.sin φ) := by ring
      _ = s ^ (k + 3) * (Real.sin (((k + 1 : ℕ) + 3 : ℝ) * φ) - Real.sin ((k + 2 : ℝ) * φ)) := by
          rw [h4, h1]; ring
      _ = _ := by rw [hr2]; ring
  exact mul_right_cancel₀ hs e

theorem phi0_facts {n : ℕ} (hn : 4 ≤ n) :
    0 < Real.pi / (2 * (n : ℝ)) ∧ Real.pi / (2 * (n : ℝ)) < Real.pi / 2 := by
  have hn' : (4 : ℝ) ≤ n := by exact_mod_cast hn
  constructor
  · positivity
  · rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [Real.pi_pos]

theorem cos_phi0_pos {n : ℕ} (hn : 4 ≤ n) : 0 < Real.cos (Real.pi / (2 * (n : ℝ))) := by
  obtain ⟨h1, h2⟩ := phi0_facts hn
  exact Real.cos_pos_of_mem_Ioo ⟨by linarith, h2⟩

theorem Rn_gt {n : ℕ} (hn : 4 ≤ n) : 1 / 4 < Rn n := by
  obtain ⟨h1, h2⟩ := phi0_facts hn
  have hc := cos_phi0_pos hn
  have hs : 0 < Real.sin (Real.pi / (2 * (n : ℝ))) := Real.sin_pos_of_pos_of_lt_pi h1 (by linarith [Real.pi_pos])
  have : Real.cos (Real.pi / (2 * (n : ℝ))) ^ 2 < 1 := by nlinarith [Real.sin_sq_add_cos_sq (Real.pi / (2 * (n : ℝ)))]
  unfold Rn
  rw [lt_div_iff₀ (by positivity)]
  nlinarith

theorem zCyc_Rn {k : ℕ} (hk : 1 ≤ k) : zCyc (Rn (k + 3)) k = 0 := by
  have hn : 4 ≤ k + 3 := by omega
  obtain ⟨h1, h2⟩ := phi0_facts hn
  have hc := cos_phi0_pos hn
  have hs : 0 < Real.sin (Real.pi / (2 * ((k + 3 : ℕ) : ℝ))) :=
    Real.sin_pos_of_pos_of_lt_pi h1 (by linarith [Real.pi_pos])
  unfold Rn
  rw [zCyc_closed hc.ne' hs.ne']
  have : ((k : ℝ) + 3) * (Real.pi / (2 * ((k + 3 : ℕ) : ℝ))) = Real.pi / 2 := by
    push_cast
    field_simp
  rw [this, Real.cos_pi_div_two]; simp

theorem pos_below {k : ℕ} (hk : 1 ≤ k) {t : ℝ} (ht0 : 0 < t) (ht : t < Rn (k + 3)) :
    (∀ j ≤ k + 2, 0 < aSeq t j) ∧ 0 < zCyc t k := by
  by_cases hq : t ≤ 1 / 4
  · exact ⟨fun j _ => (aSeq_quarter ht0.le hq j).1, zCyc_quarter ht0.le hq k⟩
  push_neg at hq
  have hn : 4 ≤ k + 3 := by omega
  obtain ⟨h1, h2⟩ := phi0_facts hn
  have hc0 := cos_phi0_pos hn
  set x : ℝ := 1 / (2 * Real.sqrt t) with hx
  have hsq : 0 < Real.sqrt t := Real.sqrt_pos.2 ht0
  have hx0 : 0 < x := by positivity
  have hx1 : x < 1 := by
    rw [hx, div_lt_one (by positivity)]
    have : 1 / 2 < Real.sqrt t := by
      rw [show (1 / 2 : ℝ) = Real.sqrt (1 / 4) by
        rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_lt_sqrt (by norm_num) hq
    linarith
  set φ := Real.arccos x with hφ
  have hcφ : Real.cos φ = x := Real.cos_arccos (by linarith) hx1.le
  have hφ0 : 0 < φ := Real.arccos_pos.2 hx1
  have hφ1 : φ < Real.pi / 2 := Real.arccos_lt_pi_div_two.2 hx0
  have htφ : t = 1 / (4 * Real.cos φ ^ 2) := by
    rw [hcφ, hx]
    have : (2 * Real.sqrt t) ^ 2 = 4 * t := by rw [mul_pow, Real.sq_sqrt ht0.le]; norm_num
    field_simp
    nlinarith [Real.sq_sqrt ht0.le]
  have hcpos : 0 < Real.cos φ := by rw [hcφ]; exact hx0
  have hsφ : 0 < Real.sin φ := Real.sin_pos_of_pos_of_lt_pi hφ0 (by linarith [Real.pi_pos])
  -- φ < π/(2n)
  have hlt : φ < Real.pi / (2 * ((k + 3 : ℕ) : ℝ)) := by
    by_contra hcon
    push_neg at hcon
    have : Real.cos φ ≤ Real.cos (Real.pi / (2 * ((k + 3 : ℕ) : ℝ))) :=
      Real.cos_le_cos_of_nonneg_of_le_pi h1.le (by linarith [Real.pi_pos]) hcon
    have h3 : Real.cos φ ^ 2 ≤ Real.cos (Real.pi / (2 * ((k + 3 : ℕ) : ℝ))) ^ 2 :=
      pow_le_pow_left₀ hcpos.le this 2
    unfold Rn at ht
    rw [htφ] at ht
    have : 1 / (4 * Real.cos (Real.pi / (2 * ((k + 3 : ℕ) : ℝ))) ^ 2) ≤ 1 / (4 * Real.cos φ ^ 2) := by
      apply one_div_le_one_div_of_le (by positivity)
      linarith
    linarith
  have hn' : (4 : ℝ) ≤ ((k + 3 : ℕ) : ℝ) := by exact_mod_cast hn
  have hnφ : ((k + 3 : ℕ) : ℝ) * φ < Real.pi / 2 := by
    have := (lt_div_iff₀ (by positivity : (0:ℝ) < 2 * ((k + 3 : ℕ) : ℝ))).1 hlt
    nlinarith
  constructor
  · intro j hj
    have h := (aSeq_closed hcpos.ne' hsφ.ne' j).1
    rw [← htφ] at h
    have hspos : 0 < (1 / (2 * Real.cos φ)) ^ (j + 1) := by positivity
    have hsin : 0 < Real.sin (((j : ℝ) + 2) * φ) := by
      apply Real.sin_pos_of_pos_of_lt_pi (by positivity)
      have hj' : (j : ℝ) ≤ k + 2 := by exact_mod_cast hj
      have h5 : ((j : ℝ) + 2) ≤ 2 * ((k + 3 : ℕ) : ℝ) := by push_cast; linarith
      nlinarith [Real.pi_pos]
    have : 0 < aSeq t j * Real.sin φ := by rw [h]; positivity
    exact (mul_pos_iff_of_pos_right hsφ).mp this
  · have h := zCyc_closed hcpos.ne' hsφ.ne' k
    rw [← htφ] at h
    rw [h]
    have : 0 < Real.cos (((k : ℝ) + 3) * φ) := by
      apply Real.cos_pos_of_mem_Ioo
      constructor
      · have : 0 < ((k : ℝ) + 3) * φ := by positivity
        linarith [Real.pi_pos]
      · push_cast at hnφ; exact hnφ
    positivity

end LocalLemmaHierarchy.Completeness.Dev.P310
end

section
set_option autoImplicit false

open scoped ENNReal NNReal

namespace LocalLemmaHierarchy.Completeness.Dev.P310

open scoped Classical

variable {V : Type} (G : SimpleGraph V)

theorem mem_edgesIn {U : Finset V} {e : Sym2 V} :
    e ∈ edgesIn G U ↔ e ∈ G.edgeSet ∧ ∀ z ∈ e, z ∈ U := by
  unfold edgesIn
  induction e using Sym2.ind with
  | h x y =>
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_product, Prod.exists]
    constructor
    · rintro ⟨⟨a, b, ⟨ha, hb⟩, hab⟩, he⟩
      refine ⟨he, ?_⟩
      intro z hz
      rw [← hab] at hz
      rcases Sym2.mem_iff.1 hz with rfl | rfl
      · exact ha
      · exact hb
    · rintro ⟨he, h⟩
      exact ⟨⟨x, y, ⟨h x (Sym2.mem_mk_left _ _), h y (Sym2.mem_mk_right _ _)⟩, rfl⟩, he⟩

/-- The set of matchings of `G[U]`. -/
noncomputable def Mset (U : Finset V) : Finset (Finset (Sym2 V)) :=
  (edgesIn G U).powerset.filter IsMatchingSet

theorem mem_Mset {U : Finset V} {M : Finset (Sym2 V)} :
    M ∈ Mset G U ↔ M ⊆ edgesIn G U ∧ IsMatchingSet M := by
  unfold Mset; simp [Finset.mem_filter, Finset.mem_powerset]

theorem matchPoly_eq (U : Finset V) :
    matchPoly G U = ∑ M ∈ Mset G U, ∏ e ∈ M, (MvPolynomial.X e : MvPolynomial (Sym2 V) ℝ) := rfl

theorem isMatchingSet_mono {M M' : Finset (Sym2 V)} (h : M' ⊆ M) (hM : IsMatchingSet M) :
    IsMatchingSet M' :=
  fun e he e' he' hne x hx => hM e (h he) e' (h he') hne x hx

variable [G.LocallyFinite]

/-- neighbors of `v` inside `U`. -/
noncomputable def nbrIn (U : Finset V) (v : V) : Finset V :=
  (G.neighborFinset v).filter (· ∈ U)

theorem Mset_decomp (U : Finset V) (v : V) (hv : v ∈ U) :
    Mset G U = Mset G (U.erase v) ∪
      (nbrIn G U v).biUnion (fun u => (Mset G (U \ {v, u})).image (insert s(v, u))) := by
  ext M
  simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_image, mem_Mset, nbrIn,
    Finset.mem_filter, SimpleGraph.mem_neighborFinset]
  constructor
  · rintro ⟨hsub, hM⟩
    by_cases h : ∃ e ∈ M, v ∈ e
    · right
      obtain ⟨e, heM, hve⟩ := h
      obtain ⟨he1, he2⟩ := (mem_edgesIn G).1 (hsub heM)
      obtain ⟨u, rfl⟩ := Sym2.mem_iff_exists.1 hve
      have hadj : G.Adj v u := by simpa using he1
      have huU : u ∈ U := he2 u (Sym2.mem_mk_right _ _)
      refine ⟨u, ⟨hadj, huU⟩, M.erase s(v, u), ⟨?_, ?_⟩, Finset.insert_erase heM⟩
      · intro e' he'
        obtain ⟨hne, he'M⟩ := Finset.mem_erase.1 he'
        obtain ⟨h1, h2⟩ := (mem_edgesIn G).1 (hsub he'M)
        refine (mem_edgesIn G).2 ⟨h1, fun z hz => ?_⟩
        simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or]
        refine ⟨h2 z hz, ?_, ?_⟩
        · rintro rfl
          exact hM _ heM _ he'M (Ne.symm hne) z (Sym2.mem_mk_left _ _) hz
        · rintro rfl
          exact hM _ heM _ he'M (Ne.symm hne) z (Sym2.mem_mk_right _ _) hz
      · exact isMatchingSet_mono (Finset.erase_subset _ _) hM
    · left
      push Not at h
      refine ⟨fun e he => ?_, hM⟩
      obtain ⟨h1, h2⟩ := (mem_edgesIn G).1 (hsub he)
      refine (mem_edgesIn G).2 ⟨h1, fun z hz => ?_⟩
      exact Finset.mem_erase.2 ⟨fun hzv => h e he (hzv ▸ hz), h2 z hz⟩
  · rintro (⟨hsub, hM⟩ | ⟨u, ⟨hadj, huU⟩, M', ⟨hsub, hM'⟩, rfl⟩)
    · refine ⟨fun e he => ?_, hM⟩
      obtain ⟨h1, h2⟩ := (mem_edgesIn G).1 (hsub he)
      exact (mem_edgesIn G).2 ⟨h1, fun z hz => Finset.mem_of_mem_erase (h2 z hz)⟩
    · have hnv : ∀ e ∈ M', v ∉ e := by
        intro e he hve
        obtain ⟨_, h2⟩ := (mem_edgesIn G).1 (hsub he)
        have := h2 v hve
        simp at this
      have hnu : ∀ e ∈ M', u ∉ e := by
        intro e he hve
        obtain ⟨_, h2⟩ := (mem_edgesIn G).1 (hsub he)
        have := h2 u hve
        simp at this
      refine ⟨?_, ?_⟩
      · intro e he
        rcases Finset.mem_insert.1 he with rfl | he
        · exact (mem_edgesIn G).2 ⟨by simpa using hadj, by
            intro z hz
            rcases Sym2.mem_iff.1 hz with rfl | rfl
            · exact hv
            · exact huU⟩
        · obtain ⟨h1, h2⟩ := (mem_edgesIn G).1 (hsub he)
          exact (mem_edgesIn G).2 ⟨h1, fun z hz => (Finset.mem_sdiff.1 (h2 z hz)).1⟩
      · intro e he e' he' hne x hx
        rcases Finset.mem_insert.1 he with rfl | hm
        · rcases Finset.mem_insert.1 he' with rfl | hm'
          · exact absurd rfl hne
          · intro hx'
            rcases Sym2.mem_iff.1 hx with rfl | rfl
            · exact hnv _ hm' hx'
            · exact hnu _ hm' hx'
        · rcases Finset.mem_insert.1 he' with rfl | hm'
          · intro hx'
            rcases Sym2.mem_iff.1 hx' with rfl | rfl
            · exact hnv _ hm hx
            · exact hnu _ hm hx
          · exact hM' e hm e' hm' hne x hx

theorem Mset_avoid {U : Finset V} {v u : V} {M' : Finset (Sym2 V)}
    (h : M' ∈ Mset G (U \ {v, u})) : ∀ e ∈ M', v ∉ e ∧ u ∉ e := by
  intro e he
  obtain ⟨_, h2⟩ := (mem_edgesIn G).1 (((mem_Mset G).1 h).1 he)
  refine ⟨fun hv => ?_, fun hu => ?_⟩
  · have := h2 v hv; simp at this
  · have := h2 u hu; simp at this

theorem matchPoly_split (U : Finset V) (v : V) (hv : v ∈ U) :
    matchPoly G U = matchPoly G (U.erase v) +
      ∑ u ∈ nbrIn G U v, MvPolynomial.X s(v, u) * matchPoly G (U \ {v, u}) := by
  rw [matchPoly_eq, matchPoly_eq, Mset_decomp G U v hv, Finset.sum_union]
  · congr 1
    rw [Finset.sum_biUnion]
    · refine Finset.sum_congr rfl fun u hu => ?_
      rw [Finset.sum_image, matchPoly_eq, Finset.mul_sum]
      · refine Finset.sum_congr rfl fun M' hM' => ?_
        rw [Finset.prod_insert]
        intro hmem
        exact (Mset_avoid G hM' _ hmem).1 (Sym2.mem_mk_left _ _)
      · intro M1 hM1 M2 hM2 heq
        have hn1 : s(v, u) ∉ M1 := fun hmem => (Mset_avoid G hM1 _ hmem).1 (Sym2.mem_mk_left _ _)
        have hn2 : s(v, u) ∉ M2 := fun hmem => (Mset_avoid G hM2 _ hmem).1 (Sym2.mem_mk_left _ _)
        rw [← Finset.erase_insert hn1, heq, Finset.erase_insert hn2]
    · intro u hu u' hu' hne
      simp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro M hM1 hM2
      simp only [Finset.mem_image] at hM1 hM2
      obtain ⟨M1, hM1, rfl⟩ := hM1
      obtain ⟨M2, hM2, heq⟩ := hM2
      have : s(v, u) ∈ insert s(v, u') M2 := heq ▸ Finset.mem_insert_self _ _
      rcases Finset.mem_insert.1 this with h | h
      · apply hne
        have := Sym2.eq_iff.1 h
        rcases this with ⟨_, h2⟩ | ⟨h1, h2⟩
        · exact h2
        · exact h2.trans h1
      · exact (Mset_avoid G hM2 _ h).1 (Sym2.mem_mk_left _ _)
  · rw [Finset.disjoint_left]
    intro M hM1 hM2
    simp only [Finset.mem_biUnion, Finset.mem_image] at hM2
    obtain ⟨u, hu, M', hM', rfl⟩ := hM2
    obtain ⟨hsub, _⟩ := (mem_Mset G).1 hM1
    obtain ⟨_, h2⟩ := (mem_edgesIn G).1 (hsub (Finset.mem_insert_self _ _))
    have := h2 v (Sym2.mem_mk_left _ _)
    simp at this

theorem edgesIn_empty : edgesIn G ∅ = ∅ := by
  ext e
  rw [mem_edgesIn]
  induction e using Sym2.ind with
  | h x y => simp only [Finset.notMem_empty, iff_false]; intro h; exact h.2 x (Sym2.mem_mk_left _ _)

theorem match_rep : IsRepresentationOf (matchRep G) (matchPoly G) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [matchPoly_eq]
    have : Mset G ∅ = {∅} := by
      ext M
      rw [mem_Mset, Finset.mem_singleton, edgesIn_empty, Finset.subset_empty]
      constructor
      · exact fun h => h.1
      · rintro rfl
        exact ⟨rfl, fun e he => absurd he (Finset.notMem_empty _)⟩
    rw [this]; simp
  · intro U
    rw [matchPoly_eq, map_sum, Finset.sum_eq_single ∅]
    · simp
    · intro M _ hne
      rw [map_prod]
      obtain ⟨w, hw⟩ := Finset.nonempty_iff_ne_empty.2 hne
      exact Finset.prod_eq_zero hw (by simp)
    · intro h
      exfalso
      apply h
      rw [mem_Mset]
      exact ⟨Finset.empty_subset _, fun e he => absurd he (Finset.notMem_empty _)⟩
  · intro U v hv
    rw [matchPoly_split G U v hv]
    congr 1
    show _ = ∑ a ∈ Finset.univ.filter (fun a : G.neighborFinset v => ({v, (a : V)} : Finset V) ⊆ U),
      MvPolynomial.C (1 : ℝ) * MvPolynomial.X s(v, (a : V)) * matchPoly G (U \ {v, (a : V)})
    rw [Finset.sum_filter]
    rw [Finset.sum_coe_sort (G.neighborFinset v)
      (fun u => if ({v, u} : Finset V) ⊆ U then
        MvPolynomial.C (1 : ℝ) * MvPolynomial.X s(v, u) * matchPoly G (U \ {v, u}) else 0)]
    rw [← Finset.sum_filter]
    unfold nbrIn
    refine Finset.sum_congr ?_ (fun u _ => by rw [map_one, one_mul])
    ext u
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, by intro w hw; simp at hw; rcases hw with rfl | rfl; exact hv; exact h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, h2 (by simp)⟩

end LocalLemmaHierarchy.Completeness.Dev.P310
end

section
set_option autoImplicit false

namespace LocalLemmaHierarchy.Completeness.Dev.P310

open scoped Classical Fin.CommRing Fin.NatCast

noncomputable local instance (priority := high) finDecEq (n : ℕ) : DecidableEq (Fin n) :=
  fun a b => Classical.propDecidable (a = b)

section Cyc

variable {m : ℕ}

theorem cast_eq_zero_iff (i : ℕ) : ((i : ℕ) : Fin (m + 4)) = 0 ↔ (m + 4) ∣ i := Fin.natCast_eq_zero

theorem cast_ne_zero {i : ℕ} (h0 : 0 < i) (h : i < m + 4) : ((i : ℕ) : Fin (m + 4)) ≠ 0 := by
  rw [Ne, cast_eq_zero_iff]
  exact fun hd => absurd (Nat.le_of_dvd h0 hd) (by omega)

/-- the interval of `k` consecutive vertices starting at `a` -/
noncomputable def Iv (a : Fin (m + 4)) (k : ℕ) : Finset (Fin (m + 4)) :=
  (Finset.range k).image (fun i : ℕ => a + (i : Fin (m + 4)))

theorem mem_Iv {a x : Fin (m + 4)} {k : ℕ} : x ∈ Iv a k ↔ ∃ i : ℕ, i < k ∧ x = a + (i : Fin (m + 4)) := by
  unfold Iv
  simp only [Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi, rfl⟩

theorem Iv_zero (a : Fin (m + 4)) : Iv a 0 = ∅ := by
  ext x; simp [mem_Iv]

theorem Iv_one (a : Fin (m + 4)) : Iv a 1 = {a} := by
  ext x; simp [mem_Iv]

theorem Iv_erase_first {k : ℕ} (hk : k ≤ m + 3) (a : Fin (m + 4)) :
    (Iv a (k + 1)).erase a = Iv (a + 1) k := by
  ext x
  rw [Finset.mem_erase, mem_Iv, mem_Iv]
  constructor
  · rintro ⟨hx, i, hi, rfl⟩
    cases i with
    | zero => simp at hx
    | succ j =>
      refine ⟨j, by omega, ?_⟩
      push_cast; ring
  · rintro ⟨j, hj, rfl⟩
    refine ⟨?_, j + 1, by omega, by push_cast; ring⟩
    intro h
    have : a + 1 + (j : Fin (m + 4)) = a + (((j + 1 : ℕ)) : Fin (m + 4)) := by push_cast; ring
    rw [this] at h
    have h2 : (((j + 1 : ℕ)) : Fin (m + 4)) = 0 := by
      have := congrArg (fun z => z - a) h
      simpa using this
    exact cast_ne_zero (by omega) (by omega) h2

theorem sub_one_notMem_Iv {k : ℕ} (hk : k ≤ m + 3) (a : Fin (m + 4)) : a - 1 ∉ Iv a k := by
  rw [mem_Iv]
  rintro ⟨i, hi, h⟩
  have h2 : (((i + 1 : ℕ)) : Fin (m + 4)) = 0 := by
    push_cast
    have : a - 1 = a + (i : Fin (m + 4)) := h
    have h3 : (i : Fin (m + 4)) + 1 = 0 := by
      have := congrArg (fun z => z - a) this
      simp only [sub_sub_cancel_left, add_sub_cancel_left] at this
      -- this : -1 = i
      rw [← this]; ring
    exact h3
  exact cast_ne_zero (by omega) (by omega) h2

theorem add_one_mem_Iv {k : ℕ} (a : Fin (m + 4)) : a + 1 ∈ Iv a (k + 2) := by
  rw [mem_Iv]
  exact ⟨1, by omega, by simp⟩

theorem add_one_notMem_Iv_one (a : Fin (m + 4)) : a + 1 ∉ Iv a 1 := by
  rw [Iv_one, Finset.mem_singleton]
  intro h
  have : (1 : Fin (m + 4)) = 0 := by simpa using h
  exact one_ne_zero this


theorem exists_start {W : Finset (Fin (m + 4))} (hne : W.Nonempty) (hW : W ≠ Finset.univ) :
    ∃ v ∈ W, v - 1 ∉ W := by
  by_contra h
  push Not at h
  apply hW
  obtain ⟨w, hw⟩ := hne
  ext x
  simp only [Finset.mem_univ, iff_true]
  have key : ∀ j : ℕ, w - (j : Fin (m + 4)) ∈ W := by
    intro j
    induction j with
    | zero => simpa using hw
    | succ j ih =>
      have := h _ ih
      convert this using 1
      push_cast; ring
  have := key (w - x).val
  rw [Fin.cast_val_eq_self] at this
  simpa using this

/-- The abstract data of a cycle recurrence. -/
structure CycData (m : ℕ) (f : Finset (Fin (m + 4)) → ℝ) (t : ℝ) (P : ℕ → ℝ) : Prop where
  f0 : f ∅ = 1
  P0 : P 0 = 1
  P2 : ∀ k, P (k + 2) = P (k + 1) - t * P k
  H1 : ∀ W v, v ∈ W → v - 1 ∉ W → v + 1 ∉ W → f W = P 1 * f (W.erase v)
  H2 : ∀ W v, v ∈ W → v - 1 ∉ W → v + 1 ∈ W →
    f W = f (W.erase v) - t * f ((W.erase v).erase (v + 1))

theorem CycData.run {f : Finset (Fin (m + 4)) → ℝ} {t : ℝ} {P : ℕ → ℝ} (D : CycData m f t P)
    (hP : ∀ j ≤ m + 3, 0 < P j) :
    ∀ c : ℕ, ∀ W : Finset (Fin (m + 4)), W.card = c → c < m + 4 →
      0 < f W ∧ ∀ v ∈ W, v - 1 ∉ W → ∃ k : ℕ, 1 ≤ k ∧ k ≤ c ∧ 0 < f (W.erase v) ∧
        f W * P (k - 1) = P k * f (W.erase v) := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    intro W hc hcN
    have hrun : ∀ v ∈ W, v - 1 ∉ W → ∃ k : ℕ, 1 ≤ k ∧ k ≤ c ∧ 0 < f (W.erase v) ∧
        f W * P (k - 1) = P k * f (W.erase v) := by
      intro v hv hv1
      have hcard : (W.erase v).card = c - 1 := by rw [Finset.card_erase_of_mem hv, hc]
      have hc1 : 1 ≤ c := by rw [← hc]; exact Finset.card_pos.2 ⟨v, hv⟩
      have hpos : 0 < f (W.erase v) :=
        (ih (c - 1) (by omega) (W.erase v) hcard (by omega)).1
      by_cases hv2 : v + 1 ∈ W
      · have hmem : v + 1 ∈ W.erase v := Finset.mem_erase.2 ⟨by
          intro h; have : (1 : Fin (m + 4)) = 0 := by simpa using h
          exact one_ne_zero this, hv2⟩
        obtain ⟨hp1, hr⟩ := ih (c - 1) (by omega) (W.erase v) hcard (by omega)
        obtain ⟨k', hk1, hk2, hk3, hk4⟩ := hr (v + 1) hmem (by
          simp)
        refine ⟨k' + 1, by omega, by omega, hpos, ?_⟩
        rw [D.H2 W v hv hv1 hv2]
        obtain ⟨j, rfl⟩ : ∃ j, k' = j + 1 := ⟨k' - 1, by omega⟩
        simp only [Nat.add_sub_cancel] at hk4 ⊢
        rw [D.P2 j]
        have e : (f (W.erase v) - t * f ((W.erase v).erase (v + 1))) * P (j + 1) =
            f (W.erase v) * P (j + 1) - t * (P (j + 1) * f ((W.erase v).erase (v + 1))) := by ring
        rw [e, ← hk4]
        ring
      · refine ⟨1, le_rfl, by omega, hpos, ?_⟩
        rw [D.H1 W v hv hv1 hv2]
        simp [D.P0]
    refine ⟨?_, hrun⟩
    by_cases h0 : W = ∅
    · subst h0; rw [D.f0]; exact one_pos
    · have hne : W.Nonempty := Finset.nonempty_iff_ne_empty.2 h0
      have hW : W ≠ Finset.univ := by
        intro h; rw [h, Finset.card_univ, Fintype.card_fin] at hc; omega
      obtain ⟨v, hv, hv1⟩ := exists_start hne hW
      obtain ⟨k, hk1, hk2, hk3, hk4⟩ := hrun v hv hv1
      have h1 : 0 < P (k - 1) := hP _ (by omega)
      have h2 : 0 < P k := hP _ (by omega)
      have : 0 < f W * P (k - 1) := by rw [hk4]; positivity
      exact (mul_pos_iff_of_pos_right h1).mp this

theorem CycData.pos {f : Finset (Fin (m + 4)) → ℝ} {t : ℝ} {P : ℕ → ℝ} (D : CycData m f t P)
    (hP : ∀ j ≤ m + 3, 0 < P j) (W : Finset (Fin (m + 4))) (hW : W ≠ Finset.univ) : 0 < f W := by
  refine (D.run hP W.card W rfl ?_).1
  by_contra h
  apply hW
  apply Finset.eq_univ_of_card
  simp only [Fintype.card_fin]
  have := Finset.card_le_univ W
  simp only [Fintype.card_fin] at this
  omega

theorem CycData.interval {f : Finset (Fin (m + 4)) → ℝ} {t : ℝ} {P : ℕ → ℝ} (D : CycData m f t P) :
    ∀ k, k ≤ m + 3 → ∀ a : Fin (m + 4), f (Iv a k) = P k := by
  intro k
  induction k using Nat.twoStepInduction with
  | zero => intro _ a; rw [Iv_zero, D.f0, D.P0]
  | one =>
    intro _ a
    rw [D.H1 (Iv a 1) a (by rw [Iv_one]; simp) (sub_one_notMem_Iv (by omega) a)
      (add_one_notMem_Iv_one a), Iv_one]
    simp [D.f0]
  | more k ih1 ih2 =>
    intro hk a
    have hm : a + 1 ∈ Iv a (k + 2) := add_one_mem_Iv a
    rw [D.H2 (Iv a (k + 2)) a (by rw [mem_Iv]; exact ⟨0, by omega, by simp⟩)
      (sub_one_notMem_Iv (by omega) a) hm]
    rw [Iv_erase_first (by omega : k + 1 ≤ m + 3) a, Iv_erase_first (by omega : k ≤ m + 3),
      ih2 (by omega), ih1 (by omega), D.P2]

/-- `x ≠ j` in terms of values -/
theorem ne_nat_iff (x : Fin (m + 4)) {j : ℕ} (hj : j < m + 4) :
    x ≠ ((j : ℕ) : Fin (m + 4)) ↔ x.val ≠ j := by
  rw [Ne, Ne, Fin.ext_iff, Fin.val_natCast, Nat.mod_eq_of_lt hj]

theorem neg_one_eq : (-1 : Fin (m + 4)) = ((m + 3 : ℕ) : Fin (m + 4)) := by
  have : ((m + 3 : ℕ) : Fin (m + 4)) + 1 = 0 := by
    have h : (((m + 3 + 1 : ℕ)) : Fin (m + 4)) = 0 := (cast_eq_zero_iff _).2 (by simp)
    exact (Nat.cast_succ (R := Fin (m + 4)) (m + 3)).symm.trans h
  exact (eq_neg_of_add_eq_zero_left this).symm

theorem val_sub_nat (x : Fin (m + 4)) {a : ℕ} (ha : a < m + 4) :
    (x - (a : Fin (m + 4))).val = if a ≤ x.val then x.val - a else x.val + (m + 4) - a := by
  rw [Fin.sub_def]
  simp only [Fin.val_natCast, Nat.mod_eq_of_lt ha]
  have hx := x.isLt
  split_ifs with h
  · have : m + 4 - a + x.val = (x.val - a) + (m + 4) := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  · rw [show m + 4 - a + x.val = x.val + (m + 4) - a by omega]
    exact Nat.mod_eq_of_lt (by omega)

theorem mem_Iv_nat (x : Fin (m + 4)) {a k : ℕ} (ha : a < m + 4) (hk : k ≤ m + 4) :
    x ∈ Iv ((a : ℕ) : Fin (m + 4)) k ↔
      (if a ≤ x.val then x.val - a else x.val + (m + 4) - a) < k := by
  rw [← val_sub_nat x ha, mem_Iv]
  constructor
  · rintro ⟨i, hi, rfl⟩
    have : ((a : Fin (m + 4)) + (i : Fin (m + 4)) - a) = (i : Fin (m + 4)) := by ring
    rw [this, Fin.val_natCast, Nat.mod_eq_of_lt (by omega)]
    exact hi
  · intro h
    refine ⟨(x - (a : Fin (m + 4))).val, h, ?_⟩
    rw [Fin.cast_val_eq_self]; ring

end Cyc

end LocalLemmaHierarchy.Completeness.Dev.P310
end

section
set_option autoImplicit false

open scoped ENNReal NNReal

namespace LocalLemmaHierarchy.Completeness.Dev.P310

open scoped Classical Fin.CommRing Fin.NatCast

noncomputable local instance (priority := high) finDecEq2 (n : ℕ) : DecidableEq (Fin n) :=
  fun a b => Classical.propDecidable (a = b)

variable {m : ℕ}

theorem fin_val_facts (x : Fin (m + 4)) :
    (x = 0 ↔ x.val = 0) ∧ (x = 1 ↔ x.val = 1) ∧ (x = -1 ↔ x.val = m + 3) ∧ (x = 2 ↔ x.val = 2) := by
  have h : ∀ j : ℕ, j < m + 4 → (x = ((j : ℕ) : Fin (m + 4)) ↔ x.val = j) := by
    intro j hj
    rw [← not_iff_not, ← Ne, ← Ne, ne_nat_iff x hj]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using h 0 (by omega)
  · simpa using h 1 (by omega)
  · rw [neg_one_eq]; exact h (m + 3) (by omega)
  · simpa using h 2 (by omega)

theorem univ_erase_zero : (Finset.univ : Finset (Fin (m + 4))).erase 0 = Iv 1 (m + 3) := by
  ext x
  have h := mem_Iv_nat x (a := 1) (k := m + 3) (by omega) (by omega)
  simp only [Nat.cast_one] at h
  rw [h, Finset.mem_erase]
  have := (fin_val_facts x).1
  have hx := x.isLt
  simp only [Finset.mem_univ, and_true]
  split_ifs <;> omega

theorem univ_sdiff_ind :
    (Finset.univ : Finset (Fin (m + 4))) \ insert 0 {(0 : Fin (m + 4)) - 1, 0 + 1} = Iv 2 (m + 1) := by
  ext x
  have h := mem_Iv_nat x (a := 2) (k := m + 1) (by omega) (by omega)
  simp only [Nat.cast_ofNat] at h
  rw [h]
  obtain ⟨a0, a1, a2, a3⟩ := fin_val_facts x
  have hx := x.isLt
  simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_and,
    not_or, zero_sub, zero_add]
  rw [a0, a1, a2]
  split_ifs <;> omega

theorem univ_sdiff_one :
    (Finset.univ : Finset (Fin (m + 4))) \ {0, (0 : Fin (m + 4)) + 1} = Iv 2 (m + 2) := by
  ext x
  have h := mem_Iv_nat x (a := 2) (k := m + 2) (by omega) (by omega)
  simp only [Nat.cast_ofNat] at h
  rw [h]
  obtain ⟨a0, a1, a2, a3⟩ := fin_val_facts x
  have hx := x.isLt
  simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_and,
    not_or, zero_add]
  rw [a0, a1]
  split_ifs <;> omega

theorem univ_sdiff_neg :
    (Finset.univ : Finset (Fin (m + 4))) \ {0, (0 : Fin (m + 4)) - 1} = Iv 1 (m + 2) := by
  ext x
  have h := mem_Iv_nat x (a := 1) (k := m + 2) (by omega) (by omega)
  simp only [Nat.cast_one] at h
  rw [h]
  obtain ⟨a0, a1, a2, a3⟩ := fin_val_facts x
  have hx := x.isLt
  simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_and,
    not_or, zero_sub]
  rw [a0, a2]
  split_ifs <;> omega

theorem indepPoly_empty {V : Type} (G : SimpleGraph V) : indepPoly G ∅ = 1 := by
  unfold indepPoly
  rw [Finset.powerset_empty, Finset.filter_singleton, if_pos (by simp [SimpleGraph.isIndepSet_iff])]
  simp

theorem cyc_nbr (v : Fin (m + 4)) :
    (SimpleGraph.cycleGraph (m + 4)).neighborFinset v = {v - 1, v + 1} :=
  by
  ext x
  rw [SimpleGraph.cycleGraph_neighborFinset (n := m + 2)]
  simp

/-- Independence polynomial of `C_{m+4}[W]` evaluated at `-t`. -/
noncomputable def fI (m : ℕ) (t : ℝ) (W : Finset (Fin (m + 4))) : ℝ :=
  MvPolynomial.eval (fun _ => -t) (indepPoly (SimpleGraph.cycleGraph (m + 4)) W)

/-- Matching polynomial of `C_{m+4}[W]` evaluated at `-t`. -/
noncomputable def fM (m : ℕ) (t : ℝ) (W : Finset (Fin (m + 4))) : ℝ :=
  MvPolynomial.eval (fun _ => -t) (matchPoly (SimpleGraph.cycleGraph (m + 4)) W)

theorem fI_split (t : ℝ) (W : Finset (Fin (m + 4))) (v : Fin (m + 4)) (hv : v ∈ W) :
    fI m t W = fI m t (W.erase v) - t * fI m t (W \ insert v {v - 1, v + 1}) := by
  have h := Dev.MZ.indep_split (SimpleGraph.cycleGraph (m + 4)) W v hv
  rw [cyc_nbr] at h
  have h2 := congrArg (MvPolynomial.eval (fun _ : Fin (m + 4) => -t)) h
  rw [map_add, map_mul, MvPolynomial.eval_X] at h2
  unfold fI
  rw [h2]
  ring

theorem fM_split (t : ℝ) (W : Finset (Fin (m + 4))) (v : Fin (m + 4)) (hv : v ∈ W) :
    fM m t W = fM m t (W.erase v) +
      ∑ u ∈ nbrIn (SimpleGraph.cycleGraph (m + 4)) W v, (-t) * fM m t (W \ {v, u}) := by
  have h := matchPoly_split (SimpleGraph.cycleGraph (m + 4)) W v hv
  have h2 := congrArg (MvPolynomial.eval (fun _ : Sym2 (Fin (m + 4)) => -t)) h
  rw [map_add, map_sum] at h2
  simp only [map_mul, MvPolynomial.eval_X] at h2
  exact h2

theorem nbrIn_cyc (W : Finset (Fin (m + 4))) (v : Fin (m + 4)) :
    nbrIn (SimpleGraph.cycleGraph (m + 4)) W v = ({v - 1, v + 1} : Finset (Fin (m + 4))).filter (· ∈ W) := by
  ext x; simp [nbrIn, cyc_nbr]

noncomputable def pM (t : ℝ) (k : ℕ) : ℝ := if k = 0 then 1 else aSeq t (k - 1)

theorem cycData_ind (t : ℝ) : CycData m (fI m t) t (aSeq t) := by
  refine ⟨?_, rfl, fun k => rfl, ?_, ?_⟩
  · unfold fI
    rw [indepPoly_empty, map_one]
  · intro W v hv h1 h2
    rw [fI_split t W v hv]
    have : W \ insert v {v - 1, v + 1} = W.erase v := by
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, Finset.mem_erase, not_or]
      constructor
      · rintro ⟨hx, h3, h4, h5⟩; exact ⟨h3, hx⟩
      · rintro ⟨h3, hx⟩
        refine ⟨hx, h3, ?_, ?_⟩
        · rintro rfl; exact h1 hx
        · rintro rfl; exact h2 hx
    rw [this]; simp [aSeq]; ring
  · intro W v hv h1 h2
    rw [fI_split t W v hv]
    have : W \ insert v {v - 1, v + 1} = (W.erase v).erase (v + 1) := by
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, Finset.mem_erase, not_or]
      constructor
      · rintro ⟨hx, h3, h4, h5⟩; exact ⟨h5, h3, hx⟩
      · rintro ⟨h5, h3, hx⟩
        refine ⟨hx, h3, ?_, h5⟩
        rintro rfl; exact h1 hx
    rw [this]

theorem cycData_match (t : ℝ) : CycData m (fM m t) t (pM t) := by
  refine ⟨?_, by simp [pM], ?_, ?_, ?_⟩
  · unfold fM
    rw [(match_rep (SimpleGraph.cycleGraph (m + 4))).1, map_one]
  · intro k
    cases k with
    | zero => simp [pM, aSeq]
    | succ k => simp only [pM]; simp [aSeq_succ_succ]
  · intro W v hv h1 h2
    rw [fM_split t W v hv, nbrIn_cyc]
    have : ({v - 1, v + 1} : Finset (Fin (m + 4))).filter (· ∈ W) = ∅ := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
        iff_false, not_and]
      rintro (rfl | rfl)
      · exact fun h => h1 h
      · exact fun h => h2 h
    rw [this]; simp [pM, aSeq]
  · intro W v hv h1 h2
    rw [fM_split t W v hv, nbrIn_cyc]
    have : ({v - 1, v + 1} : Finset (Fin (m + 4))).filter (· ∈ W) = {v + 1} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨rfl | rfl, hx⟩
        · exact absurd hx h1
        · rfl
      · rintro rfl; exact ⟨Or.inr rfl, h2⟩
    rw [this, Finset.sum_singleton]
    have e : W \ {v, v + 1} = (W.erase v).erase (v + 1) := by
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, Finset.mem_erase, not_or]
      tauto
    rw [e]; ring

theorem fI_univ (t : ℝ) : fI m t Finset.univ = zCyc t (m + 1) := by
  rw [fI_split t Finset.univ 0 (Finset.mem_univ _), univ_erase_zero, univ_sdiff_ind]
  have D := cycData_ind (m := m) t
  rw [D.interval (m + 3) le_rfl, D.interval (m + 1) (by omega)]
  rfl

theorem fM_univ (t : ℝ) : fM m t Finset.univ = zCyc t (m + 1) := by
  rw [fM_split t Finset.univ 0 (Finset.mem_univ _), nbrIn_cyc]
  have hne : (0 : Fin (m + 4)) - 1 ≠ 0 + 1 := by
    intro h
    obtain ⟨a0, a1, a2, a3⟩ := fin_val_facts ((0 : Fin (m + 4)) - 1)
    have h1 : ((0 : Fin (m + 4)) - 1) = -1 := by ring
    rw [h1] at h
    have := (fin_val_facts (-1 : Fin (m + 4))).2.1.1 (by rw [zero_add] at h; exact h)
    have := (fin_val_facts (-1 : Fin (m + 4))).2.2.1.1 rfl
    omega
  have : ({0 - 1, 0 + 1} : Finset (Fin (m + 4))).filter (· ∈ (Finset.univ : Finset (Fin (m + 4)))) =
      {0 - 1, 0 + 1} := by
    ext x; simp
  rw [this, Finset.sum_pair hne, univ_erase_zero, univ_sdiff_neg, zero_add]
  rw [show (Finset.univ : Finset (Fin (m + 4))) \ {0, 1} = Iv 2 (m + 2) from by
    have := univ_sdiff_one (m := m)
    rwa [zero_add] at this]
  have D := cycData_match (m := m) t
  rw [D.interval (m + 3) le_rfl, D.interval (m + 2) (by omega) 1, D.interval (m + 2) (by omega) 2]
  simp only [pM, zCyc, aSeq_succ_succ]
  simp
  have e1 : aSeq t (m + 2) = aSeq t (m + 1) - t * aSeq t m := aSeq_succ_succ t m
  linarith [e1]

theorem fI_pos {t : ℝ} (ht0 : 0 < t) (ht : t < Rn (m + 4)) (W : Finset (Fin (m + 4))) :
    0 < fI m t W := by
  have hb := pos_below (k := m + 1) (by omega) ht0 ht
  by_cases hW : W = Finset.univ
  · subst hW; rw [fI_univ]; exact hb.2
  · exact (cycData_ind (m := m) t).pos (fun j hj => hb.1 j (by omega)) W hW

theorem fM_pos {t : ℝ} (ht0 : 0 < t) (ht : t < Rn (m + 4)) (W : Finset (Fin (m + 4))) :
    0 < fM m t W := by
  have hb := pos_below (k := m + 1) (by omega) ht0 ht
  by_cases hW : W = Finset.univ
  · subst hW; rw [fM_univ]; exact hb.2
  · refine (cycData_match (m := m) t).pos (fun j hj => ?_) W hW
    unfold pM
    split_ifs with h
    · exact one_pos
    · exact hb.1 _ (by omega)

theorem fI_Rn : fI m (Rn (m + 4)) Finset.univ = 0 := by
  rw [fI_univ]; exact zCyc_Rn (k := m + 1) (by omega)

theorem fM_Rn : fM m (Rn (m + 4)) Finset.univ = 0 := by
  rw [fM_univ]; exact zCyc_Rn (k := m + 1) (by omega)

theorem deg_cyc (m : ℕ) (v : Fin (m + 4)) :
    ((SimpleGraph.cycleGraph (m + 4)).neighborFinset v).card ≤ 2 := by
  rw [cyc_nbr]
  exact Finset.card_le_two

end LocalLemmaHierarchy.Completeness.Dev.P310
end

section
set_option autoImplicit false

open scoped ENNReal NNReal

namespace LocalLemmaHierarchy.Completeness.Dev.P310

open scoped Classical Fin.CommRing Fin.NatCast

theorem uniformRadius_eq_of {V T : Type} [Fintype V] (R : PosLocalDeletionRep V T)
    (Z : Finset V → MvPolynomial T ℝ) (hRZ : IsRepresentationOf R Z) (r : ℝ) (hr : 0 < r)
    (hpos : ∀ (t : ℝ≥0), 0 < (t : ℝ) → (t : ℝ) < r → ∀ U, 0 < negEval Z U (fun _ => (t : ℝ)))
    (hzero : negEval Z Finset.univ (fun _ => r) = 0) :
    uniformRadius Z = ENNReal.ofReal r := by
  apply le_antisymm
  · refine (iInf_le _ Finset.univ).trans ?_
    rw [(proposition_2_4 R Z hRZ Finset.univ).1]
    refine (iInf₂_le (⟨r, hr.le⟩ : ℝ≥0) ⟨by exact_mod_cast hr, hzero⟩).trans ?_
    rw [ENNReal.ofReal, Real.toNNReal_of_nonneg hr.le]
    exact le_rfl
  · refine le_iInf fun U => ?_
    rw [(proposition_2_4 R Z hRZ U).1]
    refine le_iInf₂ fun t ht => ?_
    by_contra hlt
    push Not at hlt
    have h1 : (t : ℝ) < r := by
      have := ENNReal.toReal_strict_mono (by simp) hlt
      simpa [ENNReal.toReal_ofReal hr.le] using this
    have := hpos t (by exact_mod_cast ht.1) h1 U
    rw [ht.2] at this
    exact lt_irrefl _ this

theorem uniformRadius_ind (m : ℕ) (o : NeighborOrders (SimpleGraph.cycleGraph (m + 4))) :
    uniformRadius (indepPoly (SimpleGraph.cycleGraph (m + 4))) = ENNReal.ofReal (Rn (m + 4)) := by
  have hR : 1 / 4 < Rn (m + 4) := Rn_gt (by omega)
  refine uniformRadius_eq_of (indRep (SimpleGraph.cycleGraph (m + 4)) o) _
    (Dev.MZ.indep_rep (SimpleGraph.cycleGraph (m + 4)) o) (Rn (m + 4)) (by linarith) ?_ ?_
  · intro t ht0 htr U
    exact fI_pos ht0 htr U
  · exact fI_Rn

theorem uniformRadius_match (m : ℕ) :
    uniformRadius (matchPoly (SimpleGraph.cycleGraph (m + 4))) = ENNReal.ofReal (Rn (m + 4)) := by
  have hR : 1 / 4 < Rn (m + 4) := Rn_gt (by omega)
  refine uniformRadius_eq_of (matchRep (SimpleGraph.cycleGraph (m + 4))) _
    (match_rep (SimpleGraph.cycleGraph (m + 4))) (Rn (m + 4)) (by linarith) ?_ ?_
  · intro t ht0 htr U
    exact fM_pos ht0 htr U
  · exact fM_Rn

end LocalLemmaHierarchy.Completeness.Dev.P310
end

section
set_option autoImplicit false

open scoped ENNReal NNReal

namespace LocalLemmaHierarchy.Completeness.Dev.P310

open scoped Classical
open Dev.P33

variable {V T : Type} {R : PosLocalDeletionRep V T}

theorem last_move {s : Hist R} (hs : IsExact R Set.univ s) (hne : s.moves ≠ []) :
    ∃ m : Move R, m.2.2 = s.endpoint ∧ m.1 ∈ deleted R s.moves ∧
      m.2.2 ∈ (↑(R.D m.1 m.2.1) : Set V) ∧ m.2.2 ≠ m.1 := by
  obtain ⟨L, m, hL⟩ : ∃ L m, s.moves = L ++ [m] := by
    rcases List.eq_nil_or_concat s.moves with h | ⟨L, b, h⟩
    · exact absurd h hne
    · exact ⟨L, b, by simpa using h⟩
  have hlt : L.length < s.moves.length := by rw [hL]; simp
  have hleg := hs.2 L.length hlt
  have e1 : s.moves.take L.length = L := by rw [hL]; simp
  have e2 : s.moves[L.length]'hlt = m := by simp [hL]
  rw [e1, e2] at hleg
  obtain ⟨h1, h2, h3, h4⟩ := hleg
  refine ⟨m, ?_, ?_, h3.1, h4⟩
  · unfold Hist.endpoint Hist.endpointOf
    rw [hL]; simp
  · rw [mem_deleted]
    refine ⟨m, by rw [hL]; simp, ?_⟩
    unfold departure
    exact Finset.mem_insert_self _ _

theorem memStar_moves_ne_nil {q : ℕ} (hq : 1 ≤ q) (s : Hist R) (a : R.Opt s.endpoint) (u : V) :
    (memStar q s a u).moves ≠ [] := by
  intro h
  have h2 : (memStar q s a u).moves.length = 0 := by rw [h]; rfl
  simp only [memStar, Hist.suffix, Hist.append, List.length_drop, List.length_append,
    List.length_singleton] at h2
  omega

/-- A row bound: if every child has value `y ≥ 0`, there are at most `N` available options, each
with at most `k` factors, and `c ≤ 1`, then the update is at most `N * t * (1-y)⁻¹ ^ k`. -/
theorem memUpdate_le_gen {q : ℕ} {t : ℝ} (ht : 0 ≤ t) {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y < 1)
    {x : Hist R → ℝ} {s : Hist R}
    (hx : ∀ a u, u ∈ R.D s.endpoint a \ insert s.endpoint (deleted R s.moves) →
      x (memStar q s a u) = y)
    {N k : ℕ}
    (hN : (Finset.univ.filter
      (fun a : R.Opt s.endpoint => Disjoint (R.A s.endpoint a) (deleted R s.moves))).card ≤ N)
    (hk : ∀ a, (R.D s.endpoint a \ insert s.endpoint (deleted R s.moves)).card ≤ k)
    (hc : ∀ a, R.c s.endpoint a ≤ 1) :
    memUpdate R q (fun _ => t) x s ≤ N * (t * ((1 - y)⁻¹) ^ k) := by
  have hb : 1 ≤ (1 - y)⁻¹ := by
    rw [one_le_inv₀ (by linarith)]; linarith
  have hterm : ∀ a ∈ Finset.univ.filter
      (fun a : R.Opt s.endpoint => Disjoint (R.A s.endpoint a) (deleted R s.moves)),
      R.c s.endpoint a * t * ∏ u ∈ R.D s.endpoint a \ insert s.endpoint (deleted R s.moves),
        (1 - x (memStar q s a u))⁻¹ ≤ t * ((1 - y)⁻¹) ^ k := by
    intro a _
    have hp : ∏ u ∈ R.D s.endpoint a \ insert s.endpoint (deleted R s.moves),
        (1 - x (memStar q s a u))⁻¹ = ((1 - y)⁻¹) ^
          (R.D s.endpoint a \ insert s.endpoint (deleted R s.moves)).card := by
      rw [← Finset.prod_const]
      exact Finset.prod_congr rfl fun u hu => by rw [hx a u hu]
    rw [hp]
    have h1 : ((1 - y)⁻¹) ^ (R.D s.endpoint a \ insert s.endpoint (deleted R s.moves)).card ≤
        ((1 - y)⁻¹) ^ k := pow_le_pow_right₀ hb (hk a)
    have h2 : 0 ≤ ((1 - y)⁻¹) ^ (R.D s.endpoint a \ insert s.endpoint (deleted R s.moves)).card :=
      by positivity
    have h3 : R.c s.endpoint a * t ≤ t := by nlinarith [hc a]
    calc R.c s.endpoint a * t * ((1 - y)⁻¹) ^ (R.D s.endpoint a \
          insert s.endpoint (deleted R s.moves)).card
        ≤ t * ((1 - y)⁻¹) ^ (R.D s.endpoint a \
          insert s.endpoint (deleted R s.moves)).card := by
          exact mul_le_mul_of_nonneg_right h3 h2
      _ ≤ t * ((1 - y)⁻¹) ^ k := mul_le_mul_of_nonneg_left h1 ht
  unfold memUpdate
  refine (Finset.sum_le_card_nsmul _ _ _ hterm).trans ?_
  rw [nsmul_eq_mul]
  have : 0 ≤ t * ((1 - y)⁻¹) ^ k := by positivity
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hN) this

end LocalLemmaHierarchy.Completeness.Dev.P310
end

section
set_option autoImplicit false

open scoped ENNReal NNReal

namespace LocalLemmaHierarchy.Completeness.Dev.P310

open scoped Classical
open Dev.P33

theorem root_facts {t : ℝ} (ht0 : 0 ≤ t) (ht : t < 1 / 4) :
    ∃ y : ℝ, 0 ≤ y ∧ y < 1 / 2 ∧ t = y * (1 - y) := by
  have h1 : 0 < 1 - 4 * t := by linarith
  set r := Real.sqrt (1 - 4 * t) with hr
  have hr0 : 0 < r := Real.sqrt_pos.2 h1
  have hr2 : r ^ 2 = 1 - 4 * t := Real.sq_sqrt h1.le
  have hr1 : r ≤ 1 := by nlinarith
  refine ⟨(1 - r) / 2, by linarith, by linarith, ?_⟩
  nlinarith

theorem memRadius_ge_of {V T : Type} (R : PosLocalDeletionRep V T) (q : ℕ)
    (h : ∀ t : ℝ≥0, (t : ℝ) < 1 / 4 → ∃ x : Hist R → ℝ, IsMemCertificate R q (fun _ => (t : ℝ)) x) :
    ENNReal.ofReal (1 / 4) ≤ memRadius R q := by
  apply ENNReal.le_of_forall_nnreal_lt
  intro r hr
  have hr' : (r : ℝ) < 1 / 4 := by
    have := ENNReal.toReal_strict_mono (by simp) hr
    simpa [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 4)] using this
  exact le_iSup₂ (f := fun (t : ℝ≥0) (_ : ∃ x : Hist R → ℝ,
    IsMemCertificate R q (fun _ => (t : ℝ)) x) => (t : ℝ≥0∞)) r (h r hr')

section Ind

variable {W : Type} (G : SimpleGraph W) [G.LocallyFinite] (o : NeighborOrders G)

theorem ind_factors_le_one (hdeg : ∀ v, (G.neighborFinset v).card ≤ 2) {s : Hist (indRep G o)}
    (hs : IsExact (indRep G o) Set.univ s) (hne : s.moves ≠ []) (a : (indRep G o).Opt s.endpoint) :
    ((indRep G o).D s.endpoint a \ insert s.endpoint (deleted (indRep G o) s.moves)).card ≤ 1 := by
  obtain ⟨m, hm1, hm2, hm3, hm4⟩ := last_move hs hne
  have hD : ∀ v a, (indRep G o).D v a = insert v (G.neighborFinset v) := fun v a => rfl
  rw [hD] at hm3
  have hadj : G.Adj m.1 m.2.2 := by
    simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe,
      SimpleGraph.mem_neighborFinset] at hm3
    rcases hm3 with h | h
    · exact absurd h hm4
    · exact h
  have hpn : m.1 ∈ G.neighborFinset s.endpoint := by
    rw [SimpleGraph.mem_neighborFinset, ← hm1]; exact hadj.symm
  have hsub : (indRep G o).D s.endpoint a \ insert s.endpoint (deleted (indRep G o) s.moves) ⊆
      (G.neighborFinset s.endpoint).erase m.1 := by
    intro x hx
    rw [hD] at hx
    simp only [Finset.mem_sdiff, Finset.mem_insert, not_or] at hx
    obtain ⟨hx1, hx2, hx3⟩ := hx
    refine Finset.mem_erase.2 ⟨fun h => hx3 (h ▸ hm2), ?_⟩
    rcases hx1 with h | h
    · exact absurd h hx2
    · exact h
  refine (Finset.card_le_card hsub).trans ?_
  rw [Finset.card_erase_of_mem hpn]
  have := hdeg s.endpoint
  omega

theorem ind_lower (hdeg : ∀ v, (G.neighborFinset v).card ≤ 2) {q : ℕ} (hq : 1 ≤ q) {t : ℝ≥0}
    (ht : (t : ℝ) < 1 / 4) :
    ∃ x : Hist (indRep G o) → ℝ, IsMemCertificate (indRep G o) q (fun _ => (t : ℝ)) x := by
  obtain ⟨y, hy0, hy1, hty⟩ := root_facts t.2 ht
  have hy1' : y < 1 := by linarith
  have h1y : 0 < 1 - y := by linarith
  refine ⟨fun s => if s.moves = [] then y / (1 - y) else y, ?_⟩
  rintro s ⟨hs, hlen⟩
  have hchild : ∀ a u, u ∈ (indRep G o).D s.endpoint a \
      insert s.endpoint (deleted (indRep G o) s.moves) →
      (fun s : Hist (indRep G o) => if s.moves = [] then y / (1 - y) else y)
        (memStar q s a u) = y := by
    intro a u _
    simp only [if_neg (memStar_moves_ne_nil hq s a u)]
  have hsub : Subsingleton ((indRep G o).Opt s.endpoint) := inferInstanceAs (Subsingleton Unit)
  have hN : (Finset.univ.filter (fun a : (indRep G o).Opt s.endpoint =>
      Disjoint ((indRep G o).A s.endpoint a) (deleted (indRep G o) s.moves))).card ≤ 1 :=
    Finset.card_le_one.2 (fun a _ b _ => Subsingleton.elim a b)
  have hc : ∀ a, (indRep G o).c s.endpoint a ≤ 1 := fun a => le_rfl
  by_cases hne : s.moves = []
  · simp only [hne, if_true]
    refine ⟨?_, ?_, ?_⟩
    · positivity
    · rw [div_lt_one h1y]; linarith
    · have hB : deleted (indRep G o) s.moves = ∅ := by rw [hne]; rfl
      have hk : ∀ a, ((indRep G o).D s.endpoint a \ insert s.endpoint
          (deleted (indRep G o) s.moves)).card ≤ 2 := by
        intro a
        rw [hB]
        have : (indRep G o).D s.endpoint a \ insert s.endpoint ∅ ⊆ G.neighborFinset s.endpoint := by
          intro x hx
          have hD : (indRep G o).D s.endpoint a = insert s.endpoint (G.neighborFinset s.endpoint) := rfl
          rw [hD] at hx
          simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.notMem_empty, or_false, not_or] at hx
          rcases hx.1 with h | h
          · exact absurd h hx.2
          · exact h
        exact (Finset.card_le_card this).trans (hdeg _)
      have := memUpdate_le_gen (R := indRep G o) (q := q) t.2 hy0 hy1' (x := fun s => if s.moves = [] then y / (1 - y) else y) (s := s) hchild hN hk hc
      refine this.trans ?_
      rw [hty]
      field_simp
      simp
  · simp only [hne, if_false]
    refine ⟨hy0, hy1', ?_⟩
    have := memUpdate_le_gen (R := indRep G o) (q := q) t.2 hy0 hy1' (x := fun s => if s.moves = [] then y / (1 - y) else y) (s := s) hchild hN (k := 1) (fun a => ind_factors_le_one G o hdeg hs hne a) hc
    refine this.trans ?_
    rw [hty]
    field_simp
    simp

end Ind

section Match

variable {W : Type} (G : SimpleGraph W) [G.LocallyFinite]

/-- the neighbor chosen by an option of the matching representation -/
def oa {v : W} (a : (matchRep G).Opt v) : W :=
  Subtype.val (α := W) (p := fun x => x ∈ G.neighborFinset v) a

theorem oa_mem {v : W} (a : (matchRep G).Opt v) : oa G a ∈ G.neighborFinset v :=
  Subtype.property (α := W) (p := fun x => x ∈ G.neighborFinset v) a

theorem oa_inj {v : W} {a b : (matchRep G).Opt v} (h : oa G a = oa G b) : a = b :=
  Subtype.ext (α := W) (p := fun x => x ∈ G.neighborFinset v) h

theorem match_D (v : W) (a : (matchRep G).Opt v) : (matchRep G).D v a = {v, oa G a} := rfl

theorem match_A (v : W) (a : (matchRep G).Opt v) : (matchRep G).A v a = {v, oa G a} := rfl

theorem match_avail_le_one (hdeg : ∀ v, (G.neighborFinset v).card ≤ 2) {s : Hist (matchRep G)}
    (hs : IsExact (matchRep G) Set.univ s) (hne : s.moves ≠ []) :
    (Finset.univ.filter (fun a : (matchRep G).Opt s.endpoint =>
      Disjoint ((matchRep G).A s.endpoint a) (deleted (matchRep G) s.moves))).card ≤ 1 := by
  obtain ⟨m, hm1, hm2, hm3, hm4⟩ := last_move hs hne
  have hadj : G.Adj m.1 m.2.2 := by
    obtain ⟨v', a', u'⟩ := m
    have : u' ∈ (↑((matchRep G).D v' a') : Set W) := hm3
    rw [match_D] at this
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at this
    rcases this with h | h
    · exact absurd h hm4
    · have h' : G.Adj v' (oa G a') := by simpa using oa_mem G a'
      simpa [h] using h'
  have hpn : m.1 ∈ G.neighborFinset s.endpoint := by
    rw [SimpleGraph.mem_neighborFinset, ← hm1]; exact hadj.symm
  have hcard : (Finset.univ.filter (fun a : (matchRep G).Opt s.endpoint =>
      Disjoint ((matchRep G).A s.endpoint a) (deleted (matchRep G) s.moves))).card ≤
      ((G.neighborFinset s.endpoint).erase m.1).card := by
    refine Finset.card_le_card_of_injOn (fun a => oa G a) ?_ ?_
    · intro a ha
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ha
      rw [match_A] at ha
      have hnot : oa G a ∉ deleted (matchRep G) s.moves := by
        intro h
        exact Finset.disjoint_left.1 ha (by simp) h
      simp only [Finset.coe_erase, Set.mem_diff, Finset.mem_coe, Set.mem_singleton_iff]
      exact ⟨oa_mem G a, fun h => hnot (h ▸ hm2)⟩
    · intro a _ b _ h
      exact oa_inj G h
  refine hcard.trans ?_
  rw [Finset.card_erase_of_mem hpn]
  have := hdeg s.endpoint
  omega

theorem match_lower (hdeg : ∀ v, (G.neighborFinset v).card ≤ 2) {q : ℕ} (hq : 1 ≤ q) {t : ℝ≥0}
    (ht : (t : ℝ) < 1 / 4) :
    ∃ x : Hist (matchRep G) → ℝ, IsMemCertificate (matchRep G) q (fun _ => (t : ℝ)) x := by
  obtain ⟨y, hy0, hy1, hty⟩ := root_facts t.2 ht
  have hy1' : y < 1 := by linarith
  have h1y : 0 < 1 - y := by linarith
  refine ⟨fun s => if s.moves = [] then 2 * y else y, ?_⟩
  rintro s ⟨hs, hlen⟩
  have hchild : ∀ a u, u ∈ (matchRep G).D s.endpoint a \
      insert s.endpoint (deleted (matchRep G) s.moves) →
      (fun s : Hist (matchRep G) => if s.moves = [] then 2 * y else y)
        (memStar q s a u) = y := by
    intro a u _
    simp only [if_neg (memStar_moves_ne_nil hq s a u)]
  have hk : ∀ a, ((matchRep G).D s.endpoint a \ insert s.endpoint
      (deleted (matchRep G) s.moves)).card ≤ 1 := by
    intro a
    have : (matchRep G).D s.endpoint a \ insert s.endpoint (deleted (matchRep G) s.moves) ⊆
        {oa G a} := by
      intro x hx
      rw [match_D] at hx
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hx
      rcases hx.1 with h | h
      · exact absurd h hx.2.1
      · simp [h]
    exact (Finset.card_le_card this).trans (by simp)
  have hc : ∀ a, (matchRep G).c s.endpoint a ≤ 1 := fun a => le_rfl
  by_cases hne : s.moves = []
  · simp only [hne, if_true]
    refine ⟨by positivity, by linarith, ?_⟩
    have hB : deleted (matchRep G) s.moves = ∅ := by rw [hne]; rfl
    have hN : (Finset.univ.filter (fun a : (matchRep G).Opt s.endpoint =>
        Disjoint ((matchRep G).A s.endpoint a) (deleted (matchRep G) s.moves))).card ≤ 2 := by
      refine (Finset.card_filter_le _ _).trans ?_
      rw [Finset.card_univ]
      have : Fintype.card ((matchRep G).Opt s.endpoint) = (G.neighborFinset s.endpoint).card :=
        Fintype.card_coe _
      rw [this]
      exact hdeg _
    have := memUpdate_le_gen (R := matchRep G) (q := q) t.2 hy0 hy1'
      (x := fun s => if s.moves = [] then 2 * y else y) (s := s) hchild hN hk hc
    refine this.trans ?_
    rw [hty]
    field_simp
    first | (push_cast; linarith) | linarith | simp
  · simp only [hne, if_false]
    refine ⟨hy0, hy1', ?_⟩
    have := memUpdate_le_gen (R := matchRep G) (q := q) t.2 hy0 hy1'
      (x := fun s => if s.moves = [] then 2 * y else y) (s := s) hchild
      (match_avail_le_one G hdeg hs hne) hk hc
    refine this.trans ?_
    rw [hty]
    field_simp
    first | (push_cast; linarith) | linarith | simp

end Match

end LocalLemmaHierarchy.Completeness.Dev.P310
end

section
set_option autoImplicit false

open scoped ENNReal NNReal

namespace LocalLemmaHierarchy.Completeness.Dev.P310

open scoped Classical
open Dev.P33

variable {V T : Type} {R : PosLocalDeletionRep V T}

/-- real sequences with `x_k (1 - x_{k+1}) ≥ t > 1/4` and `0 ≤ x_k < 1` cannot exist. -/
theorem no_seq {t : ℝ} (ht : 1 / 4 < t) (x : ℕ → ℝ) (h0 : ∀ k, 0 ≤ x k) (h1 : ∀ k, x k < 1)
    (h : ∀ k, t ≤ x k * (1 - x (k + 1))) : False := by
  set ε := t - 1 / 4 with hε
  have hε0 : 0 < ε := by linarith
  have hstep : ∀ k, x (k + 1) ≤ x k - ε := by
    intro k
    have hxk : 0 < x k := by
      rcases (h0 k).eq_or_lt with h' | h'
      · have := h k; rw [← h'] at this; linarith
      · exact h'
    by_contra hcon
    push Not at hcon
    have e1 : x k * (x k - ε) < x k * x (k + 1) := mul_lt_mul_of_pos_left hcon hxk
    have e2 := h k
    nlinarith [sq_nonneg (x k - 1 / 2), h1 k]
  have hall : ∀ k : ℕ, x k ≤ x 0 - k * ε := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => push_cast; linarith [hstep k]
  obtain ⟨k, hk⟩ := exists_nat_gt (1 / ε)
  have := hall k
  have h2 : 1 < (k : ℝ) * ε := by
    rw [div_lt_iff₀ hε0] at hk; linarith
  linarith [h0 k, h1 0]

theorem no_cert_of_chain {q : ℕ} {t : ℝ} (ht : 1 / 4 < t) (hc1 : ∀ v a, R.c v a = 1)
    (s : ℕ → Hist R) (hst : ∀ k, IsMemState R q (s k))
    (hstep : ∀ k, ∃ (a : R.Opt (s k).endpoint) (u : V),
      Disjoint (R.A (s k).endpoint a) (deleted R (s k).moves) ∧
      u ∈ R.D (s k).endpoint a \ insert (s k).endpoint (deleted R (s k).moves) ∧
      memStar q (s k) a u = s (k + 1)) :
    ¬ ∃ x : Hist R → ℝ, IsMemCertificate R q (fun _ => t) x := by
  rintro ⟨x, hx⟩
  refine no_seq ht (fun k => x (s k)) (fun k => (hx _ (hst k)).1) (fun k => (hx _ (hst k)).2.1) ?_
  intro k
  obtain ⟨a, u, ha, hu, hs⟩ := hstep k
  have hcert := (hx _ (hst k)).2.2
  have ht0 : 0 ≤ t := by linarith
  have hkey : ∀ a' : R.Opt (s k).endpoint,
      Disjoint (R.A (s k).endpoint a') (deleted R (s k).moves) →
      ∀ w ∈ R.D (s k).endpoint a' \ insert (s k).endpoint (deleted R (s k).moves),
      1 ≤ (1 - x (memStar q (s k) a' w))⁻¹ ∧ 0 < (1 - x (memStar q (s k) a' w))⁻¹ := by
    intro a' ha' w hw
    have := hx _ (memStar_state (hst k) a' w ha' hw)
    have h1' : 0 < 1 - x (memStar q (s k) a' w) := by linarith [this.2.1]
    refine ⟨?_, inv_pos.2 h1'⟩
    rw [one_le_inv₀ h1']; linarith [this.1]
  have hterm_nonneg : ∀ a' ∈ Finset.univ.filter (fun a' : R.Opt (s k).endpoint =>
      Disjoint (R.A (s k).endpoint a') (deleted R (s k).moves)),
      0 ≤ R.c (s k).endpoint a' * t * ∏ w ∈ R.D (s k).endpoint a' \
        insert (s k).endpoint (deleted R (s k).moves), (1 - x (memStar q (s k) a' w))⁻¹ := by
    intro a' ha'
    rw [Finset.mem_filter] at ha'
    have := (R.c_pos (s k).endpoint a').le
    exact mul_nonneg (mul_nonneg this ht0) (Finset.prod_nonneg fun w hw => (hkey a' ha'.2 w hw).2.le)
  have hsingle := Finset.single_le_sum hterm_nonneg
    (Finset.mem_filter.2 ⟨Finset.mem_univ a, ha⟩)
  have hprod : (1 - x (memStar q (s k) a u))⁻¹ ≤ ∏ w ∈ R.D (s k).endpoint a \
      insert (s k).endpoint (deleted R (s k).moves), (1 - x (memStar q (s k) a w))⁻¹ := by
    rw [← Finset.mul_prod_erase _ _ hu]
    have h1 : 1 ≤ ∏ w ∈ (R.D (s k).endpoint a \
        insert (s k).endpoint (deleted R (s k).moves)).erase u,
        (1 - x (memStar q (s k) a w))⁻¹ := by
      calc (1 : ℝ) = ∏ w ∈ (R.D (s k).endpoint a \
            insert (s k).endpoint (deleted R (s k).moves)).erase u, (1 : ℝ) := by simp
        _ ≤ _ := Finset.prod_le_prod (fun _ _ => zero_le_one)
            (fun w hw => (hkey a ha w (Finset.mem_of_mem_erase hw)).1)
    have hp := (hkey a ha u hu).2
    nlinarith
  have hup : t * (1 - x (s (k + 1)))⁻¹ ≤ x (s k) := by
    refine le_trans ?_ hcert
    refine le_trans ?_ hsingle
    rw [hc1, ← hs]
    have : 0 ≤ t := ht0
    simp only [one_mul]
    exact mul_le_mul_of_nonneg_left hprod ht0
  have h1' : 0 < 1 - x (s (k + 1)) := by linarith [(hx _ (hst (k + 1))).2.1]
  rw [← div_eq_mul_inv, div_le_iff₀ h1'] at hup
  linarith

theorem no_cert_of_fw {A : Type} (nx : A → A) (fw : A → ℕ → Hist R) (a0 : A) {q : ℕ} {t : ℝ}
    (ht : 1 / 4 < t) (hc1 : ∀ v a, R.c v a = 1)
    (c1 : ∀ a L, L ≤ q → IsMemState R q (fw a L))
    (c2 : ∀ a L, L ≤ q → ∃ (o : R.Opt (fw a L).endpoint) (u : V),
      Disjoint (R.A (fw a L).endpoint o) (deleted R (fw a L).moves) ∧
      u ∈ R.D (fw a L).endpoint o \ insert (fw a L).endpoint (deleted R (fw a L).moves) ∧
      memStar q (fw a L) o u = if L < q then fw a (L + 1) else fw (nx a) q) :
    ¬ ∃ x : Hist R → ℝ, IsMemCertificate R q (fun _ => t) x := by
  let pos : ℕ → A × ℕ := fun k => Nat.rec (a0, 0)
    (fun _ p => if p.2 < q then (p.1, p.2 + 1) else (nx p.1, q)) k
  have hpos : ∀ k, (pos k).2 ≤ q := by
    intro k
    induction k with
    | zero => simp [pos]
    | succ k ih =>
      show (if (pos k).2 < q then ((pos k).1, (pos k).2 + 1) else (nx (pos k).1, q)).2 ≤ q
      split_ifs with h
      · simpa using h
      · exact le_rfl
  have hsucc : ∀ k, pos (k + 1) =
      if (pos k).2 < q then ((pos k).1, (pos k).2 + 1) else (nx (pos k).1, q) := fun k => rfl
  refine no_cert_of_chain ht hc1 (fun k => fw (pos k).1 (pos k).2) (fun k => c1 _ _ (hpos k)) ?_
  intro k
  obtain ⟨o, u, h1, h2, h3⟩ := c2 (pos k).1 (pos k).2 (hpos k)
  refine ⟨o, u, h1, h2, ?_⟩
  rw [h3, hsucc]
  split_ifs <;> rfl

end LocalLemmaHierarchy.Completeness.Dev.P310
end

section
set_option autoImplicit false

open scoped ENNReal NNReal

namespace LocalLemmaHierarchy.Completeness.Dev.P310

open scoped Classical Fin.CommRing Fin.NatCast
open Dev.P33

noncomputable local instance (priority := high) finDecEq3 (n : ℕ) : DecidableEq (Fin n) :=
  fun a b => Classical.propDecidable (a = b)

variable {m : ℕ}

theorem cast_inj {i j : ℕ} (hi : i < m + 4) (hj : j < m + 4)
    (h : ((i : ℕ) : Fin (m + 4)) = ((j : ℕ) : Fin (m + 4))) : i = j := by
  have := congrArg Fin.val h
  rwa [Fin.val_natCast, Fin.val_natCast, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at this

theorem hist_ext {V T : Type} {R : PosLocalDeletionRep V T} {h h' : Hist R}
    (h1 : h.start = h'.start) (h2 : h.moves = h'.moves) : h = h' := by
  cases h; cases h'; simp_all

theorem suffix_of_le {V T : Type} {R : PosLocalDeletionRep V T} {j : ℕ} {h : Hist R}
    (hj : h.moves.length ≤ j) : h.suffix j = h := by
  unfold Hist.suffix
  rw [Nat.sub_eq_zero_of_le hj]
  simp [Hist.endpointOf]

theorem endpoint_append' {V T : Type} {R : PosLocalDeletionRep V T} (h : Hist R) (mv : Move R) :
    (h.append mv).endpoint = mv.2.2 := by
  unfold Hist.endpoint Hist.append Hist.endpointOf
  simp

section Ind

variable (o : NeighborOrders (SimpleGraph.cycleGraph (m + 4)))

/-- the forward move from `v` to `u` -/
def mvI (v u : Fin (m + 4)) : Move (indRep (SimpleGraph.cycleGraph (m + 4)) o) := ⟨v, ((), u)⟩

theorem mvI_congr {v v' u u' : Fin (m + 4)} (hv : v = v') (hu : u = u') :
    mvI o v u = mvI o v' u' := by subst hv; subst hu; rfl

/-- the forward history from `a` with `L` moves -/
def fwI (a : Fin (m + 4)) (L : ℕ) : Hist (indRep (SimpleGraph.cycleGraph (m + 4)) o) :=
  ⟨a, (List.range L).map (fun i : ℕ => mvI o (a + (i : Fin (m + 4))) (a + (i : Fin (m + 4)) + 1))⟩

theorem fwI_length (a : Fin (m + 4)) (L : ℕ) : (fwI o a L).moves.length = L := by
  simp [fwI]

theorem fwI_succ (a : Fin (m + 4)) (L : ℕ) :
    fwI o a (L + 1) = (fwI o a L).append (mvI o (a + (L : Fin (m + 4))) (a + (L : Fin (m + 4)) + 1)) := by
  simp [fwI, Hist.append, List.range_succ]

theorem endpoint_fwI (a : Fin (m + 4)) (L : ℕ) : (fwI o a L).endpoint = a + (L : Fin (m + 4)) := by
  induction L with
  | zero => simp [fwI, Hist.endpoint, Hist.endpointOf]
  | succ L ih =>
    rw [fwI_succ, endpoint_append']
    simp only [mvI]
    push_cast; ring

theorem departure_mvI (v : Fin (m + 4)) {x : Fin (m + 4)}
    (hx : x ∈ departure (indRep (SimpleGraph.cycleGraph (m + 4)) o) (mvI o v (v + 1))) :
    x = v ∨ x = v - 1 := by
  have hx' : x ∈ insert v ((((indRep (SimpleGraph.cycleGraph (m + 4)) o).D v ()).erase v).filter
      (fun w => (indRep (SimpleGraph.cycleGraph (m + 4)) o).rank v () w <
        (indRep (SimpleGraph.cycleGraph (m + 4)) o).rank v () (v + 1))) := hx
  rw [Finset.mem_insert, Finset.mem_filter, Finset.mem_erase] at hx'
  rcases hx' with h | ⟨⟨hne, hD⟩, hr⟩
  · exact Or.inl h
  · right
    have hD' : x ∈ (SimpleGraph.cycleGraph (m + 4)).neighborFinset v := by
      have : (indRep (SimpleGraph.cycleGraph (m + 4)) o).D v () =
          insert v ((SimpleGraph.cycleGraph (m + 4)).neighborFinset v) := rfl
      rw [this] at hD
      simp only [Finset.mem_insert] at hD
      rcases hD with h | h
      · exact absurd h hne
      · exact h
    rw [cyc_nbr] at hD'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hD'
    rcases hD' with h | h
    · exact h
    · exfalso
      rw [h] at hr
      exact lt_irrefl _ hr

theorem deleted_fwI (a : Fin (m + 4)) (L : ℕ) {x : Fin (m + 4)}
    (hx : x ∈ deleted (indRep (SimpleGraph.cycleGraph (m + 4)) o) (fwI o a L).moves) :
    ∃ j : ℕ, j ≤ L ∧ x + 1 = a + (j : Fin (m + 4)) := by
  rw [mem_deleted] at hx
  obtain ⟨mv, hmv, hx⟩ := hx
  simp only [fwI, List.mem_map, List.mem_range] at hmv
  obtain ⟨i, hi, rfl⟩ := hmv
  rcases departure_mvI o _ hx with h | h
  · exact ⟨i + 1, by omega, by rw [h]; push_cast; ring⟩
  · exact ⟨i, by omega, by rw [h]; ring⟩

theorem step_ok_I (a : Fin (m + 4)) (L : ℕ) (hL : L ≤ m + 1) :
    Disjoint ((indRep (SimpleGraph.cycleGraph (m + 4)) o).A (fwI o a L).endpoint ())
      (deleted (indRep (SimpleGraph.cycleGraph (m + 4)) o) (fwI o a L).moves) ∧
    (a + (L : Fin (m + 4)) + 1) ∈ (indRep (SimpleGraph.cycleGraph (m + 4)) o).D (fwI o a L).endpoint () \
      insert (fwI o a L).endpoint (deleted (indRep (SimpleGraph.cycleGraph (m + 4)) o) (fwI o a L).moves) := by
  have he := endpoint_fwI o a L
  have hA : (indRep (SimpleGraph.cycleGraph (m + 4)) o).A (fwI o a L).endpoint () =
      {(fwI o a L).endpoint} := rfl
  have hD : (indRep (SimpleGraph.cycleGraph (m + 4)) o).D (fwI o a L).endpoint () =
      insert (fwI o a L).endpoint ((SimpleGraph.cycleGraph (m + 4)).neighborFinset (fwI o a L).endpoint) := rfl
  have hnot1 : (fwI o a L).endpoint ∉ deleted (indRep (SimpleGraph.cycleGraph (m + 4)) o) (fwI o a L).moves := by
    intro hx
    obtain ⟨j, hj, hjx⟩ := deleted_fwI o a L hx
    rw [he] at hjx
    have : ((L + 1 : ℕ) : Fin (m + 4)) = (j : Fin (m + 4)) := by
      have h2 : a + ((L : Fin (m + 4)) + 1) = a + (j : Fin (m + 4)) := by rw [← hjx]; ring
      have := add_left_cancel h2
      push_cast; exact this
    have := cast_inj (by omega) (by omega) this
    omega
  have hnot2 : (a + (L : Fin (m + 4)) + 1) ∉ deleted (indRep (SimpleGraph.cycleGraph (m + 4)) o) (fwI o a L).moves := by
    intro hx
    obtain ⟨j, hj, hjx⟩ := deleted_fwI o a L hx
    have : ((L + 2 : ℕ) : Fin (m + 4)) = (j : Fin (m + 4)) := by
      have h2 : a + ((L : Fin (m + 4)) + 2) = a + (j : Fin (m + 4)) := by rw [← hjx]; ring
      have := add_left_cancel h2
      push_cast; exact this
    have := cast_inj (by omega) (by omega) this
    omega
  refine ⟨?_, ?_⟩
  · rw [hA, Finset.disjoint_singleton_left]; exact hnot1
  · rw [hD, Finset.mem_sdiff, Finset.mem_insert]
    refine ⟨Or.inr ?_, ?_⟩
    · rw [cyc_nbr, he]
      simp only [Finset.mem_insert, Finset.mem_singleton, or_true]
    · rw [Finset.mem_insert, not_or]
      refine ⟨?_, hnot2⟩
      rw [he]
      intro h
      have h2 : (1 : Fin (m + 4)) = 0 := by
        have : a + (L : Fin (m + 4)) + 1 = a + (L : Fin (m + 4)) + 0 := by rw [h]; ring
        exact add_left_cancel this
      exact one_ne_zero h2

theorem fwI_exact (a : Fin (m + 4)) : ∀ L, L ≤ m + 2 → IsExact (indRep (SimpleGraph.cycleGraph (m + 4)) o) Set.univ (fwI o a L) := by
  intro L
  induction L with
  | zero =>
    intro _
    refine ⟨Set.mem_univ _, ?_⟩
    intro i hi
    simp [fwI] at hi
  | succ L ih =>
    intro hL
    have hs := ih (by omega)
    obtain ⟨h1, h2⟩ := step_ok_I o a L (by omega)
    have := append_exact hs () (a + (L : Fin (m + 4)) + 1) h1 h2
    rw [fwI_succ]
    have e : mvI o (a + (L : Fin (m + 4))) (a + (L : Fin (m + 4)) + 1) =
        ⟨(fwI o a L).endpoint, ((), a + (L : Fin (m + 4)) + 1)⟩ :=
      mvI_congr o (endpoint_fwI o a L).symm rfl
    rw [e]
    exact this

theorem suffix_fwI_full (a : Fin (m + 4)) (q : ℕ) :
    (fwI o a (q + 1)).suffix q = fwI o (a + 1) q := by
  unfold Hist.suffix
  have hlen := fwI_length o a (q + 1)
  rw [hlen, show q + 1 - q = 1 by omega]
  apply hist_ext
  · simp only [fwI, List.range_succ_eq_map, List.map_cons, List.map_map]
    simp [Hist.endpointOf, mvI]
  · simp only [fwI, List.range_succ_eq_map, List.map_cons, List.map_map, List.drop_succ_cons,
      List.drop_zero]
    refine List.map_congr_left fun i _ => ?_
    simp only [Function.comp]
    exact mvI_congr o (by push_cast; ring) (by push_cast; ring)

theorem memRadius_le_of_nocert {V T : Type} (R : PosLocalDeletionRep V T) (q : ℕ)
    (h : ∀ t : ℝ, 1 / 4 < t → ¬ ∃ x : Hist R → ℝ, IsMemCertificate R q (fun _ => t) x) :
    memRadius R q ≤ ENNReal.ofReal (1 / 4) := by
  refine iSup₂_le fun t ht => ?_
  by_contra hcon
  push Not at hcon
  have : (1 / 4 : ℝ) < t := by
    by_contra hc
    push Not at hc
    have : ENNReal.ofReal (t : ℝ) ≤ ENNReal.ofReal (1 / 4) := ENNReal.ofReal_le_ofReal hc
    rw [ENNReal.ofReal_coe_nnreal] at this
    exact absurd hcon (not_lt.2 this)
  exact h t this ht

theorem ind_upper {q : ℕ} (hq : q ≤ m + 1) :
    memRadius (indRep (SimpleGraph.cycleGraph (m + 4)) o) q ≤ ENNReal.ofReal (1 / 4) := by
  refine memRadius_le_of_nocert _ q fun t ht => ?_
  refine no_cert_of_fw (fun a : Fin (m + 4) => a + 1) (fwI o) 0 ht (fun v a => rfl) ?_ ?_
  · intro a L hL
    exact ⟨fwI_exact o a L (by omega), by rw [fwI_length]; exact hL⟩
  · intro a L hL
    obtain ⟨h1, h2⟩ := step_ok_I o a L (by omega)
    refine ⟨(), a + (L : Fin (m + 4)) + 1, h1, h2, ?_⟩
    have e : memStar q (fwI o a L) () (a + (L : Fin (m + 4)) + 1) =
        ((fwI o a L).append (mvI o (fwI o a L).endpoint (a + (L : Fin (m + 4)) + 1))).suffix q := rfl
    rw [e, endpoint_fwI, ← fwI_succ]
    split_ifs with h
    · exact suffix_of_le (by rw [fwI_length]; omega)
    · have hLq : L = q := by omega
      subst hLq
      exact suffix_fwI_full o a L

end Ind

end LocalLemmaHierarchy.Completeness.Dev.P310
end

section
set_option autoImplicit false

open scoped ENNReal NNReal

namespace LocalLemmaHierarchy.Completeness.Dev.P310

open scoped Classical Fin.CommRing Fin.NatCast
open Dev.P33

noncomputable local instance (priority := high) finDecEq4 (n : ℕ) : DecidableEq (Fin n) :=
  fun a b => Classical.propDecidable (a = b)

variable {m : ℕ}

section Match

theorem nbr_succ (v : Fin (m + 4)) : v + 1 ∈ (SimpleGraph.cycleGraph (m + 4)).neighborFinset v := by
  rw [cyc_nbr]; simp

/-- the forward move along the edge `{v, v+1}` -/
noncomputable def mvM (v : Fin (m + 4)) : Move (matchRep (SimpleGraph.cycleGraph (m + 4))) :=
  ⟨v, (⟨v + 1, nbr_succ v⟩, v + 1)⟩

theorem mvM_congr {v v' : Fin (m + 4)} (hv : v = v') : mvM v = mvM v' := by subst hv; rfl

noncomputable def fwM (a : Fin (m + 4)) (L : ℕ) : Hist (matchRep (SimpleGraph.cycleGraph (m + 4))) :=
  ⟨a, (List.range L).map (fun i : ℕ => mvM (a + (i : Fin (m + 4))))⟩

theorem fwM_length (a : Fin (m + 4)) (L : ℕ) : (fwM a L).moves.length = L := by
  simp [fwM]

theorem fwM_succ (a : Fin (m + 4)) (L : ℕ) :
    fwM a (L + 1) = (fwM a L).append (mvM (a + (L : Fin (m + 4)))) := by
  simp [fwM, Hist.append, List.range_succ]

theorem endpoint_fwM (a : Fin (m + 4)) (L : ℕ) : (fwM a L).endpoint = a + (L : Fin (m + 4)) := by
  induction L with
  | zero => simp [fwM, Hist.endpoint, Hist.endpointOf]
  | succ L ih =>
    rw [fwM_succ, endpoint_append']
    simp only [mvM]
    push_cast; ring

theorem departure_mvM (v : Fin (m + 4)) {x : Fin (m + 4)}
    (hx : x ∈ departure (matchRep (SimpleGraph.cycleGraph (m + 4))) (mvM v)) : x = v := by
  have hx' : x ∈ insert v ((((matchRep (SimpleGraph.cycleGraph (m + 4))).D v ⟨v + 1, nbr_succ v⟩).erase v).filter
      (fun w => (matchRep (SimpleGraph.cycleGraph (m + 4))).rank v ⟨v + 1, nbr_succ v⟩ w <
        (matchRep (SimpleGraph.cycleGraph (m + 4))).rank v ⟨v + 1, nbr_succ v⟩ (v + 1))) := hx
  rw [Finset.mem_insert, Finset.mem_filter] at hx'
  rcases hx' with h | ⟨_, hr⟩
  · exact h
  · exact absurd hr (lt_irrefl _)

theorem deleted_fwM (a : Fin (m + 4)) (L : ℕ) {x : Fin (m + 4)}
    (hx : x ∈ deleted (matchRep (SimpleGraph.cycleGraph (m + 4))) (fwM a L).moves) :
    ∃ j : ℕ, j < L ∧ x = a + (j : Fin (m + 4)) := by
  rw [mem_deleted] at hx
  obtain ⟨mv, hmv, hx⟩ := hx
  simp only [fwM, List.mem_map, List.mem_range] at hmv
  obtain ⟨i, hi, rfl⟩ := hmv
  exact ⟨i, hi, departure_mvM _ hx⟩

noncomputable abbrev MR (m : ℕ) := matchRep (SimpleGraph.cycleGraph (m + 4))

theorem step_ok_M (a : Fin (m + 4)) (L : ℕ) (hL : L ≤ m + 2) :
    Disjoint ((MR m).A (fwM a L).endpoint ⟨(fwM a L).endpoint + 1, nbr_succ _⟩)
      (deleted (MR m) (fwM a L).moves) ∧
    ((fwM a L).endpoint + 1) ∈ (MR m).D (fwM a L).endpoint ⟨(fwM a L).endpoint + 1, nbr_succ _⟩ \
      insert (fwM a L).endpoint (deleted (MR m) (fwM a L).moves) := by
  have he := endpoint_fwM a L
  have hnot1 : (fwM a L).endpoint ∉ deleted (MR m) (fwM a L).moves := by
    intro hx
    obtain ⟨j, hj, hjx⟩ := deleted_fwM a L hx
    rw [he] at hjx
    have h2 := add_left_cancel (hjx : a + (L : Fin (m + 4)) = a + (j : Fin (m + 4)))
    have := cast_inj (by omega) (by omega) h2
    omega
  have hnot2 : ((fwM a L).endpoint + 1) ∉ deleted (MR m) (fwM a L).moves := by
    intro hx
    obtain ⟨j, hj, hjx⟩ := deleted_fwM a L hx
    rw [he] at hjx
    have h2 : a + ((L : Fin (m + 4)) + 1) = a + (j : Fin (m + 4)) := by rw [← hjx]; ring
    have h3 := add_left_cancel h2
    have h4 : ((L + 1 : ℕ) : Fin (m + 4)) = (j : Fin (m + 4)) := by push_cast; exact h3
    have := cast_inj (by omega) (by omega) h4
    omega
  have hA : (MR m).A (fwM a L).endpoint ⟨(fwM a L).endpoint + 1, nbr_succ _⟩ =
      {(fwM a L).endpoint, (fwM a L).endpoint + 1} := rfl
  have hD : (MR m).D (fwM a L).endpoint ⟨(fwM a L).endpoint + 1, nbr_succ _⟩ =
      {(fwM a L).endpoint, (fwM a L).endpoint + 1} := rfl
  refine ⟨?_, ?_⟩
  · rw [hA, Finset.disjoint_left]
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hnot1
    · exact hnot2
  · rw [hD, Finset.mem_sdiff]
    refine ⟨by simp, ?_⟩
    rw [Finset.mem_insert, not_or]
    refine ⟨?_, hnot2⟩
    intro h
    have h2 : (1 : Fin (m + 4)) = 0 := by
      have : (fwM a L).endpoint + 1 = (fwM a L).endpoint + 0 := by rw [h]; ring
      exact add_left_cancel this
    exact one_ne_zero h2

theorem fwM_exact (a : Fin (m + 4)) : ∀ L, L ≤ m + 3 → IsExact (MR m) Set.univ (fwM a L) := by
  intro L
  induction L with
  | zero =>
    intro _
    refine ⟨Set.mem_univ _, ?_⟩
    intro i hi
    simp [fwM] at hi
  | succ L ih =>
    intro hL
    have hs := ih (by omega)
    obtain ⟨h1, h2⟩ := step_ok_M a L (by omega)
    have := append_exact hs ⟨(fwM a L).endpoint + 1, nbr_succ _⟩ ((fwM a L).endpoint + 1) h1 h2
    rw [fwM_succ]
    have e : mvM (a + (L : Fin (m + 4))) =
        ⟨(fwM a L).endpoint, (⟨(fwM a L).endpoint + 1, nbr_succ _⟩, (fwM a L).endpoint + 1)⟩ :=
      mvM_congr (endpoint_fwM a L).symm
    rw [e]
    exact this

theorem suffix_fwM_full (a : Fin (m + 4)) (q : ℕ) :
    (fwM (a + 1) q) = (fwM a (q + 1)).suffix q := by
  unfold Hist.suffix
  have hlen := fwM_length a (q + 1)
  rw [hlen, show q + 1 - q = 1 by omega]
  apply hist_ext
  · simp only [fwM, List.range_succ_eq_map, List.map_cons, List.map_map]
    simp [Hist.endpointOf, mvM]
  · simp only [fwM, List.range_succ_eq_map, List.map_cons, List.map_map, List.drop_succ_cons,
      List.drop_zero]
    refine (List.map_congr_left fun i _ => ?_).symm
    simp only [Function.comp]
    exact mvM_congr (by push_cast; ring)

theorem match_upper {q : ℕ} (hq : q ≤ m + 2) :
    memRadius (MR m) q ≤ ENNReal.ofReal (1 / 4) := by
  refine memRadius_le_of_nocert _ q fun t ht => ?_
  refine no_cert_of_fw (fun a : Fin (m + 4) => a + 1) fwM 0 ht (fun v a => rfl) ?_ ?_
  · intro a L hL
    exact ⟨fwM_exact a L (by omega), by rw [fwM_length]; exact hL⟩
  · intro a L hL
    obtain ⟨h1, h2⟩ := step_ok_M a L (by omega)
    refine ⟨⟨(fwM a L).endpoint + 1, nbr_succ _⟩, (fwM a L).endpoint + 1, h1, h2, ?_⟩
    have e : memStar q (fwM a L) ⟨(fwM a L).endpoint + 1, nbr_succ _⟩ ((fwM a L).endpoint + 1) =
        ((fwM a L).append (mvM (fwM a L).endpoint)).suffix q := rfl
    rw [e, endpoint_fwM, ← fwM_succ]
    split_ifs with h
    · exact suffix_of_le (by rw [fwM_length]; omega)
    · have hLq : L = q := by omega
      subst hLq
      exact (suffix_fwM_full a L).symm

end Match

end LocalLemmaHierarchy.Completeness.Dev.P310
end

section
set_option autoImplicit false

open scoped ENNReal NNReal

namespace LocalLemmaHierarchy.Completeness.Dev.P310

theorem ind_all (m : ℕ) (o : NeighborOrders (SimpleGraph.cycleGraph (m + 4))) (q : ℕ)
    (h1 : 1 ≤ q) (h2 : q ≤ m + 1) :
    memRadius (indRep (SimpleGraph.cycleGraph (m + 4)) o) q = ENNReal.ofReal (1 / 4) :=
  le_antisymm (ind_upper o h2)
    (memRadius_ge_of _ q fun t ht => ind_lower _ o (deg_cyc m) h1 ht)

theorem match_all (m : ℕ) (q : ℕ) (h1 : 1 ≤ q) (h2 : q ≤ m + 2) :
    memRadius (matchRep (SimpleGraph.cycleGraph (m + 4))) q = ENNReal.ofReal (1 / 4) :=
  le_antisymm (match_upper h2)
    (memRadius_ge_of _ q fun t ht => match_lower _ (deg_cyc m) h1 ht)

theorem trig_part (m : ℕ) :
    (1 / 4 : ℝ) = Rn (m + 4) * Real.cos (Real.pi / (2 * (((m + 4 - 3 : ℕ) : ℝ) + 3))) ^ 2 ∧
    Rn (m + 4) - 1 / 4 = 1 / 4 * Real.tan (Real.pi / (2 * (((m + 4 - 3 : ℕ) : ℝ) + 3))) ^ 2 ∧
    Real.pi ^ 2 / (16 * (((m + 4 - 3 : ℕ) : ℝ) + 3) ^ 2) ≤
      1 / 4 * Real.tan (Real.pi / (2 * (((m + 4 - 3 : ℕ) : ℝ) + 3))) ^ 2 := by
  have hn : (((m + 4 - 3 : ℕ) : ℝ) + 3) = ((m + 4 : ℕ) : ℝ) := by
    rw [show m + 4 - 3 = m + 1 by omega]; push_cast; ring
  rw [hn]
  have h4 : 4 ≤ m + 4 := by omega
  obtain ⟨h1, h2⟩ := phi0_facts h4
  have hc := cos_phi0_pos h4
  set x := Real.pi / (2 * ((m + 4 : ℕ) : ℝ)) with hx
  have hcne : Real.cos x ≠ 0 := hc.ne'
  have hsc : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
  have htan : Real.tan x ^ 2 = Real.sin x ^ 2 / Real.cos x ^ 2 := by
    rw [Real.tan_eq_sin_div_cos, div_pow]
  refine ⟨?_, ?_, ?_⟩
  · unfold Rn; rw [← hx]; field_simp
  · unfold Rn; rw [← hx, htan]; field_simp; linarith
  · have hle : x ≤ Real.tan x := Real.le_tan h1.le h2
    have h3 : x ^ 2 ≤ Real.tan x ^ 2 := pow_le_pow_left₀ h1.le hle 2
    have hnr : (0 : ℝ) < ((m + 4 : ℕ) : ℝ) := by positivity
    have : Real.pi ^ 2 / (16 * ((m + 4 : ℕ) : ℝ) ^ 2) = 1 / 4 * x ^ 2 := by
      rw [hx]; field_simp; ring
    rw [this]
    nlinarith

end LocalLemmaHierarchy.Completeness.Dev.P310

namespace LocalLemmaHierarchy.Completeness

open Dev.P310 in
theorem chk_proposition_3_10 (n : ℕ) (hn : 4 ≤ n) (o : NeighborOrders (SimpleGraph.cycleGraph n)) :
    uniformRadius (indepPoly (SimpleGraph.cycleGraph n)) =
        ENNReal.ofReal (1 / (4 * Real.cos (Real.pi / (2 * n)) ^ 2)) ∧
    (∀ q : ℕ, 1 ≤ q → q ≤ n - 3 →
      memRadius (indRep (SimpleGraph.cycleGraph n) o) q = ENNReal.ofReal (1 / 4)) ∧
    ((memRadius (indRep (SimpleGraph.cycleGraph n) o) (n - 3)).toReal =
        (uniformRadius (indepPoly (SimpleGraph.cycleGraph n))).toReal *
          Real.cos (Real.pi / (2 * (((n - 3 : ℕ) : ℝ) + 3))) ^ 2 ∧
      (uniformRadius (indepPoly (SimpleGraph.cycleGraph n))).toReal -
          (memRadius (indRep (SimpleGraph.cycleGraph n) o) (n - 3)).toReal =
        1 / 4 * Real.tan (Real.pi / (2 * (((n - 3 : ℕ) : ℝ) + 3))) ^ 2 ∧
      Real.pi ^ 2 / (16 * (((n - 3 : ℕ) : ℝ) + 3) ^ 2) ≤
        1 / 4 * Real.tan (Real.pi / (2 * (((n - 3 : ℕ) : ℝ) + 3))) ^ 2) ∧
    uniformRadius (matchPoly (SimpleGraph.cycleGraph n)) =
        ENNReal.ofReal (1 / (4 * Real.cos (Real.pi / (2 * n)) ^ 2)) ∧
    ∀ q : ℕ, 1 ≤ q → q ≤ n - 2 →
      memRadius (matchRep (SimpleGraph.cycleGraph n)) q = ENNReal.ofReal (1 / 4) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  have hR : (1 : ℝ) / 4 < Rn (m + 4) := Rn_gt hn
  have hind := uniformRadius_ind m o
  have hmem : memRadius (indRep (SimpleGraph.cycleGraph (m + 4)) o) (m + 4 - 3) =
      ENNReal.ofReal (1 / 4) := ind_all m o _ (by omega) (by omega)
  obtain ⟨t1, t2, t3⟩ := trig_part m
  have e1 : (ENNReal.ofReal (1 / 4)).toReal = 1 / 4 := ENNReal.toReal_ofReal (by norm_num)
  have e2 : (ENNReal.ofReal (Rn (m + 4))).toReal = Rn (m + 4) :=
    ENNReal.toReal_ofReal (by linarith)
  refine ⟨hind, ?_, ⟨?_, ?_, ?_⟩, uniformRadius_match m, ?_⟩
  · intro q h1 h2
    exact ind_all m o q h1 (by omega)
  · rw [hmem, hind, e1, e2]
    exact t1
  · rw [hmem, hind, e1, e2]
    exact t2
  · exact t3
  · intro q h1 h2
    exact match_all m q h1 (by omega)

end LocalLemmaHierarchy.Completeness
end

theorem solution : type_of% @LocalLemmaHierarchy.Completeness.chk_proposition_3_10 := @LocalLemmaHierarchy.Completeness.chk_proposition_3_10
