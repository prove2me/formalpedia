-- Prove2me | solution 1 for LocalLemmaHierarchy.Completeness.theorem_3_9
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T07:44:01.812206+00:00
-- url     : https://prove2.me/submissions/4ad22cb4-5d20-4226-bde0-92a919450bb4

import Mathlib
import Definitions.Def_LocalLemmaHierarchy_Completeness_Representation
import Definitions.Def_LocalLemmaHierarchy_Completeness_Histories
import Definitions.Def_LocalLemmaHierarchy_Completeness_Memory
import Theorems.Thm_LocalLemmaHierarchy_Completeness_proposition_3_4
import Definitions.Def_LocalLemmaHierarchy_Completeness_Weights
import Theorems.Thm_LocalLemmaHierarchy_Completeness_lemma_3_6
import Theorems.Thm_LocalLemmaHierarchy_Completeness_lemma_F_1
import Theorems.Thm_LocalLemmaHierarchy_Completeness_lemma_F_2
import Theorems.Thm_LocalLemmaHierarchy_Completeness_lemma_F_3
import Theorems.Thm_LocalLemmaHierarchy_Completeness_theorem_3_2
import Theorems.Thm_LocalLemmaHierarchy_Completeness_theorem_3_7
import Theorems.Thm_LocalLemmaHierarchy_Completeness_proposition_3_3

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

open scoped ENNReal NNReal

namespace LocalLemmaHierarchy.Completeness.Dev.T32

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

theorem endpoint_suffix (j : ℕ) (h : Hist R) : (h.suffix j).endpoint = h.endpoint := by
  show Hist.endpointOf (Hist.endpointOf h.start (h.moves.take (h.moves.length - j)))
    (h.moves.drop (h.moves.length - j)) = Hist.endpointOf h.start h.moves
  rw [← endpointOf_append, List.take_append_drop]

end LocalLemmaHierarchy.Completeness.Dev.T32
end

section
set_option autoImplicit false

open scoped ENNReal NNReal

namespace LocalLemmaHierarchy.Completeness.Dev.T32

open scoped Classical

variable {V T : Type} {R : PosLocalDeletionRep V T}

end LocalLemmaHierarchy.Completeness.Dev.T32
end

section
set_option autoImplicit false

open scoped ENNReal NNReal

namespace LocalLemmaHierarchy.Completeness.Dev.L36

open scoped Classical
open LocalLemmaHierarchy.Completeness.Dev.T32

variable {V T : Type} {R : PosLocalDeletionRep V T}

theorem deleted_suffix_sub (j : ℕ) (s : Hist R) : deleted R (s.suffix j).moves ⊆ deleted R s.moves := by
  apply deleted_mono
  intro m hm
  exact List.mem_of_mem_drop hm

end LocalLemmaHierarchy.Completeness.Dev.L36

namespace LocalLemmaHierarchy.Completeness

end LocalLemmaHierarchy.Completeness
end

section
set_option autoImplicit false

open scoped ENNReal NNReal

namespace LocalLemmaHierarchy.Completeness.Dev.T39

open scoped Classical

variable {V T : Type}

/-! ### Rows of the memory system as `productRowUpdate` data -/

/-- Index type of options at histories. -/
abbrev Ix (R : PosLocalDeletionRep V T) : Type := Σ s : Hist R, R.Opt s.endpoint

noncomputable def rowA (R : PosLocalDeletionRep V T) (q : ℕ) (s : Hist R) : Finset (Ix R) :=
  if IsMemState R q s then
    (Finset.univ.filter
      (fun a : R.Opt s.endpoint => Disjoint (R.A s.endpoint a) (deleted R s.moves))).map
      ⟨Sigma.mk s, sigma_mk_injective⟩
  else ∅

noncomputable def rowT (R : PosLocalDeletionRep V T) (ν : ℝ) (_ : Hist R) (i : Ix R) : ℝ :=
  R.c i.1.endpoint i.2 * ν

noncomputable def rowC (R : PosLocalDeletionRep V T) (q : ℕ) (_ : Hist R) (i : Ix R) :
    Multiset (Hist R) :=
  (R.D i.1.endpoint i.2 \ insert i.1.endpoint (deleted R i.1.moves)).val.map
    (memStar q i.1 i.2)

theorem row_eq (R : PosLocalDeletionRep V T) (q : ℕ) (ν : ℝ) (x : Hist R → ℝ) (s : Hist R)
    (hs : IsMemState R q s) :
    productRowUpdate (rowA R q) (rowT R ν) (rowC R q) x s = memUpdate R q (fun _ => ν) x s := by
  unfold productRowUpdate memUpdate rowA
  rw [if_pos hs, Finset.sum_map]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Function.Embedding.coeFn_mk, rowT, rowC]
  congr 1
  rw [Finset.prod_eq_multiset_prod, Multiset.map_map]
  rfl

theorem row_zero (R : PosLocalDeletionRep V T) (q : ℕ) (ν : ℝ) (x : Hist R → ℝ) (s : Hist R)
    (hs : ¬ IsMemState R q s) :
    productRowUpdate (rowA R q) (rowT R ν) (rowC R q) x s = 0 := by
  unfold productRowUpdate rowA
  rw [if_neg hs]; simp

theorem memUpdate_congr (R : PosLocalDeletionRep V T) (q : ℕ) (p : T → ℝ) (x y : Hist R → ℝ)
    (s : Hist R) (hs : IsMemState R q s) (h : ∀ u, IsMemState R q u → x u = y u) :
    memUpdate R q p x s = memUpdate R q p y s := by
  unfold memUpdate
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [Finset.mem_filter] at ha
  congr 1
  refine Finset.prod_congr rfl fun u hu => ?_
  rw [h _ (Dev.P33.memStar_state hs a u ha.2 hu)]

theorem memUpdate_scale (R : PosLocalDeletionRep V T) (q : ℕ) (ν l : ℝ) (hν : ν ≠ 0)
    (x : Hist R → ℝ) (s : Hist R) :
    memUpdate R q (fun _ => l) x s = l / ν * memUpdate R q (fun _ => ν) x s := by
  unfold memUpdate
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  field_simp

/-! ### Sums and products over `Icc 1 q` -/

theorem icc_sum (f : ℕ → ℝ) (q : ℕ) : ∑ j ∈ Finset.Icc 1 q, f j = ∑ i ∈ Finset.range q, f (i + 1) := by
  induction q with
  | zero => simp
  | succ n ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

theorem icc_prod (f : ℕ → ℝ) (q : ℕ) : ∏ j ∈ Finset.Icc 1 q, f j = ∏ i ∈ Finset.range q, f (i + 1) := by
  induction q with
  | zero => simp
  | succ n ih => rw [Finset.prod_Icc_succ_top (by omega), ih, Finset.prod_range_succ]

/-- (F.8) in the form used for the memory rows. -/
theorem gm_bound (q : ℕ) (hq : 1 ≤ q) (y : ℕ → ℝ) (hy : ∀ j ≤ q, 0 ≤ y j ∧ y j ≤ 1) :
    ∏ j ∈ Finset.Icc 1 q, y (j - 1) ^ sineWeight q j +
      ∏ j ∈ Finset.Icc 1 q, (1 - y j) ^ sineWeight q j ≤ 1 + dq q := by
  obtain ⟨_, _, hdir, hpos, hsum⟩ := lemma_F_3 q hq
  set w := sineWeight q with hw
  have hext : ∀ i, 1 ≤ i → i ≤ q → extWeights q w i = w i := fun i h1 h2 => by
    simp [extWeights, h1, h2]
  have hext0 : extWeights q w 0 = 0 := by simp [extWeights]
  have hextq : extWeights q w (q + 1) = 0 := by simp [extWeights]
  have hext_nn : ∀ i, 0 ≤ extWeights q w i := fun i => by
    unfold extWeights
    split_ifs with h
    · exact (hpos i (Finset.mem_Icc.2 h)).le
    · exact le_rfl
  have hsA : ∑ i : Fin (q + 1), extWeights q w ((i : ℕ) + 1) = 1 := by
    rw [Fin.sum_univ_eq_sum_range (fun i => extWeights q w (i + 1)), Finset.sum_range_succ,
      hextq, add_zero, ← hsum, icc_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    exact hext _ (by omega) (by have := Finset.mem_range.1 hi; omega)
  have hsB : ∑ i : Fin (q + 1), extWeights q w (i : ℕ) = 1 := by
    rw [Fin.sum_univ_eq_sum_range (fun i => extWeights q w i), Finset.sum_range_succ', hext0,
      add_zero, ← hsum, icc_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    exact hext _ (by omega) (by have := Finset.mem_range.1 hi; omega)
  have F2 := lemma_F_2 (fun i : Fin (q + 1) => extWeights q w ((i : ℕ) + 1))
    (fun i : Fin (q + 1) => extWeights q w (i : ℕ)) (fun i => hext_nn _) hsA
    (fun i => hext_nn _) hsB (fun i : Fin (q + 1) => y i) (fun i => hy i (by omega))
  have h2 := F2.1.trans F2.2
  have hE : ∑ i : Fin (q + 1), (Real.sqrt (extWeights q w ((i : ℕ) + 1)) -
      Real.sqrt (extWeights q w (i : ℕ))) ^ 2 = dq q := by
    rw [Fin.sum_univ_eq_sum_range (fun i => (Real.sqrt (extWeights q w (i + 1)) -
      Real.sqrt (extWeights q w i)) ^ 2)]
    exact hdir
  rw [hE] at h2
  have hGA : geomMean (fun i : Fin (q + 1) => extWeights q w ((i : ℕ) + 1))
      (fun i : Fin (q + 1) => y i) = ∏ j ∈ Finset.Icc 1 q, y (j - 1) ^ w j := by
    unfold geomMean
    rw [Fin.prod_univ_eq_prod_range (fun i => y i ^ extWeights q w (i + 1)), Finset.prod_range_succ,
      hextq, Real.rpow_zero, mul_one, icc_prod]
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [hext _ (by omega) (by have := Finset.mem_range.1 hi; omega)]
    simp
  have hGB : geomMean (fun i : Fin (q + 1) => extWeights q w (i : ℕ))
      (fun i : Fin (q + 1) => 1 - y i) = ∏ j ∈ Finset.Icc 1 q, (1 - y j) ^ w j := by
    unfold geomMean
    rw [Fin.prod_univ_eq_prod_range (fun i => (1 - y i) ^ extWeights q w i), Finset.prod_range_succ',
      hext0, Real.rpow_zero, mul_one, icc_prod]
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [hext _ (by omega) (by have := Finset.mem_range.1 hi; omega)]
  rw [hGA, hGB] at h2
  exact h2

end LocalLemmaHierarchy.Completeness.Dev.T39
end

section
set_option autoImplicit false

open scoped ENNReal NNReal

namespace LocalLemmaHierarchy.Completeness.Dev.T39

open scoped Classical

variable {V T : Type}

theorem cert (R : PosLocalDeletionRep V T) (Z : Finset V → MvPolynomial T ℝ)
    (hRZ : IsRepresentationOf R Z) (hc : 0 < R.cstar) (q : ℕ) (hq : 1 ≤ q)
    (ν : ℝ) (hν : 0 < ν) (hνR : ENNReal.ofReal ν < uniformRadius Z) (l : ℝ) (hl : 0 < l)
    (hlν : l + dq q / R.cstar ≤ ν) :
    ∃ x : Hist R → ℝ, IsMemCertificate R q (fun _ => l) x := by
  obtain ⟨P1, P2, -, -, P5, -⟩ := proposition_3_4 R Z hRZ ν hν hνR
  have hne : ENNReal.ofReal ν / uniformRadius Z ≠ ⊤ := P1.ne_top
  set b : ℝ := (ENNReal.ofReal ν / uniformRadius Z).toReal with hbdef
  have hb0 : 0 ≤ b := ENNReal.toReal_nonneg
  have hb1 : b < 1 := by
    have := (ENNReal.toReal_lt_toReal hne ENNReal.one_ne_top).2 P1
    rwa [ENNReal.toReal_one] at this
  have hXb : ∀ h : Hist R, IsExact R Set.univ h → 0 ≤ canonicalBranch R ν h ∧
      canonicalBranch R ν h ≤ b := fun h hh => by
    obtain ⟨_, h1, h2, _⟩ := P2 h hh
    exact ⟨h1, (ENNReal.ofReal_le_iff_le_toReal hne).1 h2⟩
  let Y : ℕ → Hist R → ℝ := fun j s => if IsMemState R q s then canonicalBranch R ν (s.suffix j) else 0
  have hY : ∀ j, ∀ s, 0 ≤ Y j s ∧ Y j s ≤ b := fun j s => by
    by_cases hs : IsMemState R q s
    · simp only [Y, if_pos hs]
      exact hXb _ (Dev.P33.suffix_exact hs.1 j)
    · simp only [Y, if_neg hs]; exact ⟨le_rfl, hb0⟩
  have hYs : ∀ j s, IsMemState R q s → Y j s = canonicalBranch R ν (s.suffix j) := fun j s hs => by
    simp only [Y, if_pos hs]
  have hcpos : ∀ s : Hist R, ∀ i ∈ rowA R q s, 0 < rowT R ν s i := fun s i _ =>
    mul_pos (R.c_pos _ _) hν
  have hF : ∀ j, 1 ≤ j → j ≤ q → ∀ s, productRowUpdate (rowA R q) (rowT R ν) (rowC R q) (Y j) s ≤
      Y (j - 1) s := by
    intro j hj1 hjq s
    by_cases hs : IsMemState R q s
    · rw [row_eq R q ν _ s hs, memUpdate_congr R q (fun _ => ν) (Y j)
        (fun s' => canonicalBranch R ν (s'.suffix j)) s hs (fun u hu => hYs j u hu),
        hYs _ s hs]
      exact lemma_3_6 R Z hRZ ν hν hνR q j hj1 hjq s hs
    · rw [row_zero R q ν _ s hs]
      simp only [Y, if_neg hs]; exact le_rfl
  obtain ⟨_, _, hdir, hpos, hsum⟩ := lemma_F_3 q hq
  have hF1 := lemma_F_1 (rowA R q) (rowT R ν) (rowC R q) (fun s i hi => hcpos s i hi) q b hb1 Y
    (fun j _ s => hY j s) (sineWeight q) hpos hsum
  obtain ⟨hx, hFx, hFz⟩ := hF1
  refine ⟨fun s => 1 - ∏ j ∈ Finset.Icc 1 q, (1 - Y j s) ^ sineWeight q j, ?_⟩
  intro s hs
  refine ⟨(hx s).1, lt_of_le_of_lt (hx s).2 hb1, ?_⟩
  rw [memUpdate_scale R q ν l hν.ne', ← row_eq R q ν _ s hs]
  have hlν0 : 0 ≤ l / ν := by positivity
  by_cases hA : (rowA R q s).Nonempty
  · have hav : ∃ a : R.Opt s.endpoint, Disjoint (R.A s.endpoint a) (deleted R s.moves) := by
      obtain ⟨i, hi⟩ := hA
      unfold rowA at hi
      rw [if_pos hs, Finset.mem_map] at hi
      obtain ⟨a, ha, _⟩ := hi
      exact ⟨a, (Finset.mem_filter.1 ha).2⟩
    obtain ⟨a0, ha0⟩ := hav
    have key : ∀ (h' : Hist R) (v : V), h'.endpoint = v → ∀ a : R.Opt v,
        Disjoint (R.A v a) (deleted R s.moves) → deleted R h'.moves ⊆ deleted R s.moves →
        HasAvailableOption R h' := by
      intro h' v hv a ha hd; subst hv; exact ⟨a, Finset.disjoint_of_subset_right hd ha⟩
    have hlow : ∀ j ≤ q, R.cstar * ν ≤ Y j s := fun j hj => by
      rw [hYs j s hs]
      exact P5 _ (Dev.P33.suffix_exact hs.1 j)
        (key _ _ (Dev.T32.endpoint_suffix j s) a0 ha0 (Dev.L36.deleted_suffix_sub j s))
    have hFj : ∀ j ∈ Finset.Icc 1 q,
        0 ≤ productRowUpdate (rowA R q) (rowT R ν) (rowC R q) (Y j) s := fun j hj => by
      unfold productRowUpdate
      refine Finset.sum_nonneg fun a ha => mul_nonneg (hcpos s a ha).le ?_
      refine Multiset.prod_nonneg fun r hr => ?_
      rw [Multiset.mem_map] at hr
      obtain ⟨u, _, rfl⟩ := hr
      exact inv_nonneg.2 (by linarith [(hY j u).2])
    have hw0 : ∀ j ∈ Finset.Icc 1 q, 0 ≤ sineWeight q j := fun j hj => (hpos j hj).le
    have hprod : productRowUpdate (rowA R q) (rowT R ν) (rowC R q)
        (fun s => 1 - ∏ j ∈ Finset.Icc 1 q, (1 - Y j s) ^ sineWeight q j) s ≤
        ∏ j ∈ Finset.Icc 1 q, Y (j - 1) s ^ sineWeight q j :=
      (hFx s hA).trans (Finset.prod_le_prod (fun j hj => Real.rpow_nonneg (hFj j hj) _)
        (fun j hj => Real.rpow_le_rpow (hFj j hj)
          (hF j (Finset.mem_Icc.1 hj).1 (Finset.mem_Icc.1 hj).2 s) (hw0 j hj)))
    have hcν : 0 < R.cstar * ν := mul_pos hc hν
    have hAlow : R.cstar * ν ≤ ∏ j ∈ Finset.Icc 1 q, Y (j - 1) s ^ sineWeight q j := by
      calc R.cstar * ν = ∏ j ∈ Finset.Icc 1 q, (R.cstar * ν) ^ sineWeight q j := by
            rw [← Real.rpow_sum_of_nonneg hcν.le hw0, hsum, Real.rpow_one]
        _ ≤ _ := Finset.prod_le_prod (fun j hj => Real.rpow_nonneg hcν.le _) (fun j hj =>
            Real.rpow_le_rpow hcν.le (hlow (j - 1) (by have := (Finset.mem_Icc.1 hj).2; omega))
              (hw0 j hj))
    have hgm := gm_bound q hq (fun j => Y j s)
      (fun j hj => ⟨(hY j s).1, by linarith [(hY j s).2]⟩)
    set Ah := ∏ j ∈ Finset.Icc 1 q, Y (j - 1) s ^ sineWeight q j with hAh
    set B := ∏ j ∈ Finset.Icc 1 q, (1 - Y j s) ^ sineWeight q j with hB
    have hd0 : 0 ≤ dq q := by
      unfold dq; have := Real.cos_le_one (Real.pi / ((q : ℝ) + 1)); linarith
    have hlν' : l ≤ ν := by
      have : 0 ≤ dq q / R.cstar := div_nonneg hd0 hc.le
      linarith
    have hdc : dq q ≤ R.cstar * (ν - l) := by
      have := (div_le_iff₀ hc).1 (by linarith : dq q / R.cstar ≤ ν - l)
      linarith
    have hk : 0 ≤ (ν - l) / ν := div_nonneg (by linarith) hν.le
    have e1 : l / ν * Ah = Ah - (ν - l) / ν * Ah := by field_simp; ring
    have e2 : (ν - l) / ν * (R.cstar * ν) = R.cstar * (ν - l) := by field_simp
    have h3 : (ν - l) / ν * (R.cstar * ν) ≤ (ν - l) / ν * Ah :=
      mul_le_mul_of_nonneg_left hAlow hk
    have h4 := mul_le_mul_of_nonneg_left hprod hlν0
    show l / ν * _ ≤ 1 - B
    linarith
  · have := hFz s (Finset.not_nonempty_iff_eq_empty.1 hA)
    rw [this, mul_zero]
    exact (hx s).1

end LocalLemmaHierarchy.Completeness.Dev.T39
end

section
set_option autoImplicit false

open scoped ENNReal NNReal

namespace LocalLemmaHierarchy.Completeness.Dev.T39

open scoped Classical

variable {V T : Type}

/-- The certified radius of a grouped presentation equals the memory radius. -/
theorem radius_eq (R : PosLocalDeletionRep V T) (q : ℕ) (P : GroupedPresentation R q (fun _ => 1)) :
    P.radius = memRadius R q := by
  unfold GroupedPresentation.radius memRadius
  refine iSup_congr fun t => iSup_congr_Prop ?_ (fun _ => rfl)
  let P' : GroupedPresentation R q (fun _ => (t : ℝ)) :=
    { Θ := P.Θ
      fintypeΘ := P.fintypeΘ
      type := P.type
      rows := fun k => (P.rows k).map (fun r => ((t : ℝ) * r.1, r.2))
      type_surj := P.type_surj
      row_eq := by
        intro s hs
        have h := P.row_eq s hs
        have e : memRowData R q (fun _ => (t : ℝ)) P.type s =
            (memRowData R q (fun _ => 1) P.type s).map (fun r => ((t : ℝ) * r.1, r.2)) := by
          unfold memRowData
          rw [Multiset.map_map]
          refine Multiset.map_congr rfl fun a _ => ?_
          simp [mul_comm]
        rw [e, h] }
  have hG : ∀ y k, groupedUpdate P'.rows y k = (t : ℝ) * groupedUpdate P.rows y k := by
    intro y k
    show (((P.rows k).map (fun r => ((t : ℝ) * r.1, r.2))).map _).sum = _
    unfold groupedUpdate
    rw [Multiset.map_map, ← Multiset.sum_map_mul_left]
    congr 1
    refine Multiset.map_congr rfl fun r _ => ?_
    simp only [Function.comp_apply, mul_assoc]
    rfl
  have h33 := (proposition_3_3 R q (fun _ => (t : ℝ)) (fun _ => t.2)).2.2 P'
  rw [← h33]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, fun k => ⟨(hy k).1, (hy k).2.1, by rw [hG]; exact (hy k).2.2⟩⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, fun k => ⟨(hy k).1, (hy k).2.1, by have := (hy k).2.2; rwa [hG] at this⟩⟩

theorem ennreal_aux (a b M : ℝ≥0∞) (hM0 : M ≠ 0) (hMt : M ≠ ⊤) (h1 : a ≤ M) (h2 : M ≤ a + b) :
    a / M ≤ 1 ∧ 1 - a / M ≤ b / M := by
  refine ⟨?_, ?_⟩
  · calc a / M ≤ M / M := ENNReal.div_le_div_right h1 _
      _ = 1 := ENNReal.div_self hM0 hMt
  · rw [tsub_le_iff_right, ← ENNReal.add_div, add_comm]
    calc (1 : ℝ≥0∞) = M / M := (ENNReal.div_self hM0 hMt).symm
      _ ≤ _ := ENNReal.div_le_div_right h2 _

end LocalLemmaHierarchy.Completeness.Dev.T39
end

section
set_option autoImplicit false

open scoped ENNReal NNReal

namespace LocalLemmaHierarchy.Completeness

open LocalLemmaHierarchy.Completeness.Dev.T39

theorem chk_theorem_3_9 {V T : Type} (R : PosLocalDeletionRep V T)
    (Z : Finset V → MvPolynomial T ℝ) (hRZ : IsRepresentationOf R Z) (hnc : IsNonconstant Z)
    (q : ℕ) (hq : 1 ≤ q) :
    dq q / R.cstar ≤ Real.pi ^ 2 / (R.cstar * ((q : ℝ) + 1) ^ 2) ∧
    (memRadius R q ≤ uniformRadius Z ∧
      uniformRadius Z ≤ memRadius R q + ENNReal.ofReal (dq q / R.cstar)) ∧
    (0 < uniformRadius Z →
      memRadius R q / uniformRadius Z ≤ 1 ∧
      1 - memRadius R q / uniformRadius Z ≤
        ENNReal.ofReal (Real.pi ^ 2 / (R.cstar * ((q : ℝ) + 1) ^ 2)) / uniformRadius Z) ∧
    ∀ P : GroupedPresentation R q (fun _ => 1),
      (P.radius ≤ uniformRadius Z ∧
        uniformRadius Z ≤ P.radius + ENNReal.ofReal (dq q / R.cstar)) ∧
      (0 < uniformRadius Z →
        P.radius / uniformRadius Z ≤ 1 ∧
        1 - P.radius / uniformRadius Z ≤
          ENNReal.ofReal (Real.pi ^ 2 / (R.cstar * ((q : ℝ) + 1) ^ 2)) / uniformRadius Z) := by
  classical
  obtain ⟨_, _, T7c, T7d⟩ := theorem_3_7 R Z hRZ
  obtain ⟨v0, ⟨o0⟩⟩ := T7c.1 hnc
  obtain ⟨hRle, -⟩ := T7d hnc
  have hRtop : uniformRadius Z ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hRle
  have : Nonempty (Σ v : V, R.Opt v) := ⟨⟨v0, o0⟩⟩
  have hc : 0 < R.cstar := by
    obtain ⟨c₀, hc₀, hc₀'⟩ := R.cstar_pos
    exact lt_of_lt_of_le hc₀ (le_ciInf (fun p : (Σ v : V, R.Opt v) => hc₀' p.1 p.2))
  have hq1 : (0 : ℝ) < (q : ℝ) + 1 := by positivity
  have hd0 : 0 ≤ dq q := by
    unfold dq; have := Real.cos_le_one (Real.pi / ((q : ℝ) + 1)); linarith
  have hdq : dq q ≤ Real.pi ^ 2 / ((q : ℝ) + 1) ^ 2 := by
    unfold dq
    have := Real.one_sub_sq_div_two_le_cos (x := Real.pi / ((q : ℝ) + 1))
    have e : (Real.pi / ((q : ℝ) + 1)) ^ 2 = Real.pi ^ 2 / ((q : ℝ) + 1) ^ 2 := by
      rw [div_pow]
    rw [e] at this
    linarith
  have hD : dq q / R.cstar ≤ Real.pi ^ 2 / (R.cstar * ((q : ℝ) + 1) ^ 2) := by
    calc dq q / R.cstar ≤ Real.pi ^ 2 / ((q : ℝ) + 1) ^ 2 / R.cstar :=
          div_le_div_of_nonneg_right hdq hc.le
      _ = _ := by field_simp
  have hMle : memRadius R q ≤ uniformRadius Z := by
    obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    exact (theorem_3_2 R Z hRZ).2 q' |>.2
  have hlow : uniformRadius Z ≤ memRadius R q + ENNReal.ofReal (dq q / R.cstar) := by
    apply ENNReal.le_of_forall_pos_le_add
    intro ε hε _
    have hD0 : 0 ≤ dq q / R.cstar := div_nonneg hd0 hc.le
    set r := (uniformRadius Z).toReal with hr
    have hRr : uniformRadius Z = ENNReal.ofReal r := (ENNReal.ofReal_toReal hRtop).symm
    by_cases hcase : r ≤ dq q / R.cstar + ε
    · rw [hRr]
      calc ENNReal.ofReal r ≤ ENNReal.ofReal (dq q / R.cstar + (ε : ℝ)) :=
            ENNReal.ofReal_le_ofReal hcase
        _ = ENNReal.ofReal (dq q / R.cstar) + ε := by
            rw [ENNReal.ofReal_add hD0 ε.coe_nonneg, ENNReal.ofReal_coe_nnreal]
        _ ≤ _ := by
            rw [add_comm (memRadius R q), add_right_comm]
            exact le_self_add
    · rw [not_le] at hcase
      set l : ℝ := r - dq q / R.cstar - ε with hl
      have hl0 : 0 < l := by rw [hl]; linarith
      have hεpos : (0 : ℝ) < ε := by exact_mod_cast hε
      have hlt : ENNReal.ofReal (l + dq q / R.cstar) < uniformRadius Z := by
        rw [hRr]
        exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by rw [hl]; linarith)
      obtain ⟨x, hx⟩ := cert R Z hRZ hc q hq (l + dq q / R.cstar) (by linarith) hlt l hl0 le_rfl
      have hM : ENNReal.ofReal l ≤ memRadius R q := by
        have : ENNReal.ofReal l = ((l.toNNReal : ℝ≥0) : ℝ≥0∞) := rfl
        rw [this]
        unfold memRadius
        refine le_iSup₂_of_le l.toNNReal ⟨x, ?_⟩ le_rfl
        simpa [Real.coe_toNNReal l hl0.le] using hx
      rw [hRr]
      have : r = l + dq q / R.cstar + ε := by rw [hl]; ring
      rw [this, ENNReal.ofReal_add (by linarith) ε.coe_nonneg, ENNReal.ofReal_add hl0.le hD0,
        ENNReal.ofReal_coe_nnreal]
      exact add_le_add (add_le_add hM le_rfl) le_rfl
  have hB : uniformRadius Z ≤ memRadius R q +
      ENNReal.ofReal (Real.pi ^ 2 / (R.cstar * ((q : ℝ) + 1) ^ 2)) := by
    refine hlow.trans ?_
    exact add_le_add le_rfl (ENNReal.ofReal_le_ofReal hD)
  refine ⟨hD, ⟨hMle, hlow⟩, ?_, ?_⟩
  · intro h0
    exact ennreal_aux _ _ _ h0.ne' hRtop hMle hB
  · intro P
    rw [radius_eq R q P]
    exact ⟨⟨hMle, hlow⟩, fun h0 => ennreal_aux _ _ _ h0.ne' hRtop hMle hB⟩

end LocalLemmaHierarchy.Completeness
end

theorem solution : type_of% @LocalLemmaHierarchy.Completeness.chk_theorem_3_9 := @LocalLemmaHierarchy.Completeness.chk_theorem_3_9
