-- Prove2me | solution 1 for LocalLemmaHierarchy.Completeness.lemma_3_6
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T07:31:57.374099+00:00
-- url     : https://prove2.me/submissions/074f17ae-e44a-4834-b387-5df4a0814158

import Mathlib
import Definitions.Def_LocalLemmaHierarchy_Completeness_Representation
import Definitions.Def_LocalLemmaHierarchy_Completeness_Histories
import Definitions.Def_LocalLemmaHierarchy_Completeness_Memory
import Theorems.Thm_LocalLemmaHierarchy_Completeness_proposition_3_4

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

/-- A suffix of a history exact in `U` is an ambient exact history of at most `j` moves. -/
theorem suffix_state {U : Set V} {h : Hist R} (he : IsExact R U h) (j : ℕ) :
    IsMemState R j (h.suffix j) := by
  refine ⟨⟨Set.mem_univ _, ?_⟩, ?_⟩
  · intro i hi
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
      exact fun hh => this.2 (hsub hh)
    · refine ⟨h3.1, Set.mem_sdiff_of_mem (Set.mem_univ _) ?_⟩
      intro hh
      have := h3.2
      simp only [Set.mem_sdiff, Finset.mem_coe] at this
      exact this.2 (hsub hh)
  · show ((h.moves).drop (h.moves.length - j)).length ≤ j
    simp only [List.length_drop]
    omega

theorem suffix_state_univ {s : Hist R} (hs : IsExact R Set.univ s) (j : ℕ) :
    IsMemState R j (s.suffix j) := suffix_state hs j

/-- Appending a legal move to an exact history. -/
theorem append_exact {U : Set V} {s : Hist R} (hs : IsExact R U s) (m : Move R)
    (hm : LegalExactStep R U s.start s.moves m) : IsExact R U (s.append m) := by
  refine ⟨hs.1, ?_⟩
  intro i hi
  have hi' : i < s.moves.length + 1 := by
    simpa [Hist.append] using hi
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi' with hlt | heq
  · have := hs.2 i hlt
    have e1 : (s.append m).moves.take i = s.moves.take i := by
      simp only [Hist.append]
      rw [List.take_append_of_le_length hlt.le]
    have e2 : (s.append m).moves[i] = s.moves[i] := by
      simp only [Hist.append]
      rw [List.getElem_append_left hlt]
    show LegalExactStep R U s.start ((s.append m).moves.take i) ((s.append m).moves[i])
    rw [e1, e2]
    exact this
  · subst heq
    have e1 : (s.append m).moves.take s.moves.length = s.moves := by
      simp [Hist.append]
    have e2 : (s.append m).moves[s.moves.length] = m := by
      simp [Hist.append]
    show LegalExactStep R U s.start ((s.append m).moves.take s.moves.length)
      ((s.append m).moves[s.moves.length])
    rw [e1, e2]
    exact hm

theorem endpoint_suffix (j : ℕ) (h : Hist R) : (h.suffix j).endpoint = h.endpoint := by
  show Hist.endpointOf (Hist.endpointOf h.start (h.moves.take (h.moves.length - j)))
    (h.moves.drop (h.moves.length - j)) = Hist.endpointOf h.start h.moves
  rw [← endpointOf_append, List.take_append_drop]

theorem suffix_suffix {q j : ℕ} (hqj : q ≤ j) (h : Hist R) :
    (h.suffix j).suffix q = h.suffix q := by
  obtain ⟨s, ms⟩ := h
  simp only [Hist.suffix, List.length_drop]
  have e : (ms.length - j) + (ms.length - (ms.length - j) - q) = ms.length - q := by omega
  have e1 : Hist.endpointOf (Hist.endpointOf s (ms.take (ms.length - j)))
      ((ms.drop (ms.length - j)).take (ms.length - (ms.length - j) - q))
      = Hist.endpointOf s (ms.take (ms.length - q)) := by
    rw [← endpointOf_append, ← List.take_add, e]
  have e2 : (ms.drop (ms.length - j)).drop (ms.length - (ms.length - j) - q)
      = ms.drop (ms.length - q) := by
    rw [List.drop_drop, e]
  rw [e1, e2]

theorem append_suffix (j : ℕ) (h : Hist R) (m : Move R) :
    (h.suffix j).append m = (h.append m).suffix (j + 1) := by
  obtain ⟨s, ms⟩ := h
  simp only [Hist.suffix, Hist.append, List.length_append, List.length_singleton]
  have e : ms.length + 1 - (j + 1) = ms.length - j := by omega
  rw [e, List.take_append_of_le_length (by omega), List.drop_append_of_le_length (by omega)]

end LocalLemmaHierarchy.Completeness.Dev.T32
end

section
set_option autoImplicit false

open scoped ENNReal NNReal

namespace LocalLemmaHierarchy.Completeness.Dev.T32

open scoped Classical

variable {V T : Type} {R : PosLocalDeletionRep V T}

/-- Generic domination of a sum of products of `(1-f)⁻¹` factors. -/
theorem gen_le {ι : Type} [Fintype ι] (c : ι → ℝ) (hc : ∀ a, 0 ≤ c a) (P Q : ι → Prop) [DecidablePred P] [DecidablePred Q]
    (hPQ : ∀ a, P a → Q a) (E M : ι → Finset V) (hEM : ∀ a, P a → E a ⊆ M a)
    (f g : ι → V → ℝ) (hfg : ∀ a, P a → ∀ u ∈ E a, f a u = g a u)
    (hg : ∀ a, Q a → ∀ u ∈ M a, 0 ≤ g a u ∧ g a u < 1) :
    ∑ a ∈ Finset.univ.filter P, c a * ∏ u ∈ E a, (1 - f a u)⁻¹
      ≤ ∑ a ∈ Finset.univ.filter Q, c a * ∏ u ∈ M a, (1 - g a u)⁻¹ := by
  have hpos : ∀ a, Q a → ∀ u ∈ M a, 1 ≤ (1 - g a u)⁻¹ ∧ 0 ≤ (1 - g a u)⁻¹ := by
    intro a ha u hu
    obtain ⟨h0, h1⟩ := hg a ha u hu
    have hp : 0 < 1 - g a u := by linarith
    refine ⟨?_, (inv_pos.mpr hp).le⟩
    rw [one_le_inv₀ hp]; linarith
  calc ∑ a ∈ Finset.univ.filter P, c a * ∏ u ∈ E a, (1 - f a u)⁻¹
      ≤ ∑ a ∈ Finset.univ.filter P, c a * ∏ u ∈ M a, (1 - g a u)⁻¹ := by
        apply Finset.sum_le_sum
        intro a ha
        have haP : P a := (Finset.mem_filter.mp ha).2
        apply mul_le_mul_of_nonneg_left _ (hc a)
        calc ∏ u ∈ E a, (1 - f a u)⁻¹ = ∏ u ∈ E a, (1 - g a u)⁻¹ :=
              Finset.prod_congr rfl (fun u hu => by rw [hfg a haP u hu])
          _ ≤ ∏ u ∈ M a, (1 - g a u)⁻¹ := by
              apply Finset.prod_le_prod_of_subset_of_one_le (hEM a haP)
              · intro u hu; exact (hpos a (hPQ a haP) u (hEM a haP hu)).2
              · intro u hu _; exact (hpos a (hPQ a haP) u hu).1
    _ ≤ ∑ a ∈ Finset.univ.filter Q, c a * ∏ u ∈ M a, (1 - g a u)⁻¹ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro a ha
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hPQ a (Finset.mem_filter.mp ha).2⟩
        · intro a ha _
          have haQ : Q a := (Finset.mem_filter.mp ha).2
          exact mul_nonneg (hc a) (Finset.prod_nonneg (fun u hu => (hpos a haQ u hu).2))

/-- Exact update at `h` (endpoint generalised to `v`). -/
noncomputable def exU (U : Set V) (p : T → ℝ) (x : Hist R → ℝ) (h : Hist R) (v : V) : ℝ :=
  ∑ a ∈ Finset.univ.filter
      (fun a : R.Opt v => (↑(R.A v a) : Set V) ⊆ U \ ↑(deleted R h.moves)),
    R.c v a * p (R.label v a) *
      ∏ u ∈ ((R.D v a).erase v).filter (fun u => u ∈ U \ ↑(deleted R h.moves)),
        (1 - x (h.append ⟨v, a, u⟩))⁻¹

/-- Memory update at `s` (endpoint generalised to `v`). -/
noncomputable def memU (q : ℕ) (p : T → ℝ) (x : Hist R → ℝ) (s : Hist R) (v : V) : ℝ :=
  ∑ a ∈ Finset.univ.filter (fun a : R.Opt v => Disjoint (R.A v a) (deleted R s.moves)),
    R.c v a * p (R.label v a) *
      ∏ u ∈ R.D v a \ insert v (deleted R s.moves),
        (1 - x ((s.append ⟨v, a, u⟩).suffix q))⁻¹

theorem exactUpdate_eq (U : Set V) (p : T → ℝ) (x : Hist R → ℝ) (h : Hist R) :
    exactUpdate R U p x h = exU U p x h h.endpoint := rfl

theorem memUpdate_eq (q : ℕ) (p : T → ℝ) (x : Hist R → ℝ) (s : Hist R) :
    memUpdate R q p x s = memU q p x s s.endpoint := rfl

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

theorem child_exact {h : Hist R} (hh : IsExact R Set.univ h) (v : V) (hv : h.endpoint = v)
    (a : R.Opt v) (ha : (↑(R.A v a) : Set V) ⊆ Set.univ \ ↑(deleted R h.moves))
    (u : V) (hu : u ∈ ((R.D v a).erase v).filter (fun u => u ∈ Set.univ \ ↑(deleted R h.moves))) :
    IsExact R Set.univ (h.append ⟨v, a, u⟩) := by
  simp only [Finset.mem_filter, Finset.mem_erase] at hu
  refine append_exact hh _ ⟨hv.symm, ha, ⟨hu.1.2, hu.2⟩, hu.1.1⟩

theorem cmp {ν : ℝ} (hν : 0 < ν) (U : Set V) (hU : ∀ x, x ∈ U) (X : Hist R → ℝ) (q j' : ℕ) (hjq : j' + 1 ≤ q)
    (s h : Hist R) (hh : h = s.suffix j') (v : V)
    (hxs : ∀ (a : R.Opt v), (↑(R.A v a) : Set V) ⊆ U \ ↑(deleted R h.moves) →
      ∀ u ∈ (R.D v a).erase v, u ∉ deleted R h.moves →
        0 ≤ X (h.append ⟨v, a, u⟩) ∧ X (h.append ⟨v, a, u⟩) < 1) :
    memU q (fun _ => ν) (fun s' => X (s'.suffix (j' + 1))) s v ≤
      exU U (fun _ => ν) X h v := by
  have hBs : deleted R h.moves ⊆ deleted R s.moves := by rw [hh]; exact deleted_suffix_sub j' s
  unfold exU memU
  beta_reduce
  refine gen_le (fun a => R.c v a * ν) (fun a => (mul_pos (R.c_pos v a) hν).le)
    (fun a => Disjoint (R.A v a) (deleted R s.moves))
    (fun a => (↑(R.A v a) : Set V) ⊆ U \ ↑(deleted R h.moves)) ?_
    (fun a => R.D v a \ insert v (deleted R s.moves))
    (fun a => ((R.D v a).erase v).filter (fun u => u ∈ U \ ↑(deleted R h.moves))) ?_
    (fun a u => X (((s.append ⟨v, a, u⟩).suffix q).suffix (j' + 1)))
    (fun a u => X (h.append ⟨v, a, u⟩)) ?_ ?_
  · intro a ha w hw
    simp only [Set.mem_sdiff, Finset.mem_coe]
    exact ⟨hU _, fun hws => Finset.disjoint_left.mp ha hw (hBs hws)⟩
  · intro a ha u hu
    simp only [Finset.mem_sdiff, Finset.mem_insert, not_or] at hu
    simp only [Finset.mem_filter, Finset.mem_erase, Set.mem_sdiff, Finset.mem_coe]
    exact ⟨⟨hu.2.1, hu.1⟩, hU _, fun hh' => hu.2.2 (hBs hh')⟩
  · intro a _ u _
    rw [hh, suffix_suffix hjq, ← append_suffix j']
  · intro a ha u hu
    simp only [Finset.mem_filter, Set.mem_sdiff, Finset.mem_coe] at hu
    exact hxs a ha u hu.1 hu.2.2

end LocalLemmaHierarchy.Completeness.Dev.L36

namespace LocalLemmaHierarchy.Completeness

open scoped Classical in
open Dev.T32 Dev.L36 in
theorem chk_lemma_3_6 {V T : Type} (R : PosLocalDeletionRep V T)
    (Z : Finset V → MvPolynomial T ℝ) (hRZ : IsRepresentationOf R Z)
    (ν : ℝ) (hν : 0 < ν) (hνR : ENNReal.ofReal ν < uniformRadius Z) (q j : ℕ)
    (hj1 : 1 ≤ j) (hjq : j ≤ q) :
    ∀ s : Hist R, IsMemState R q s →
      memUpdate R q (fun _ => ν) (fun s' => canonicalBranch R ν (s'.suffix j)) s ≤
        canonicalBranch R ν (s.suffix (j - 1)) := by
  intro s hs
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  have hj : j' + 1 - 1 = j' := by omega
  rw [hj]
  have h34 := proposition_3_4 R Z hRZ ν hν hνR
  have hhs : IsExact R Set.univ (s.suffix j') := (suffix_state_univ hs.1 j').1
  rw [(h34.2.1 _ hhs).1, exactUpdate_eq, memUpdate_eq, ← endpoint_suffix j' s]
  generalize hv : (s.suffix j').endpoint = v
  refine cmp hν Set.univ (fun _ => Set.mem_univ _) _ q j' hjq s _ rfl v ?_
  intro a ha u hu1 hu2
  have hu : u ∈ ((R.D v a).erase v).filter (fun u => u ∈ Set.univ \ ↑(deleted R (s.suffix j').moves)) := by
    simp only [Finset.mem_filter, Set.mem_sdiff, Set.mem_univ, true_and, Finset.mem_coe]
    exact ⟨hu1, hu2⟩
  have he := child_exact hhs v hv a ha u hu
  have := h34.2.1 _ he
  exact ⟨this.2.1, this.2.2.2⟩

end LocalLemmaHierarchy.Completeness
end

theorem solution : type_of% @LocalLemmaHierarchy.Completeness.chk_lemma_3_6 := @LocalLemmaHierarchy.Completeness.chk_lemma_3_6
