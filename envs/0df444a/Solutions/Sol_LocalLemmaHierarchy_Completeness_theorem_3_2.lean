-- Prove2me | solution 1 for LocalLemmaHierarchy.Completeness.theorem_3_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T07:18:19.841645+00:00
-- url     : https://prove2.me/submissions/b5d54a0d-4a97-40bf-b066-ee5f80cc0f62

import Mathlib
import Definitions.Def_LocalLemmaHierarchy_Completeness_Representation
import Definitions.Def_LocalLemmaHierarchy_Completeness_Histories
import Definitions.Def_LocalLemmaHierarchy_Completeness_Memory
import Theorems.Thm_LocalLemmaHierarchy_Completeness_theorem_2_3

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

theorem suffix_append_suffix {q j : ℕ} (hqj : q ≤ j) (h : Hist R) (m : Move R) :
    ((h.suffix j).append m).suffix q = (h.append m).suffix q := by
  rw [append_suffix, suffix_suffix (by omega)]

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

theorem coef_nonneg {p : T → ℝ} (hp : ∀ τ, 0 ≤ p τ) (v : V) (a : R.Opt v) :
    0 ≤ R.c v a * p (R.label v a) := mul_nonneg (R.c_pos v a).le (hp _)

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

theorem exU_le_memU (U : Set V) (q : ℕ) (p : T → ℝ) (hp : ∀ τ, 0 ≤ p τ) (x : Hist R → ℝ)
    (h s : Hist R) (v : V) (hBs : deleted R s.moves ⊆ deleted R h.moves)
    (hxe : ∀ (a : R.Opt v) (u : V),
      x ((h.append ⟨v, a, u⟩).suffix q) = x ((s.append ⟨v, a, u⟩).suffix q))
    (hxs : ∀ (a : R.Opt v), Disjoint (R.A v a) (deleted R s.moves) →
      ∀ u ∈ R.D v a \ insert v (deleted R s.moves),
        0 ≤ x ((s.append ⟨v, a, u⟩).suffix q) ∧ x ((s.append ⟨v, a, u⟩).suffix q) < 1) :
    exU U p (fun h => x (h.suffix q)) h v ≤ memU q p x s v := by
  unfold exU memU
  beta_reduce
  refine gen_le (fun a => R.c v a * p (R.label v a)) (fun a => coef_nonneg hp v a)
    (fun a => (↑(R.A v a) : Set V) ⊆ U \ ↑(deleted R h.moves))
    (fun a => Disjoint (R.A v a) (deleted R s.moves)) ?_
    (fun a => ((R.D v a).erase v).filter (fun u => u ∈ U \ ↑(deleted R h.moves)))
    (fun a => R.D v a \ insert v (deleted R s.moves)) ?_
    (fun a u => x ((h.append ⟨v, a, u⟩).suffix q)) (fun a u => x ((s.append ⟨v, a, u⟩).suffix q))
    ?_ hxs
  · intro a ha
    rw [Finset.disjoint_left]
    intro w hw hws
    have := ha hw
    simp only [Set.mem_sdiff, Finset.mem_coe] at this
    exact this.2 (hBs hws)
  · intro a ha u hu
    simp only [Finset.mem_filter, Finset.mem_erase] at hu
    simp only [Finset.mem_sdiff, Finset.mem_insert, not_or]
    refine ⟨hu.1.2, hu.1.1, ?_⟩
    intro hh
    have := hu.2
    simp only [Set.mem_sdiff, Finset.mem_coe] at this
    exact this.2 (hBs hh)
  · intro a _ u _
    exact hxe a u

end LocalLemmaHierarchy.Completeness.Dev.T32
end

section
set_option autoImplicit false

open scoped ENNReal NNReal

namespace LocalLemmaHierarchy.Completeness.Dev.T32

open scoped Classical

variable {V T : Type} {R : PosLocalDeletionRep V T}

theorem child_bounds {q : ℕ} {p : T → ℝ} {x : Hist R → ℝ} (hx : IsMemCertificate R q p x)
    {s : Hist R} (hs : IsExact R Set.univ s) (v : V) (hv : s.endpoint = v) (a : R.Opt v)
    (ha : Disjoint (R.A v a) (deleted R s.moves))
    (u : V) (hu : u ∈ R.D v a \ insert v (deleted R s.moves)) :
    0 ≤ x ((s.append ⟨v, a, u⟩).suffix q) ∧ x ((s.append ⟨v, a, u⟩).suffix q) < 1 := by
  subst hv
  simp only [Finset.mem_sdiff, Finset.mem_insert, not_or] at hu
  have hl : LegalExactStep R Set.univ s.start s.moves ⟨s.endpoint, a, u⟩ := by
    refine ⟨rfl, ?_, ?_, hu.2.1⟩
    · intro w hw
      simp only [Set.mem_sdiff, Set.mem_univ, true_and, Finset.mem_coe]
      exact Finset.disjoint_left.mp ha hw
    · refine ⟨by simpa using hu.1, ?_⟩
      simp only [Set.mem_sdiff, Set.mem_univ, true_and, Finset.mem_coe]
      exact hu.2.2
  have hst := suffix_state (append_exact hs _ hl) q
  obtain ⟨h0, h1, _⟩ := hx _ hst
  exact ⟨h0, h1⟩

theorem exact_sup {q : ℕ} {p : T → ℝ} (hp : ∀ τ, 0 ≤ p τ) {x : Hist R → ℝ}
    (hx : IsMemCertificate R q p x) (U : Set V) :
    IsExactSupersolution R U p (fun h => x (h.suffix q)) := by
  intro h hh
  have hs := suffix_state hh q
  obtain ⟨h0, h1, h2⟩ := hx _ hs
  refine ⟨h0, h1, le_trans ?_ h2⟩
  rw [exactUpdate_eq, memUpdate_eq, endpoint_suffix]
  refine exU_le_memU U q p hp x h (h.suffix q) h.endpoint ?_ ?_ ?_
  · apply deleted_mono
    intro m hm
    exact List.mem_of_mem_drop hm
  · intro a u
    rw [suffix_append_suffix le_rfl]
  · intro a ha u hu
    exact child_bounds hx hs.1 h.endpoint (endpoint_suffix q h) a ha u hu

theorem sound {q : ℕ} {p : T → ℝ} (hp : ∀ τ, 0 ≤ p τ) {x : Hist R → ℝ}
    (hx : IsMemCertificate R q p x) (Z : Finset V → MvPolynomial T ℝ)
    (hRZ : IsRepresentationOf R Z) (U : Finset V) : ZeroFreeOn Z U p := by
  have h23 := LocalLemmaHierarchy.Completeness.theorem_2_3 R Z hRZ U p hp
  exact h23.1.mpr (h23.2.1.mpr ⟨_, exact_sup hp hx (↑U : Set V)⟩)

theorem nest {q : ℕ} {p : T → ℝ} (hp : ∀ τ, 0 ≤ p τ) {x : Hist R → ℝ}
    (hx : IsMemCertificate R q p x) :
    IsMemCertificate R (q + 1) p (fun s => x (s.suffix q)) := by
  intro s hs
  have hs' := suffix_state hs.1 q
  obtain ⟨h0, h1, h2⟩ := hx _ hs'
  refine ⟨h0, h1, le_trans ?_ h2⟩
  rw [memUpdate_eq, memUpdate_eq, endpoint_suffix]
  unfold memU
  beta_reduce
  refine gen_le (fun a => R.c s.endpoint a * p (R.label s.endpoint a))
    (fun a => coef_nonneg hp _ a)
    (fun a => Disjoint (R.A s.endpoint a) (deleted R s.moves))
    (fun a => Disjoint (R.A s.endpoint a) (deleted R (s.suffix q).moves)) ?_
    (fun a => R.D s.endpoint a \ insert s.endpoint (deleted R s.moves))
    (fun a => R.D s.endpoint a \ insert s.endpoint (deleted R (s.suffix q).moves)) ?_
    (fun a u => x (((s.append ⟨s.endpoint, a, u⟩).suffix (q + 1)).suffix q))
    (fun a u => x (((s.suffix q).append ⟨s.endpoint, a, u⟩).suffix q)) ?_ ?_
  · have hsub : deleted R (s.suffix q).moves ⊆ deleted R s.moves := by
      apply deleted_mono
      intro m hm
      exact List.mem_of_mem_drop hm
    intro a ha
    exact Finset.disjoint_of_subset_right hsub ha
  · have hsub : deleted R (s.suffix q).moves ⊆ deleted R s.moves := by
      apply deleted_mono
      intro m hm
      exact List.mem_of_mem_drop hm
    intro a _ u hu
    simp only [Finset.mem_sdiff, Finset.mem_insert, not_or] at hu ⊢
    exact ⟨hu.1, hu.2.1, fun hh => hu.2.2 (hsub hh)⟩
  · intro a _ u _
    rw [suffix_suffix (Nat.le_succ q), suffix_append_suffix le_rfl]
  · intro a ha u hu
    exact child_bounds hx hs'.1 s.endpoint (endpoint_suffix q s) a ha u hu

end LocalLemmaHierarchy.Completeness.Dev.T32

namespace LocalLemmaHierarchy.Completeness

open Dev.T32 in
theorem chk_theorem_3_2 {V T : Type} (R : PosLocalDeletionRep V T)
    (Z : Finset V → MvPolynomial T ℝ) (hRZ : IsRepresentationOf R Z) :
    (∀ (q : ℕ) (p : T → ℝ), (∀ τ, 0 ≤ p τ) → ∀ x : Hist R → ℝ, IsMemCertificate R q p x →
      ∀ U : Finset V, ZeroFreeOn Z U p) ∧
    ∀ q : ℕ, memRadius R q ≤ memRadius R (q + 1) ∧ memRadius R (q + 1) ≤ uniformRadius Z := by
  refine ⟨fun q p hp x hx U => sound hp hx Z hRZ U, fun q => ⟨?_, ?_⟩⟩
  · refine iSup₂_le ?_
    intro t ⟨x, hx⟩
    exact le_iSup₂_of_le t ⟨_, nest (fun _ => t.2) hx⟩ le_rfl
  · refine iSup₂_le ?_
    intro t ⟨x, hx⟩
    refine le_iInf (fun U => ?_)
    exact le_iSup₂_of_le t (sound (fun _ => t.2) hx Z hRZ U) le_rfl

end LocalLemmaHierarchy.Completeness
end

theorem solution : type_of% @LocalLemmaHierarchy.Completeness.chk_theorem_3_2 := @LocalLemmaHierarchy.Completeness.chk_theorem_3_2
