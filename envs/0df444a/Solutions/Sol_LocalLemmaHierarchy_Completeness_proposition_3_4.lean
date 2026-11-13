-- Prove2me | solution 1 for LocalLemmaHierarchy.Completeness.proposition_3_4
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T07:31:57.309935+00:00
-- url     : https://prove2.me/submissions/553486a8-d0e0-4e88-9d95-38f7b3e6d0cb

import Mathlib
import Definitions.Def_LocalLemmaHierarchy_Completeness_Representation
import Definitions.Def_LocalLemmaHierarchy_Completeness_Histories
import Theorems.Thm_LocalLemmaHierarchy_Completeness_theorem_2_3
import Theorems.Thm_LocalLemmaHierarchy_Completeness_proposition_2_4

section
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace LocalLemmaHierarchy.Completeness.Dev.T23

open LocalLemmaHierarchy.Completeness


section hist

variable {V T : Type} [DecidableEq V] {R : PosLocalDeletionRep V T}

lemma mem_departure (m : Move R) (w : V) :
    w ∈ departure R m ↔ w = m.1 ∨ (w ∈ R.D m.1 m.2.1 ∧ w ≠ m.1 ∧
      R.rank m.1 m.2.1 w < R.rank m.1 m.2.1 m.2.2) := by
  classical
  simp only [departure, Finset.mem_insert, Finset.mem_filter, Finset.mem_erase]
  tauto

lemma mem_deleted (ms : List (Move R)) (w : V) :
    w ∈ deleted R ms ↔ ∃ m ∈ ms, w ∈ departure R m := by
  classical
  induction ms with
  | nil => simp [deleted]
  | cons m ms ih =>
    have : w ∈ deleted R (m :: ms) ↔ w ∈ departure R m ∨ w ∈ deleted R ms := by
      simp [deleted]
    rw [this, ih]
    simp

lemma endpoint_append (h : Hist R) (m : Move R) : (h.append m).endpoint = m.2.2 := by
  simp [Hist.endpoint, Hist.append, Hist.endpointOf]

lemma mem_residual (U : Finset V) (h : Hist R) (w : V) :
    w ∈ residual R U h ↔ w ∈ U ∧ w ∉ deleted R h.moves := by
  classical
  simp [residual]

lemma exact_append_iff (U : Set V) (h : Hist R) (m : Move R) :
    IsExact R U (h.append m) ↔ IsExact R U h ∧ LegalExactStep R U h.start h.moves m := by
  obtain ⟨s, ms⟩ := h
  simp only [IsExact, Hist.append, List.length_append, List.length_singleton]
  constructor
  · intro ⟨hs, hall⟩
    refine ⟨⟨hs, fun i hi => ?_⟩, ?_⟩
    · have := hall i (by omega)
      rwa [List.take_append_of_le_length hi.le, List.getElem_append_left hi] at this
    · have := hall ms.length (by omega)
      rw [List.take_left', List.getElem_append_right (by simp)] at this
      · simpa using this
      · simp
  · intro ⟨⟨hs, hall⟩, hm⟩
    refine ⟨hs, fun i hi => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h1 | h1
    · rw [List.take_append_of_le_length h1.le, List.getElem_append_left h1]
      exact hall i h1
    · subst h1
      rw [List.take_left', List.getElem_append_right (by simp)]
      · simpa using hm
      · simp

end hist


section row

variable {V T : Type} [DecidableEq V] {R : PosLocalDeletionRep V T}

/-- The surviving factor sites of option `a` at `v` inside `W`. -/
def RowSet (R : PosLocalDeletionRep V T) (W : Finset V) (v : V) (a : R.Opt v) : Finset V :=
  ((R.D v a).erase v).filter (fun u => u ∈ W)

lemma mem_RowSet (W : Finset V) (v : V) (a : R.Opt v) (u : V) :
    u ∈ RowSet R W v a ↔ u ∈ R.D v a ∧ u ≠ v ∧ u ∈ W := by
  simp only [RowSet, Finset.mem_filter, Finset.mem_erase]
  tauto

end row


section exact

variable {V T : Type} [DecidableEq V] {R : PosLocalDeletionRep V T}

lemma exactUpdate_eq (U : Finset V) (p : T → ℝ) (x : Hist R → ℝ) (h : Hist R) :
    exactUpdate R (↑U : Set V) p x h =
      ∑ a ∈ Finset.univ.filter (fun a : R.Opt h.endpoint => R.A h.endpoint a ⊆ residual R U h),
        R.c h.endpoint a * p (R.label h.endpoint a) *
          ∏ u ∈ RowSet R (residual R U h) h.endpoint a,
            (1 - x (h.append ⟨h.endpoint, a, u⟩))⁻¹ := by
  classical
  unfold exactUpdate
  have hmem : ∀ w : V, w ∈ residual R U h ↔ w ∈ (↑U : Set V) \ ↑(deleted R h.moves) := by
    intro w; rw [mem_residual]; simp
  refine Finset.sum_congr ?_ (fun a _ => ?_)
  · apply Finset.filter_congr
    intro a _
    constructor
    · intro hA w hw; exact (hmem w).2 (hA hw)
    · intro hA w hw; exact (hmem w).1 (hA hw)
  · congr 1
    apply Finset.prod_congr _ (fun _ _ => rfl)
    ext u
    rw [mem_RowSet]
    simp only [Finset.mem_filter, Finset.mem_erase, hmem]
    tauto

lemma legal_of (U : Finset V) (h : Hist R) (a : R.Opt h.endpoint) (u : V)
    (hA : R.A h.endpoint a ⊆ residual R U h)
    (hu : u ∈ RowSet R (residual R U h) h.endpoint a) :
    LegalExactStep R (↑U : Set V) h.start h.moves ⟨h.endpoint, a, u⟩ := by
  have hmem : ∀ w : V, w ∈ residual R U h → w ∈ (↑U : Set V) \ ↑(deleted R h.moves) := by
    intro w hw; rw [mem_residual] at hw; simpa using hw
  rw [mem_RowSet] at hu
  refine ⟨rfl, fun w hw => hmem w (hA hw), ⟨hu.1, hmem u hu.2.2⟩, hu.2.1⟩

lemma child_exact (U : Finset V) (h : Hist R) (hh : IsExact R (↑U : Set V) h)
    (a : R.Opt h.endpoint) (u : V)
    (hA : R.A h.endpoint a ⊆ residual R U h)
    (hu : u ∈ RowSet R (residual R U h) h.endpoint a) :
    IsExact R (↑U : Set V) (h.append ⟨h.endpoint, a, u⟩) :=
  (exact_append_iff _ _ _).2 ⟨hh, legal_of U h a u hA hu⟩

end exact

end LocalLemmaHierarchy.Completeness.Dev.T23
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace LocalLemmaHierarchy.Completeness.Dev.T23

open LocalLemmaHierarchy.Completeness

section real

variable {V T : Type} [inst : DecidableEq V] {R : PosLocalDeletionRep V T}

lemma upd_mono (U : Finset V) (p : T → ℝ) (hp : ∀ τ, 0 ≤ p τ) (x y : Hist R → ℝ) (h : Hist R)
    (hh : IsExact R (↑U : Set V) h)
    (hxy : ∀ h', IsExact R (↑U : Set V) h' → x h' ≤ y h' ∧ y h' < 1) :
    exactUpdate R (↑U : Set V) p x h ≤ exactUpdate R (↑U : Set V) p y h := by
  rw [exactUpdate_eq, exactUpdate_eq]
  refine Finset.sum_le_sum (fun a ha => ?_)
  rw [Finset.mem_filter] at ha
  refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (R.c_pos _ _).le (hp _))
  refine Finset.prod_le_prod (fun u hu => ?_) (fun u hu => ?_)
  · have := hxy _ (child_exact U h hh a u ha.2 hu)
    exact (inv_pos.2 (by linarith [this.1, this.2])).le
  · have := hxy _ (child_exact U h hh a u ha.2 hu)
    exact inv_anti₀ (by linarith [this.1, this.2]) (by linarith [this.1, this.2])

lemma iter_le (U : Finset V) (p : T → ℝ) (hp : ∀ τ, 0 ≤ p τ) (x : Hist R → ℝ)
    (hx : IsExactSupersolution R (↑U : Set V) p x) :
    ∀ N : ℕ, ∀ h : Hist R, IsExact R (↑U : Set V) h →
      exactIter R (↑U : Set V) p N h ≤ x h := by
  intro N
  induction N with
  | zero => intro h hh; exact (hx h hh).1
  | succ N ih =>
    intro h hh
    show exactUpdate R (↑U : Set V) p (exactIter R (↑U : Set V) p N) h ≤ x h
    refine le_trans (upd_mono U p hp _ x h hh (fun h' hh' => ⟨ih h' hh', (hx h' hh').2.1⟩))
      (hx h hh).2.2

end real

end LocalLemmaHierarchy.Completeness.Dev.T23
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace LocalLemmaHierarchy.Completeness.Dev.P34

open LocalLemmaHierarchy.Completeness LocalLemmaHierarchy.Completeness.Dev.T23
open scoped Classical

variable {V T : Type} {R : PosLocalDeletionRep V T}

lemma child_exact_set (U : Set V) (h : Hist R) (hh : IsExact R U h) (a : R.Opt h.endpoint) (u : V)
    (hA : (↑(R.A h.endpoint a) : Set V) ⊆ U \ ↑(deleted R h.moves))
    (hu : u ∈ ((R.D h.endpoint a).erase h.endpoint).filter
      (fun u => u ∈ U \ ↑(deleted R h.moves))) :
    IsExact R U (h.append ⟨h.endpoint, a, u⟩) := by
  rw [Finset.mem_filter, Finset.mem_erase] at hu
  exact (exact_append_iff _ _ _).2 ⟨hh, rfl, hA, ⟨hu.1.2, hu.2⟩, hu.1.1⟩

lemma upd_mono_set (U : Set V) (p : T → ℝ) (hp : ∀ τ, 0 ≤ p τ) (x y : Hist R → ℝ) (h : Hist R)
    (hh : IsExact R U h)
    (hxy : ∀ h', IsExact R U h' → x h' ≤ y h' ∧ y h' < 1) :
    exactUpdate R U p x h ≤ exactUpdate R U p y h := by
  unfold exactUpdate
  refine Finset.sum_le_sum (fun a ha => ?_)
  rw [Finset.mem_filter] at ha
  refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (R.c_pos _ _).le (hp _))
  refine Finset.prod_le_prod (fun u hu => ?_) (fun u hu => ?_)
  · have := hxy _ (child_exact_set U h hh a u ha.2 hu)
    exact (inv_pos.2 (by linarith [this.1, this.2])).le
  · have := hxy _ (child_exact_set U h hh a u ha.2 hu)
    exact inv_anti₀ (by linarith [this.1, this.2]) (by linarith [this.1, this.2])

lemma iter_nonneg_set (U : Set V) (p : T → ℝ) (hp : ∀ τ, 0 ≤ p τ)
    (H : ∀ N : ℕ, ∀ h : Hist R, IsExact R U h → exactIter R U p N h < 1) :
    ∀ N : ℕ, ∀ h : Hist R, IsExact R U h → 0 ≤ exactIter R U p N h := by
  intro N
  induction N with
  | zero => intro h _; simp [exactIter]
  | succ N ih =>
    intro h hh
    show 0 ≤ exactUpdate R U p (exactIter R U p N) h
    unfold exactUpdate
    refine Finset.sum_nonneg (fun a ha => ?_)
    rw [Finset.mem_filter] at ha
    refine mul_nonneg (mul_nonneg (R.c_pos _ _).le (hp _)) (Finset.prod_nonneg (fun u hu => ?_))
    have := H N _ (child_exact_set U h hh a u ha.2 hu)
    exact (inv_pos.2 (by linarith)).le

lemma iter_scale (U : Set V) (s t : ℝ) (hs : 0 < s) (hst : s ≤ t)
    (H : ∀ N : ℕ, ∀ h : Hist R, IsExact R U h → exactIter R U (fun _ => t) N h < 1) :
    ∀ N : ℕ, ∀ h : Hist R, IsExact R U h →
      0 ≤ exactIter R U (fun _ => s) N h ∧
      exactIter R U (fun _ => s) N h * t ≤ s * exactIter R U (fun _ => t) N h := by
  have ht : 0 < t := lt_of_lt_of_le hs hst
  have hnt := iter_nonneg_set U (fun _ => t) (fun _ => ht.le) H
  intro N
  induction N with
  | zero => intro h _; simp [exactIter]
  | succ N ih =>
    intro h hh
    show 0 ≤ exactUpdate R U (fun _ => s) (exactIter R U (fun _ => s) N) h ∧
      exactUpdate R U (fun _ => s) (exactIter R U (fun _ => s) N) h * t ≤
        s * exactUpdate R U (fun _ => t) (exactIter R U (fun _ => t) N) h
    have hchild : ∀ a u, a ∈ Finset.univ.filter
        (fun a : R.Opt h.endpoint => (↑(R.A h.endpoint a) : Set V) ⊆ U \ ↑(deleted R h.moves)) →
        u ∈ ((R.D h.endpoint a).erase h.endpoint).filter
          (fun u => u ∈ U \ ↑(deleted R h.moves)) →
        0 ≤ exactIter R U (fun _ => s) N (h.append ⟨h.endpoint, a, u⟩) ∧
        exactIter R U (fun _ => s) N (h.append ⟨h.endpoint, a, u⟩) ≤
          exactIter R U (fun _ => t) N (h.append ⟨h.endpoint, a, u⟩) ∧
        exactIter R U (fun _ => t) N (h.append ⟨h.endpoint, a, u⟩) < 1 := by
      intro a u ha hu
      rw [Finset.mem_filter] at ha
      have hc := child_exact_set U h hh a u ha.2 hu
      obtain ⟨h1, h2⟩ := ih _ hc
      have h3 := hnt N _ hc
      refine ⟨h1, ?_, H N _ hc⟩
      by_contra hlt
      push Not at hlt
      nlinarith
    refine ⟨?_, ?_⟩
    · unfold exactUpdate
      refine Finset.sum_nonneg (fun a ha => ?_)
      refine mul_nonneg (mul_nonneg (R.c_pos _ _).le hs.le) (Finset.prod_nonneg (fun u hu => ?_))
      have := hchild a u ha hu
      exact (inv_pos.2 (by linarith [this.1, this.2.1, this.2.2])).le
    · unfold exactUpdate
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_le_sum (fun a ha => ?_)
      have hprod : ∏ u ∈ ((R.D h.endpoint a).erase h.endpoint).filter
            (fun u => u ∈ U \ ↑(deleted R h.moves)),
            (1 - exactIter R U (fun _ => s) N (h.append ⟨h.endpoint, a, u⟩))⁻¹ ≤
          ∏ u ∈ ((R.D h.endpoint a).erase h.endpoint).filter
            (fun u => u ∈ U \ ↑(deleted R h.moves)),
            (1 - exactIter R U (fun _ => t) N (h.append ⟨h.endpoint, a, u⟩))⁻¹ := by
        refine Finset.prod_le_prod (fun u hu => ?_) (fun u hu => ?_)
        · have := hchild a u ha hu
          exact (inv_pos.2 (by linarith [this.1, this.2.1, this.2.2])).le
        · have := hchild a u ha hu
          exact inv_anti₀ (by linarith [this.1, this.2.1, this.2.2])
            (by linarith [this.1, this.2.1, this.2.2])
      have hc0 := R.c_pos h.endpoint a
      calc R.c h.endpoint a * s * _ * t
          = (R.c h.endpoint a * (s * t)) * ∏ u ∈ ((R.D h.endpoint a).erase h.endpoint).filter
            (fun u => u ∈ U \ ↑(deleted R h.moves)),
            (1 - exactIter R U (fun _ => s) N (h.append ⟨h.endpoint, a, u⟩))⁻¹ := by ring
        _ ≤ (R.c h.endpoint a * (s * t)) * ∏ u ∈ ((R.D h.endpoint a).erase h.endpoint).filter
            (fun u => u ∈ U \ ↑(deleted R h.moves)),
            (1 - exactIter R U (fun _ => t) N (h.append ⟨h.endpoint, a, u⟩))⁻¹ :=
          mul_le_mul_of_nonneg_left hprod (by positivity)
        _ = _ := by ring

/-- one step of closure under deletion supports -/
noncomputable def stepD (R : PosLocalDeletionRep V T) (S : Finset V) : Finset V :=
  S ∪ S.biUnion (fun w => Finset.univ.biUnion (fun a : R.Opt w => R.D w a))

lemma subset_stepD (S : Finset V) : S ⊆ stepD R S := Finset.subset_union_left

lemma D_subset_stepD (S : Finset V) (w : V) (hw : w ∈ S) (a : R.Opt w) :
    R.D w a ⊆ stepD R S := by
  intro x hx
  refine Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨w, hw, Finset.mem_biUnion.2 ⟨a, Finset.mem_univ _, hx⟩⟩)

lemma stepD_mono {S S' : Finset V} (h : S ⊆ S') : stepD R S ⊆ stepD R S' := by
  intro x hx
  rcases Finset.mem_union.1 hx with hx | hx
  · exact Finset.mem_union_left _ (h hx)
  · obtain ⟨w, hw, hx⟩ := Finset.mem_biUnion.1 hx
    exact Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨w, h hw, hx⟩)

lemma iter_stepD_mono (n : ℕ) {S S' : Finset V} (h : S ⊆ S') :
    (stepD R)^[n] S ⊆ (stepD R)^[n] S' := by
  induction n generalizing S S' with
  | zero => exact h
  | succ n ih => exact ih (stepD_mono h)

lemma iter_stepD_le (n : ℕ) (S : Finset V) : S ⊆ (stepD R)^[n] S := by
  induction n generalizing S with
  | zero => exact subset_refl _
  | succ n ih => exact (subset_stepD S).trans (ih _)

lemma iter_univ_eq_finite (p : T → ℝ) (W : Finset V) :
    ∀ N : ℕ, ∀ h : Hist R, (stepD R)^[N] {h.endpoint} ⊆ W →
      exactIter R Set.univ p N h = exactIter R (↑W : Set V) p N h := by
  intro N
  induction N with
  | zero => intro h _; rfl
  | succ N ih =>
    intro h hW
    show exactUpdate R Set.univ p (exactIter R Set.univ p N) h =
      exactUpdate R (↑W : Set V) p (exactIter R (↑W : Set V) p N) h
    have hD : ∀ a : R.Opt h.endpoint, R.D h.endpoint a ⊆ W := by
      intro a
      refine (D_subset_stepD (R := R) {h.endpoint} h.endpoint (by simp) a).trans ?_
      refine (?_ : stepD R {h.endpoint} ⊆ (stepD R)^[N + 1] {h.endpoint}).trans hW
      have := iter_stepD_le (R := R) N (stepD R {h.endpoint})
      rwa [← Function.iterate_succ_apply] at this
    unfold exactUpdate
    refine Finset.sum_congr (Finset.filter_congr (fun a _ => ?_)) (fun a ha => ?_)
    · constructor
      · intro hA w hw
        exact ⟨hD a (R.A_subset_D _ _ hw), (hA hw).2⟩
      · intro hA w hw
        exact ⟨Set.mem_univ _, (hA hw).2⟩
    · rw [Finset.mem_filter] at ha
      congr 1
      refine Finset.prod_congr ?_ (fun u hu => ?_)
      · ext u
        simp only [Finset.mem_filter, Finset.mem_erase, Set.mem_sdiff, Set.mem_univ, true_and,
          Finset.mem_coe]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨h1, hD a h1.2, h2⟩
        · rintro ⟨h1, _, h2⟩; exact ⟨h1, h2⟩
      · have hu' : u ∈ R.D h.endpoint a := by
          simp only [Finset.mem_filter, Finset.mem_erase] at hu; exact hu.1.2
        have key : (stepD R)^[N] {u} ⊆ W := by
          refine (iter_stepD_mono N (S := {u}) (S' := stepD R {h.endpoint}) ?_).trans ?_
          · simpa using D_subset_stepD (R := R) {h.endpoint} h.endpoint (by simp) a hu'
          · rw [← Function.iterate_succ_apply]; exact hW
        rw [ih _ (by rw [endpoint_append]; exact key)]

end LocalLemmaHierarchy.Completeness.Dev.P34
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped ENNReal NNReal Classical

namespace LocalLemmaHierarchy.Completeness.Dev.P34

open LocalLemmaHierarchy.Completeness LocalLemmaHierarchy.Completeness.Dev.T23

variable {V T : Type} {R : PosLocalDeletionRep V T}

/-- the image of a move under a symmetry -/
def mapMove (g : RepSymmetry R) (m : Move R) : Move R :=
  ⟨g.site m.1, g.opt m.1 m.2.1, g.site m.2.2⟩

/-- a move whose target lies in the deletion support, different from its source -/
def GoodMove (m : Move R) : Prop := m.2.2 ∈ R.D m.1 m.2.1 ∧ m.2.2 ≠ m.1

def GoodHist (h : Hist R) : Prop := ∀ m ∈ h.moves, GoodMove m

lemma mem_departure_map (g : RepSymmetry R) (m : Move R) (hm : GoodMove m) (w : V) :
    w ∈ departure R (mapMove g m) ↔ g.site.symm w ∈ departure R m := by
  obtain ⟨x, rfl⟩ := g.site.surjective w
  rw [Equiv.symm_apply_apply, mem_departure, mem_departure]
  obtain ⟨v, a, u⟩ := m
  obtain ⟨hu1, hu2⟩ := hm
  simp only [mapMove] at *
  have hD : ∀ y, g.site y ∈ R.D (g.site v) (g.opt v a) ↔ y ∈ R.D v a := by
    intro y
    rw [g.D_map]
    exact Finset.mem_map' g.site.toEmbedding
  constructor
  · rintro (h | ⟨h1, h2, h3⟩)
    · exact Or.inl (g.site.injective h)
    · refine Or.inr ⟨(hD x).1 h1, fun h => h2 (by rw [h]), ?_⟩
      have hx := (hD x).1 h1
      have := g.rank_map v a x hx u hu1 (fun h => h2 (by rw [h])) hu2
      exact this.2 h3
  · rintro (h | ⟨h1, h2, h3⟩)
    · exact Or.inl (by rw [h])
    · refine Or.inr ⟨(hD x).2 h1, fun h => h2 (g.site.injective h), ?_⟩
      have := g.rank_map v a x h1 u hu1 h2 hu2
      exact this.1 h3

lemma mem_deleted_map (g : RepSymmetry R) (ms : List (Move R)) (hms : ∀ m ∈ ms, GoodMove m)
    (w : V) :
    w ∈ deleted R (ms.map (mapMove g)) ↔ g.site.symm w ∈ deleted R ms := by
  rw [mem_deleted, mem_deleted]
  constructor
  · rintro ⟨m', hm', hw⟩
    obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hm'
    exact ⟨m, hm, (mem_departure_map g m (hms m hm) w).1 hw⟩
  · rintro ⟨m, hm, hw⟩
    exact ⟨mapMove g m, List.mem_map.2 ⟨m, hm, rfl⟩, (mem_departure_map g m (hms m hm) w).2 hw⟩

lemma endpoint_mapHist (g : RepSymmetry R) (h : Hist R) :
    (g.mapHist h).endpoint = g.site h.endpoint := by
  unfold Hist.endpoint RepSymmetry.mapHist Hist.endpointOf
  simp only [List.getLast?_map]
  cases h.moves.getLast? <;> simp

lemma mapHist_append (g : RepSymmetry R) (h : Hist R) (m : Move R) :
    g.mapHist (h.append m) = (g.mapHist h).append (mapMove g m) := by
  simp [RepSymmetry.mapHist, Hist.append, mapMove]

lemma exists_phi (g : RepSymmetry R) (v w : V) (e : w = g.site v) :
    ∃ φ : R.Opt v ≃ R.Opt w, (∀ a, R.A w (φ a) = (R.A v a).map g.site.toEmbedding) ∧
      (∀ a, R.D w (φ a) = (R.D v a).map g.site.toEmbedding) ∧ (∀ a, R.c w (φ a) = R.c v a) ∧
      ∀ a u, (⟨w, φ a, g.site u⟩ : Move R) = ⟨g.site v, g.opt v a, g.site u⟩ := by
  subst e
  exact ⟨g.opt v, g.A_map v, g.D_map v, g.c_map v, fun _ _ => rfl⟩

/-- The row of the exact update at an endpoint `v` with deleted set `B`. -/
noncomputable def rowSum (R : PosLocalDeletionRep V T) (v : V) (B : Finset V) (ν : ℝ)
    (f : ∀ a : R.Opt v, V → ℝ) : ℝ :=
  ∑ a ∈ Finset.univ.filter (fun a : R.Opt v => (↑(R.A v a) : Set V) ⊆ Set.univ \ ↑B),
    R.c v a * ν * ∏ u ∈ ((R.D v a).erase v).filter (fun u => u ∈ (Set.univ : Set V) \ ↑B),
      (1 - f a u)⁻¹

lemma exactUpdate_eq_rowSum (ν : ℝ) (x : Hist R → ℝ) (h : Hist R) :
    exactUpdate R Set.univ (fun _ => ν) x h =
      rowSum R h.endpoint (deleted R h.moves) ν
        (fun a u => x (h.append ⟨h.endpoint, a, u⟩)) := by
  unfold exactUpdate rowSum
  refine Finset.sum_congr (Finset.filter_congr (fun _ _ => Iff.rfl)) (fun a _ => ?_)
  congr 1
  refine Finset.prod_congr ?_ (fun _ _ => rfl)
  ext u
  simp

lemma rowSum_equiv (g : RepSymmetry R) (ν : ℝ) (v w : V) (e : w = g.site v)
    (φ : R.Opt v ≃ R.Opt w)
    (hA : ∀ a, R.A w (φ a) = (R.A v a).map g.site.toEmbedding)
    (hD : ∀ a, R.D w (φ a) = (R.D v a).map g.site.toEmbedding)
    (hc : ∀ a, R.c w (φ a) = R.c v a)
    (B B' : Finset V) (hB : ∀ x, g.site x ∈ B' ↔ x ∈ B)
    (f : ∀ a : R.Opt v, V → ℝ) (f' : ∀ a : R.Opt w, V → ℝ)
    (hf : ∀ a u, u ∈ (R.D v a).erase v → f' (φ a) (g.site u) = f a u) :
    rowSum R w B' ν f' = rowSum R v B ν f := by
  subst e
  have hB2 : ∀ y, y ∈ B' ↔ g.site.symm y ∈ B := by
    intro y; simpa using hB (g.site.symm y)
  unfold rowSum
  symm
  refine Finset.sum_equiv φ (fun a => ?_) (fun a ha => ?_)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hA]
    constructor
    · intro hsub y hy
      rw [Finset.mem_coe, Finset.mem_map_equiv] at hy
      have := hsub (Finset.mem_coe.2 hy)
      exact ⟨Set.mem_univ _, fun hb => this.2 ((hB2 y).1 hb)⟩
    · intro hsub x hx
      have := hsub (Finset.mem_coe.2 ((Finset.mem_map_equiv (f := g.site) (b := g.site x)).2 (by simpa using hx)))
      exact ⟨Set.mem_univ _, fun hb => this.2 ((hB x).2 hb)⟩
  · rw [hc]
    congr 1
    refine Finset.prod_equiv g.site (fun u => ?_) (fun u hu => ?_)
    · simp only [Finset.mem_filter, Finset.mem_erase, hD, Finset.mem_map_equiv, Set.mem_sdiff,
        Set.mem_univ, true_and, Finset.mem_coe, hB, Equiv.symm_apply_apply]
      simp [hB]
    · have hu' : u ∈ (R.D v a).erase v := by
        simp only [Finset.mem_filter] at hu; exact hu.1
      rw [hf a u hu']


lemma goodHist_of_exact (h : Hist R) (hh : IsExact R Set.univ h) : GoodHist h := by
  intro m hm
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hm
  obtain ⟨_, _, h3, h4⟩ := hh.2 i hi
  exact ⟨h3.1, h4⟩

lemma goodHist_append (h : Hist R) (m : Move R) (hh : GoodHist h) (hm : GoodMove m) :
    GoodHist (h.append m) := by
  intro m' hm'
  simp only [Hist.append, List.mem_append, List.mem_singleton] at hm'
  rcases hm' with hm' | rfl
  · exact hh m' hm'
  · exact hm

lemma iter_symm (g : RepSymmetry R) (ν : ℝ) :
    ∀ N : ℕ, ∀ h : Hist R, GoodHist h →
      exactIter R Set.univ (fun _ => ν) N (g.mapHist h) =
        exactIter R Set.univ (fun _ => ν) N h := by
  intro N
  induction N with
  | zero => intro h _; rfl
  | succ N ih =>
    intro h hh
    show exactUpdate R Set.univ (fun _ => ν) (exactIter R Set.univ (fun _ => ν) N) (g.mapHist h) =
      exactUpdate R Set.univ (fun _ => ν) (exactIter R Set.univ (fun _ => ν) N) h
    rw [exactUpdate_eq_rowSum, exactUpdate_eq_rowSum]
    obtain ⟨φ, hA, hD, hc, hmv⟩ := exists_phi g h.endpoint (g.mapHist h).endpoint
      (endpoint_mapHist g h)
    refine rowSum_equiv g ν h.endpoint _ (endpoint_mapHist g h) φ hA hD hc _ _ ?_ _ _ ?_
    · intro x
      have := mem_deleted_map g h.moves hh (g.site x)
      show g.site x ∈ deleted R (h.moves.map (mapMove g)) ↔ _
      simpa using this
    · intro a u hu
      rw [Finset.mem_erase] at hu
      have hgood : GoodMove (⟨h.endpoint, a, u⟩ : Move R) := ⟨hu.2, hu.1⟩
      show exactIter R Set.univ (fun _ => ν) N ((g.mapHist h).append ⟨_, φ a, g.site u⟩) = _
      rw [hmv a u]
      have := mapHist_append g h ⟨h.endpoint, a, u⟩
      simp only [mapMove] at this
      rw [← this]
      exact ih _ (goodHist_append h _ hh hgood)

end LocalLemmaHierarchy.Completeness.Dev.P34
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped ENNReal NNReal Classical

namespace LocalLemmaHierarchy.Completeness.Dev.P34

open LocalLemmaHierarchy.Completeness LocalLemmaHierarchy.Completeness.Dev.T23

variable {V T : Type} {R : PosLocalDeletionRep V T}

open Classical in
/-- finite set of the sites and supports used by the moves of `h` -/
noncomputable def usedSites (h : Hist R) : Finset V :=
  insert h.start (h.moves.toFinset.biUnion (fun m => insert m.1 (R.D m.1 m.2.1)))

lemma exact_of_univ (W : Finset V) (N : ℕ) (h : Hist R) (hh : IsExact R Set.univ h)
    (hW : usedSites h ⊆ W) : IsExact R (↑W : Set V) h := by
  classical
  have hmem : ∀ m ∈ h.moves, R.D m.1 m.2.1 ⊆ W := by
    intro m hm x hx
    refine hW (Finset.mem_insert_of_mem (Finset.mem_biUnion.2 ⟨m, List.mem_toFinset.2 hm, ?_⟩))
    exact Finset.mem_insert_of_mem hx
  refine ⟨hW (Finset.mem_insert_self _ _), fun i hi => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := hh.2 i hi
  have hm : h.moves[i] ∈ h.moves := List.getElem_mem hi
  have hD := hmem _ hm
  refine ⟨h1, fun w hw => ⟨?_, (h2 hw).2⟩, ⟨h3.1, ?_, h3.2.2⟩, h4⟩
  · exact hD (R.A_subset_D _ _ hw)
  · exact hD h3.1

lemma zf_of_lt (Z : Finset V → MvPolynomial T ℝ) (hRZ : IsRepresentationOf R Z)
    (W : Finset V) (t : ℝ) (ht : 0 < t) (htR : ENNReal.ofReal t < uniformRadius Z) :
    ∀ W' ⊆ W, 0 < negEval Z W' (fun _ => t) := by
  classical
  have h24 := (proposition_2_4 R Z hRZ W).2.2.2.2 t.toNNReal
  have hle : uniformRadius Z ≤ regionRadius Z W := iInf_le _ W
  have hzf : ZeroFreeOn Z W (fun _ => ((t.toNNReal : ℝ≥0) : ℝ)) := by
    refine h24.2 ?_
    have : ((t.toNNReal : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal t := rfl
    rw [this]
    exact lt_of_lt_of_le htR hle
  rw [Real.coe_toNNReal t ht.le] at hzf
  exact ((theorem_2_3 R Z hRZ W (fun _ => t) (fun _ => ht.le)).1.1 hzf)

lemma bound (Z : Finset V → MvPolynomial T ℝ) (hRZ : IsRepresentationOf R Z)
    (ν ν' : ℝ) (hν : 0 < ν) (hνν' : ν < ν') (hν'R : ENNReal.ofReal ν' < uniformRadius Z) :
    ∀ N : ℕ, ∀ h : Hist R, IsExact R Set.univ h → branchIter R ν N h * ν' ≤ ν := by
  classical
  intro N h hh
  have hν'0 : 0 < ν' := lt_trans hν hνν'
  set W : Finset V := (stepD R)^[N] {h.endpoint} ∪ usedSites h with hWdef
  have hWex : IsExact R (↑W : Set V) h :=
    exact_of_univ W N h hh (Finset.subset_union_right)
  have hpos := zf_of_lt Z hRZ W ν' hν'0 hν'R
  have h23 := (theorem_2_3 R Z hRZ W (fun _ => ν') (fun _ => hν'0.le)).2.2 hpos
  have hH : ∀ N' : ℕ, ∀ h' : Hist R, IsExact R (↑W : Set V) h' →
      exactIter R (↑W : Set V) (fun _ => ν') N' h' < 1 := by
    intro N' h' hh'
    refine lt_of_le_of_lt (iter_le W (fun _ => ν') (fun _ => hν'0.le) _ h23.1 N' h' hh')
      (h23.1 h' hh').2.1
  have hsc := iter_scale (↑W : Set V) ν ν' hν hνν'.le hH N h hWex
  have heq : branchIter R ν N h = exactIter R (↑W : Set V) (fun _ => ν) N h :=
    iter_univ_eq_finite (fun _ => ν) W N h Finset.subset_union_left
  rw [heq]
  have := hH N h hWex
  nlinarith [hsc.2]


section canon

variable (ν ν₀ : ℝ) (hν : 0 < ν)
  (hb : ∀ N : ℕ, ∀ h : Hist R, IsExact R Set.univ h → branchIter R ν N h < 1)

include hν hb

lemma iter_nonneg' : ∀ N : ℕ, ∀ h : Hist R, IsExact R Set.univ h → 0 ≤ branchIter R ν N h :=
  iter_nonneg_set Set.univ (fun _ => ν) (fun _ => hν.le) hb

lemma iter_mono' : ∀ N : ℕ, ∀ h : Hist R, IsExact R Set.univ h →
    branchIter R ν N h ≤ branchIter R ν (N + 1) h := by
  intro N
  induction N with
  | zero =>
    intro h hh
    exact iter_nonneg' ν hν hb 1 h hh
  | succ N ih =>
    intro h hh
    show exactUpdate R Set.univ (fun _ => ν) (exactIter R Set.univ (fun _ => ν) N) h ≤
      exactUpdate R Set.univ (fun _ => ν) (exactIter R Set.univ (fun _ => ν) (N + 1)) h
    exact upd_mono_set Set.univ (fun _ => ν) (fun _ => hν.le) _ _ h hh
      (fun h' hh' => ⟨ih h' hh', hb (N + 1) h' hh'⟩)

lemma iter_tendsto (h : Hist R) (hh : IsExact R Set.univ h) :
    Filter.Tendsto (fun N => branchIter R ν N h) Filter.atTop (nhds (canonicalBranch R ν h)) := by
  refine tendsto_atTop_ciSup (monotone_nat_of_le_succ (fun N => iter_mono' ν hν hb N h hh)) ?_
  exact ⟨1, by rintro _ ⟨N, rfl⟩; exact (hb N h hh).le⟩

lemma canon_lt (hbd : ∀ N : ℕ, ∀ h : Hist R, IsExact R Set.univ h → branchIter R ν N h * ν₀ ≤ ν)
    (hνν₀ : ν < ν₀) (h : Hist R) (hh : IsExact R Set.univ h) :
    canonicalBranch R ν h * ν₀ ≤ ν ∧ canonicalBranch R ν h < 1 := by
  have hν₀ : 0 < ν₀ := lt_trans hν hνν₀
  have h1 : canonicalBranch R ν h ≤ ν / ν₀ := by
    refine ciSup_le (fun N => ?_)
    rw [le_div_iff₀ hν₀]; exact hbd N h hh
  have h2 : ν / ν₀ < 1 := by rw [div_lt_one hν₀]; exact hνν₀
  refine ⟨?_, lt_of_le_of_lt h1 h2⟩
  rw [le_div_iff₀ hν₀] at h1; exact h1

lemma canon_fixed (hbd : ∀ N : ℕ, ∀ h : Hist R, IsExact R Set.univ h → branchIter R ν N h * ν₀ ≤ ν)
    (hνν₀ : ν < ν₀) (h : Hist R) (hh : IsExact R Set.univ h) :
    canonicalBranch R ν h = exactUpdate R Set.univ (fun _ => ν) (canonicalBranch R ν) h := by
  have hlim : Filter.Tendsto (fun N => exactUpdate R Set.univ (fun _ => ν)
      (exactIter R Set.univ (fun _ => ν) N) h) Filter.atTop
      (nhds (exactUpdate R Set.univ (fun _ => ν) (canonicalBranch R ν) h)) := by
    unfold exactUpdate
    refine tendsto_finsetSum _ (fun a ha => ?_)
    rw [Finset.mem_filter] at ha
    refine tendsto_const_nhds.mul (tendsto_finsetProd _ (fun u hu => ?_))
    have hc := child_exact_set Set.univ h hh a u ha.2 hu
    have hT := iter_tendsto ν hν hb _ hc
    have hlt := (canon_lt ν ν₀ hν hb hbd hνν₀ _ hc).2
    exact (tendsto_const_nhds.sub hT).inv₀ (by linarith)
  have hT := iter_tendsto ν hν hb h hh
  have hT' : Filter.Tendsto (fun N => exactUpdate R Set.univ (fun _ => ν)
      (exactIter R Set.univ (fun _ => ν) N) h) Filter.atTop (nhds (canonicalBranch R ν h)) :=
    (Filter.tendsto_add_atTop_iff_nat 1).2 hT
  exact tendsto_nhds_unique hT' hlim

end canon


lemma exists_gt_lt (r : ℝ≥0∞) (d : ℝ) (hd : 0 < d) (hdr : ENNReal.ofReal d < r) :
    ∃ d' : ℝ, d < d' ∧ ENNReal.ofReal d' < r := by
  obtain ⟨c, hc1, hc2⟩ := exists_between hdr
  have hne : c ≠ ⊤ := ne_top_of_lt hc2
  refine ⟨c.toReal, ?_, by rwa [ENNReal.ofReal_toReal hne]⟩
  rw [← ENNReal.ofReal_toReal hne] at hc1
  exact ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg hd.le).1 hc1)

lemma ofReal_le_div (a ν : ℝ) (r : ℝ≥0∞) (hν : 0 < ν) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hr : ENNReal.ofReal ν < r)
    (hcl : ∀ ν' : ℝ, ν < ν' → ENNReal.ofReal ν' < r → a * ν' ≤ ν) :
    ENNReal.ofReal a ≤ ENNReal.ofReal ν / r := by
  rcases ha0.eq_or_lt with rfl | ha
  · simp
  have hνa : ν < ν / a := by rw [lt_div_iff₀ ha]; nlinarith
  have hpos : 0 < ν / a := div_pos hν ha
  have hr2 : r ≤ ENNReal.ofReal (ν / a) := by
    by_contra hlt
    push Not at hlt
    obtain ⟨d', hd1, hd2⟩ := exists_gt_lt r (ν / a) hpos hlt
    have := hcl d' (lt_trans hνa hd1) hd2
    rw [div_lt_iff₀ ha] at hd1
    nlinarith
  calc ENNReal.ofReal a = ENNReal.ofReal ν / ENNReal.ofReal (ν / a) := by
        rw [← ENNReal.ofReal_div_of_pos hpos]
        congr 1
        field_simp
    _ ≤ ENNReal.ofReal ν / r := ENNReal.div_le_div_left hr2 _

end LocalLemmaHierarchy.Completeness.Dev.P34

namespace LocalLemmaHierarchy.Completeness

open Dev.P34

/-- **Proposition 3.4 (Canonical exact branch)**, printed p. 9 / PDF 11 (proof App. B.3, printed 18 /
PDF 20). For `0 < ν < R`, the branch `X^ν = sup_N X^{ν,N}` of finite-depth evaluations (B.2) is the
least exact branch satisfying `X^ν_h = Φ_{ν,h}(X^ν)` and `0 ≤ X^ν_h ≤ ν/R < 1` (3.4) at every ambient
exact history `h` (with `ν/∞ = 0`); it is invariant under symmetries preserving the representation;
and `X^ν_h ≥ c_∗ ν` if an option is available at `h`, while `X^ν_h = 0` otherwise. -/
theorem chk_proposition_3_4 {V T : Type} (R : PosLocalDeletionRep V T)
    (Z : Finset V → MvPolynomial T ℝ) (hRZ : IsRepresentationOf R Z)
    (ν : ℝ) (hν : 0 < ν) (hνR : ENNReal.ofReal ν < uniformRadius Z) :
    ENNReal.ofReal ν / uniformRadius Z < 1 ∧
    (∀ h : Hist R, IsExact R Set.univ h →
      canonicalBranch R ν h = exactUpdate R Set.univ (fun _ => ν) (canonicalBranch R ν) h ∧
      0 ≤ canonicalBranch R ν h ∧
      ENNReal.ofReal (canonicalBranch R ν h) ≤ ENNReal.ofReal ν / uniformRadius Z ∧
      canonicalBranch R ν h < 1) ∧
    (∀ Y : Hist R → ℝ,
      (∀ h : Hist R, IsExact R Set.univ h →
        Y h = exactUpdate R Set.univ (fun _ => ν) Y h ∧ 0 ≤ Y h ∧
        ENNReal.ofReal (Y h) ≤ ENNReal.ofReal ν / uniformRadius Z ∧ Y h < 1) →
      ∀ h : Hist R, IsExact R Set.univ h → canonicalBranch R ν h ≤ Y h) ∧
    (∀ g : RepSymmetry R, ∀ h : Hist R, IsExact R Set.univ h →
      canonicalBranch R ν (g.mapHist h) = canonicalBranch R ν h) ∧
    (∀ h : Hist R, IsExact R Set.univ h → HasAvailableOption R h →
      R.cstar * ν ≤ canonicalBranch R ν h) ∧
    (∀ h : Hist R, IsExact R Set.univ h → ¬ HasAvailableOption R h →
      canonicalBranch R ν h = 0) := by
  classical
  obtain ⟨ν₀, hνν₀, hν₀R⟩ := exists_gt_lt (uniformRadius Z) ν hν hνR
  have hν₀ : 0 < ν₀ := lt_trans hν hνν₀
  have hbd : ∀ N : ℕ, ∀ h : Hist R, IsExact R Set.univ h → branchIter R ν N h * ν₀ ≤ ν :=
    fun N h hh => bound Z hRZ ν ν₀ hν hνν₀ hν₀R N h hh
  have hb : ∀ N : ℕ, ∀ h : Hist R, IsExact R Set.univ h → branchIter R ν N h < 1 := by
    intro N h hh
    by_contra hlt
    push Not at hlt
    have := hbd N h hh
    nlinarith
  have hbdd : ∀ h : Hist R, IsExact R Set.univ h →
      BddAbove (Set.range fun N => branchIter R ν N h) := fun h hh =>
    ⟨1, by rintro _ ⟨N, rfl⟩; exact (hb N h hh).le⟩
  have hcn : ∀ h : Hist R, IsExact R Set.univ h → 0 ≤ canonicalBranch R ν h := by
    intro h hh
    refine le_trans ?_ (le_ciSup (hbdd h hh) 0)
    exact iter_nonneg' ν hν hb 0 h hh
  have hcl : ∀ h : Hist R, IsExact R Set.univ h → ∀ ν' : ℝ, ν < ν' →
      ENNReal.ofReal ν' < uniformRadius Z → canonicalBranch R ν h * ν' ≤ ν := by
    intro h hh ν' h1 h2
    have hp : 0 < ν' := lt_trans hν h1
    have : canonicalBranch R ν h ≤ ν / ν' := by
      refine ciSup_le (fun N => ?_)
      rw [le_div_iff₀ hp]; exact bound Z hRZ ν ν' hν h1 h2 N h hh
    rwa [le_div_iff₀ hp] at this
  have hlt1 := fun h hh => (canon_lt ν ν₀ hν hb hbd hνν₀ h hh).2
  have hcR : ∀ h : Hist R, IsExact R Set.univ h →
      ENNReal.ofReal (canonicalBranch R ν h) ≤ ENNReal.ofReal ν / uniformRadius Z :=
    fun h hh => ofReal_le_div _ ν _ hν (hcn h hh) (hlt1 h hh) hνR (hcl h hh)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ENNReal.div_lt_of_lt_mul (by rwa [one_mul])
  · intro h hh
    exact ⟨canon_fixed ν ν₀ hν hb hbd hνν₀ h hh, hcn h hh, hcR h hh, hlt1 h hh⟩
  · intro Y hY h hh
    have : ∀ N : ℕ, ∀ h : Hist R, IsExact R Set.univ h → branchIter R ν N h ≤ Y h := by
      intro N
      induction N with
      | zero => intro h hh; exact (hY h hh).2.1
      | succ N ih =>
        intro h hh
        show exactUpdate R Set.univ (fun _ => ν) (exactIter R Set.univ (fun _ => ν) N) h ≤ Y h
        refine le_trans (upd_mono_set Set.univ (fun _ => ν) (fun _ => hν.le) _ Y h hh
          (fun h' hh' => ⟨ih h' hh', (hY h' hh').2.2.2⟩)) (hY h hh).1.ge
    exact ciSup_le (fun N => this N h hh)
  · intro g h hh
    have hgood := goodHist_of_exact h hh
    unfold canonicalBranch
    exact iSup_congr (fun N => iter_symm g ν N h hgood)
  · intro h hh ⟨a, ha⟩
    have h1 : branchIter R ν 1 h ≤ canonicalBranch R ν h := le_ciSup (hbdd h hh) 1
    refine le_trans ?_ h1
    obtain ⟨c₀, hc₀, hc₀le⟩ := R.cstar_pos
    have hbdd' : BddBelow (Set.range fun p : (Σ v : V, R.Opt v) => R.c p.1 p.2) :=
      ⟨c₀, by rintro _ ⟨p, rfl⟩; exact hc₀le p.1 p.2⟩
    have hcs : R.cstar ≤ R.c h.endpoint a := ciInf_le hbdd' ⟨h.endpoint, a⟩
    show R.cstar * ν ≤ exactUpdate R Set.univ (fun _ => ν) (fun _ => 0) h
    unfold exactUpdate
    have hmem : a ∈ Finset.univ.filter (fun a : R.Opt h.endpoint =>
        (↑(R.A h.endpoint a) : Set V) ⊆ Set.univ \ ↑(deleted R h.moves)) := by
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, fun w hw => ⟨Set.mem_univ _, ?_⟩⟩
      exact fun hd => Finset.disjoint_left.1 ha hw hd
    simp only [sub_zero, inv_one, Finset.prod_const_one, mul_one]
    refine le_trans ?_ (Finset.single_le_sum (f := fun a : R.Opt h.endpoint =>
      R.c h.endpoint a * ν) (fun a' _ => mul_nonneg (R.c_pos _ _).le hν.le) hmem)
    exact mul_le_mul_of_nonneg_right hcs hν.le
  · intro h hh hno
    have hz : ∀ N : ℕ, branchIter R ν N h = 0 := by
      intro N
      cases N with
      | zero => rfl
      | succ N =>
        show exactUpdate R Set.univ (fun _ => ν) (exactIter R Set.univ (fun _ => ν) N) h = 0
        unfold exactUpdate
        rw [Finset.sum_eq_zero]
        intro a ha
        exfalso
        rw [Finset.mem_filter] at ha
        exact hno ⟨a, Finset.disjoint_left.2 (fun w hw hd => (ha.2 hw).2 hd)⟩
    unfold canonicalBranch
    simp [hz]

end LocalLemmaHierarchy.Completeness
end

theorem solution : type_of% @LocalLemmaHierarchy.Completeness.chk_proposition_3_4 := @LocalLemmaHierarchy.Completeness.chk_proposition_3_4
