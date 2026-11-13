-- Prove2me | solution 1 for LocalLemmaHierarchy.Completeness.theorem_2_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T07:01:47.337403+00:00
-- url     : https://prove2.me/submissions/7bb09a5f-bab4-44cb-b600-9dfbce307fff

import Mathlib
import Definitions.Def_LocalLemmaHierarchy_Completeness_Representation
import Definitions.Def_LocalLemmaHierarchy_Completeness_Histories

section
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace LocalLemmaHierarchy.Completeness.Dev.T23

open LocalLemmaHierarchy.Completeness

/-- Telescoping of ratios along a rank order. -/
lemma tele {V K : Type} [DecidableEq V] [Field K] (F : Finset V → K) (r : V → ℕ)
    (S : Finset V) : ∀ B : Finset V, S ⊆ B → Set.InjOn r (↑S : Set V) →
      (∀ u ∈ S, F (B \ S.filter (fun w => r w < r u)) ≠ 0) →
      F (B \ S) = F B * ∏ u ∈ S, (F ((B \ S.filter (fun w => r w < r u)).erase u) /
        F (B \ S.filter (fun w => r w < r u))) := by
  refine Finset.induction_on_max_value r S ?_ ?_
  · intro B _ _ _; simp
  · intro a s ha hmax ih B hSB hinj hne
    have hs : s ⊆ B := fun x hx => hSB (Finset.mem_insert_of_mem hx)
    have hinj' : Set.InjOn r (↑s : Set V) := hinj.mono (by simp)
    have hlt : ∀ x ∈ s, r x < r a := fun x hx =>
      lt_of_le_of_ne (hmax x hx) (fun h => ha (by
        have := hinj (by simp [hx]) (by simp) h
        rw [this] at hx; exact hx))
    have hfil : ∀ u ∈ s, (insert a s).filter (fun w => r w < r u) = s.filter (fun w => r w < r u) := by
      intro u hu
      ext w
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨hw | hw, h⟩
        · subst hw; exact absurd h (not_lt.2 (hmax u hu))
        · exact ⟨hw, h⟩
      · rintro ⟨hw, h⟩; exact ⟨Or.inr hw, h⟩
    have hfa : (insert a s).filter (fun w => r w < r a) = s := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨hw | hw, h⟩
        · subst hw; exact absurd h (lt_irrefl _)
        · exact hw
      · intro hw; exact ⟨Or.inr hw, hlt w hw⟩
    have hne_s : ∀ u ∈ s, F (B \ s.filter (fun w => r w < r u)) ≠ 0 := by
      intro u hu
      have := hne u (Finset.mem_insert_of_mem hu)
      rwa [hfil u hu] at this
    have hne_a : F (B \ s) ≠ 0 := by
      have := hne a (Finset.mem_insert_self _ _)
      rwa [hfa] at this
    have ih' := ih B hs hinj' hne_s
    rw [Finset.prod_insert ha, hfa]
    have hprod : ∏ u ∈ s, (F ((B \ (insert a s).filter (fun w => r w < r u)).erase u) /
        F (B \ (insert a s).filter (fun w => r w < r u))) =
        ∏ u ∈ s, (F ((B \ s.filter (fun w => r w < r u)).erase u) /
        F (B \ s.filter (fun w => r w < r u))) :=
      Finset.prod_congr rfl (fun u hu => by rw [hfil u hu])
    rw [hprod]
    have hset : B \ insert a s = (B \ s).erase a := by
      ext w; simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]; tauto
    rw [hset, mul_left_comm, ← ih']
    field_simp


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

lemma mem_deleted_append (ms : List (Move R)) (m : Move R) (w : V) :
    w ∈ deleted R (ms ++ [m]) ↔ w ∈ deleted R ms ∨ w ∈ departure R m := by
  rw [mem_deleted, mem_deleted]
  simp only [List.mem_append, List.mem_singleton]
  constructor
  · rintro ⟨m', hm' | hm', hw⟩
    · exact Or.inl ⟨m', hm', hw⟩
    · subst hm'; exact Or.inr hw
  · rintro (⟨m', hm', hw⟩ | hw)
    · exact ⟨m', Or.inl hm', hw⟩
    · exact ⟨m, Or.inr rfl, hw⟩

lemma endpoint_append (h : Hist R) (m : Move R) : (h.append m).endpoint = m.2.2 := by
  simp [Hist.endpoint, Hist.append, Hist.endpointOf]

lemma mem_residual (U : Finset V) (h : Hist R) (w : V) :
    w ∈ residual R U h ↔ w ∈ U ∧ w ∉ deleted R h.moves := by
  classical
  simp [residual]

lemma residual_append (U : Finset V) (h : Hist R) (m : Move R) :
    residual R U (h.append m) = residual R U h \ departure R m := by
  classical
  ext w
  simp only [mem_residual, Finset.mem_sdiff]
  simp only [Hist.append, mem_deleted_append]
  tauto

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

lemma endpoint_mem_residual (U : Finset V) (h : Hist R) (hh : IsExact R (↑U : Set V) h) :
    h.endpoint ∈ residual R U h := by
  obtain ⟨s, ms⟩ := h
  induction ms using List.reverseRecOn with
  | nil =>
    simp only [Hist.endpoint, Hist.endpointOf, List.getLast?_nil, mem_residual, deleted]
    simpa using hh.1
  | append_singleton ms m ih =>
    have h2 : IsExact R (↑U : Set V) (Hist.append ⟨s, ms⟩ m) := hh
    rw [exact_append_iff] at h2
    obtain ⟨h1, hl⟩ := h2
    have hep : (Hist.append ⟨s, ms⟩ m).endpoint = m.2.2 := endpoint_append _ _
    show (Hist.append ⟨s, ms⟩ m).endpoint ∈ residual R U (Hist.append ⟨s, ms⟩ m)
    rw [hep, residual_append, Finset.mem_sdiff, mem_residual]
    obtain ⟨_, _, h3, h4⟩ := hl
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact h3.2.1
    · exact h3.2.2
    · rw [mem_departure]
      rintro (h5 | ⟨_, _, h5⟩)
      · exact h4 h5
      · exact lt_irrefl _ h5

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

/-- The telescoped deletion identity, in an arbitrary field. -/
lemma row {K : Type} [Field K] (F : Finset V → K) (κ : ∀ v, R.Opt v → K)
    (hF : ∀ (W : Finset V) (v : V), v ∈ W →
      F W = F (W.erase v) + ∑ a ∈ Finset.univ.filter (fun a : R.Opt v => R.A v a ⊆ W),
        κ v a * F (W \ R.D v a))
    (W : Finset V) (v : V) (hv : v ∈ W) (h0 : F (W.erase v) ≠ 0)
    (h1 : ∀ a : R.Opt v, R.A v a ⊆ W → ∀ u ∈ RowSet R W v a,
      F (W \ departure R ⟨v, a, u⟩) ≠ 0) :
    1 - F W / F (W.erase v) =
      - ∑ a ∈ Finset.univ.filter (fun a : R.Opt v => R.A v a ⊆ W),
        κ v a * ∏ u ∈ RowSet R W v a,
          F ((W \ departure R ⟨v, a, u⟩).erase u) / F (W \ departure R ⟨v, a, u⟩) := by
  have key : ∀ a ∈ Finset.univ.filter (fun a : R.Opt v => R.A v a ⊆ W),
      F (W \ R.D v a) / F (W.erase v) =
        ∏ u ∈ RowSet R W v a,
          F ((W \ departure R ⟨v, a, u⟩).erase u) / F (W \ departure R ⟨v, a, u⟩) := by
    intro a ha
    rw [Finset.mem_filter] at ha
    have hsub : RowSet R W v a ⊆ W.erase v := by
      intro u hu
      rw [mem_RowSet] at hu
      exact Finset.mem_erase.2 ⟨hu.2.1, hu.2.2⟩
    have hinj : Set.InjOn (R.rank v a) (↑(RowSet R W v a) : Set V) := by
      refine (R.rank_injOn v a).mono ?_
      intro u hu
      have := (mem_RowSet W v a u).1 hu
      exact ⟨this.1, this.2.1⟩
    have hB : (W.erase v) \ RowSet R W v a = W \ R.D v a := by
      ext w
      simp only [Finset.mem_sdiff, Finset.mem_erase, mem_RowSet]
      have := R.A_subset_D v a (R.self_mem_A v a)
      constructor
      · rintro ⟨⟨h2, h3⟩, h4⟩
        exact ⟨h3, fun h5 => h4 ⟨h5, h2, h3⟩⟩
      · rintro ⟨h3, h4⟩
        refine ⟨⟨?_, h3⟩, fun h5 => h4 h5.1⟩
        rintro rfl; exact h4 this
    have hC : ∀ u ∈ RowSet R W v a,
        (W.erase v) \ (RowSet R W v a).filter (fun w => R.rank v a w < R.rank v a u) =
          W \ departure R ⟨v, a, u⟩ := by
      intro u hu
      ext w
      simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_filter, mem_RowSet,
        mem_departure]
      tauto
    have := tele F (R.rank v a) (RowSet R W v a) (W.erase v) hsub hinj (by
      intro u hu
      rw [hC u hu]; exact h1 a ha.2 u hu)
    rw [hB] at this
    rw [this, mul_div_cancel_left₀ _ h0]
    refine Finset.prod_congr rfl (fun u hu => ?_)
    rw [hC u hu]
  rw [hF W v hv]
  have e1 : (F (W.erase v) + ∑ a ∈ Finset.univ.filter (fun a : R.Opt v => R.A v a ⊆ W),
        κ v a * F (W \ R.D v a)) / F (W.erase v) =
      1 + ∑ a ∈ Finset.univ.filter (fun a : R.Opt v => R.A v a ⊆ W),
        κ v a * (F (W \ R.D v a) / F (W.erase v)) := by
    rw [add_div, div_self h0, Finset.sum_div]
    congr 1
    exact Finset.sum_congr rfl (fun a _ => by ring)
  have e2 : ∑ a ∈ Finset.univ.filter (fun a : R.Opt v => R.A v a ⊆ W),
        κ v a * (F (W \ R.D v a) / F (W.erase v)) =
      ∑ a ∈ Finset.univ.filter (fun a : R.Opt v => R.A v a ⊆ W), κ v a * ∏ u ∈ RowSet R W v a,
          F ((W \ departure R ⟨v, a, u⟩).erase u) / F (W \ departure R ⟨v, a, u⟩) :=
    Finset.sum_congr rfl (fun a ha => by rw [key a ha])
  rw [e1, e2]; ring

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

lemma child_card (U : Finset V) (h : Hist R) (hh : IsExact R (↑U : Set V) h)
    (m : Move R) (hm : m.1 = h.endpoint) :
    (residual R U (h.append m)).card < (residual R U h).card := by
  rw [residual_append]
  apply Finset.card_lt_card
  refine ⟨Finset.sdiff_subset, fun hsub => ?_⟩
  have hv := endpoint_mem_residual U h hh
  have := hsub hv
  rw [Finset.mem_sdiff, mem_departure] at this
  exact this.2 (Or.inl hm.symm)

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

lemma real_deletion (Z : Finset V → MvPolynomial T ℝ) (hRZ : IsRepresentationOf R Z)
    (q : T → ℝ) (W : Finset V) (v : V) (hv : v ∈ W) :
    negEval Z W q = negEval Z (W.erase v) q +
      ∑ a ∈ Finset.univ.filter (fun a : R.Opt v => R.A v a ⊆ W),
        (-(R.c v a * q (R.label v a))) * negEval Z (W \ R.D v a) q := by
  obtain rfl : inst = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  have := congrArg (MvPolynomial.eval (fun τ => -q τ)) (hRZ.2.2 W v hv)
  simp only [map_add, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X] at this
  show MvPolynomial.eval (fun τ => -q τ) (Z W) = _
  rw [this]
  refine congrArg₂ (fun a b : ℝ => a + b) rfl ?_
  exact Finset.sum_congr rfl (fun a _ => by unfold negEval; ring)

lemma child_inv (Z : Finset V → MvPolynomial T ℝ) (U : Finset V) (p : T → ℝ) (h : Hist R)
    (a : R.Opt h.endpoint) (u : V) :
    (1 - exactRatio R Z U p (h.append ⟨h.endpoint, a, u⟩))⁻¹ =
      negEval Z ((residual R U h \ departure R ⟨h.endpoint, a, u⟩).erase u) p /
        negEval Z (residual R U h \ departure R ⟨h.endpoint, a, u⟩) p := by
  unfold exactRatio deletionRatio
  simp only [residual_append, endpoint_append]
  rw [sub_sub_cancel, inv_div]

lemma real_main (Z : Finset V → MvPolynomial T ℝ) (hRZ : IsRepresentationOf R Z)
    (U : Finset V) (p : T → ℝ) (hp : ∀ τ, 0 ≤ p τ)
    (hpos : ∀ W ⊆ U, 0 < negEval Z W p) (h : Hist R) (hh : IsExact R (↑U : Set V) h) :
    exactUpdate R (↑U : Set V) p (exactRatio R Z U p) h = exactRatio R Z U p h ∧
      0 ≤ exactRatio R Z U p h ∧ exactRatio R Z U p h < 1 := by
  have hv := endpoint_mem_residual U h hh
  have hWU : residual R U h ⊆ U := fun w hw => ((mem_residual U h w).1 hw).1
  have hrow := row (fun W => negEval Z W p) (fun v a => -(R.c v a * p (R.label v a)))
    (fun W v hv => real_deletion Z hRZ p W v hv) (residual R U h) h.endpoint hv
    (hpos ((residual R U h).erase h.endpoint) ((Finset.erase_subset _ _).trans hWU)).ne'
    (by intro a _ u _; exact (hpos _ (Finset.sdiff_subset.trans hWU)).ne')
  have hX : exactRatio R Z U p h = 1 - negEval Z (residual R U h) p /
      negEval Z ((residual R U h).erase h.endpoint) p := rfl
  have hupd : exactUpdate R (↑U : Set V) p (exactRatio R Z U p) h =
      ∑ a ∈ Finset.univ.filter (fun a : R.Opt h.endpoint => R.A h.endpoint a ⊆ residual R U h),
        R.c h.endpoint a * p (R.label h.endpoint a) *
          ∏ u ∈ RowSet R (residual R U h) h.endpoint a,
            (negEval Z ((residual R U h \ departure R ⟨h.endpoint, a, u⟩).erase u) p /
              negEval Z (residual R U h \ departure R ⟨h.endpoint, a, u⟩) p) := by
    rw [exactUpdate_eq]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    congr 1
    exact Finset.prod_congr rfl (fun u _ => child_inv Z U p h a u)
  have heq : exactUpdate R (↑U : Set V) p (exactRatio R Z U p) h = exactRatio R Z U p h := by
    rw [hupd, hX, hrow, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    ring
  refine ⟨heq, ?_, ?_⟩
  · rw [← heq, hupd]
    refine Finset.sum_nonneg (fun a _ => mul_nonneg (mul_nonneg (R.c_pos _ _).le (hp _))
      (Finset.prod_nonneg (fun u _ => ?_)))
    exact (div_pos (hpos _ ((Finset.erase_subset _ _).trans (Finset.sdiff_subset.trans hWU)))
      (hpos _ (Finset.sdiff_subset.trans hWU))).le
  · rw [hX]
    have := div_pos (hpos _ hWU) (hpos ((residual R U h).erase h.endpoint) ((Finset.erase_subset _ _).trans hWU))
    linarith

lemma upd_congr (U : Finset V) (p : T → ℝ) (x y : Hist R → ℝ) (h : Hist R)
    (hh : IsExact R (↑U : Set V) h) (hxy : ∀ h', IsExact R (↑U : Set V) h' → x h' = y h') :
    exactUpdate R (↑U : Set V) p x h = exactUpdate R (↑U : Set V) p y h := by
  rw [exactUpdate_eq, exactUpdate_eq]
  refine Finset.sum_congr rfl (fun a ha => ?_)
  rw [Finset.mem_filter] at ha
  congr 1
  refine Finset.prod_congr rfl (fun u hu => ?_)
  rw [hxy _ (child_exact U h hh a u ha.2 hu)]

lemma iter_eq (Z : Finset V → MvPolynomial T ℝ) (hRZ : IsRepresentationOf R Z)
    (U : Finset V) (p : T → ℝ) (hp : ∀ τ, 0 ≤ p τ)
    (hpos : ∀ W ⊆ U, 0 < negEval Z W p) :
    ∀ N : ℕ, ∀ h : Hist R, IsExact R (↑U : Set V) h → (residual R U h).card ≤ N →
      exactIter R (↑U : Set V) p N h = exactRatio R Z U p h := by
  intro N
  induction N with
  | zero =>
    intro h hh hc
    have := Finset.card_pos.2 ⟨_, endpoint_mem_residual U h hh⟩
    omega
  | succ N ih =>
    intro h hh hc
    show exactUpdate R (↑U : Set V) p (exactIter R (↑U : Set V) p N) h = _
    rw [← (real_main Z hRZ U p hp hpos h hh).1, exactUpdate_eq, exactUpdate_eq]
    refine Finset.sum_congr rfl (fun a ha => ?_)
    rw [Finset.mem_filter] at ha
    congr 1
    refine Finset.prod_congr rfl (fun u hu => ?_)
    rw [ih _ (child_exact U h hh a u ha.2 hu)]
    have := child_card U h hh ⟨h.endpoint, a, u⟩ rfl
    omega

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

namespace LocalLemmaHierarchy.Completeness.Dev.T23

open LocalLemmaHierarchy.Completeness

section complexpart

variable {V T : Type} [inst : DecidableEq V] {R : PosLocalDeletionRep V T}

lemma complex_deletion (Z : Finset V → MvPolynomial T ℝ) (hRZ : IsRepresentationOf R Z)
    (z : T → ℂ) (W : Finset V) (v : V) (hv : v ∈ W) :
    MvPolynomial.aeval z (Z W) = MvPolynomial.aeval z (Z (W.erase v)) +
      ∑ a ∈ Finset.univ.filter (fun a : R.Opt v => R.A v a ⊆ W),
        (algebraMap ℝ ℂ (R.c v a) * z (R.label v a)) *
          MvPolynomial.aeval z (Z (W \ R.D v a)) := by
  obtain rfl : inst = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  have := congrArg (MvPolynomial.aeval z) (hRZ.2.2 W v hv)
  simp only [map_add, map_sum, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X] at this
  rw [this]

lemma complex_main (Z : Finset V → MvPolynomial T ℝ) (hRZ : IsRepresentationOf R Z)
    (U : Finset V) (p : T → ℝ) (hp : ∀ τ, 0 ≤ p τ) (x : Hist R → ℝ)
    (hx : IsExactSupersolution R (↑U : Set V) p x) (z : T → ℂ) (hz : ∀ τ, ‖z τ‖ ≤ p τ) :
    ∀ n : ℕ, ∀ W : Finset V, W.card = n → W ⊆ U →
      MvPolynomial.aeval z (Z W) ≠ 0 ∧
      ∀ h : Hist R, IsExact R (↑U : Set V) h → h.endpoint ∈ W → W ⊆ residual R U h →
        ‖1 - MvPolynomial.aeval z (Z W) / MvPolynomial.aeval z (Z (W.erase h.endpoint))‖ ≤ x h := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro W hWn hWU
  have hbound : ∀ h : Hist R, IsExact R (↑U : Set V) h → h.endpoint ∈ W → W ⊆ residual R U h →
        ‖1 - MvPolynomial.aeval z (Z W) / MvPolynomial.aeval z (Z (W.erase h.endpoint))‖ ≤ x h := by
    intro h hh hvW hWh
    have h0 : MvPolynomial.aeval z (Z (W.erase h.endpoint)) ≠ 0 :=
      (ih _ (by rw [← hWn]; exact Finset.card_erase_lt_of_mem hvW) _ rfl
        ((Finset.erase_subset _ _).trans hWU)).1
    have hsubW : ∀ a : R.Opt h.endpoint, ∀ u ∈ RowSet R W h.endpoint a,
        u ∈ RowSet R (residual R U h) h.endpoint a := by
      intro a u hu
      rw [mem_RowSet] at hu ⊢
      exact ⟨hu.1, hu.2.1, hWh hu.2.2⟩
    have hrow := row (fun W => MvPolynomial.aeval z (Z W))
      (fun v a => algebraMap ℝ ℂ (R.c v a) * z (R.label v a))
      (fun W v hv => complex_deletion Z hRZ z W v hv) W h.endpoint hvW h0
      (by
        intro a _ u hu
        have hu' := (mem_RowSet W h.endpoint a u).1 hu
        have hlt : (W \ departure R ⟨h.endpoint, a, u⟩).card < n := by
          rw [← hWn]
          apply Finset.card_lt_card
          refine ⟨Finset.sdiff_subset, fun hsub => ?_⟩
          have := hsub hvW
          rw [Finset.mem_sdiff, mem_departure] at this
          exact this.2 (Or.inl rfl)
        exact (ih _ hlt _ rfl (Finset.sdiff_subset.trans hWU)).1)
    -- norm bound of the ratio factor
    have hratio : ∀ a : R.Opt h.endpoint, R.A h.endpoint a ⊆ W →
        ∀ u ∈ RowSet R W h.endpoint a,
        ‖MvPolynomial.aeval z (Z ((W \ departure R ⟨h.endpoint, a, u⟩).erase u)) /
          MvPolynomial.aeval z (Z (W \ departure R ⟨h.endpoint, a, u⟩))‖ ≤
          (1 - x (h.append ⟨h.endpoint, a, u⟩))⁻¹ := by
      intro a hA u hu
      have hA' : R.A h.endpoint a ⊆ residual R U h := hA.trans hWh
      have hu' := hsubW a u hu
      have hch := child_exact U h hh a u hA' hu'
      have hu'' := (mem_RowSet W h.endpoint a u).1 hu
      have hlt : (W \ departure R ⟨h.endpoint, a, u⟩).card < n := by
        rw [← hWn]
        apply Finset.card_lt_card
        refine ⟨Finset.sdiff_subset, fun hsub => ?_⟩
        have := hsub hvW
        rw [Finset.mem_sdiff, mem_departure] at this
        exact this.2 (Or.inl rfl)
      have huW : u ∈ W \ departure R ⟨h.endpoint, a, u⟩ := by
        rw [Finset.mem_sdiff, mem_departure]
        refine ⟨hu''.2.2, ?_⟩
        rintro (h5 | ⟨_, _, h5⟩)
        · exact hu''.2.1 h5
        · exact lt_irrefl _ h5
      have hsub : W \ departure R ⟨h.endpoint, a, u⟩ ⊆
          residual R U (h.append ⟨h.endpoint, a, u⟩) := by
        rw [residual_append]
        exact Finset.sdiff_subset_sdiff hWh (le_refl _)
      have hb := (ih _ hlt _ rfl (Finset.sdiff_subset.trans hWU)).2
        (h.append ⟨h.endpoint, a, u⟩) hch (by rw [endpoint_append]; exact huW) hsub
      rw [endpoint_append] at hb
      have hxlt := (hx _ hch).2.1
      set A := MvPolynomial.aeval z (Z (W \ departure R ⟨h.endpoint, a, u⟩))
      set B := MvPolynomial.aeval z (Z ((W \ departure R ⟨h.endpoint, a, u⟩).erase u))
      have hA0 : A ≠ 0 := (ih _ hlt _ rfl (Finset.sdiff_subset.trans hWU)).1
      have hB0 : B ≠ 0 := (ih _ (lt_of_le_of_lt (Finset.card_le_card (Finset.erase_subset _ _)) hlt)
        _ rfl ((Finset.erase_subset _ _).trans (Finset.sdiff_subset.trans hWU))).1
      have h1 : 1 - x (h.append ⟨h.endpoint, a, u⟩) ≤ ‖A / B‖ := by
        have := norm_sub_norm_le (1 : ℂ) (1 - A / B)
        simp only [sub_sub_cancel, norm_one] at this
        linarith
      rw [norm_div B A]
      have e : ‖B‖ / ‖A‖ = (‖A / B‖)⁻¹ := by rw [norm_div, inv_div]
      rw [e]
      exact inv_anti₀ (by linarith) h1
    -- the chain of inequalities
    have hxch : ∀ a : R.Opt h.endpoint, R.A h.endpoint a ⊆ residual R U h →
        ∀ u ∈ RowSet R (residual R U h) h.endpoint a,
        0 ≤ x (h.append ⟨h.endpoint, a, u⟩) ∧ x (h.append ⟨h.endpoint, a, u⟩) < 1 := by
      intro a hA u hu
      have := hx _ (child_exact U h hh a u hA hu)
      exact ⟨this.1, this.2.1⟩
    have hterm_nonneg : ∀ a : R.Opt h.endpoint, R.A h.endpoint a ⊆ residual R U h →
        0 ≤ R.c h.endpoint a * p (R.label h.endpoint a) *
          ∏ u ∈ RowSet R (residual R U h) h.endpoint a,
            (1 - x (h.append ⟨h.endpoint, a, u⟩))⁻¹ := by
      intro a hA
      refine mul_nonneg (mul_nonneg (R.c_pos _ _).le (hp _)) (Finset.prod_nonneg (fun u hu => ?_))
      have := hxch a hA u hu
      exact (inv_pos.2 (by linarith [this.1, this.2])).le
    rw [hrow, norm_neg]
    calc ‖∑ a ∈ Finset.univ.filter (fun a : R.Opt h.endpoint => R.A h.endpoint a ⊆ W),
          (algebraMap ℝ ℂ (R.c h.endpoint a) * z (R.label h.endpoint a)) *
          ∏ u ∈ RowSet R W h.endpoint a,
            MvPolynomial.aeval z (Z ((W \ departure R ⟨h.endpoint, a, u⟩).erase u)) /
              MvPolynomial.aeval z (Z (W \ departure R ⟨h.endpoint, a, u⟩))‖
        ≤ ∑ a ∈ Finset.univ.filter (fun a : R.Opt h.endpoint => R.A h.endpoint a ⊆ W),
            R.c h.endpoint a * p (R.label h.endpoint a) *
              ∏ u ∈ RowSet R W h.endpoint a, (1 - x (h.append ⟨h.endpoint, a, u⟩))⁻¹ := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun a ha => ?_))
          rw [Finset.mem_filter] at ha
          rw [norm_mul, norm_mul, norm_prod, norm_algebraMap', Real.norm_of_nonneg (R.c_pos _ _).le]
          exact mul_le_mul (mul_le_mul_of_nonneg_left (hz _) (R.c_pos _ _).le)
            (Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun u hu => hratio a ha.2 u hu))
            (Finset.prod_nonneg fun _ _ => norm_nonneg _)
            (mul_nonneg (R.c_pos _ _).le (hp _))
      _ ≤ ∑ a ∈ Finset.univ.filter (fun a : R.Opt h.endpoint => R.A h.endpoint a ⊆ W),
            R.c h.endpoint a * p (R.label h.endpoint a) *
              ∏ u ∈ RowSet R (residual R U h) h.endpoint a,
                (1 - x (h.append ⟨h.endpoint, a, u⟩))⁻¹ := by
          refine Finset.sum_le_sum (fun a ha => ?_)
          rw [Finset.mem_filter] at ha
          have hA' : R.A h.endpoint a ⊆ residual R U h := ha.2.trans hWh
          refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (R.c_pos _ _).le (hp _))
          refine Finset.prod_le_prod_of_subset_of_one_le (fun u hu => hsubW a u hu) ?_ ?_
          · intro u hu
            have := hxch a hA' u (hsubW a u hu)
            exact (inv_pos.2 (by linarith [this.1, this.2])).le
          · intro u hu _
            have := hxch a hA' u hu
            exact (one_le_inv₀ (by linarith [this.1, this.2])).2 (by linarith [this.1, this.2])
      _ ≤ ∑ a ∈ Finset.univ.filter (fun a : R.Opt h.endpoint => R.A h.endpoint a ⊆ residual R U h),
            R.c h.endpoint a * p (R.label h.endpoint a) *
              ∏ u ∈ RowSet R (residual R U h) h.endpoint a,
                (1 - x (h.append ⟨h.endpoint, a, u⟩))⁻¹ := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun a ha _ => ?_)
          · intro a ha
            rw [Finset.mem_filter] at ha ⊢
            exact ⟨ha.1, ha.2.trans hWh⟩
          · rw [Finset.mem_filter] at ha
            exact hterm_nonneg a ha.2
      _ = exactUpdate R (↑U : Set V) p x h := (exactUpdate_eq U p x h).symm
      _ ≤ x h := (hx h hh).2.2
  refine ⟨?_, hbound⟩
  rcases W.eq_empty_or_nonempty with rfl | ⟨v, hv⟩
  · simp [map_one, (hRZ.1)]
  · intro h0
    have hex : IsExact R (↑U : Set V) ⟨v, []⟩ := ⟨by exact_mod_cast hWU hv, by simp⟩
    have hres : residual R U (⟨v, []⟩ : Hist R) = U := by
      ext w; rw [mem_residual]; simp [deleted]
    have hb := hbound ⟨v, []⟩ hex (by simpa [Hist.endpoint, Hist.endpointOf] using hv)
      (by rw [hres]; exact hWU)
    have hlt := (hx _ hex).2.1
    simp only [h0, zero_div, sub_zero, norm_one] at hb
    linarith

end complexpart

end LocalLemmaHierarchy.Completeness.Dev.T23
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace LocalLemmaHierarchy.Completeness.Dev.T23

open LocalLemmaHierarchy.Completeness

section firstzero

variable {V T : Type} [inst : DecidableEq V] {R : PosLocalDeletionRep V T}

lemma real_deletion' (Z : Finset V → MvPolynomial T ℝ) (hRZ : IsRepresentationOf R Z)
    (q : T → ℝ) (W : Finset V) (v : V) (hv : v ∈ W) :
    negEval Z W q = negEval Z (W.erase v) q +
      ∑ a ∈ Finset.univ.filter (fun a : R.Opt v => R.A v a ⊆ W),
        (-(R.c v a * q (R.label v a))) * negEval Z (W \ R.D v a) q := by
  obtain rfl : inst = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  have := congrArg (MvPolynomial.eval (fun τ => -q τ)) (hRZ.2.2 W v hv)
  simp only [map_add, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X] at this
  show MvPolynomial.eval (fun τ => -q τ) (Z W) = _
  rw [this]
  refine congrArg₂ (fun a b : ℝ => a + b) rfl ?_
  exact Finset.sum_congr rfl (fun a _ => by unfold negEval; ring)

/-- At a point `q ≥ 0` where all `P_S(q)`, `S ⊆ U`, are nonnegative, deleting a site does not
decrease. -/
lemma le_erase (Z : Finset V → MvPolynomial T ℝ) (hRZ : IsRepresentationOf R Z)
    (U : Finset V) (q : T → ℝ) (hq : ∀ τ, 0 ≤ q τ) (hnn : ∀ S ⊆ U, 0 ≤ negEval Z S q)
    (S : Finset V) (hS : S ⊆ U) (v : V) (hv : v ∈ S) :
    negEval Z S q ≤ negEval Z (S.erase v) q := by
  rw [real_deletion' Z hRZ q S v hv]
  have : ∑ a ∈ Finset.univ.filter (fun a : R.Opt v => R.A v a ⊆ S),
      (-(R.c v a * q (R.label v a))) * negEval Z (S \ R.D v a) q ≤ 0 := by
    refine Finset.sum_nonpos (fun a _ => ?_)
    have := mul_nonneg (mul_nonneg (R.c_pos v a).le (hq (R.label v a))) (hnn (S \ R.D v a) (Finset.sdiff_subset.trans hS))
    nlinarith
  linarith

lemma le_of_subset (Z : Finset V → MvPolynomial T ℝ) (hRZ : IsRepresentationOf R Z)
    (U : Finset V) (q : T → ℝ) (hq : ∀ τ, 0 ≤ q τ) (hnn : ∀ S ⊆ U, 0 ≤ negEval Z S q)
    (W : Finset V) : ∀ n : ℕ, ∀ S : Finset V, S ⊆ U → W ⊆ S → (S \ W).card = n →
      negEval Z S q ≤ negEval Z W q := by
  intro n
  induction n with
  | zero =>
    intro S _ hWS hc
    have : S = W := by
      have := Finset.card_eq_zero.1 hc
      exact Finset.Subset.antisymm (Finset.sdiff_eq_empty_iff_subset.1 this) hWS
    rw [this]
  | succ n ih =>
    intro S hSU hWS hc
    obtain ⟨v, hv⟩ : (S \ W).Nonempty := Finset.card_pos.1 (by omega)
    rw [Finset.mem_sdiff] at hv
    refine (le_erase Z hRZ U q hq hnn S hSU v hv.1).trans ?_
    refine ih (S.erase v) ((Finset.erase_subset _ _).trans hSU)
      (fun w hw => Finset.mem_erase.2 ⟨fun h => hv.2 (h ▸ hw), hWS hw⟩) ?_
    have : (S.erase v) \ W = (S \ W).erase v := by
      ext w; simp only [Finset.mem_sdiff, Finset.mem_erase]; tauto
    rw [this, Finset.card_erase_of_mem (by rw [Finset.mem_sdiff]; exact hv)]
    omega

lemma pos_of_zeroFree (Z : Finset V → MvPolynomial T ℝ) (hRZ : IsRepresentationOf R Z)
    (U : Finset V) (p : T → ℝ) (hp : ∀ τ, 0 ≤ p τ) (hz : ZeroFreeOn Z U p) :
    ∀ W ⊆ U, 0 < negEval Z W p := by
  by_contra hcon
  push Not at hcon
  obtain ⟨W, hWU, hW⟩ := hcon
  have hne : U.powerset.Nonempty := ⟨∅, Finset.empty_mem_powerset _⟩
  let g : ℝ → ℝ := fun s => U.powerset.inf' hne (fun S => negEval Z S (fun τ => s * p τ))
  have hc : ∀ S : Finset V, Continuous (fun s : ℝ => negEval Z S (fun τ => s * p τ)) := by
    intro S
    unfold negEval
    exact (MvPolynomial.continuous_eval (Z S)).comp
      (continuous_pi (fun τ => (continuous_id.mul continuous_const).neg))
  have hcont : Continuous g := by
    refine continuous_iff_continuousAt.2 (fun s => ?_)
    exact ContinuousAt.finset_inf'_apply (f := fun S s => negEval Z S (fun τ => s * p τ)) hne
      (fun S _ => (hc S).continuousAt)
  have hg0 : g 0 = 1 := by
    have : ∀ S ∈ U.powerset, negEval Z S (fun τ => 0 * p τ) = 1 := by
      intro S _
      have h1 := hRZ.2.1 S
      show MvPolynomial.eval (fun τ => -(0 * p τ)) (Z S) = 1
      rw [show (fun τ : T => -(0 * p τ)) = 0 by funext τ; simp]
      exact h1
    simp only [g]
    rw [Finset.inf'_congr hne rfl this]
    simp
  have hg1 : g 1 ≤ 0 := by
    refine (Finset.inf'_le _ (Finset.mem_powerset.2 hWU)).trans ?_
    have : negEval Z W (fun τ => 1 * p τ) = negEval Z W p := by simp
    rw [this]; exact hW
  obtain ⟨s, hs, hgs⟩ := intermediate_value_Icc' (zero_le_one' ℝ) hcont.continuousOn
    (show (0 : ℝ) ∈ Set.Icc (g 1) (g 0) from ⟨hg1, by rw [hg0]; exact zero_le_one⟩)
  set q : T → ℝ := fun τ => s * p τ with hqdef
  have hq : ∀ τ, 0 ≤ q τ := fun τ => mul_nonneg hs.1 (hp τ)
  have hnn : ∀ S ⊆ U, 0 ≤ negEval Z S q := by
    intro S hS
    exact (Finset.le_inf'_iff hne _).1 (le_of_eq hgs.symm) S (Finset.mem_powerset.2 hS)
  obtain ⟨S0, hS0, hS0eq⟩ := Finset.exists_mem_eq_inf' hne (fun S => negEval Z S q)
  have hP0 : negEval Z S0 q = 0 := by rw [← hS0eq]; exact hgs
  have hUle := le_of_subset Z hRZ U q hq hnn S0 _ U (le_refl _) (Finset.mem_powerset.1 hS0) rfl
  have hPU : negEval Z U q = 0 := le_antisymm (hP0 ▸ hUle) (hnn U (le_refl _))
  have hzU := hz (algebraMap ℝ ℂ ∘ (fun τ => -q τ)) (by
    intro τ
    simp only [Function.comp, norm_algebraMap']
    rw [norm_neg, Real.norm_of_nonneg (hq τ)]
    exact mul_le_of_le_one_left (hp τ) hs.2)
  apply hzU
  rw [MvPolynomial.aeval_algebraMap_apply]
  have : MvPolynomial.aeval (fun τ => -q τ) (Z U) = negEval Z U q := rfl
  rw [this, hPU, map_zero]

end firstzero

end LocalLemmaHierarchy.Completeness.Dev.T23
end

section
set_option autoImplicit false

open scoped ENNReal NNReal

namespace LocalLemmaHierarchy.Completeness

open Dev.T23 in
theorem chk_theorem_2_3 {V T : Type} [DecidableEq V] (R : PosLocalDeletionRep V T)
    (Z : Finset V → MvPolynomial T ℝ) (hRZ : IsRepresentationOf R Z)
    (U : Finset V) (p : T → ℝ) (hp : ∀ τ, 0 ≤ p τ) :
    (ZeroFreeOn Z U p ↔ ∀ W ⊆ U, 0 < negEval Z W p) ∧
    ((∀ W ⊆ U, 0 < negEval Z W p) ↔ ∃ x : Hist R → ℝ, IsExactSupersolution R (↑U) p x) ∧
    ((∀ W ⊆ U, 0 < negEval Z W p) →
      IsExactSupersolution R (↑U) p (exactIter R (↑U) p U.card) ∧
      (∀ x : Hist R → ℝ, IsExactSupersolution R (↑U) p x →
        ∀ h : Hist R, IsExact R (↑U) h → exactIter R (↑U) p U.card h ≤ x h) ∧
      (∀ h : Hist R, IsExact R (↑U) h →
        exactUpdate R (↑U) p (exactIter R (↑U) p U.card) h = exactIter R (↑U) p U.card h ∧
        exactIter R (↑U) p U.card h = exactRatio R Z U p h ∧
        0 ≤ exactRatio R Z U p h ∧ exactRatio R Z U p h < 1)) := by
  have hsuper : (∀ W ⊆ U, 0 < negEval Z W p) →
      IsExactSupersolution R (↑U : Set V) p (exactRatio R Z U p) := by
    intro hpos h hh
    have := real_main Z hRZ U p hp hpos h hh
    exact ⟨this.2.1, this.2.2, this.1.le⟩
  have hiter : (∀ W ⊆ U, 0 < negEval Z W p) → ∀ h : Hist R, IsExact R (↑U : Set V) h →
      exactIter R (↑U : Set V) p U.card h = exactRatio R Z U p h := by
    intro hpos h hh
    refine iter_eq Z hRZ U p hp hpos U.card h hh (Finset.card_le_card ?_)
    exact fun w hw => ((mem_residual U h w).1 hw).1
  have hZF : (∃ x : Hist R → ℝ, IsExactSupersolution R (↑U : Set V) p x) → ZeroFreeOn Z U p := by
    rintro ⟨x, hx⟩ z hz
    exact (complex_main Z hRZ U p hp x hx z hz U.card U rfl (le_refl _)).1
  refine ⟨⟨pos_of_zeroFree Z hRZ U p hp, fun hpos => hZF ⟨_, hsuper hpos⟩⟩,
    ⟨fun hpos => ⟨_, hsuper hpos⟩, fun hx => pos_of_zeroFree Z hRZ U p hp (hZF hx)⟩, ?_⟩
  intro hpos
  have hupd : ∀ h : Hist R, IsExact R (↑U : Set V) h →
      exactUpdate R (↑U : Set V) p (exactIter R (↑U : Set V) p U.card) h =
        exactRatio R Z U p h := fun h hh =>
    (upd_congr U p _ _ h hh (fun h' hh' => hiter hpos h' hh')).trans
      (real_main Z hRZ U p hp hpos h hh).1
  refine ⟨?_, ?_, ?_⟩
  · intro h hh
    have := real_main Z hRZ U p hp hpos h hh
    rw [hiter hpos h hh]
    exact ⟨this.2.1, this.2.2, by rw [hupd h hh]⟩
  · intro x hx h hh
    exact iter_le U p hp x hx U.card h hh
  · intro h hh
    have := real_main Z hRZ U p hp hpos h hh
    rw [hiter hpos h hh]
    exact ⟨by rw [hupd h hh], rfl, this.2.1, this.2.2⟩

end LocalLemmaHierarchy.Completeness
end

theorem solution : type_of% @LocalLemmaHierarchy.Completeness.chk_theorem_2_3 := @LocalLemmaHierarchy.Completeness.chk_theorem_2_3
