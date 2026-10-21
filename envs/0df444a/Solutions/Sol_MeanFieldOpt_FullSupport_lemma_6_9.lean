-- Prove2me | solution 1 for MeanFieldOpt.FullSupport.lemma_6_9
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T03:15:30.07186+00:00
-- url     : https://prove2.me/submissions/cab4e550-08b8-491e-b670-d7e4bfe5303c

import Mathlib
import Definitions.Def_MeanFieldOpt_FullSupport_InL
import Definitions.Def_MeanFieldOpt_FullSupport_Support

set_option autoImplicit false
open MeanFieldOpt.FullSupport Set

theorem solution (ξ : Mixture) (γ : ℝ → ℝ) (hγ : InL ξ γ)
    (hrc : ∀ t ∈ Set.Ico (0 : ℝ) 1, ContinuousWithinAt γ (Set.Ici t) t) :
    ∃ A : Set (ℝ × ℝ × Bool), A.Countable ∧ (∀ α ∈ A, α.1 < α.2.1) ∧
      A.PairwiseDisjoint
        (fun α => if α.2.2 then Set.Ico α.1 α.2.1 else Set.Ioo α.1 α.2.1) ∧
      S γ = ⋃ α ∈ A, (if α.2.2 then Set.Ico α.1 α.2.1 else Set.Ioo α.1 α.2.1) := by
  classical
  set T := S γ with hT
  -- every point of `T` has a right neighbourhood inside `T`
  have hright : ∀ t ∈ T, ∃ u, t < u ∧ Set.Ico t u ⊆ T := by
    intro t ht
    obtain ⟨ht01, htpos⟩ := ht
    have h1 : ∀ᶠ y in nhdsWithin t (Set.Ici t), 0 < γ y :=
      (hrc t ht01).eventually (lt_mem_nhds htpos)
    have h2 : ∀ᶠ y in nhdsWithin t (Set.Ici t), y < 1 :=
      (eventually_lt_nhds ht01.2).filter_mono nhdsWithin_le_nhds
    have h3 : ∀ᶠ y in nhdsWithin t (Set.Ici t), 0 ≤ y :=
      eventually_nhdsWithin_of_forall (fun y hy => ht01.1.trans hy)
    obtain ⟨u, hu, hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.mp (h1.and (h2.and h3))
    exact ⟨u, hu, fun y hy => by
      obtain ⟨a, b, c⟩ := hsub hy
      exact ⟨⟨c, b⟩, a⟩⟩
  set C : ℝ → Set ℝ := fun t => ordConnectedComponent T t with hC
  have hCmem : ∀ t y, y ∈ C t ↔ Set.uIcc t y ⊆ T := fun t y => mem_ordConnectedComponent
  have hCself : ∀ t ∈ T, t ∈ C t := fun t ht => (self_mem_ordConnectedComponent).mpr ht
  have hCsub : ∀ t, C t ⊆ T := fun t => ordConnectedComponent_subset
  have hCbdd : ∀ t, BddBelow (C t) ∧ BddAbove (C t) := by
    intro t
    exact ⟨⟨0, fun y hy => (hCsub t hy).1.1⟩, ⟨1, fun y hy => (hCsub t hy).1.2.le⟩⟩
  have hbetween : ∀ t c1 c2 x, c1 ∈ C t → c2 ∈ C t → c1 ≤ x → x ≤ c2 → x ∈ C t := by
    intro t c1 c2 x h1 h2 hx1 hx2
    rw [hCmem] at h1 h2 ⊢
    rcases le_total t x with htx | htx
    · rw [Set.uIcc_of_le htx]
      have : t ≤ c2 := htx.trans hx2
      refine (Set.Icc_subset_Icc le_rfl hx2).trans ?_
      rw [Set.uIcc_of_le this] at h2
      exact h2
    · rw [Set.uIcc_of_ge htx]
      have : c1 ≤ t := hx1.trans htx
      refine (Set.Icc_subset_Icc hx1 le_rfl).trans ?_
      rw [Set.uIcc_of_ge this] at h1
      exact h1
  -- the supremum of a component is not attained
  have hsup : ∀ t ∈ T, sSup (C t) ∉ C t := by
    intro t ht hK
    have hKT := hCsub t hK
    obtain ⟨u, hu, hsub⟩ := hright _ hKT
    have htK : t ≤ sSup (C t) := le_csSup (hCbdd t).2 (hCself t ht)
    set y := (sSup (C t) + u) / 2 with hy
    have hy1 : sSup (C t) ≤ y := by rw [hy]; linarith
    have hy2 : y < u := by rw [hy]; linarith
    have hyC : y ∈ C t := by
      rw [hCmem, Set.uIcc_of_le (htK.trans hy1)]
      intro z hz
      by_cases hzK : z ≤ sSup (C t)
      · have := (hCmem t _).mp hK
        rw [Set.uIcc_of_le htK] at this
        exact this ⟨hz.1, hzK⟩
      · exact hsub ⟨(not_le.mp hzK).le, lt_of_le_of_lt hz.2 hy2⟩
    have := le_csSup (hCbdd t).2 hyC
    rw [hy] at this
    linarith
  -- structure of a component
  have hE : ∀ t ∈ T, C t = if sInf (C t) ∈ C t then Set.Ico (sInf (C t)) (sSup (C t))
      else Set.Ioo (sInf (C t)) (sSup (C t)) := by
    intro t ht
    have hne : (C t).Nonempty := ⟨t, hCself t ht⟩
    have hKnot := hsup t ht
    ext x
    split_ifs with hI
    · constructor
      · intro hx
        refine ⟨csInf_le (hCbdd t).1 hx, lt_of_le_of_ne (le_csSup (hCbdd t).2 hx) ?_⟩
        rintro rfl
        exact hKnot hx
      · rintro ⟨hx1, hx2⟩
        rcases hx1.eq_or_lt with h | h
        · rw [← h]; exact hI
        · obtain ⟨c1, hc1, hc1x⟩ := exists_lt_of_csInf_lt hne h
          obtain ⟨c2, hc2, hc2x⟩ := exists_lt_of_lt_csSup hne hx2
          exact hbetween t c1 c2 x hc1 hc2 hc1x.le hc2x.le
    · constructor
      · intro hx
        refine ⟨lt_of_le_of_ne (csInf_le (hCbdd t).1 hx) ?_,
          lt_of_le_of_ne (le_csSup (hCbdd t).2 hx) ?_⟩
        · rintro rfl
          exact hI hx
        · rintro rfl
          exact hKnot hx
      · rintro ⟨hx1, hx2⟩
        obtain ⟨c1, hc1, hc1x⟩ := exists_lt_of_csInf_lt hne hx1
        obtain ⟨c2, hc2, hc2x⟩ := exists_lt_of_lt_csSup hne hx2
        exact hbetween t c1 c2 x hc1 hc2 hc1x.le hc2x.le
  have hlt : ∀ t ∈ T, sInf (C t) < sSup (C t) := by
    intro t ht
    obtain ⟨u, hu, hsub⟩ := hright t ht
    set y := (t + u) / 2 with hy
    have hyC : y ∈ C t := by
      rw [hCmem, Set.uIcc_of_le (by rw [hy]; linarith)]
      intro z hz
      exact hsub ⟨hz.1, by rw [hy] at hz; linarith [hz.2]⟩
    have h1 := le_csSup (hCbdd t).2 hyC
    have h2 := csInf_le (hCbdd t).1 (hCself t ht)
    have : t < y := by rw [hy]; linarith
    linarith
  let f : ℝ × ℝ × Bool → Set ℝ := fun α => if α.2.2 then Set.Ico α.1 α.2.1 else Set.Ioo α.1 α.2.1
  let g : ℝ → ℝ × ℝ × Bool := fun t => (sInf (C t), sSup (C t), decide (sInf (C t) ∈ C t))
  have hfg : ∀ t ∈ T, f (g t) = C t := by
    intro t ht
    conv_rhs => rw [hE t ht]
    simp only [f, g, decide_eq_true_eq]
  have hdisj : ∀ t ∈ T, ∀ t' ∈ T, g t ≠ g t' → Disjoint (C t) (C t') := by
    intro t ht t' ht' hne
    rw [Set.disjoint_left]
    intro z hz hz'
    apply hne
    have e1 : C t = C z := ordConnectedComponent_eq ((hCmem t z).mp hz)
    have e2 : C t' = C z := ordConnectedComponent_eq ((hCmem t' z).mp hz')
    simp only [g]
    rw [e1, e2]
  refine ⟨g '' T, ?_, ?_, ?_, ?_⟩
  · apply Set.PairwiseDisjoint.countable_of_nonempty_interior (s := f)
    · rintro _ ⟨t, ht, rfl⟩ _ ⟨t', ht', rfl⟩ hne
      simp only [Function.onFun]
      rw [hfg t ht, hfg t' ht']
      exact hdisj t ht t' ht' hne
    · rintro _ ⟨t, ht, rfl⟩
      have : Set.Ioo (sInf (C t)) (sSup (C t)) ⊆ f (g t) := by
        simp only [f, g]
        split_ifs
        · exact Set.Ioo_subset_Ico_self
        · exact subset_rfl
      exact (Set.nonempty_Ioo.mpr (hlt t ht)).mono
        (isOpen_Ioo.subset_interior_iff.mpr this)
  · rintro _ ⟨t, ht, rfl⟩
    exact hlt t ht
  · rintro _ ⟨t, ht, rfl⟩ _ ⟨t', ht', rfl⟩ hne
    simp only [Function.onFun]
    show Disjoint (f (g t)) (f (g t'))
    rw [hfg t ht, hfg t' ht']
    exact hdisj t ht t' ht' hne
  · ext x
    simp only [Set.mem_iUnion, Set.mem_image]
    constructor
    · intro hx
      exact ⟨g x, ⟨x, hx, rfl⟩, by
        show x ∈ f (g x)
        rw [hfg x hx]; exact hCself x hx⟩
    · rintro ⟨_, ⟨t, ht, rfl⟩, hx⟩
      have : x ∈ f (g t) := hx
      rw [hfg t ht] at this
      exact hCsub t this
