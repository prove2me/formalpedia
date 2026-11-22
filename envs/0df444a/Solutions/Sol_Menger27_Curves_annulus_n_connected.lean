-- Prove2me | solution 1 for Menger27.Curves.annulus_n_connected
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T19:57:51.301936+00:00
-- url     : https://prove2.me/submissions/d02f690f-ff5a-4422-a133-4af5024ffdc5

import Mathlib
import Definitions.Def_Menger27_Curves_Basic
import Definitions.Def_Menger27_Curves_Separation

set_option autoImplicit false

open Set Menger27.Curves

set_option linter.unusedVariables false in
theorem solution {X : Type*} [MetricSpace X]
    [CompactSpace X] [ConnectedSpace X]
    (hcurve : IsRegularCurve X) (p : X) (n : ℕ)
    (U U' : Set X) (hU : IsOpen U) (hpU : p ∈ U)
    (hU' : IsOpen U') (hpU' : p ∈ U')
    (hnest : closure U' ⊆ U)
    (hboundary : (frontier U).encard = n)
    (hmin : ∀ V : Set X, IsOpen V → p ∈ V → V ⊆ U →
      n ≤ (frontier V).encard) :
    NPointConnected (closure U \ U') (frontier U) (frontier U') n := by
  intro E hEM hEn ⟨M₁, M₂, hU12, hd, h1, h2, hA1, hB2⟩
  have hEc : IsClosed E := (Set.encard_ne_top_iff.mp (ne_top_of_lt hEn)).isClosed
  -- The neighbourhood `V = U' ∪ (U ∩ M₂)` of `p` would have all its boundary inside `E`.
  have hVo : IsOpen (U' ∪ (U ∩ M₂)) := by
    rw [isOpen_iff_forall_mem_open]
    rintro x (hx | ⟨hxU, hxM₂⟩)
    · exact ⟨U', subset_union_left, hU', hx⟩
    · have hxRE : x ∈ (closure U \ U') \ E := by
        rw [hU12]
        exact Or.inr hxM₂
      have hxc : x ∉ closure M₁ := by
        intro hxc
        have hx1 : x ∈ M₁ := by
          rw [h1]
          exact ⟨hxRE, hxc⟩
        exact disjoint_left.mp hd hx1 hxM₂
      refine ⟨U ∩ (closure M₁)ᶜ ∩ Eᶜ, ?_,
        (hU.inter isClosed_closure.isOpen_compl).inter hEc.isOpen_compl, ⟨⟨hxU, hxc⟩, hxRE.2⟩⟩
      rintro z ⟨⟨hzU, hzM₁⟩, hzE⟩
      by_cases hz' : z ∈ U'
      · exact Or.inl hz'
      · have hzR : z ∈ (closure U \ U') \ E := ⟨⟨subset_closure hzU, hz'⟩, hzE⟩
        rw [hU12] at hzR
        rcases hzR with h | h
        · exact absurd (subset_closure h) hzM₁
        · exact Or.inr ⟨hzU, h⟩
  have hVU : U' ∪ (U ∩ M₂) ⊆ U := union_subset (subset_closure.trans hnest) inter_subset_left
  have hfront : frontier (U' ∪ (U ∩ M₂)) ⊆ E := by
    rw [hVo.frontier_eq]
    rintro y ⟨hycl, hyV⟩
    by_contra hyE
    have hyU' : y ∉ U' := fun h => hyV (Or.inl h)
    have hyclU : y ∈ closure U := closure_mono hVU hycl
    have hyRE : y ∈ (closure U \ U') \ E := ⟨⟨hyclU, hyU'⟩, hyE⟩
    have hyRE' := hyRE
    rw [hU12] at hyRE'
    rcases hyRE' with hy1 | hy2
    · rw [closure_union] at hycl
      rcases hycl with hc | hc
      · have hyf : y ∈ frontier U' := by
          rw [hU'.frontier_eq]
          exact ⟨hc, hyU'⟩
        exact disjoint_left.mp hd hy1 (hB2 ⟨hyf, hyE⟩)
      · have hy2 : y ∈ M₂ := by
          rw [h2]
          exact ⟨hyRE, closure_mono inter_subset_right hc⟩
        exact disjoint_left.mp hd hy1 hy2
    · by_cases hyU : y ∈ U
      · exact hyV (Or.inr ⟨hyU, hy2⟩)
      · have hyf : y ∈ frontier U := by
          rw [hU.frontier_eq]
          exact ⟨hyclU, hyU⟩
        exact disjoint_left.mp hd (hA1 ⟨hyf, hyE⟩) hy2
  have hge := hmin _ hVo (Or.inl hpU') hVU
  exact absurd (hge.trans (Set.encard_le_encard hfront)) (not_le.mpr hEn)
