-- Prove2me | solution 1 for OAI.TriangularHilbert.finite_disjoint_selection
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T03:32:38.353991+00:00
-- url     : https://prove2.me/submissions/4b47861e-d096-4da2-a0e6-8351abd9c559

import Mathlib
import Definitions.Def_TriangularHilbert
import Definitions.Def_OAI_Analysis_TriangularHilbert_Gaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_MeshMass
import Definitions.Def_OAI_Analysis_TriangularHilbert_GaussianMoments
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedWindowScalar
import Definitions.Def_OAI_Analysis_TriangularHilbert_MatrixSupport
import Definitions.Def_OAI_Analysis_TriangularHilbert_Support
import Definitions.Def_OAI_Analysis_TriangularHilbert_WeightedGram
import Definitions.Def_OAI_Analysis_TriangularHilbert_WeightedStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_GroupedGaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatCost
import Definitions.Def_OAI_Analysis_TriangularHilbert_NormBounds
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatInsert
import Definitions.Def_OAI_Analysis_TriangularHilbert_GaussianDom
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneChart
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneDom
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatBound
import Definitions.Def_OAI_Analysis_TriangularHilbert_GramDeriv
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneIntegral
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneDissipation
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedTraceOrder
import Definitions.Def_OAI_Analysis_TriangularHilbert_MassPlane
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedConvolution
import Definitions.Def_OAI_Analysis_TriangularHilbert_RankJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_ZeroStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_StarJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_InitialAlgebra
import Definitions.Def_OAI_Analysis_TriangularHilbert_InitialPlane
import Definitions.Def_OAI_Analysis_TriangularHilbert_TotalJump

open OAI OAI.TriangularHilbert
universe uκ uX
open scoped BigOperators


theorem solution {κ : Type uκ} {X : Type uX} (s : Finset κ) (B : κ → Set X)
  (δ : κ → ℝ) (hne : ∀ a ∈ s, (B a).Nonempty) :
  ∃ u : Finset κ, u ⊆ s ∧
    (∀ a ∈ u, ∀ b ∈ u, a ≠ b → Disjoint (B a) (B b)) ∧
    ∀ a ∈ s, ∃ b ∈ u, (B a ∩ B b).Nonempty ∧ δ a ≤ δ b := by
  classical
  induction s using Finset.strongInduction with
  | H s ih =>
    rcases s.eq_empty_or_nonempty with hs | hs
    · exact ⟨∅, by simp, by simp, by simp [hs]⟩
    obtain ⟨a, ha, hmax⟩ := s.exists_max_image δ hs
    set s' := s.filter (fun b => Disjoint (B a) (B b)) with hs'
    have haB := hne a ha
    have hsub : s' ⊂ s := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _, ?_⟩
      intro heq
      have : a ∈ s' := heq ▸ ha
      rw [Finset.mem_filter] at this
      obtain ⟨x, hx⟩ := haB
      exact Set.disjoint_left.mp this.2 hx hx
    obtain ⟨u', hu's, hu'd, hu'c⟩ := ih s' hsub (fun b hb => hne b (Finset.filter_subset _ _ hb))
    have hau' : a ∉ u' := by
      intro h
      have := Finset.mem_filter.mp (hu's h)
      obtain ⟨x, hx⟩ := haB
      exact Set.disjoint_left.mp this.2 hx hx
    refine ⟨insert a u', ?_, ?_, ?_⟩
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact ha
      · exact Finset.filter_subset _ _ (hu's hx)
    · intro x hx y hy hxy
      rcases Finset.mem_insert.mp hx with hxa | hxu <;> rcases Finset.mem_insert.mp hy with hya | hyu
      · exact absurd (hxa.trans hya.symm) hxy
      · subst hxa; exact (Finset.mem_filter.mp (hu's hyu)).2
      · subst hya; exact (Finset.mem_filter.mp (hu's hxu)).2.symm
      · exact hu'd x hxu y hyu hxy
    · intro c hc
      by_cases hd : Disjoint (B a) (B c)
      · obtain ⟨b, hb, h1, h2⟩ := hu'c c (Finset.mem_filter.mpr ⟨hc, hd⟩)
        exact ⟨b, Finset.mem_insert_of_mem hb, h1, h2⟩
      · refine ⟨a, Finset.mem_insert_self _ _, ?_, hmax c hc⟩
        rw [Set.not_disjoint_iff_nonempty_inter] at hd
        rwa [Set.inter_comm]

