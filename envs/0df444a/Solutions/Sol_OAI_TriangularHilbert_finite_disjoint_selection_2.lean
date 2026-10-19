-- Prove2me | solution 2 for OAI.TriangularHilbert.finite_disjoint_selection
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T04:29:36.213062+00:00
-- url     : https://prove2.me/submissions/39bb26c1-ac63-4c12-acb8-92b9b8cb980f

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/FiniteVitali.lean:L11-L48
-- (upload_full_project.md Phase 4): solution for node OAI.TriangularHilbert.finite_disjoint_selection. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
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

-- ---- from OAI.Analysis.TriangularHilbert.FiniteVitali ----
namespace OAI

universe uκ uX

section
namespace TriangularHilbert
open scoped BigOperators

lemma finite_disjoint_selection {κ : Type uκ} {X : Type uX} (s : Finset κ) (B : κ → Set X)
  (δ : κ → ℝ) (hne : ∀ a ∈ s, (B a).Nonempty) :
  ∃ u : Finset κ, u ⊆ s ∧
    (∀ a ∈ u, ∀ b ∈ u, a ≠ b → Disjoint (B a) (B b)) ∧
    ∀ a ∈ s, ∃ b ∈ u, (B a ∩ B b).Nonempty ∧ δ a ≤ δ b := by
  classical
  revert hne
  refine Finset.strongInductionOn s (fun s ih hne => ?_)
  by_cases hs : s.Nonempty
  · obtain ⟨b,hb,hmax⟩ := s.exists_max_image δ hs
    let t := s.filter (fun a => Disjoint (B a) (B b))
    have hts : t ⊆ s := Finset.filter_subset _ _
    have hbt : b ∉ t := by
      simp only [t,Finset.mem_filter,not_and]
      intro _ hd
      obtain ⟨x,hx⟩ := hne b hb
      exact Set.disjoint_left.mp hd hx hx
    have htss : t ⊂ s := Finset.ssubset_iff_subset_ne.mpr ⟨hts,by
      intro he; exact hbt (he.symm ▸ hb)⟩
    obtain ⟨u,hu,hdis,hcover⟩ := ih t htss (fun a ha => hne a (hts ha))
    refine ⟨insert b u,Finset.insert_subset hb (hu.trans hts),?_,?_⟩
    · intro a ha c hc hac
      rcases Finset.mem_insert.mp ha with hab | hau
      · subst a
        rcases Finset.mem_insert.mp hc with hcb | hcu
        · exact (hac hcb.symm).elim
        · exact (Finset.mem_filter.mp (hu hcu)).2.symm
      · rcases Finset.mem_insert.mp hc with hcb | hcu
        · subst c
          exact (Finset.mem_filter.mp (hu hau)).2
        · exact hdis a hau c hcu hac
    · intro a ha
      by_cases hab : Disjoint (B a) (B b)
      · obtain ⟨c,hc,hac,hδ⟩ := hcover a (Finset.mem_filter.mpr ⟨ha,hab⟩)
        exact ⟨c,Finset.mem_insert_of_mem hc,hac,hδ⟩
      · exact ⟨b,Finset.mem_insert_self _ _,Set.not_disjoint_iff_nonempty_inter.mp hab,hmax a ha⟩
  · refine ⟨∅,Finset.empty_subset _,by simp,?_⟩
    simp [Finset.not_nonempty_iff_eq_empty.mp hs]

end TriangularHilbert
end

end OAI

-- ---- platform node ----
open OAI OAI.TriangularHilbert
open scoped BigOperators


theorem solution.{uκ,uX} : type_of% @_root_.OAI.TriangularHilbert.finite_disjoint_selection.{uκ,uX} := @_root_.OAI.TriangularHilbert.finite_disjoint_selection.{uκ,uX}
