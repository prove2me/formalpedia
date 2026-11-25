-- Prove2me | solution 1 for GlobalTheory.AnLogRes.eq_univ_of_interior_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:32:11.985426+00:00
-- url     : https://prove2.me/submissions/9c7bb1da-f7ca-4f91-9b92-ac3acd8fe00a

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffFubiniStudyRatioCompChart0
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PushAFinsumInter
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AnalyticLogResolution
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__LogResolutionProjectiveLine_09840aae280abe50
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.AnForm.M.ima_apply
attribute [local simp] ReciprocityTheory.AnForm.M.rea_apply



set_option autoImplicit false
open GlobalTheory
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions GlobalTheory.LogResInt
open GlobalTheory.AnLogRes
variable {d : ℕ} {X : Type} [TopologicalSpace X]
namespace GlobalTheory.AnLogRes
theorem _root_.solution [PreconnectedSpace X] (A : FinHolAtlas d X) {S : Set X}
    (hS : A.IsAnalyticSubset S) (h : (interior S).Nonempty) : S = Set.univ := by
  have hc : IsClosed (interior S) := by
    refine isClosed_of_closure_subset fun x hx => ?_
    obtain ⟨W, hW, hxW, r, f, hf, hSW⟩ := hS x
    obtain ⟨j, hj⟩ := A.cover x
    have ho : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' W) :=
      (A.chart j).symm.isOpen_inter_preimage hW
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 ho (A.chart j x)
      ⟨(A.chart j).map_source hj, by simpa [(A.chart j).left_inv hj] using hxW⟩
    have hN : IsOpen ((A.chart j).source ∩ A.chart j ⁻¹' Metric.ball (A.chart j x) ε) :=
      (A.chart j).isOpen_inter_preimage Metric.isOpen_ball
    have hxN : x ∈ (A.chart j).source ∩ A.chart j ⁻¹' Metric.ball (A.chart j x) ε :=
      ⟨hj, Metric.mem_ball_self hε⟩
    obtain ⟨p, hpN, hpS⟩ := mem_closure_iff.1 hx _ hN hxN
    have hz : ∀ i, Set.EqOn (f i ∘ (A.chart j).symm) 0 (Metric.ball (A.chart j x) ε) := by
      intro i
      refine ((hf i j).mono hball).eqOn_zero_of_preconnected_of_eventuallyEq_zero
        (convex_ball _ _).isPreconnected hpN.2 ?_
      have ho' : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (interior S ∩ W)) :=
        (A.chart j).symm.isOpen_inter_preimage (isOpen_interior.inter hW)
      have hpW : p ∈ W := by simpa [(A.chart j).left_inv hpN.1] using (hball hpN.2).2
      filter_upwards [ho'.mem_nhds ⟨(A.chart j).map_source hpN.1, by
        simpa [(A.chart j).left_inv hpN.1] using And.intro hpS hpW⟩] with w hw
      have : (A.chart j).symm w ∈ S ∩ W := ⟨interior_subset hw.2.1, hw.2.2⟩
      rw [hSW] at this
      exact this.2 i
    refine mem_interior.2 ⟨_, fun y hy => ?_, hN, hxN⟩
    have hyW : y ∈ W := by simpa [(A.chart j).left_inv hy.1] using (hball hy.2).2
    have : y ∈ S ∩ W := by
      rw [hSW]
      exact ⟨hyW, fun i => by simpa [(A.chart j).left_inv hy.1] using hz i hy.2⟩
    exact this.1
  exact Set.eq_univ_of_univ_subset
    ((IsClopen.eq_univ ⟨hc, isOpen_interior⟩ h).symm.subset.trans interior_subset)
end GlobalTheory.AnLogRes
