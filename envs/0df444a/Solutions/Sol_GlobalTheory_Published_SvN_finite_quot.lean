-- Prove2me | solution 1 for GlobalTheory.Published.SvN.finite_quot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:39:59.724639+00:00
-- url     : https://prove2.me/submissions/4a542e85-60ae-4bff-84ad-7c0dff80a117

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_EqOneOfPowClose
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_GlobalTheta_PlaneFormNondegenerate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
open GlobalTheory GlobalTheory.Published
open GlobalTheory.Published.SvN
namespace GlobalTheory.Published.SvN
theorem _root_.solution {W : Type} [AddCommGroup W] [TopologicalSpace W] [IsTopologicalAddGroup W] (A U : AddSubgroup W)
    (hU : (U : Set W) ∈ 𝓝 0) {K : Set W} (hK : IsCompact K) (hA : (A : Set W) ⊆ K) : Finite (A ⧸ U.addSubgroupOf A) := by
  have := QuotientAddGroup.discreteTopology (U.isOpen_of_mem_nhds hU)
  have hfin : ((QuotientAddGroup.mk : W → W ⧸ U) '' K).Finite := (hK.image QuotientAddGroup.continuous_mk).finite_of_discrete
  refine Set.finite_univ_iff.1 (Set.Finite.of_finite_image (f := fun q : A ⧸ U.addSubgroupOf A => (q.out.1 : W ⧸ U))
    (hfin.subset ?_) fun p _ q _ hpq => ?_)
  · rintro _ ⟨q, -, rfl⟩
    exact ⟨_, hA q.out.2, rfl⟩
  · rw [← p.out_eq, ← q.out_eq]
    have := QuotientAddGroup.eq.1 hpq
    exact QuotientAddGroup.eq.2 this
end GlobalTheory.Published.SvN
