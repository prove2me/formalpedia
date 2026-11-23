-- Prove2me | solution 1 for GlobalTheory.QuotInt.sb_of_quot
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:59:30.021253+00:00
-- url     : https://prove2.me/submissions/d2727ac9-8fbe-40cf-b2df-fb2d86e85854

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsMulLeftInvariantVolGL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeUnipotentHaarAndModulusStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_QuotientIntegralParabolicUnfolding

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
noncomputable section
open GlobalTheory GlobalTheory.QuotInt
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
namespace GlobalTheory.QuotInt
theorem _root_.solution (K : Subgroup G) (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G))
    (S : Finset (G ⧸ K)) (a : G ⧸ K → ℂ) (ha : ∀ q, q ∉ S → a q = 0) :
    (fun g : G => a (g : G ⧸ K)) ∈ SB G := by
  haveI := QuotientGroup.discreteTopology hKo
  refine ⟨(IsLocallyConstant.of_discrete a).comp_continuous QuotientGroup.continuous_mk, ?_⟩
  have hc : IsCompact (⋃ q ∈ S, (fun x => q.out * x) '' (K : Set G)) :=
    S.isCompact_biUnion fun q _ => hKc.image (by fun_prop)
  refine HasCompactSupport.intro hc fun g hg => ha _ fun hq => hg ?_
  simp only [Set.mem_iUnion]
  refine ⟨_, hq, ((g : G ⧸ K).out)⁻¹ * g, ?_, by simp⟩
  exact QuotientGroup.eq.1 (by simp)
end GlobalTheory.QuotInt
