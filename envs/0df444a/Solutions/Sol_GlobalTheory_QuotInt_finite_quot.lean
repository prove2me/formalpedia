-- Prove2me | solution 1 for GlobalTheory.QuotInt.finite_quot
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:59:29.644451+00:00
-- url     : https://prove2.me/submissions/3a35fb3e-3246-4a70-99a1-98cce25eeee4

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
theorem _root_.solution (K : Subgroup G) (hKo : IsOpen (K : Set G)) {C : Set G} (hC : IsCompact C) :
    ∃ S : Finset (G ⧸ K), ∀ g ∈ C, (g : G ⧸ K) ∈ S := by
  haveI := QuotientGroup.discreteTopology hKo
  have := (hC.image (QuotientGroup.continuous_mk (N := K))).finite_of_discrete
  exact ⟨this.toFinset, fun g hg => by simpa using ⟨g, hg, rfl⟩⟩
end GlobalTheory.QuotInt
