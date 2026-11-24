-- Prove2me | solution 1 for GlobalTheory.SmGL.Stages.eventually_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:50:24.361241+00:00
-- url     : https://prove2.me/submissions/193fe745-be40-46a4-9338-b145a03f21d6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyInv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory Topology Filter
open scoped TensorProduct
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.Stages
variable {F G M W X Y Z : Type} [Field F] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group M] [TopologicalSpace M] [IsTopologicalGroup M] [AddCommGroup W] [Module F W]
  [AddCommGroup X] [Module F X] [AddCommGroup Y] [Module F Y] [AddCommGroup Z] [Module F Z]
namespace GlobalTheory.SmGL.Stages
theorem _root_.solution {P : Subgroup G} {σ : Representation F P W} (f : smoothPart (ind P σ)) :
    ∀ᶠ u in 𝓝 (1 : G), ∀ x, f.1.1 (x * u) = f.1.1 x :=
  Filter.mem_of_superset (IsOpen.mem_nhds f.2 (by simp)) fun g hg x =>
    congrFun (congrArg Subtype.val (show ind P σ g f.1 = f.1 from hg)) x
end GlobalTheory.SmGL.Stages
