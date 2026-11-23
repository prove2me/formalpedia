-- Prove2me | solution 1 for GlobalTheory.LGrp.LeviDatum.IsOpposite.prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:48:28.672298+00:00
-- url     : https://prove2.me/submissions/4374dc71-2878-4f17-be6b-9df5d4298ec1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EqOfHasValueAtInfinite
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LineOppositeParabolicUnitaryLeviSectionEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped NNReal TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.LGrp
open GlobalTheory.PRep
open GlobalTheory.LGrp.LeviDatum
variable {G M : Type} [Group G] [TopologicalSpace G] [Group M] [TopologicalSpace M] (P : LeviDatum G M)
variable {P} {P' : LeviDatum G M}
namespace GlobalTheory.LGrp.LeviDatum
namespace IsOpposite
theorem _root_.solution (h : P.IsOpposite P') (H : Type) [Group H] [TopologicalSpace H] :
    (P.prod H).IsOpposite (P'.prod H) := by
  refine ⟨congrArg (·.prodMap (MonoidHom.id H)) h.1, le_antisymm (fun g hg => ?_) ?_⟩
  · obtain ⟨m, hm⟩ : g.1 ∈ P.L := h.2.le hg
    exact ⟨(m, g.2), Prod.ext hm rfl⟩
  · rintro _ ⟨m, rfl⟩
    exact h.2.ge ⟨m.1, rfl⟩
end IsOpposite
end GlobalTheory.LGrp.LeviDatum
