-- Prove2me | solution 1 for GlobalTheory.LGrp.LeviDatum.reparam_U
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:01:01.481798+00:00
-- url     : https://prove2.me/submissions/99054c6b-185c-4b23-9bb3-6f05beb74963

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
namespace GlobalTheory.LGrp.LeviDatum
theorem _root_.solution {M' : Type} [Group M'] [TopologicalSpace M'] (e : M' ≃ₜ* M) : (P.reparam e).U = P.U := by
  ext g
  rw [mem_U, mem_U]
  exact exists_congr fun h => map_eq_one_iff e.symm e.symm.injective
end GlobalTheory.LGrp.LeviDatum
