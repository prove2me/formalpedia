-- Prove2me | solution 1 for GlobalTheory.LGrp.LeviDatum.delta_of_mem_U
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:57:47.056473+00:00
-- url     : https://prove2.me/submissions/210d8ee5-a03e-47bf-9548-28da2070c9cb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EqOfHasValueAtInfinite
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LineOppositeParabolicUnitaryLeviSectionEq
import Theorems.Thm_GlobalTheory_LGrp_checkFun_apply
import Theorems.Thm_GlobalTheory_LGrp_checkFun_checkFun
import Theorems.Thm_GlobalTheory_LGrp_lFactor_singleton
import Theorems.Thm_GlobalTheory_LGrp_lFactor_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.LGrp.checkFun_apply
attribute [local simp] GlobalTheory.LGrp.checkFun_checkFun
attribute [local simp] GlobalTheory.LGrp.lFactor_singleton
attribute [local simp] GlobalTheory.LGrp.lFactor_zero



set_option autoImplicit false
open MeasureTheory Matrix
open scoped NNReal TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.LGrp
open GlobalTheory.PRep
open GlobalTheory.LGrp.LeviDatum
variable {G M : Type} [Group G] [TopologicalSpace G] [Group M] [TopologicalSpace M] (P : LeviDatum G M)
variable [IsTopologicalGroup G] [LocallyCompactSpace G] [T1Space M]
namespace GlobalTheory.LGrp.LeviDatum
theorem _root_.solution (q : P.Q) (h : (q : G) ∈ P.U) : P.delta q = 1 := by
  obtain ⟨_, e⟩ := P.mem_U.1 h
  have e' : P.p q = 1 := e
  simp only [delta, MonoidHom.comp_apply, e', map_one]
end GlobalTheory.LGrp.LeviDatum
