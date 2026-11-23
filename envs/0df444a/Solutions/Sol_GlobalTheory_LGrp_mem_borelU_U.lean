-- Prove2me | solution 1 for GlobalTheory.LGrp.mem_borelU_U
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:52:09.115193+00:00
-- url     : https://prove2.me/submissions/245c67d5-e73f-48c0-b300-2764be8c781d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EqOfHasValueAtInfinite
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LineOppositeParabolicUnitaryLeviSectionEq
import Theorems.Thm_GlobalTheory_LGrp_mem_borelU_Q

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
open Formalism.UG
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {α : Type} [LinearOrder α]
namespace GlobalTheory.LGrp
theorem _root_.solution (σ : L →+* L) (n : ℕ) (g : GU σ n) : g ∈ (borelU σ n).U ↔ IsUnipU g := by
  rw [LeviDatum.mem_U]
  constructor
  · rintro ⟨h, e⟩
    exact ⟨(mem_borelU_Q σ n g).1 h, fun i => congrArg (fun t : torusU σ n => (t.1 i : L)) e⟩
  · rintro ⟨h, e⟩
    exact ⟨(mem_borelU_Q σ n g).2 h, Subtype.ext (funext fun i => Units.ext (e i))⟩
end GlobalTheory.LGrp
