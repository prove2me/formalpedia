-- Prove2me | solution 1 for GlobalTheory.LGrp.mem_lineParU_U
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:50:24.035713+00:00
-- url     : https://prove2.me/submissions/78505d98-7782-419d-b3cd-409de312d465

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EqOfHasValueAtInfinite
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LineOppositeParabolicUnitaryLeviSectionEq
import Theorems.Thm_GlobalTheory_LGrp_lineParU_p
import Theorems.Thm_GlobalTheory_LGrp_mem_lineParU_Q
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans


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
variable {n : ℕ}
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
variable (σ : L →+* L) (hσ : ∀ x, σ (σ x) = x) (hc : Continuous σ)
namespace GlobalTheory.LGrp
theorem _root_.solution (g : GU σ (n + 2)) :
    g ∈ (lineParU σ hσ hc n).U ↔ (∀ i, i ≠ 0 → g.1.val i 0 = 0) ∧ g.1.val 0 0 = 1 ∧
      ∀ i j, g.1.val (midIdx i) (midIdx j) = (1 : Matrix (Fin n) (Fin n) L) i j := by
  rw [LeviDatum.mem_U, ← mem_lineParU_Q σ hσ hc]
  constructor
  · rintro ⟨h, e⟩
    have := lineParU_p σ hσ hc ⟨g, h⟩
    rw [e] at this
    exact ⟨h, this.1.symm, fun i j => (this.2 i j).symm⟩
  · rintro ⟨h, e, e'⟩
    have := lineParU_p σ hσ hc ⟨g, h⟩
    exact ⟨h, Prod.ext (Units.ext (this.1.trans e))
      (Subtype.ext (Units.ext (Matrix.ext fun i j => (this.2 i j).trans (e' i j))))⟩
end GlobalTheory.LGrp
