-- Prove2me | solution 1 for GlobalTheory.LGrp.locallyCompact_lineLevi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:59:02.42864+00:00
-- url     : https://prove2.me/submissions/2c651b10-401a-405f-9547-c307ac616148

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
open Formalism.UG
variable {n : ℕ}
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
variable (σ : L →+* L) (hσ : ∀ x, σ (σ x) = x) (hc : Continuous σ)
omit σ hσ hc
variable {ϖ : L} {σ : L →+* L} {q : ℕ}
namespace GlobalTheory.LGrp
theorem _root_.solution (hσ : ∀ x, σ (σ x) = x) (hc : Continuous σ) [LocallyCompactSpace (GU σ (n + 2))] :
    LocallyCompactSpace (Lˣ × GU σ n) :=
  (lineLevi σ hσ hc n).toHomeomorph.isClosedEmbedding.locallyCompactSpace
end GlobalTheory.LGrp
