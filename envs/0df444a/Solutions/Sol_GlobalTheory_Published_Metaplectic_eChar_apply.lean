-- Prove2me | solution 1 for GlobalTheory.Published.Metaplectic.eChar_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:20:07.699009+00:00
-- url     : https://prove2.me/submissions/58e758e8-e92e-4ced-b928-3be977fe0931

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_MetaplecticRepresentation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix Complex
open scoped Real SchwartzMap ComplexConjugate
open GlobalTheory GlobalTheory.Published
open GlobalTheory.Published.Metaplectic
variable {ι : Type} [Fintype ι]
namespace GlobalTheory.Published.Metaplectic
theorem _root_.solution (x : ℝ) : eChar x = cexp (2 * π * x * I) := by
  show ((Real.fourierChar x : Circle) : ℂ) = _
  rw [Real.fourierChar_apply]
  push_cast
  ring_nf
end GlobalTheory.Published.Metaplectic
