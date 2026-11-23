-- Prove2me | solution 1 for GlobalTheory.WeilM.hilbertNinetyQuotientHom_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:06:00.861065+00:00
-- url     : https://prove2.me/submissions/c3388413-c816-46a2-a681-d4442767a1b7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain MeasureTheory Matrix
open scoped NNReal Classical
open GlobalTheory GlobalTheory.WeilM
variable {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
variable {c}
namespace GlobalTheory.WeilM
theorem _root_.solution {z u : Eˣ} : h90 c z = u ↔ (u : E) * c z = z :=
  div_eq_iff_eq_mul.trans (Units.ext_iff.trans eq_comm)
end GlobalTheory.WeilM
