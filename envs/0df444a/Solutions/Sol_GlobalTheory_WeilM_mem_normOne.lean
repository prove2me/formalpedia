-- Prove2me | solution 1 for GlobalTheory.WeilM.mem_normOne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:06:00.821492+00:00
-- url     : https://prove2.me/submissions/03fe4ef2-a636-4233-bcae-5fc10fb5f4a7

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
theorem _root_.solution {u : Eˣ} : u ∈ normOne c ↔ (u : E) * c u = 1 := Units.ext_iff
end GlobalTheory.WeilM
