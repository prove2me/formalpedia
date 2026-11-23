-- Prove2me | solution 1 for GlobalTheory.polyChartHom_X
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:53:05.30465+00:00
-- url     : https://prove2.me/submissions/21e2184b-fd98-42cd-afa6-8de7de784d6a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_PolyChartSmoothFractionLift
import Theorems.Thm_GlobalTheory_polyChartHom_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open MvPolynomial
variable {K F₀ : Type} (V : Type) [Field K] [Field F₀] [Algebra K F₀] (R₀ : Subalgebra K F₀)
namespace GlobalTheory
theorem _root_.solution (v : V) :
    polyChartHom V R₀ (X v) =
      algebraMap (MvPolynomial V F₀) (FractionRing (MvPolynomial V F₀)) (X v) := by
  rw [polyChartHom_apply, MvPolynomial.map_X]
end GlobalTheory
