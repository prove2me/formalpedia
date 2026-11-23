-- Prove2me | solution 1 for GlobalTheory.polyChartHom_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:36:18.593218+00:00
-- url     : https://prove2.me/submissions/991fadd4-e37b-446d-bfb6-c17e1d42993d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_PolyChartSmoothFractionLift

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
theorem _root_.solution (p : MvPolynomial V R₀) :
    polyChartHom V R₀ p = algebraMap (MvPolynomial V F₀) (FractionRing (MvPolynomial V F₀))
      (MvPolynomial.map (R₀.val : R₀ →+* F₀) p) := rfl
end GlobalTheory
