-- Prove2me | solution 1 for GlobalTheory.polyChartHom_C
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:53:05.240672+00:00
-- url     : https://prove2.me/submissions/de213a83-9fdf-46be-abdd-8eefe9f01081

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
theorem _root_.solution (a : R₀) :
    polyChartHom V R₀ (C a) = algebraMap F₀ (FractionRing (MvPolynomial V F₀)) a := by
  rw [polyChartHom_apply, MvPolynomial.map_C,
    IsScalarTower.algebraMap_apply F₀ (MvPolynomial V F₀) (FractionRing (MvPolynomial V F₀))]
  rfl
end GlobalTheory
