-- Prove2me | solution 1 for GlobalTheory.polyChartHom_injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:19:56.890973+00:00
-- url     : https://prove2.me/submissions/f9ac148b-42ec-428d-a93d-4af7c46a3c87

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
theorem _root_.solution : Function.Injective (polyChartHom V R₀) := by
  intro p q h
  rw [polyChartHom_apply, polyChartHom_apply] at h
  exact MvPolynomial.map_injective _ Subtype.val_injective
    (IsFractionRing.injective (MvPolynomial V F₀) (FractionRing (MvPolynomial V F₀)) h)
end GlobalTheory
