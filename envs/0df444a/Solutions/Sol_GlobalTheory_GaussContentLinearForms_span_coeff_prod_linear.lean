-- Prove2me | solution 1 for GlobalTheory.GaussContentLinearForms.span_coeff_prod_linear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:24:48.47699+00:00
-- url     : https://prove2.me/submissions/6877d905-e590-4870-85df-2f92d1458a50

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SpanCoeffProdLinear
import Theorems.Thm_GlobalTheory_GaussContentLinearForms_span_coeff_prod
import Theorems.Thm_GlobalTheory_GaussContentLinearForms_span_coeff_linear

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory
open GlobalTheory.GaussContentLinearForms
variable {V : Type} [CommRing V] {σ : Type}
namespace GlobalTheory.GaussContentLinearForms
theorem _root_.solution (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (d m : ℕ) (c : Fin d → Fin m → V) :
    Ideal.span (Set.range fun s =>
        (∏ j, ∑ i, C (c j i) * X i : MvPolynomial (Fin m) V).coeff s) =
      ∏ j, Ideal.span (Set.range (c j)) := by
  rw [span_coeff_prod]
  exact Finset.prod_congr rfl fun j _ => span_coeff_linear (c j)
end GlobalTheory.GaussContentLinearForms
