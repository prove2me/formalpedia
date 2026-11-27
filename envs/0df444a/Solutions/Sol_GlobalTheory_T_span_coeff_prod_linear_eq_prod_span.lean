-- Prove2me | solution 1 for GlobalTheory.T.span_coeff_prod_linear_eq_prod_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:33:43.600593+00:00
-- url     : https://prove2.me/submissions/d9253b8c-30be-4704-a1aa-2d75db064e72

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SpanCoeffProdLinear
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SpanCoeffProdLinearStatement
import Theorems.Thm_GlobalTheory_GaussContentLinearForms_span_coeff_prod_linear


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (d m : ℕ)
    (c : Fin d → Fin m → V),
    Ideal.span (Set.range fun s => (∏ j, ∑ i, C (c j i) * X i : MvPolynomial (Fin m) V).coeff s) =
      ∏ j, Ideal.span (Set.range (c j)) := by
  first | exact @GlobalTheory.GaussContentLinearForms.span_coeff_prod_linear | exact GlobalTheory.GaussContentLinearForms.span_coeff_prod_linear | (intros; apply GlobalTheory.GaussContentLinearForms.span_coeff_prod_linear <;> assumption)
end _root_.GlobalTheory.T
