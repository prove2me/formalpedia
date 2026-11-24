-- Prove2me | solution 1 for GlobalTheory.GaussContentLinearForms.span_coeff_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:05:17.121533+00:00
-- url     : https://prove2.me/submissions/1fb77a68-5760-4518-9c46-221c1b82e8e1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SpanCoeffProdLinear
import Theorems.Thm_GlobalTheory_GaussContentLinearForms_span_coeff_one
import Theorems.Thm_GlobalTheory_GaussContentLinearForms_span_coeff_mul

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
theorem _root_.solution [IsDomain V] [IsDiscreteValuationRing V] {ι : Type} (t : Finset ι)
    (f : ι → MvPolynomial σ V) :
    Ideal.span (Set.range fun s => (∏ j ∈ t, f j).coeff s) =
      ∏ j ∈ t, Ideal.span (Set.range fun s => (f j).coeff s) := by
  classical
  induction t using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.prod_empty, span_coeff_one, Ideal.one_eq_top]
  | insert j t hj ih => rw [Finset.prod_insert hj, Finset.prod_insert hj, span_coeff_mul, ih]
end GlobalTheory.GaussContentLinearForms
