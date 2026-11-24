-- Prove2me | solution 1 for GlobalTheory.GaussContentLinearForms.span_coeff_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:32:38.133069+00:00
-- url     : https://prove2.me/submissions/7a7259d3-ece0-436e-af3a-e49ddd47573b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SpanCoeffProdLinear
import Theorems.Thm_GlobalTheory_GaussContentLinearForms_span_coeff_C_mul
import Theorems.Thm_GlobalTheory_GaussContentLinearForms_span_coeff_eq_top_iff
import Theorems.Thm_GlobalTheory_GaussContentLinearForms_exists_primitive_part

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
theorem _root_.solution [IsDomain V] [IsDiscreteValuationRing V] (f g : MvPolynomial σ V) :
    Ideal.span (Set.range fun s => (f * g).coeff s) =
      Ideal.span (Set.range fun s => f.coeff s) * Ideal.span (Set.range fun s => g.coeff s) := by
  obtain ⟨a, f', rfl, hf⟩ := exists_primitive_part f
  obtain ⟨b, g', rfl, hg⟩ := exists_primitive_part g
  have hfg : Ideal.span (Set.range fun s => (f' * g').coeff s) = ⊤ := by
    rw [span_coeff_eq_top_iff] at hf hg ⊢
    rw [map_mul]
    exact mul_ne_zero hf hg
  have e : C a * f' * (C b * g') = C (a * b) * (f' * g') := by
    rw [map_mul]; ring
  rw [e, span_coeff_C_mul, span_coeff_C_mul, span_coeff_C_mul, hf, hg, hfg, Ideal.mul_top,
    Ideal.mul_top, Ideal.mul_top, Ideal.span_singleton_mul_span_singleton]
end GlobalTheory.GaussContentLinearForms
