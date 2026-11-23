-- Prove2me | solution 1 for GlobalTheory.GaussContentLinearForms.span_coeff_C_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:46:14.850775+00:00
-- url     : https://prove2.me/submissions/bb4fc2b1-d990-46fd-9953-ecea20965aa7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SpanCoeffProdLinear

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
theorem _root_.solution (a : V) (f : MvPolynomial σ V) :
    Ideal.span (Set.range fun s => (C a * f).coeff s) =
      Ideal.span {a} * Ideal.span (Set.range fun s => f.coeff s) := by
  rw [Ideal.span_mul_span']
  congr 1
  ext x
  simp only [coeff_C_mul, Set.mem_range, Set.mem_mul, Set.mem_singleton_iff]
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨a, rfl, _, ⟨s, rfl⟩, rfl⟩
  · rintro ⟨b, rfl, y, ⟨s, rfl⟩, rfl⟩
    exact ⟨s, rfl⟩
end GlobalTheory.GaussContentLinearForms
