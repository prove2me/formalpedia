-- Prove2me | solution 1 for GlobalTheory.GaussContentLinearForms.span_coeff_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:46:35.384633+00:00
-- url     : https://prove2.me/submissions/8ac34d0b-1ea0-46c6-9b21-02d63665dd46

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
theorem _root_.solution :
    Ideal.span (Set.range fun s => (1 : MvPolynomial σ V).coeff s) = ⊤ := by
  classical
  rw [Ideal.eq_top_iff_one]
  exact Ideal.subset_span ⟨0, by simp⟩
end GlobalTheory.GaussContentLinearForms
