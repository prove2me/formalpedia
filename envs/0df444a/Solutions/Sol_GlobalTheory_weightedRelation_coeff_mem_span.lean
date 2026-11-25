-- Prove2me | solution 1 for GlobalTheory.weightedRelation_coeff_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:06:33.251212+00:00
-- url     : https://prove2.me/submissions/84b4d12b-0d53-49ce-a477-0fd9462a9727

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsQuasiRegularSeqSelfIffLocalizationMaximal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CoeffMemSpanOfWeightedHomogeneousRelationQuasiRe
import Theorems.Thm_GlobalTheory_coeff_mem_span_of_isWeightedHomogeneous_of_eval_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open GlobalTheory
open MvPolynomial
variable {R : Type} [CommRing R] {n : ℕ}
namespace GlobalTheory
theorem _root_.solution : ∀ {R : Type} [CommRing R] {n : ℕ} (z : Fin n → R)
    (w : Fin n → ℕ), (∀ i, 1 ≤ w i) →
    IsQuasiRegularSeq R z → ∀ (D : ℕ) (F : MvPolynomial (Fin n) R),
    F.IsWeightedHomogeneous w D → MvPolynomial.eval z F = 0 →
    ∀ α : Fin n →₀ ℕ, F.coeff α ∈ Ideal.span (Set.range z) :=
  fun z w hw hz D F hF h0 α =>
    coeff_mem_span_of_isWeightedHomogeneous_of_eval_eq_zero z w hw hz D F hF h0 α
end GlobalTheory
