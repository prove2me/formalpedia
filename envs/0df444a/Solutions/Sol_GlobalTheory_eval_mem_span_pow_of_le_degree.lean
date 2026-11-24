-- Prove2me | solution 1 for GlobalTheory.eval_mem_span_pow_of_le_degree
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:38:07.739882+00:00
-- url     : https://prove2.me/submissions/f400a864-6543-4d0d-b7fc-6fdddadf89ae

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsQuasiRegularSeqSelfIffLocalizationMaximal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CoeffMemSpanOfWeightedHomogeneousRelationQuasiRe

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
theorem _root_.solution (z : Fin n → R) (m : ℕ) (P : MvPolynomial (Fin n) R)
    (hP : ∀ β, P.coeff β ≠ 0 → m ≤ β.degree) :
    MvPolynomial.eval z P ∈ Ideal.span (Set.range z) ^ m := by
  rw [MvPolynomial.eval_eq]
  refine Ideal.sum_mem _ fun β hβ => ?_
  have h1 := monoVal_mem_pow z (⟨β, rfl⟩ : MonoDeg (Fin n) β.degree)
  exact Ideal.mul_mem_left _ _
    (Ideal.pow_le_pow_right (hP β (MvPolynomial.mem_support_iff.mp hβ)) h1)
end GlobalTheory
