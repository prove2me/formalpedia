-- Prove2me | solution 1 for GlobalTheory.exists_eval_eq_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:41:33.803784+00:00
-- url     : https://prove2.me/submissions/eace3ceb-5447-4830-87f6-e86ada4a3f39

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
theorem _root_.solution (z : Fin n → R) (P : MvPolynomial (Fin n) R)
    (hP : ∀ β, P.coeff β ∈ Ideal.span (Set.range z)) :
    ∃ G : MvPolynomial (Fin n) R, MvPolynomial.eval z G = MvPolynomial.eval z P ∧
      ∀ γ, G.coeff γ ≠ 0 → ∃ β j, P.coeff β ≠ 0 ∧ γ = β + Finsupp.single j 1 := by
  classical
  choose g hg using fun β => (Ideal.mem_span_range_iff_exists_fun).mp (hP β)
  refine ⟨∑ β ∈ P.support, ∑ j, MvPolynomial.monomial (β + Finsupp.single j 1) (g β j), ?_, ?_⟩
  · have key : ∀ β j, MvPolynomial.eval z (MvPolynomial.monomial (β + Finsupp.single j 1) (g β j))
        = g β j * z j * monoVal z β := by
      intro β j
      rw [MvPolynomial.eval_monomial]
      change _ * monoVal z _ = _
      rw [monoVal_add, monoVal_single, pow_one]
      ring
    simp only [map_sum, key]
    rw [MvPolynomial.eval_eq]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [← Finset.sum_mul, hg β]
    rfl
  · intro γ hγ
    rw [MvPolynomial.coeff_sum] at hγ
    obtain ⟨β, hβ, hβ'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hγ
    rw [MvPolynomial.coeff_sum] at hβ'
    obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hβ'
    rw [MvPolynomial.coeff_monomial] at hj
    split_ifs at hj with h
    · exact ⟨β, j, MvPolynomial.mem_support_iff.mp hβ, h.symm⟩
    · exact absurd rfl hj
end GlobalTheory
