-- Prove2me | solution 1 for GlobalTheory.exists_homogeneous_lift_nat_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:47:46.928846+00:00
-- url     : https://prove2.me/submissions/b5528860-50ac-459d-9eaf-34703b7f751b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ConeClosureArcOfIntegralImageReduction
import Theorems.Thm_GlobalTheory_exists_common_nat_denominator

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {R F J : Type*} [CommRing R] [CommRing F] (φ : R →+* F)
    (h : ∀ x : F, ∃ (r : R) (n : ℕ), 0 < n ∧ φ r = n * x) (G : MvPolynomial J F) (d : ℕ)
    (hG : G.IsHomogeneous d) :
    ∃ (n : ℕ) (G' : MvPolynomial J R), 0 < n ∧ G'.IsHomogeneous d ∧
      MvPolynomial.map φ G' = (n : MvPolynomial J F) * G := by
  classical
  obtain ⟨n, hn, hS⟩ := exists_common_nat_denominator φ h (fun s => G.coeff s) G.support
  choose! r hr using hS
  refine ⟨n, ∑ s ∈ G.support, MvPolynomial.monomial s (r s), hn, ?_, ?_⟩
  · refine MvPolynomial.IsHomogeneous.sum _ _ _ fun s hs => ?_
    refine MvPolynomial.isHomogeneous_monomial _ ?_
    have := hG (MvPolynomial.mem_support_iff.1 hs)
    rw [Finsupp.degree_eq_weight_one]
    exact this
  · rw [map_sum]
    conv_rhs => rw [G.as_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [MvPolynomial.map_monomial, hr s hs, ← map_natCast (MvPolynomial.C : F →+* MvPolynomial J F),
      MvPolynomial.C_mul_monomial]
end GlobalTheory
