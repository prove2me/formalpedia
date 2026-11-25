-- Prove2me | solution 1 for GroundTheory.Automorphic.Spherical.isIntegral_of_forall
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:00:32.019204+00:00
-- url     : https://prove2.me/submissions/45c48763-0afe-4f68-98c7-e804ffd2bf01

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SphericalLaurent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Spherical
open AddMonoidAlgebra
variable {n : ℕ}
namespace GroundTheory.Automorphic.Spherical
theorem _root_.solution (A : Subalgebra ℂ (LaurentRing n))
    (h₁ : ∀ i, IsIntegral A (monomial (Pi.single i 1 : Fin n → ℤ)))
    (h₂ : ∀ i, IsIntegral A (monomial (Pi.single i (-1) : Fin n → ℤ))) :
    Algebra.IsIntegral A (LaurentRing n) := by
  let S : Subalgebra ℂ (LaurentRing n) := (integralClosure A (LaurentRing n)).restrictScalars ℂ
  have hmono : ∀ l : Fin n → ℤ, monomial l ∈ S := by
    intro l
    have hl : monomial l = ∏ i, monomial (Pi.single i (l i) : Fin n → ℤ) := by
      rw [AddMonoidAlgebra.prod_single]
      simp only [Finset.prod_const_one]
      congr 1
      funext j
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hl]
    refine Subalgebra.prod_mem _ fun i _ => ?_
    rcases le_or_gt 0 (l i) with h | h
    · obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le h
      have : monomial (Pi.single i (l i) : Fin n → ℤ) = monomial (Pi.single i 1) ^ k := by
        rw [AddMonoidAlgebra.single_pow, one_pow, hk, ← Pi.single_smul]
        simp
      rw [this]
      exact Subalgebra.pow_mem _ (h₁ i) k
    · obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (neg_nonneg.2 h.le)
      have : monomial (Pi.single i (l i) : Fin n → ℤ) = monomial (Pi.single i (-1)) ^ k := by
        rw [AddMonoidAlgebra.single_pow, one_pow, ← Pi.single_smul]
        congr 2
        simp only [nsmul_eq_mul, mul_neg, mul_one]
        omega
      rw [this]
      exact Subalgebra.pow_mem _ (h₂ i) k
  refine ⟨fun p => ?_⟩
  have : p ∈ S := by
    rw [← AddMonoidAlgebra.sum_coeff_single p]
    refine Subalgebra.sum_mem _ fun l _ => ?_
    have : (single l (p.coeff l) : LaurentRing n) = p.coeff l • monomial l := by
      rw [AddMonoidAlgebra.smul_single', mul_one]
    rw [this]
    exact Subalgebra.smul_mem _ (hmono l) _
  exact this
end GroundTheory.Automorphic.Spherical
