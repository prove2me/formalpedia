-- Prove2me | solution 1 for GlobalTheory.TriangularityLowCoeff.der_mem_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:38:05.915793+00:00
-- url     : https://prove2.me/submissions/8acb0451-9d6e-4406-8574-a73b60715d42

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CoeffAnnihilatedOfAevalMemKerPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory GlobalTheory.TriangularityLowCoeff
open MvPolynomial
namespace GlobalTheory.TriangularityLowCoeff
theorem _root_.solution {R A : Type} [CommRing R] [CommRing A] [Algebra R A]
    (D : Derivation R A A) (J : Ideal A) : ∀ (k : ℕ) (x : A), x ∈ J ^ (k + 1) → D x ∈ J ^ k
  | 0, x, _ => by simp
  | k + 1, x, hx => by
    rw [pow_succ'] at hx
    refine Submodule.mul_induction_on (C := fun x => D x ∈ J ^ (k + 1)) hx ?_ ?_
    · intro a ha b hb
      rw [D.leibniz, smul_eq_mul, smul_eq_mul]
      refine Ideal.add_mem _ ?_ (Ideal.mul_mem_right _ _ hb)
      rw [pow_succ']
      exact Ideal.mul_mem_mul ha (solution D J k b hb)
    · intro x y hx hy
      rw [map_add]
      exact Ideal.add_mem _ hx hy
end GlobalTheory.TriangularityLowCoeff
