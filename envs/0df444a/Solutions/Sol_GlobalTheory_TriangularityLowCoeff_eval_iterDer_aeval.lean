-- Prove2me | solution 1 for GlobalTheory.TriangularityLowCoeff.eval_iterDer_aeval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:52:07.467293+00:00
-- url     : https://prove2.me/submissions/cc30b0c6-3c62-45c0-9a4e-87ef5bc66af1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CoeffAnnihilatedOfAevalMemKerPow
import Theorems.Thm_GlobalTheory_TriangularityLowCoeff_der_mem_pow
import Theorems.Thm_GlobalTheory_TriangularityLowCoeff_iterDer_mem
import Theorems.Thm_GlobalTheory_TriangularityLowCoeff_der_aeval
import Theorems.Thm_GlobalTheory_TriangularityLowCoeff_aeval_mem_pow
import Theorems.Thm_GlobalTheory_TriangularityLowCoeff_eval_aeval

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
theorem _root_.solution {R B : Type} [CommRing R] [CommRing B] [Algebra R B] {d : ℕ}
    (ε : B →ₐ[R] R) (y : Fin d → B) (D : Fin d → Derivation R B B)
    (hy : ∀ i, ε (y i) = 0) (hD : ∀ i j, ε (D i (y j)) = if i = j then 1 else 0) :
    ∀ (L : List (Fin d)) (Q : MvPolynomial (Fin d) R), Q ∈ idealOfVars (Fin d) R ^ L.length →
      ε (iterDer D L (aeval y Q)) = coeff 0 (iterDer (fun i => pderiv i) L Q)
  | [], Q, _ => by simpa [iterDer] using eval_aeval ε y hy Q
  | i :: L, Q, hQ => by
    show ε (iterDer D L (D i (aeval y Q))) = coeff 0 (iterDer (fun i => pderiv i) L (pderiv i Q))
    have hP : ∀ j, pderiv j Q ∈ idealOfVars (Fin d) R ^ L.length := fun j =>
      der_mem_pow (pderiv j) _ L.length Q (by simpa using hQ)
    have key : ∀ j, ε (iterDer D L (aeval y (pderiv j Q) * D i (y j))) =
        ε (D i (y j)) * coeff 0 (iterDer (fun i => pderiv i) L (pderiv j Q)) := by
      intro j
      set x := aeval y (pderiv j Q)
      set u := D i (y j)
      have split : x * u = ε u • x + x * (u - algebraMap R B (ε u)) := by
        rw [Algebra.smul_def]; ring
      have hmem : x * (u - algebraMap R B (ε u)) ∈ RingHom.ker ε ^ (L.length + 1) := by
        rw [pow_succ]
        refine Ideal.mul_mem_mul (aeval_mem_pow ε y hy _ _ (hP j)) ?_
        simp [RingHom.mem_ker]
      have h0 : ε (iterDer D L (x * (u - algebraMap R B (ε u)))) = 0 := by
        have := iterDer_mem D (RingHom.ker ε) L 1 _ hmem
        rw [pow_one, RingHom.mem_ker] at this
        exact this
      rw [split, map_add, map_add, h0, add_zero, map_smul, map_smul, smul_eq_mul,
        solution ε y D hy hD L (pderiv j Q) (hP j)]
    rw [der_aeval, map_sum, map_sum]
    simp only [key, hD, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
end GlobalTheory.TriangularityLowCoeff
