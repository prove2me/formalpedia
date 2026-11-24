-- Prove2me | solution 1 for GlobalTheory.TriangularityLowCoeff.coeff_iterPD
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:38:57.612804+00:00
-- url     : https://prove2.me/submissions/75fd1b6a-48d7-4c5e-8894-4cf232dd87d8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CoeffAnnihilatedOfAevalMemKerPow
import Theorems.Thm_GlobalTheory_TriangularityLowCoeff_expOf_cons

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
theorem _root_.solution {R : Type} [CommRing R] {d : ℕ} :
    ∀ (L : List (Fin d)) (m : Fin d →₀ ℕ) (Q : MvPolynomial (Fin d) R),
      coeff m (iterDer (fun i => pderiv i) L Q) = coeff (m + expOf L) Q * (fac L m : R)
  | [], m, Q => by simp [iterDer, expOf, fac]
  | i :: L, m, Q => by
    show coeff m (iterDer (fun i => pderiv i) L (pderiv i Q)) = _
    rw [solution L m, coeff_pderiv, fac, expOf_cons]
    have e : m + expOf L + Finsupp.single i 1 = m + (Finsupp.single i 1 + expOf L) := by abel
    rw [e]; push_cast; ring
end GlobalTheory.TriangularityLowCoeff
