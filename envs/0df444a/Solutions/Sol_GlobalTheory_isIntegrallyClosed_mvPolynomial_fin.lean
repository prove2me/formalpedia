-- Prove2me | solution 1 for GlobalTheory.isIntegrallyClosed_mvPolynomial_fin
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:15:35.78217+00:00
-- url     : https://prove2.me/submissions/ce364843-76c9-4e37-8713-a7b938f87fed

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
universe u
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (A : Type*) [CommRing A] [IsDomain A]
    [IsIntegrallyClosed A] (n : ℕ) : IsIntegrallyClosed (MvPolynomial (Fin n) A) := by
  induction n with
  | zero => exact IsIntegrallyClosed.of_equiv (MvPolynomial.isEmptyRingEquiv A (Fin 0)).symm
  | succ n ih => exact IsIntegrallyClosed.of_equiv (MvPolynomial.finSuccEquiv A n).symm.toRingEquiv
end GlobalTheory
