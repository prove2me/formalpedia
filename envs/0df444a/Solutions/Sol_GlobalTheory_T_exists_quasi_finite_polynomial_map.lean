-- Prove2me | solution 1 for GlobalTheory.T.exists_quasi_finite_polynomial_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:55:29.538798+00:00
-- url     : https://prove2.me/submissions/0af2e481-dc62-48e2-ae4c-18e203acc643

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsQuasiFinitePolynomialMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsQuasiFinitePolynomialMapStatement
import Theorems.Thm_GlobalTheory_exists_algebraicIndependent_int_quasiFiniteAt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (S : Type) [CommRing S] [IsDomain S] [CharZero S] [Algebra.FiniteType ℤ S] (𝔮 : Ideal S) [𝔮.IsPrime], ∃ (r : ℕ) (y : Fin r → S), AlgebraicIndependent ℤ y ∧ @Algebra.QuasiFiniteAt (MvPolynomial (Fin r) ℤ) S _ _ (MvPolynomial.aeval y : MvPolynomial (Fin r) ℤ →ₐ[ℤ] S).toRingHom.toAlgebra 𝔮 _ := by
  first | exact @GlobalTheory.exists_algebraicIndependent_int_quasiFiniteAt | exact GlobalTheory.exists_algebraicIndependent_int_quasiFiniteAt | (intros; apply GlobalTheory.exists_algebraicIndependent_int_quasiFiniteAt <;> assumption)
end _root_.GlobalTheory.T
