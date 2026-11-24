-- Prove2me | solution 1 for GlobalTheory.IsIntegralDetLattice.isIntegral_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:07:08.609052+00:00
-- url     : https://prove2.me/submissions/94781ae8-cd6e-455b-8640-56225a5382f7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsIntegralDetOfPreservesLattice
import Theorems.Thm_GlobalTheory_IsIntegralDetLattice_isIntegral_of_isRoot_charpoly

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.IsIntegralDetLattice
namespace GlobalTheory.IsIntegralDetLattice
theorem _root_.solution {R E : Type} [CommRing R] [Field E] [Algebra R E] {N : ℕ}
    (A : Matrix (Fin N) (Fin N) E) (hA : IsIntegral R A) : IsIntegral R A.det := by

  let φ : E →ₐ[R] AlgebraicClosure E := IsScalarTower.toAlgHom R E (AlgebraicClosure E)
  have hA' : IsIntegral R (A.map (algebraMap E (AlgebraicClosure E))) := by
    exact hA.map (φ.mapMatrix (m := Fin N))
  have hdet : (A.map (algebraMap E (AlgebraicClosure E))).det = algebraMap E (AlgebraicClosure E) A.det := by
    rw [RingHom.map_det]; rfl
  rw [← isIntegral_algHom_iff φ (algebraMap E (AlgebraicClosure E)).injective]
  show IsIntegral R (algebraMap E (AlgebraicClosure E) A.det)
  rw [← hdet, Matrix.det_eq_prod_roots_charpoly]
  exact multiset_prod_mem (S := integralClosure R (AlgebraicClosure E)) _
    fun r hr => isIntegral_of_isRoot_charpoly _ hA' r (Polynomial.isRoot_of_mem_roots hr)
end GlobalTheory.IsIntegralDetLattice
