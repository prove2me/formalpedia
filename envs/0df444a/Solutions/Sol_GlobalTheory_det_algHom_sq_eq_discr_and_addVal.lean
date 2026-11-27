-- Prove2me | solution 1 for GlobalTheory.det_algHom_sq_eq_discr_and_addVal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:37:46.468196+00:00
-- url     : https://prove2.me/submissions/da3fd2ba-6f4b-484b-a598-ccef149534df

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthCommensurableSpanSpanOfDetNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin
import Theorems.Thm_GlobalTheory_discr_eq_det_toMatrix_sq_mul
import Theorems.Thm_GlobalTheory_addVal_discr_eq_two_mul_length_add
import Theorems.Thm_GlobalTheory_two_mul_length_le_addVal_discr
import Theorems.Thm_GlobalTheory_algebraMap_discr_eq_det_sq_of_basis
import Theorems.Thm_GlobalTheory_algebraMap_discr_basis_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module IsDiscreteValuationRing Polynomial
open scoped TensorProduct
open GlobalTheory
variable {R S L ι : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing S]
  [Algebra R S] [CommRing L] [IsDomain L] [Algebra R L] [Fintype ι] [DecidableEq ι]
namespace GlobalTheory
theorem _root_.solution (e : Basis ι R S) {P : ι → (S →ₐ[R] L)}
    (hP : Function.Injective P) (v : ι → S) :
    (Matrix.of fun i j => P j (v i)).det ^ 2 = algebraMap R L (Algebra.discr R v) ∧
    Algebra.discr R v = (e.toMatrix v).det ^ 2 * Algebra.discr R e ∧
    Algebra.discr R e ≠ 0 ∧
    addVal R (Algebra.discr R v) =
      2 * Module.length R (S ⧸ Submodule.span R (Set.range v)) + addVal R (Algebra.discr R e) ∧
    2 * Module.length R (S ⧸ Submodule.span R (Set.range v)) ≤ addVal R (Algebra.discr R v) :=
  ⟨(algebraMap_discr_eq_det_sq_of_basis e hP v).symm, discr_eq_det_toMatrix_sq_mul e v,
    fun h => algebraMap_discr_basis_ne_zero e hP (by rw [h, map_zero]),
    addVal_discr_eq_two_mul_length_add e v, two_mul_length_le_addVal_discr e v⟩
end GlobalTheory
