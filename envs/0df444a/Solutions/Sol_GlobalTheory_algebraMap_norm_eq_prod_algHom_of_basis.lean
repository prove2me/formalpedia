-- Prove2me | solution 1 for GlobalTheory.algebraMap_norm_eq_prod_algHom_of_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:35:54.441274+00:00
-- url     : https://prove2.me/submissions/fcb93929-5293-474e-8d82-77adf928cc22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthCommensurableSpanSpanOfDetNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin
import Theorems.Thm_GlobalTheory_det_algHom_basis_ne_zero
import Theorems.Thm_GlobalTheory_algHom_matrix_mul_leftMulMatrix

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
variable {R S L ι : Type*} [CommRing R] [CommRing S] [Algebra R S] [CommRing L] [IsDomain L]
  [Algebra R L] [Fintype ι] [DecidableEq ι]
namespace GlobalTheory
theorem _root_.solution (e : Basis ι R S) {P : ι → (S →ₐ[R] L)}
    (hP : Function.Injective P) (x : S) :
    algebraMap R L (Algebra.norm R x) = ∏ j, P j x := by
  have hQ₀ : (Matrix.of fun j i => P j (e i)).det ≠ 0 := by
    rw [← Matrix.det_transpose]
    exact det_algHom_basis_ne_zero e hP
  have h := congrArg Matrix.det (algHom_matrix_mul_leftMulMatrix e P x)
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, mul_comm] at h
  rw [Algebra.norm_eq_matrix_det e, RingHom.map_det]
  exact mul_right_cancel₀ hQ₀ h
end GlobalTheory
