-- Prove2me | solution 1 for GlobalTheory.projMatrix_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:54:29.971152+00:00
-- url     : https://prove2.me/submissions/0e168121-be8c-4311-9d6d-6d92abb4b065

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsMatricesOfProjectiveComplex
import Theorems.Thm_GlobalTheory_GrSum_map_of
import Theorems.Thm_GlobalTheory_Wick_dividedContraction_one
import Theorems.Thm_GlobalTheory_locCubeMap_app_toLocCube
import Theorems.Thm_GlobalTheory_locCubeMap_id
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.GrSum.map_of
attribute [local simp] GlobalTheory.Wick.dividedContraction_one
attribute [local simp] GlobalTheory.locCubeMap_app_toLocCube
attribute [local simp] GlobalTheory.locCubeMap_id



set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {R : Type} [CommRing R] (R' : Type) [CommRing R'] [Algebra R R']
    {a b : ℕ} (f : (Fin a → R) →ₗ[R] (Fin b → R)) (x : R' ⊗[R] (Fin a → R)) :
    ((LinearMap.toMatrix' f).map (algebraMap R R')).mulVec
        (TensorProduct.piScalarRight R R' R' (Fin a) x) =
      TensorProduct.piScalarRight R R' R' (Fin b) (f.baseChange R' x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, Matrix.mulVec_add, hx, hy]
  | tmul r y =>
    ext i
    have hy : f y = (LinearMap.toMatrix' f).mulVec y := by
      rw [LinearMap.toMatrix'_mulVec]
    rw [LinearMap.baseChange_tmul, hy]
    simp only [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul,
      Matrix.mulVec, dotProduct, Matrix.map_apply, Finset.sum_smul, Algebra.smul_def, map_mul,
      map_sum, Finset.sum_mul, mul_assoc]
end GlobalTheory
