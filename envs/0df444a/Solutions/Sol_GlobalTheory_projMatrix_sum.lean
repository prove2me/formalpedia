-- Prove2me | solution 1 for GlobalTheory.projMatrix_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:52:36.618722+00:00
-- url     : https://prove2.me/submissions/51ff41d2-d6a0-4e7b-96dc-905cd408fac7

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
    {a : ℕ} {P : Type} [AddCommGroup P] [Module R P] (p : (Fin a → R) →ₗ[R] P)
    (x : R' ⊗[R] (Fin a → R)) :
    ∑ k, TensorProduct.piScalarRight R R' R' (Fin a) x k ⊗ₜ[R] p (Pi.single k 1) =
      p.baseChange R' x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
    simp only [map_add, Pi.add_apply, TensorProduct.add_tmul, Finset.sum_add_distrib, hx, hy]
  | tmul r y =>
    have hy : p y = ∑ k, y k • p (Pi.single k 1) := by
      simp only [← map_smul, ← map_sum]
      congr 1
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    rw [LinearMap.baseChange_tmul, hy]
    simp only [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul,
      TensorProduct.tmul_sum, TensorProduct.smul_tmul]
end GlobalTheory
