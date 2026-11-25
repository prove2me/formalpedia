-- Prove2me | solution 1 for GlobalTheory.finite_cechHomology_of_finite_cubeHomology
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:01:22.397358+00:00
-- url     : https://prove2.me/submissions/9eb735ec-40f9-40d0-b47c-d86404242675

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexAcyclicIffQuasiIsoCechAug
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_FiniteCechHomologyOfFiniteCubeHomology
import Theorems.Thm_GlobalTheory_finite_cycles_of_finite_homology
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
theorem _root_.solution (ι : Type) [LinearOrder ι] (R : Type)
    [CommRing R] [IsNoetherianRing R] (A : Cube.{0} ι R) (h₀ : Module.Finite R (A.obj ∅))
    (h : ∀ p, Module.Finite R ((cubeComplex A).homology p)) (p : ℕ) :
    Module.Finite R ((cechComplex A).homology p) := by
  cases p with
  | zero =>
    have h1 := h 1
    have h2 : Module.Finite R ((cubeComplex A).X 0) :=
      Module.Finite.equiv (Cube.termZeroEquiv A).symm
    have h3 := finite_cycles_of_finite_homology (cubeComplex A) 0 1 (by simp)
    exact Module.Finite.equiv
      (cubeCyclesIso A 1 ≪≫ (cechHomologyZeroIso A).symm).toLinearEquiv
  | succ p =>
    have h1 := h (p + 2)
    exact Module.Finite.equiv (cechHomologySuccIso A p).symm.toLinearEquiv
end GlobalTheory
