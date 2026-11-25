-- Prove2me | solution 1 for GlobalTheory.finite_piece_of_polyGradedSMul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:52:38.367902+00:00
-- url     : https://prove2.me/submissions/3e30baab-fda2-4beb-ae7b-e46758a6a4a8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_XSmulMemWeightedHomogeneousSubmodule
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_FinitePieceOfPolyGradedSMul
import Theorems.Thm_GlobalTheory_GrSum_map_of
import Theorems.Thm_GlobalTheory_Wick_dividedContraction_one
import Theorems.Thm_GlobalTheory_X_mem_polyGrading
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
theorem _root_.solution : ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type)
    [CommRing R] (M : Type) [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
    [IsScalarTower R (MvPolynomial ι R) M] (ℳ : ℤ → Submodule R M) [PolyGradedSMul ι ℳ]
    [Decomposition ℳ], Module.Finite (MvPolynomial ι R) M → ∀ n, Module.Finite R (ℳ n) := by
  intro ι _ _ R _ M _ _ _ _ ℳ _ _ _ n
  refine GradedHilbert.finite_piece (ι := ι) ℳ (fun i k m hm => ?_) n
  have := grSMul_mem ℳ (X_mem_polyGrading i) hm
  first
    | exact this
    | exact add_comm k 1 ▸ this
    | simpa [add_comm] using this
end GlobalTheory
