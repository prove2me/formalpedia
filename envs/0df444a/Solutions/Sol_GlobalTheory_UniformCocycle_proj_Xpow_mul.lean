-- Prove2me | solution 1 for GlobalTheory.UniformCocycle.proj_Xpow_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:14:01.22652+00:00
-- url     : https://prove2.me/submissions/aef86b63-d904-4839-ae33-a1aa1de104cf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsHomogeneousIdealOverReesAlgebraStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCoboundaryOfFractionCocycleHomogeneousIdeaStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UniformSerreVanishingCechCocycles
import Theorems.Thm_GlobalTheory_UniformCocycle_proj_X_mul
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
open MvPolynomial
open GlobalTheory GlobalTheory.UniformCocycle
variable {R : Type} [CommRing R] {σ : Type}
namespace GlobalTheory.UniformCocycle
theorem _root_.solution (I : Ideal R) (e : ℕ) (i : σ) (k : ℕ) (P : MvPolynomial σ (reesAlgebra I)) :
    proj I e (X i ^ k * P) = X i ^ k * proj I e P := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', mul_assoc, proj_X_mul, ih, ← mul_assoc, ← pow_succ']
end GlobalTheory.UniformCocycle
