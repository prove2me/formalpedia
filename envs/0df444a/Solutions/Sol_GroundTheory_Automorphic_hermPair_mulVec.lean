-- Prove2me | solution 1 for GroundTheory.Automorphic.hermPair_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:02:57.330309+00:00
-- url     : https://prove2.me/submissions/1276de0d-998a-4a8a-8b2e-a7c13e1ac18c

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicUnitaryGroups_Anisotropic
import Definitions.Def_GroundTheory_AutomorphicForms_DefiniteClassNumber_HermTraceSelfOfHermValue

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open Module Matrix TensorProduct
variable {K E : Type*} [Field K] [CommRing E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] (H : Matrix ι ι E)
variable (K) (R : Type*) [CommRing R] [Algebra K R]
variable {K H R}
variable [DecidableEq ι]
namespace GroundTheory.Automorphic
theorem _root_.solution (g : unitaryPoints K E H R) (x y : ι → R ⊗[K] E) :
    hermPair K H R (unitaryMat g *ᵥ x) (unitaryMat g *ᵥ y) = hermPair K H R x y := by
  have hg : ((unitaryMat g).map (conjBase K E R))ᵀ * baseMatrix K H R * unitaryMat g =
      baseMatrix K H R := g.2
  have h1 : (fun i => conjBase K E R ((unitaryMat g *ᵥ x) i)) =
      (unitaryMat g).map (conjBase K E R) *ᵥ (fun i => conjBase K E R (x i)) := by
    funext i
    exact RingHom.map_mulVec _ _ _ i
  unfold hermPair
  rw [h1, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose,
    Matrix.vecMul_vecMul, ← Matrix.mul_assoc, hg, Matrix.dotProduct_mulVec]
end GroundTheory.Automorphic
