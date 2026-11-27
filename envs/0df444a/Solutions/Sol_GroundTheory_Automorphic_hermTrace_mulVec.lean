-- Prove2me | solution 1 for GroundTheory.Automorphic.hermTrace_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:44:59.835979+00:00
-- url     : https://prove2.me/submissions/d07f29cf-6532-47cb-9c0f-5cf614e2a188

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicUnitaryGroups_Anisotropic
import Definitions.Def_GroundTheory_AutomorphicForms_DefiniteClassNumber_HermTraceSelfOfHermValue
import Theorems.Thm_GroundTheory_Automorphic_hermPair_mulVec

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
    hermTrace K H R (unitaryMat g *ᵥ x) (unitaryMat g *ᵥ y) = hermTrace K H R x y := by
  rw [hermTrace, hermPair_mulVec]; rfl
end GroundTheory.Automorphic
