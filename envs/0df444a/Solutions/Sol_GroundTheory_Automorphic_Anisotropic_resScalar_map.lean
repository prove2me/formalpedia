-- Prove2me | solution 1 for GroundTheory.Automorphic.Anisotropic.resScalar_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:43:46.075969+00:00
-- url     : https://prove2.me/submissions/9c520021-d624-4bc7-ab12-4eabab004b10

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AnisotropicRestrict
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicUnitaryGroups
import Definitions.Def_GroundTheory_AutomorphicForms_AnisotropicUnitaryRes
import Theorems.Thm_GroundTheory_Automorphic_Anisotropic_resHom_baseMap
import Theorems.Thm_GroundTheory_Automorphic_Anisotropic_baseMap_baseBasis


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open Module Matrix TensorProduct
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.Anisotropic
variable {K E : Type*} [Field K] [CommRing E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [Fintype κ] [DecidableEq κ] (b : Basis κ K E)
variable (R : Type*) [CommRing R] [Algebra K R] {R' : Type*} [CommRing R'] [Algebra K R']
local notation "𝒩" => Fintype.card (ι × κ)
variable {R}
variable (R)
variable {R}
namespace GroundTheory.Automorphic.Anisotropic
theorem _root_.solution (f : K →ₐ[K] R) (j : κ) :
    (resScalar (ι := ι) b j).map f = resHom b R (Matrix.scalar ι (baseBasis b R j)) := by
  rw [resScalar, ← resHom_baseMap, Matrix.scalar_apply, Matrix.diagonal_map (map_zero _),
    baseMap_baseBasis, Matrix.scalar_apply]
end GroundTheory.Automorphic.Anisotropic
