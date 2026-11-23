-- Prove2me | solution 1 for GroundTheory.Automorphic.matrixCoords_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:09:55.162785+00:00
-- url     : https://prove2.me/submissions/66d6f216-88ea-43ec-a0c4-25560f8f3041

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryGroupScheme
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryGroupEquations
import Theorems.Thm_GroundTheory_Automorphic_matrixCoords_apply
import Theorems.Thm_GroundTheory_Automorphic_repr_tensorMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open Module Matrix TensorProduct
variable {F E : Type*} [Field F] [CommRing E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [Fintype κ] (b : Basis κ F E)
variable (R : Type*) [CommRing R] [Algebra F R] {S : Type*} [CommRing S] [Algebra F S]
variable {R}
omit [Algebra.IsQuadraticExtension F E] [Fintype ι] [DecidableEq ι]
namespace GroundTheory.Automorphic
theorem _root_.solution (f : R →ₐ[F] S) (g : Matrix ι ι (R ⊗[F] E)) :
    matrixCoords b S (g.map (tensorMap E f)) = f ∘ matrixCoords b R g := by
  funext ⟨i, j, k⟩
  rw [Function.comp_apply, matrixCoords_apply, matrixCoords_apply, Matrix.map_apply, repr_tensorMap]
end GroundTheory.Automorphic
