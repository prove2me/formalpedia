-- Prove2me | solution 1 for GroundTheory.Automorphic.unitaryGroupEquivMatrix_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:34:00.898612+00:00
-- url     : https://prove2.me/submissions/f69553d4-2b04-4332-92aa-d89b2baf0dab

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_QuadraticConj
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianSpaces

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open Module Matrix
variable (F E : Type*) [Field F] [CommRing E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable (V : Type*) [AddCommGroup V] [Module E V]
variable {F E V}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace GroundTheory.Automorphic
theorem _root_.solution (h : HermitianForm F E V) (v : Basis ι E V)
    (g : h.unitaryGroup) :
    ((unitaryGroupEquivMatrix h v g : GL ι E) : Matrix ι ι E) =
      LinearMap.toMatrix v v ((g : V ≃ₗ[E] V) : V →ₗ[E] V) :=
  autEquivGL_apply v g
end GroundTheory.Automorphic
