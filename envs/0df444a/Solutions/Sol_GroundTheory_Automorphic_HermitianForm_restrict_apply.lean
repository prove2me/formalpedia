-- Prove2me | solution 1 for GroundTheory.Automorphic.HermitianForm.restrict_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:26:06.610132+00:00
-- url     : https://prove2.me/submissions/4c0cffdc-c0d5-4b82-8dff-cfb9cf16eda7

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianSpaces
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianOrthogonal

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
open Module
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {V V' V'' : Type*} [AddCommGroup V] [Module E V] [AddCommGroup V'] [Module E V']
  [AddCommGroup V''] [Module E V'']
open GroundTheory.Automorphic.HermitianForm
namespace GroundTheory.Automorphic.HermitianForm
theorem _root_.solution (h : HermitianForm F E V) (W W' : Submodule E V)
    (hW : h.IsOrthoCompl W W') (x y : W) :
    (h.restrict W W' hW).toSesq x y = h.toSesq x y := rfl
end GroundTheory.Automorphic.HermitianForm
