-- Prove2me | solution 1 for GroundTheory.Automorphic.HermitianForm.mem_unitaryGroup
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:34:00.659071+00:00
-- url     : https://prove2.me/submissions/34866e44-6164-4080-9c77-8aba74baa3fa

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
open GroundTheory.Automorphic.HermitianForm
namespace GroundTheory.Automorphic.HermitianForm
theorem _root_.solution {h : HermitianForm F E V} {g : V ≃ₗ[E] V} :
    g ∈ h.unitaryGroup ↔ ∀ x y, h.toSesq (g x) (g y) = h.toSesq x y := Iff.rfl
end GroundTheory.Automorphic.HermitianForm
