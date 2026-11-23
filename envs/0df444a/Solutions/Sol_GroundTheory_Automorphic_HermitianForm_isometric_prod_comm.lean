-- Prove2me | solution 1 for GroundTheory.Automorphic.HermitianForm.isometric_prod_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:56:54.773461+00:00
-- url     : https://prove2.me/submissions/75f7c990-5c34-4d14-b405-f44a78974eb6

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
theorem _root_.solution (h : HermitianForm F E V) (h' : HermitianForm F E V') :
    Isometric (h.prod h') (h'.prod h) :=
  ⟨LinearEquiv.prodComm E V V', fun p q => by
    show h'.toSesq p.2 q.2 + h.toSesq p.1 q.1 = h.toSesq p.1 q.1 + h'.toSesq p.2 q.2
    rw [add_comm]⟩
end GroundTheory.Automorphic.HermitianForm
