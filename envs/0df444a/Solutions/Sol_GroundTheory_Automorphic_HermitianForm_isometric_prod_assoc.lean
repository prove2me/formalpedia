-- Prove2me | solution 1 for GroundTheory.Automorphic.HermitianForm.isometric_prod_assoc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:54:29.659135+00:00
-- url     : https://prove2.me/submissions/4cdda9fe-9bc1-41ad-b0f3-887f63d1b4ac

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
theorem _root_.solution (h : HermitianForm F E V) (h' : HermitianForm F E V')
    (h'' : HermitianForm F E V'') :
    Isometric ((h.prod h').prod h'') (h.prod (h'.prod h'')) :=
  ⟨LinearEquiv.prodAssoc E V V' V'', fun p q => by
    show h.toSesq p.1.1 q.1.1 + (h'.toSesq p.1.2 q.1.2 + h''.toSesq p.2 q.2) =
      (h.toSesq p.1.1 q.1.1 + h'.toSesq p.1.2 q.1.2) + h''.toSesq p.2 q.2
    rw [add_assoc]⟩
end GroundTheory.Automorphic.HermitianForm
