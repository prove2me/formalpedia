-- Prove2me | solution 1 for GroundTheory.Automorphic.HermitianForm.mem_orthogonal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:54:30.459127+00:00
-- url     : https://prove2.me/submissions/620a8183-f25c-4d00-b9bf-70906e7e493b

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianOrthogonal
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianWitt

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
variable {V V₁ V₂ : Type*} [AddCommGroup V] [Module E V] [AddCommGroup V₁] [Module E V₁]
  [AddCommGroup V₂] [Module E V₂]
open GroundTheory.Automorphic.HermitianForm
namespace GroundTheory.Automorphic.HermitianForm
theorem _root_.solution (h : HermitianForm F E V) (U : Submodule E V) (y : V) :
    y ∈ h.orthogonal U ↔ ∀ x ∈ U, h.toSesq x y = 0 := Iff.rfl
end GroundTheory.Automorphic.HermitianForm
