-- Prove2me | solution 1 for GroundTheory.Automorphic.HermitianForm.inKernel_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:22:21.595955+00:00
-- url     : https://prove2.me/submissions/f141b7c1-5fe4-4bc8-8c08-f4660f26407d

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_StableConjTorus
import Definitions.Def_GroundTheory_AutomorphicForms_StableConjInvariant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open Module
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {V : Type*} [AddCommGroup V] [Module E V] [FiniteDimensional E V]
open GroundTheory.Automorphic.HermitianForm
variable (h : HermitianForm F E V)
variable (γ : h.unitaryGroup) [Fact (IsRegularSemisimple (γ : V ≃ₗ[E] V))]
namespace GroundTheory.Automorphic.HermitianForm
theorem _root_.solution (c : h.selfAdjointTorus γ) :
    h.InKernel γ (QuotientGroup.mk c) ↔ Isometric (h.twistOf γ c) h := Iff.rfl
end GroundTheory.Automorphic.HermitianForm
