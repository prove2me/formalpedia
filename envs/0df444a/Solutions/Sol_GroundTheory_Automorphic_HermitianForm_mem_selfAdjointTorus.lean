-- Prove2me | solution 1 for GroundTheory.Automorphic.HermitianForm.mem_selfAdjointTorus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:21:22.469999+00:00
-- url     : https://prove2.me/submissions/22adb72f-e831-474a-919a-3077248c5d50

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
theorem _root_.solution {c : TorusE (γ : V ≃ₗ[E] V)} :
    c ∈ h.selfAdjointTorus γ ↔ h.torusStar γ c = c := Iff.rfl
end GroundTheory.Automorphic.HermitianForm
