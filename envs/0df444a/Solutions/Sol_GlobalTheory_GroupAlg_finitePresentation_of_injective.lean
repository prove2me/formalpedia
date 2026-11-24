-- Prove2me | solution 1 for GlobalTheory.GroupAlg.finitePresentation_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:06:20.397788+00:00
-- url     : https://prove2.me/submissions/035a090b-a4d2-4ce3-95ed-2d381ed8b33f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FinitePresentationOfInjective
import Theorems.Thm_GlobalTheory_GroupAlg_free_of_injective
import Theorems.Thm_GlobalTheory_GroupAlg_finite_of_finiteIndex

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AddMonoidAlgebra
open GlobalTheory GlobalTheory.GroupAlg
variable (R : Type*) [CommRing R] {X Y : Type*} [AddCommGroup X] [AddCommGroup Y] (u : Y →+ X)
namespace GlobalTheory.GroupAlg
theorem _root_.solution (hu : Function.Injective u) [u.range.FiniteIndex] :
    (mapDomainRingHom R u).FinitePresentation := by
  letI := mapAlgebra R u
  have := free_of_injective R u hu
  have : Module.Finite R[Y] R[X] := finite_of_finiteIndex R u
  have : Module.FinitePresentation R[Y] R[X] := Module.finitePresentation_of_projective _ _
  exact (inferInstance : Algebra.FinitePresentation R[Y] R[X])
end GlobalTheory.GroupAlg
