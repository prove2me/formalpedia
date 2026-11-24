-- Prove2me | solution 1 for GlobalTheory.Descent.projective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:46:40.364334+00:00
-- url     : https://prove2.me/submissions/0403c913-84ec-44ac-bcec-fc2bcf72718b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SpanSingletonEqTopIffIsUnitOfIsBaseChange
import Theorems.Thm_GlobalTheory_Descent_flat
import Theorems.Thm_GlobalTheory_Descent_finitePresentation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory
open GlobalTheory.Descent
variable {A : Type*} (A' : Type*) [CommRing A] [CommRing A'] [Algebra A A']
  [Module.FaithfullyFlat A A'] {M : Type*} [AddCommGroup M] [Module A M]
namespace GlobalTheory.Descent
theorem _root_.solution [Module.Finite A' (A' ⊗[A] M)] [Module.Projective A' (A' ⊗[A] M)] :
    Module.Projective A M := by
  have : Module.FinitePresentation A' (A' ⊗[A] M) := Module.finitePresentation_of_projective _ _
  have : Module.FinitePresentation A M := finitePresentation A'
  have : Module.Flat A M := flat A'
  exact Module.Flat.projective_of_finitePresentation
end GlobalTheory.Descent
