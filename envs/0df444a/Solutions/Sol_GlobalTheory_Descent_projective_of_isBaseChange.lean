-- Prove2me | solution 1 for GlobalTheory.Descent.projective_of_isBaseChange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:08:06.125804+00:00
-- url     : https://prove2.me/submissions/b70002df-973d-48a0-8251-17e504db1dd5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SpanSingletonEqTopIffIsUnitOfIsBaseChange
import Theorems.Thm_GlobalTheory_Descent_projective

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
variable {A A' : Type*} [CommRing A] [CommRing A'] [Algebra A A'] [Module.FaithfullyFlat A A']
  {M M' : Type*} [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module A M'] [Module A' M']
  [IsScalarTower A A' M'] {f : M →ₗ[A] M'} (hf : IsBaseChange A' f)
include hf
namespace GlobalTheory.Descent
theorem _root_.solution [Module.Finite A' M'] [Module.Projective A' M'] :
    Module.Projective A M :=
  have := Module.Finite.equiv hf.equiv.symm
  have := Module.Projective.of_equiv hf.equiv.symm
  projective A'
end GlobalTheory.Descent
