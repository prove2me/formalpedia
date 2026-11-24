-- Prove2me | solution 1 for GlobalTheory.Descent.finite_of_isBaseChange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:10:48.954296+00:00
-- url     : https://prove2.me/submissions/e17690df-c842-477d-87b3-2e58e00d9d6e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SpanSingletonEqTopIffIsUnitOfIsBaseChange
import Theorems.Thm_GlobalTheory_Descent_finite

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
theorem _root_.solution [Module.Finite A' M'] : Module.Finite A M :=
  have := Module.Finite.equiv hf.equiv.symm
  finite A'
end GlobalTheory.Descent
