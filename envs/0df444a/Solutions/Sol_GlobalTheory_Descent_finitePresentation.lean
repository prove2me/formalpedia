-- Prove2me | solution 1 for GlobalTheory.Descent.finitePresentation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:26:31.167418+00:00
-- url     : https://prove2.me/submissions/3c14c9e9-bbf6-4163-a043-134c244240ab

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SpanSingletonEqTopIffIsUnitOfIsBaseChange
import Theorems.Thm_GlobalTheory_Descent_finite
import Theorems.Thm_GlobalTheory_Descent_fg_of_baseChange

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
theorem _root_.solution [Module.FinitePresentation A' (A' ⊗[A] M)] :
    Module.FinitePresentation A M := by
  have : Module.Finite A M := finite A'
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' A M
  refine Module.finitePresentation_of_free_of_surjective f hf (fg_of_baseChange A' ?_)
  have hf' : Function.Surjective (f.baseChange A') := LinearMap.lTensor_surjective A' hf
  have hker : (LinearMap.ker f).baseChange A' = LinearMap.ker (f.baseChange A') := by
    have hex : Function.Exact ((LinearMap.ker f).subtype.baseChange A') (f.baseChange A') :=
      lTensor_exact A' (LinearMap.exact_subtype_ker_map f) hf
    exact (LinearMap.exact_iff.mp hex).symm
  rw [hker]
  exact Module.FinitePresentation.fg_ker _ hf'
end GlobalTheory.Descent
