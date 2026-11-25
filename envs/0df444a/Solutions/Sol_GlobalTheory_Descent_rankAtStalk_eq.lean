-- Prove2me | solution 1 for GlobalTheory.Descent.rankAtStalk_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:38:39.323818+00:00
-- url     : https://prove2.me/submissions/d6a8e7e8-ef32-47b2-8ed8-6bd7012f3e6b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SpanSingletonEqTopIffIsUnitOfIsBaseChange
import Theorems.Thm_GlobalTheory_Descent_finite
import Theorems.Thm_GlobalTheory_Descent_flat

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
theorem _root_.solution [Module.Finite A' (A' ⊗[A] M)] [Module.Flat A' (A' ⊗[A] M)] {r : ℕ}
    (h : ∀ q : PrimeSpectrum A', Module.rankAtStalk (A' ⊗[A] M) q = r) (p : PrimeSpectrum A) :
    Module.rankAtStalk M p = r := by
  have : Module.Finite A M := finite A'
  have : Module.Flat A M := flat A'
  obtain ⟨q, rfl⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := A) (B := A') p
  rw [← Module.rankAtStalk_baseChange, h]
end GlobalTheory.Descent
