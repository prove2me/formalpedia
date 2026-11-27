-- Prove2me | solution 1 for GroundTheory.ProfCoh.Involution.tatePair_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:50:24.61433+00:00
-- url     : https://prove2.me/submissions/d7aa62fc-1d01-4b48-935e-24e854063f1f

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_TorsionDualFinite
import Definitions.Def_GroundTheory_ProfiniteCohomology_RealPlaces_InvolutionDuality
import Theorems.Thm_GroundTheory_ProfCoh_Involution_tatePair_injective
import Theorems.Thm_GroundTheory_ProfCoh_Involution_tatePair_flip_injective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open GroundTheory.ProfCoh.Involution
variable {M : Type*} [AddCommGroup M]
variable {σ : M →+ M}
namespace GroundTheory.ProfCoh.Involution
theorem _root_.solution [Finite M] : Function.Bijective (tatePair σ) := by
  have : Finite (tateQuot (dualInv σ) →+ QZ) := Nat.finite_of_card_ne_zero (by
    rw [QZ.card_hom]; exact Nat.card_pos.ne')
  refine (tatePair_injective (σ := σ)).bijective_of_nat_card_le ?_
  rw [QZ.card_hom]
  have h := Nat.card_le_card_of_injective _ (tatePair_flip_injective (σ := σ))
  rwa [QZ.card_hom] at h
end GroundTheory.ProfCoh.Involution
