-- Prove2me | solution 1 for GroundTheory.ProfCoh.mem_range_restrictScalarsHom_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:24:46.075247+00:00
-- url     : https://prove2.me/submissions/81913d76-842f-4eb0-8b97-dc025fe024ef

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_Ramification

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.ProfCoh
open NumberField IsDedekindDomain
variable {F E M : Type*} [Field F] [Field E] [Field M] [Algebra F E] [Algebra E M] [Algebra F M]
  [IsScalarTower F E M]
namespace GroundTheory.ProfCoh
theorem _root_.solution (σ : Gal(M/F)) :
    σ ∈ (AlgEquiv.restrictScalarsHom F : Gal(M/E) →* Gal(M/F)).range ↔
      ∀ x : E, σ (algebraMap E M x) = algebraMap E M x := by
  constructor
  · rintro ⟨τ, rfl⟩ x
    exact τ.commutes x
  · intro h
    exact ⟨AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) h, AlgEquiv.ext fun _ => rfl⟩
end GroundTheory.ProfCoh
