-- Prove2me | solution 1 for GroundTheory.ProfCoh.restrictScalars_mem_inertia_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:25:32.624321+00:00
-- url     : https://prove2.me/submissions/b494ae61-e5d5-44ae-9058-b8d08baeab93

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
theorem _root_.solution (Q : Ideal (𝓞 M)) (σ : Gal(M/E)) :
    AlgEquiv.restrictScalarsHom F σ ∈ Q.inertia Gal(M/F) ↔ σ ∈ Q.inertia Gal(M/E) :=
  Iff.rfl
end GroundTheory.ProfCoh
