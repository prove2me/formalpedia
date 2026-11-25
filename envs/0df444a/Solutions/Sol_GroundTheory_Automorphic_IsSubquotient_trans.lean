-- Prove2me | solution 1 for GroundTheory.Automorphic.IsSubquotient.trans
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:11:08.653647+00:00
-- url     : https://prove2.me/submissions/072872aa-efee-4428-b5f6-f3260c635bdb

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteLengthLattice
import Definitions.Def_GroundTheory_AutomorphicForms_JacquetAdmissible
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteLengthSubquotient
import Theorems.Thm_GroundTheory_Automorphic_IsSubquotient_of_injective_of_surjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Automorphic
open Function Parabolic
universe u
variable {G : Type*} [Group G] {V W U : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
  [Module ℂ W] [AddCommGroup U] [Module ℂ U]
variable {π : Representation ℂ G W} {ρ : Representation ℂ G V} {θ : Representation ℂ G U}
namespace GroundTheory.Automorphic
namespace IsSubquotient
theorem _root_.solution (h₁ : IsSubquotient π ρ) (h₂ : IsSubquotient ρ θ) :
    IsSubquotient π θ := by
  obtain ⟨C, p, hp⟩ := h₁
  obtain ⟨D, q, hq⟩ := h₂

  let E : Subrepresentation D.toRepresentation := subrepComap q C
  let qE : E.toSubmodule →ₗ[ℂ] C.toSubmodule :=
    { toFun := fun e => ⟨q e, e.2⟩
      map_add' := fun _ _ => Subtype.ext (map_add q _ _)
      map_smul' := fun _ _ => Subtype.ext (map_smul q _ _) }
  refine .of_injective_of_surjective ((subrepInclusion D).comp (subrepInclusion E))
    (fun x y h => Subtype.ext (Subtype.ext h))
    (p.comp ⟨qE, fun g => LinearMap.ext fun e =>
        Subtype.ext (Representation.IntertwiningMap.isIntertwining _ _ q g e)⟩) ?_
  intro y
  obtain ⟨c, rfl⟩ := hp y
  obtain ⟨d, hd⟩ := hq c
  exact ⟨⟨d, show q d ∈ C from hd ▸ c.2⟩, by
    show p ⟨q d, _⟩ = p c
    congr 1
    exact Subtype.ext hd⟩
end IsSubquotient
end GroundTheory.Automorphic
