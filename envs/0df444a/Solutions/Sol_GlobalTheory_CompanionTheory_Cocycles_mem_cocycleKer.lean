-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Cocycles.mem_cocycleKer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:36:29.558915+00:00
-- url     : https://prove2.me/submissions/4ff38947-fcbc-4e32-a122-e150cf80afce

import Mathlib
import Definitions.Def_ReciprocityTheory_Hypotheses_GalCoh
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_IsUnramifiedOutsideIffLeMaxUnramifiedOutside
import Definitions.Def_GroundTheory_ProfiniteCohomology_ContinuousCochains
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_FiniteContinuousCrossedHomomorphisms

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal Formalism.ConjugateSelfDual
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Cocycles
variable {k G V : Type} [CommRing k] [Group G] [AddCommGroup V] [Module k V]
  {ρ : Representation k G V} {f : G → V}
namespace GlobalTheory.CompanionTheory.Cocycles
theorem _root_.solution (hf : ∀ g h : G, f (g * h) = f g + ρ g (f h)) (g : G) :
    g ∈ cocycleKer ρ f hf ↔ ρ g = 1 ∧ f g = 0 := by
  exact Iff.rfl
end GlobalTheory.CompanionTheory.Cocycles
