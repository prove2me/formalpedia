-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Cocycles.cocycle_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:15:27.540807+00:00
-- url     : https://prove2.me/submissions/66b563fb-607d-46d3-9497-76103e7ed129

import Mathlib
import Definitions.Def_ReciprocityTheory_Hypotheses_GalCoh
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_IsUnramifiedOutsideIffLeMaxUnramifiedOutside
import Definitions.Def_GroundTheory_ProfiniteCohomology_ContinuousCochains
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_FiniteContinuousCrossedHomomorphisms
import Theorems.Thm_GlobalTheory_CompanionTheory_Cocycles_mem_cocycleKer

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
theorem _root_.solution (hf : ∀ g h : G, f (g * h) = f g + ρ g (f h)) (g : G) {c : G}
    (hc : c ∈ cocycleKer ρ f hf) : f (g * c) = f g := by
  have hc' := ((mem_cocycleKer hf c).1 hc).2
  rw [hf, hc', map_zero, add_zero]
end GlobalTheory.CompanionTheory.Cocycles
