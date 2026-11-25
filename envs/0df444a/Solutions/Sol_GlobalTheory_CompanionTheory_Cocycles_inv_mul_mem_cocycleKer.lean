-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Cocycles.inv_mul_mem_cocycleKer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:15:29.519289+00:00
-- url     : https://prove2.me/submissions/b3cb6a2f-9ea9-4c92-8a00-3e1dc08d7e70

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
theorem _root_.solution (hf : ∀ g h : G, f (g * h) = f g + ρ g (f h)) {a b : G}
    (h1 : f a = f b) (h2 : ρ a = ρ b) : a⁻¹ * b ∈ cocycleKer ρ f hf := by
  refine (mem_cocycleKer hf _).2 ⟨?_, ?_⟩
  · rw [map_mul, ← h2, ← map_mul, inv_mul_cancel, map_one]
  · rw [hf, cocycle_map_inv hf, h1, neg_add_cancel]
end GlobalTheory.CompanionTheory.Cocycles
