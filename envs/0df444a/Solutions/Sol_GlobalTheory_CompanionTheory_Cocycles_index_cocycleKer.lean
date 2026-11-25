-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Cocycles.index_cocycleKer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:25:19.445042+00:00
-- url     : https://prove2.me/submissions/224ba481-7e9e-4143-88ce-fcbf03b92160

import Mathlib
import Definitions.Def_ReciprocityTheory_Hypotheses_GalCoh
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_IsUnramifiedOutsideIffLeMaxUnramifiedOutside
import Definitions.Def_GroundTheory_ProfiniteCohomology_ContinuousCochains
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_FiniteContinuousCrossedHomomorphisms
import Theorems.Thm_GlobalTheory_CompanionTheory_Cocycles_injective_out_cocycleKer

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
theorem _root_.solution [Finite V] (hf : ∀ g h : G, f (g * h) = f g + ρ g (f h)) :
    (cocycleKer ρ f hf).index ≠ 0 ∧
      (cocycleKer ρ f hf).index ≤ Nat.card (V × (V → V)) := by
  have hinj := injective_out_cocycleKer hf
  haveI : Finite (G ⧸ cocycleKer ρ f hf) := Finite.of_injective _ hinj
  exact ⟨Subgroup.index_ne_zero_of_finite, Nat.card_le_card_of_injective _ hinj⟩
end GlobalTheory.CompanionTheory.Cocycles
