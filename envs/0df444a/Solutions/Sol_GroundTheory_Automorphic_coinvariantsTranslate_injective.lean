-- Prove2me | solution 1 for GroundTheory.Automorphic.coinvariantsTranslate_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:14:46.398118+00:00
-- url     : https://prove2.me/submissions/868301fd-a7c7-47d3-ba5f-6e6496374878

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Definitions.Def_GroundTheory_AutomorphicForms_InductionJacquet
import Theorems.Thm_GroundTheory_Automorphic_coinvariantsTranslate_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.coinvariantsTranslate_mk

set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open Set Filter Topology
variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ G V) (N : Subgroup G)
variable {ρ N}
namespace GroundTheory.Automorphic
theorem _root_.solution {a : G} (ha : ∀ n ∈ N, a * n * a⁻¹ ∈ N)
    (ha' : ∀ n ∈ N, a⁻¹ * n * a ∈ N) :
    Function.Injective (coinvariantsTranslate ρ N a ha) := by
  have ha'' : ∀ n ∈ N, a⁻¹ * n * a⁻¹⁻¹ ∈ N := fun n hn => by simpa using ha' n hn
  refine Function.LeftInverse.injective (g := coinvariantsTranslate ρ N a⁻¹ ha'') fun u => ?_
  obtain ⟨u, rfl⟩ := Representation.Coinvariants.mk_surjective _ u
  rw [coinvariantsTranslate_mk, coinvariantsTranslate_mk, ← Module.End.mul_apply, ← map_mul,
    inv_mul_cancel, map_one, Module.End.one_apply]
end GroundTheory.Automorphic
