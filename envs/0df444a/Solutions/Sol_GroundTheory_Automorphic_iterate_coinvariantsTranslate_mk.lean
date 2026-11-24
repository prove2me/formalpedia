-- Prove2me | solution 1 for GroundTheory.Automorphic.iterate_coinvariantsTranslate_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:14:48.309052+00:00
-- url     : https://prove2.me/submissions/fa817f50-16a6-4c20-a894-a7833af75f13

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
theorem _root_.solution {a : G} (ha : ∀ n ∈ N, a * n * a⁻¹ ∈ N) (m : ℕ)
    (u : V) :
    (coinvariantsTranslate ρ N a ha)^[m] (Representation.Coinvariants.mk _ u) =
      Representation.Coinvariants.mk _ (ρ (a ^ m) u) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih, coinvariantsTranslate_mk, pow_succ', map_mul,
      Module.End.mul_apply]
end GroundTheory.Automorphic
