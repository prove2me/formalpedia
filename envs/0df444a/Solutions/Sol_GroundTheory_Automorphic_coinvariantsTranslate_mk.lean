-- Prove2me | solution 1 for GroundTheory.Automorphic.coinvariantsTranslate_mk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:24:39.315315+00:00
-- url     : https://prove2.me/submissions/1b1ff82f-a30e-4546-abb1-ca8e1fc10237

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Definitions.Def_GroundTheory_AutomorphicForms_InductionJacquet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open Set Filter Topology
variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ G V) (N : Subgroup G)
variable {ρ N}
namespace GroundTheory.Automorphic
theorem _root_.solution {a : G} (ha : ∀ n ∈ N, a * n * a⁻¹ ∈ N) (u : V) :
    coinvariantsTranslate ρ N a ha (Representation.Coinvariants.mk _ u) =
      Representation.Coinvariants.mk _ (ρ a u) := rfl
end GroundTheory.Automorphic
