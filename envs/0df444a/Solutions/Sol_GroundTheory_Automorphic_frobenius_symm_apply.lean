-- Prove2me | solution 1 for GroundTheory.Automorphic.frobenius_symm_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:24:33.494308+00:00
-- url     : https://prove2.me/submissions/2aaff639-4189-4ad4-9907-8f195e83f555

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Definitions.Def_GroundTheory_AutomorphicForms_Induction

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
open Set Filter Topology Pointwise
variable {G : Type*} [Group G] [TopologicalSpace G] (H : Subgroup G)
  {W : Type*} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ H W)
variable [IsTopologicalGroup G]
variable {V : Type*} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V)
variable {π}
namespace GroundTheory.Automorphic
theorem _root_.solution (hπ : IsSmooth π)
    (φ : Representation.IntertwiningMap (π.comp H.subtype) σ) (v : V) (g : G) :
    ((frobenius H σ hπ).symm φ v : G → W) g = φ (π g v) := rfl
end GroundTheory.Automorphic
