-- Prove2me | solution 1 for GroundTheory.Automorphic.frobenius_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:25:03.386277+00:00
-- url     : https://prove2.me/submissions/193ea48a-fbfa-4a8b-9ea1-d1a2a2f64f92

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
theorem _root_.solution (hπ : IsSmooth π) (Φ : Representation.IntertwiningMap π (indRep H σ))
    (v : V) : frobenius H σ hπ Φ v = (Φ v : G → W) 1 := rfl
end GroundTheory.Automorphic
