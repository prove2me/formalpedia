-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.relVol_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:57:52.328166+00:00
-- url     : https://prove2.me/submissions/063a353e-c896-48dc-858f-00c773dda217

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaAverage

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
open GroundTheory.Automorphic.Parabolic
open Set
variable {G : Type*} [Group G]
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (K₀ : Subgroup G) : relVol K₀ K₀ = 1 := by
  simp [relVol, Subgroup.relIndex_self]
end GroundTheory.Automorphic.Parabolic
