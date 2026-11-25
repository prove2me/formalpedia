-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.relVol_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:57:51.627144+00:00
-- url     : https://prove2.me/submissions/d9b21433-88a0-4956-af8c-555a8248a2c5

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
theorem _root_.solution {K₀ K : Subgroup G} (h₁ : K₀.relIndex K ≠ 0) (h₂ : K.relIndex K₀ ≠ 0) :
    0 < relVol K₀ K :=
  div_pos (Nat.cast_pos.2 (Nat.pos_of_ne_zero h₁)) (Nat.cast_pos.2 (Nat.pos_of_ne_zero h₂))
end GroundTheory.Automorphic.Parabolic
