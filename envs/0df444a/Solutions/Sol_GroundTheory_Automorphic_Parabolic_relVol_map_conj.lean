-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.relVol_map_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:43:27.506889+00:00
-- url     : https://prove2.me/submissions/9f908a4c-52bd-444f-93bd-81866d3201f8

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
theorem _root_.solution (g : G) (K₀ K : Subgroup G) :
    relVol (K₀.map (MulAut.conj g).toMonoidHom) (K.map (MulAut.conj g).toMonoidHom) =
      relVol K₀ K := by
  have hinj : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
  unfold relVol
  rw [Subgroup.relIndex_map_map_of_injective _ _ hinj, Subgroup.relIndex_map_map_of_injective _ _ hinj]
end GroundTheory.Automorphic.Parabolic
