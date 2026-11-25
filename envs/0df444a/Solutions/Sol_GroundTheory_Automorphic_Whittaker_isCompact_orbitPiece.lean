-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.isCompact_orbitPiece
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:02:11.63025+00:00
-- url     : https://prove2.me/submissions/1e8588da-7525-46bc-8a23-9fa6deccfdf1

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerLSpace
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerOrbit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Whittaker
open Set Topology MulAction
open scoped Pointwise
variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [TotallyDisconnectedSpace X]
  {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]
  [T2Space H] [TotallyDisconnectedSpace H] [SigmaCompactSpace H]
  [MulAction H X] [ContinuousSMul H X]
omit [T2Space X] [LocallyCompactSpace X] [TotallyDisconnectedSpace X] [IsTopologicalGroup H]
  [LocallyCompactSpace H] [T2Space H] [TotallyDisconnectedSpace H] [SigmaCompactSpace H]
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution {L : Subgroup H} (hL : IsCompact (L : Set H)) (y : X) :
    IsCompact (orbitPiece L y) :=
  hL.image (continuous_id.smul continuous_const)
end GroundTheory.Automorphic.Whittaker
