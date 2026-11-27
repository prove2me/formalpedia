-- Prove2me | solution 1 for GroundTheory.Global.j_map_residue
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:45:48.064875+00:00
-- url     : https://prove2.me/submissions/0454de39-9af8-4a07-8aec-aa6841a47e23

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_PrimeLocalization
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_GoodReductionAlmostAll

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField IsDedekindDomain IsLocalRing
noncomputable section
variable {L : Type*} [Field L] [NumberField L]
namespace GroundTheory.Global
theorem _root_.solution {R : Type*} [CommRing R] [IsLocalRing R] (W : WeierstrassCurve R)
    [W.IsElliptic] : (W.map (residue R)).j = residue R W.j :=
  W.map_j _
end GroundTheory.Global
