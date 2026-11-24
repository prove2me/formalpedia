-- Prove2me | solution 1 for GroundTheory.PAdicHodge.Ideal.adicTopology_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:42:34.058808+00:00
-- url     : https://prove2.me/submissions/ccbc4c77-223d-4798-899c-adeb478aab1a

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow
import Definitions.Def_GroundTheory_PAdicHodge_AInfTopology

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
open WittVector Filter Topology
open GroundTheory GroundTheory.PAdicHodge
namespace GroundTheory.PAdicHodge
namespace Ideal
theorem _root_.solution {A : Type*} [CommRing A] {I J : Ideal A} (h : I ≤ J) :
    I.adicTopology ≤ J.adicTopology := by
  rw [le_iff_nhds]
  intro x
  rw [(J.hasBasis_nhds_adic x).ge_iff]
  intro n _
  exact (I.hasBasis_nhds_adic x).mem_iff.2 ⟨n, trivial, Set.image_mono (Ideal.pow_right_mono h n)⟩
end Ideal
end GroundTheory.PAdicHodge
