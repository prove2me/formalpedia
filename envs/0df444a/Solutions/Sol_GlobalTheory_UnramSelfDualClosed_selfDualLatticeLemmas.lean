-- Prove2me | solution 1 for GlobalTheory.UnramSelfDualClosed.selfDualLatticeLemmas
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:39:19.070416+00:00
-- url     : https://prove2.me/submissions/60278d39-a1c2-4496-a63e-1f8802a0d084

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_SelfDualLatticeActions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DisjointSpanPerpLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsOfFixedInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SelfDualLatticesUnramifiedPlaceNoHypothesis
import Theorems.Thm_GlobalTheory_SelfDualLatticeCompare_selfDualLattices_iff
import Theorems.Thm_GlobalTheory_UnramSelfDual_selfDualLattices


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.UnramSelfDualClosed
namespace GlobalTheory.UnramSelfDualClosed
theorem _root_.solution : GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeActions.SelfDualLatticeLemmas :=
  GlobalTheory.SelfDualLatticeCompare.selfDualLattices_iff.1 GlobalTheory.UnramSelfDual.selfDualLattices
end GlobalTheory.UnramSelfDualClosed
