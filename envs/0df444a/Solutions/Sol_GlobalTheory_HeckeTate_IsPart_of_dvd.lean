-- Prove2me | solution 1 for GlobalTheory.HeckeTate.IsPart.of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:36:08.221575+00:00
-- url     : https://prove2.me/submissions/c5f65f98-6036-49e6-ae4a-bfde663f63c8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DvdMulOfIdem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.HeckeTate
variable {R : Type} [CommRing R]
namespace GlobalTheory.HeckeTate
namespace IsPart
theorem _root_.solution {P : Ideal R} {N N' e : R} (h : IsPart P N' e) (hN : N ∣ N') : IsPart P N e :=
  ⟨hN.trans h.1, h.2.1, fun q hq hq' hne => h.2.2 q hq (q.mem_of_dvd hN hq') hne⟩
end IsPart
end GlobalTheory.HeckeTate
