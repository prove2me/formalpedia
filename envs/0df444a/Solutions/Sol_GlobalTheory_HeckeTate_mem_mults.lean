-- Prove2me | solution 1 for GlobalTheory.HeckeTate.mem_mults
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:47:37.632823+00:00
-- url     : https://prove2.me/submissions/5bb05a89-adcc-45aa-a4b4-a920a41c3c48

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
variable {R : Type} [CommRing R] {M M' : Type} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
namespace GlobalTheory.HeckeTate
theorem _root_.solution {N : R} {x : M} : x ∈ mults M N ↔ ∃ y, x = N • y := by
  simp [mults, eq_comm]
end GlobalTheory.HeckeTate
