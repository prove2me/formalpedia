-- Prove2me | solution 1 for GlobalTheory.LatOrb.mem_stdLat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:21:34.611281+00:00
-- url     : https://prove2.me/submissions/8511554d-c49f-4412-8deb-7ba5c622b526

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemMatLat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LatOrb
open Polynomial Matrix
variable (O : Type) {K : Type} [CommRing O] [Field K] [Algebra O K]
variable {O}
namespace GlobalTheory.LatOrb
theorem _root_.solution {n : ℕ} (v : Fin n → K) : v ∈ stdLat O n ↔ ∀ i, v i ∈ (algebraMap O K).range :=
  Iff.rfl
end GlobalTheory.LatOrb
