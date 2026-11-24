-- Prove2me | solution 1 for GlobalTheory.LatOrb.matLat_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:37:54.053723+00:00
-- url     : https://prove2.me/submissions/41dd737a-d3b7-4a4e-9810-331f9c80497f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemMatLat
import Theorems.Thm_GlobalTheory_LatOrb_mem_matLat

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
theorem _root_.solution {n : ℕ} (M : Submodule O (Fin n → K)) : matLat O 1 M = M := by
  ext v
  simp [mem_matLat]
end GlobalTheory.LatOrb
