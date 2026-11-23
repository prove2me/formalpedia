-- Prove2me | solution 1 for GlobalTheory.LatOrb.mem_matLat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:05:09.16731+00:00
-- url     : https://prove2.me/submissions/db572d36-fcce-483b-a960-6ac5b3f47645

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
theorem _root_.solution {n : ℕ} (g : Matrix (Fin n) (Fin n) K) (M : Submodule O (Fin n → K))
    (v : Fin n → K) : v ∈ matLat O g M ↔ ∃ u ∈ M, g *ᵥ u = v := by
  simp [matLat]
end GlobalTheory.LatOrb
