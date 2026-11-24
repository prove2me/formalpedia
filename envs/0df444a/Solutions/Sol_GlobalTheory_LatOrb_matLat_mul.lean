-- Prove2me | solution 1 for GlobalTheory.LatOrb.matLat_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:54:09.994832+00:00
-- url     : https://prove2.me/submissions/f859fe6b-0c0e-485e-8f5d-5713f710e954

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
theorem _root_.solution {n : ℕ} (a b : Matrix (Fin n) (Fin n) K) (M : Submodule O (Fin n → K)) :
    matLat O (a * b) M = matLat O a (matLat O b M) := by
  ext v
  simp only [mem_matLat]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨b *ᵥ u, ⟨u, hu, rfl⟩, by rw [Matrix.mulVec_mulVec]⟩
  · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    exact ⟨u, hu, by rw [Matrix.mulVec_mulVec]⟩
end GlobalTheory.LatOrb
