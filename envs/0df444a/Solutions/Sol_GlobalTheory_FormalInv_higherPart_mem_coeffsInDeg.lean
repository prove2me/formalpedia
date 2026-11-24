-- Prove2me | solution 1 for GlobalTheory.FormalInv.higherPart_mem_coeffsInDeg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:11:54.240825+00:00
-- url     : https://prove2.me/submissions/448a0d22-12a2-4cdb-b74d-1acba32b436f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_CoeffSubstInvMemOfTwoLeOrder
import Theorems.Thm_GlobalTheory_FormalInv_mem_coeffsInDeg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries Finsupp
noncomputable section
open GlobalTheory GlobalTheory.FormalInv
variable {σ τ υ ι : Type*} {R : Type*} [CommRing R]
namespace GlobalTheory.FormalInv
theorem _root_.solution [Fintype σ] {u : ι → MvPowerSeries σ R} {i : ι}
    (hu : constantCoeff (u i) = 0) {S : Subring R} {g : ℕ} (huS : u i ∈ coeffsInDeg σ S g) :
    higherPart u i ∈ coeffsInDeg σ S g := by
  classical
  rw [mem_coeffsInDeg] at huS ⊢
  intro d hd
  by_cases h2 : d.degree < 2
  · rw [mem_degGe.1 (higherPart_mem_degGe hu) d h2]; exact S.zero_mem
  · have : ∀ j, d ≠ single j 1 := by rintro j rfl; simp at h2
    simpa [higherPart, coeff_X, this] using huS d hd
end GlobalTheory.FormalInv
