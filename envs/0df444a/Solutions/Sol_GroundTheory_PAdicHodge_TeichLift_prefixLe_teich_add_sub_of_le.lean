-- Prove2me | solution 1 for GroundTheory.PAdicHodge.TeichLift.prefixLe_teich_add_sub_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:03:15.629884+00:00
-- url     : https://prove2.me/submissions/c41095e9-a8f6-46d3-be9e-a81e594c5016

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ExtRobbaTeich
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_PrefixLe_mono
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_le_rpow_mix
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_rpow_mix_le
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_inv_pow_pos_le_one
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_prefixLe_teich_add_sub

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
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
open GroundTheory GroundTheory.PAdicHodge
open Ideal
open GroundTheory.PAdicHodge.TeichLift
variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L] [CharP L p]
  [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ)
namespace GroundTheory.PAdicHodge.TeichLift
theorem _root_.solution {a e : L} {B δ : ℝ} (ha : ‖a‖ ≤ B) (he : ‖e‖ ≤ δ) (hδ : 0 ≤ δ)
    (hδB : δ ≤ B) (k : ℕ) :
    T.PrefixLe (T.teich (a + e) - T.teich a - T.teich e) k
      (B ^ (1 - ((p ^ k : ℕ) : ℝ)⁻¹) * δ ^ ((p ^ k : ℕ) : ℝ)⁻¹) := by
  obtain ⟨ht0, ht1⟩ := inv_pow_pos_le_one (p := p) k
  set t := ((p ^ k : ℕ) : ℝ)⁻¹
  rcases le_total ‖e‖ ‖a‖ with h | h
  · refine (T.prefixLe_teich_add_sub h k).mono ?_
    exact mul_le_mul (Real.rpow_le_rpow (norm_nonneg _) ha (by linarith))
      (Real.rpow_le_rpow (norm_nonneg _) he ht0.le) (Real.rpow_nonneg (norm_nonneg _) _)
      (Real.rpow_nonneg (hδ.trans hδB) _)
  · have := T.prefixLe_teich_add_sub h k
    rw [show T.teich (e + a) - T.teich e - T.teich a = T.teich (a + e) - T.teich a - T.teich e by
      rw [add_comm]; ring] at this
    refine this.mono ?_
    calc ‖e‖ ^ (1 - t) * ‖a‖ ^ t ≤ ‖e‖ := rpow_mix_le (norm_nonneg _) h ht0.le ht1
      _ ≤ δ := he
      _ ≤ B ^ (1 - t) * δ ^ t := le_rpow_mix hδ hδB ht1
end GroundTheory.PAdicHodge.TeichLift
