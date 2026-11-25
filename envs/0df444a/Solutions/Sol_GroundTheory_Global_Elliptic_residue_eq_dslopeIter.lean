-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.residue_eq_dslopeIter
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:17:26.995302+00:00
-- url     : https://prove2.me/submissions/e1ab1456-8549-43bc-9f5e-2d8c56c18134

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_Residue
import Theorems.Thm_GroundTheory_Global_Elliptic_dslopeIter_succ
import Theorems.Thm_GroundTheory_Global_Elliptic_swap_dslope_sub_mul
import Theorems.Thm_GroundTheory_Global_Elliptic_meromorphicShift_le
import Theorems.Thm_GroundTheory_Global_Elliptic_analyticAt_pow_mul_of_meromorphicShift_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology Set
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic
namespace GroundTheory.Global.Elliptic
theorem _root_.solution {f : ℂ → ℂ} {p : ℂ} {n : ℕ}
    (hn : AnalyticAt ℂ (fun z ↦ (z - p) ^ (n + 1) * f z) p) :
    residue f p = dslopeIter p n (fun z ↦ (z - p) ^ (n + 1) * f z) p := by
  have hf : MeromorphicAt f p := ⟨n + 1, by simpa [smul_eq_mul] using hn⟩
  set m := meromorphicShift f p with hm
  have step : ∀ j, m ≤ j + 1 →
      dslopeIter p (j + 1) (fun z ↦ (z - p) ^ (j + 1 + 1) * f z) p =
        dslopeIter p j (fun z ↦ (z - p) ^ (j + 1) * f z) p := by
    intro j hj
    have hd : DifferentiableAt ℂ (fun z ↦ (z - p) ^ (j + 1) * f z) p :=
      (analyticAt_pow_mul_of_meromorphicShift_le hf hj).differentiableAt
    rw [dslopeIter_succ]
    have e : (fun z ↦ (z - p) ^ (j + 1 + 1) * f z) =
        fun z ↦ (z - p) * ((z - p) ^ (j + 1) * f z) := by
      funext z; ring
    rw [e, swap_dslope_sub_mul hd]
  have up : ∀ j, m ≤ j →
      dslopeIter p j (fun z ↦ (z - p) ^ (j + 1) * f z) p = residue f p := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => rfl
    | succ j hj ih => rw [step j (by omega), ih]
  have hmn : m ≤ n + 1 := meromorphicShift_le hn
  rcases Nat.lt_or_ge n m with h | h
  · rw [← step n (by omega), up (n + 1) (by omega)]
  · exact (up n h).symm
end GroundTheory.Global.Elliptic
