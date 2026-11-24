-- Prove2me | solution 1 for GlobalTheory.PMonE.LinCount.gsum_lin_last
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:32:39.165624+00:00
-- url     : https://prove2.me/submissions/c11c489e-20a6-4dd5-87c8-aa4331a38f52

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdditiveSystemIntegralSolutionCountOfOrderOne
import Theorems.Thm_GlobalTheory_PMonE_LinCount_lin_zero_last
import Theorems.Thm_GlobalTheory_PMonE_LinCount_lin_succ_last

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PMonE GlobalTheory.PMonE.LinCount
open Finset GlobalTheory.PMonE
variable {F : Type*} [NormedField F] {m : Type*} [Fintype m] [DecidableEq m]
namespace GlobalTheory.PMonE.LinCount
theorem _root_.solution (q K E : ℕ) (M : ℕ → Matrix m m F) (x : m → F) (a : m) :
    gsum q E (lin K M) (fun r => x r.2 ^ q ^ (r.1 : ℕ)) (Fin.last K, a) = gsum q (K + E) M x a := by
  simp only [gsum, Finset.sum_apply]
  rw [Finset.sum_range_succ', show K + E + 1 = (K + 1) + E by ring, Finset.sum_range_add, add_comm]
  congr 1
  · rw [lin_zero_last, Finset.sum_range]
    simp
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [lin_succ_last, show k + 1 + K = K + 1 + k by ring]
    congr 1
    funext b
    simp only [Fin.val_last]
    rw [← pow_mul, ← pow_add, show K + (k + 1) = K + 1 + k by ring]
end GlobalTheory.PMonE.LinCount
