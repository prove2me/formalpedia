-- Prove2me | solution 1 for GlobalTheory.LGrowth.mellin_summatory
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:44:29.267396+00:00
-- url     : https://prove2.me/submissions/91f9e88f-f66c-4230-b50c-0b9e3d92d46b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DifferentiableAtMellinSummatory
import Theorems.Thm_GlobalTheory_LGrowth_summatory_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory GlobalTheory.LGrowth
open Filter Topology Asymptotics
variable {f : ℕ → ℂ} {C : ℝ}
namespace GlobalTheory.LGrowth
theorem _root_.solution (s : ℂ) :
    mellin (summatory f) (-s) =
      ∫ t in Set.Ioi (1 : ℝ), (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ (-(s + 1)) := by
  rw [mellin, setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ioi
    (s := Set.Ici (1 : ℝ)) (fun t ht => Set.mem_Ioi.2 (zero_lt_one.trans_le (Set.mem_Ici.1 ht))), integral_Ici_eq_integral_Ioi]
  · refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp only [summatory, smul_eq_mul]
    rw [mul_comm]
    congr 2
    ring
  · intro t ht
    rw [summatory_eq_zero (not_le.1 ht.2), smul_zero]
end GlobalTheory.LGrowth
