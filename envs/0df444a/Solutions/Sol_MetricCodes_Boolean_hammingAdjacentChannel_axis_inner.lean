-- Prove2me | solution 1 for MetricCodes.Boolean.hammingAdjacentChannel_axis_inner
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:27.702855+00:00
-- url     : https://prove2.me/submissions/8547d35f-e103-48dd-8ad5-96fd05f4d2fc

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Boolean_twist_smul
import Theorems.Thm_MetricCodes_Boolean_hammingSourceChannelCoefficient_eq_zero_of_not_adjacent
import Theorems.Thm_MetricCodes_Boolean_coordinateDot_deleteChannel_hammingAxisTensor
import Theorems.Thm_MetricCodes_Boolean_coordinateDot_addChannel_hammingAxisTensor
import Theorems.Thm_MetricCodes_Boolean_hammingSourceChannelCoefficient_sqrt_deletion
import Theorems.Thm_MetricCodes_Boolean_hammingSourceChannelCoefficient_sqrt_insertion

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
noncomputable section
open scoped BigOperators Matrix
open MetricCodes.Boolean
variable {n : ℕ}
namespace MetricCodes.Boolean
theorem _root_.solution
    {n k L : ℕ} (hn : 0 < n)
    (hkL : k ≤ L) (hLn : L + k ≤ n)
    (x : BinaryWord n)
    (target source : Fin (L - k + 1))
    (f h : Function n) (hh : IsHarmonic k h) :
    coordinateDot
      (hammingAdjacentChannel n k L target source f)
      (hammingAxisTensor x (wordHarmonicEmbedding x k target.val h)) =
      Real.sqrt (hammingSourceChannelCoefficient n k L source target) *
        dot f (wordHarmonicEmbedding x k source.val h) := by
  classical
  have hs := source.isLt
  have ht := target.isLt
  by_cases hdelete : target.val + 1 = source.val
  · simp only [hammingAdjacentChannel, hdelete, ↓reduceIte]
    unfold wordHarmonicEmbedding
    rw [coordinateDot_deleteChannel_hammingAxisTensor]
    rw [raise_harmonicEmbedding h target.val (by omega),
      twist_smul, dot_smul_right,
      hammingSourceChannelCoefficient_sqrt_deletion
        hn hkL hLn source target hdelete]
    have hval : target.val + 1 = source.val := hdelete
    rw [hval]
    simp only [Nat.cast_add]
    ring
  · by_cases hadd : source.val + 1 = target.val
    · simp only [hammingAdjacentChannel, hdelete,
        hadd, ↓reduceIte]
      unfold wordHarmonicEmbedding
      rw [coordinateDot_addChannel_hammingAxisTensor]
      have hval : target.val = source.val + 1 := by omega
      rw [hval,
        lower_harmonicEmbedding h hh source.val (by omega),
        twist_smul, dot_smul_right,
        hammingSourceChannelCoefficient_sqrt_insertion
          hn hkL hLn source target hadd]
      rw [hval]
      simp only [Nat.cast_add]
      ring
    · have hzero :=
        hammingSourceChannelCoefficient_eq_zero_of_not_adjacent
          n k L source target (by tauto)
      simp [hammingAdjacentChannel, hdelete, hadd,
        hammingAxisTensor, coordinateDot, dot, hzero]
end MetricCodes.Boolean
