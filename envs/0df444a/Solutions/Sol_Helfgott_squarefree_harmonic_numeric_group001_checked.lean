-- Prove2me | solution 1 for Helfgott.squarefree_harmonic_numeric_group001_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-08T23:51:49.344935+00:00
-- url     : https://prove2.me/submissions/b90381d3-6018-422c-a4fe-a22dac60ab38

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
open Finset Nat
open scoped BigOperators
namespace Helfgott

private theorem squarefreeInitCount_5120_5184 : (∑ n ∈ Ico 5120 5184, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (39 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_5184_5248 : (∑ n ∈ Ico 5184 5248, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (37 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_5120_5248 : (∑ n ∈ Ico 5120 5248, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (76 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 5120 5184, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 5184 5248, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 5120 ≤ 5184) (by norm_num : 5184 ≤ 5248)).symm
    _ = (39 : ℤ) + (37 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_5120_5184 squarefreeInitCount_5184_5248
    _ = (76 : ℤ) := by norm_num

private theorem squarefreeInitCount_5248_5312 : (∑ n ∈ Ico 5248 5312, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (40 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_5312_5376 : (∑ n ∈ Ico 5312 5376, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (38 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_5248_5376 : (∑ n ∈ Ico 5248 5376, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (78 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 5248 5312, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 5312 5376, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 5248 ≤ 5312) (by norm_num : 5312 ≤ 5376)).symm
    _ = (40 : ℤ) + (38 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_5248_5312 squarefreeInitCount_5312_5376
    _ = (78 : ℤ) := by norm_num

private theorem squarefreeInitCount_5120_5376 : (∑ n ∈ Ico 5120 5376, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (154 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 5120 5248, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 5248 5376, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 5120 ≤ 5248) (by norm_num : 5248 ≤ 5376)).symm
    _ = (76 : ℤ) + (78 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_5120_5248 squarefreeInitCount_5248_5376
    _ = (154 : ℤ) := by norm_num

private theorem squarefreeInitCount_5376_5440 : (∑ n ∈ Ico 5376 5440, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (39 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_5440_5504 : (∑ n ∈ Ico 5440 5504, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (39 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_5376_5504 : (∑ n ∈ Ico 5376 5504, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (78 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 5376 5440, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 5440 5504, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 5376 ≤ 5440) (by norm_num : 5440 ≤ 5504)).symm
    _ = (39 : ℤ) + (39 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_5376_5440 squarefreeInitCount_5440_5504
    _ = (78 : ℤ) := by norm_num

private theorem squarefreeInitCount_5504_5568 : (∑ n ∈ Ico 5504 5568, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (38 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_5568_5632 : (∑ n ∈ Ico 5568 5632, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (39 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_5504_5632 : (∑ n ∈ Ico 5504 5632, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (77 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 5504 5568, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 5568 5632, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 5504 ≤ 5568) (by norm_num : 5568 ≤ 5632)).symm
    _ = (38 : ℤ) + (39 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_5504_5568 squarefreeInitCount_5568_5632
    _ = (77 : ℤ) := by norm_num

private theorem squarefreeInitCount_5376_5632 : (∑ n ∈ Ico 5376 5632, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (155 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 5376 5504, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 5504 5632, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 5376 ≤ 5504) (by norm_num : 5504 ≤ 5632)).symm
    _ = (78 : ℤ) + (77 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_5376_5504 squarefreeInitCount_5504_5632
    _ = (155 : ℤ) := by norm_num

theorem squarefreeInitCount_5120_5632 : (∑ n ∈ Ico 5120 5632, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (309 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 5120 5376, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 5376 5632, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 5120 ≤ 5376) (by norm_num : 5376 ≤ 5632)).symm
    _ = (154 : ℤ) + (155 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_5120_5376 squarefreeInitCount_5376_5632
    _ = (309 : ℤ) := by norm_num

private theorem squarefreeInitUpper_5120_5184 : (∑ n ∈ Ico 5120 5184, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (7588 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_5184_5248 : (∑ n ∈ Ico 5184 5248, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (7113 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_5120_5248 : (∑ n ∈ Ico 5120 5248, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (14701 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 5120 5184, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 5184 5248, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 5120 ≤ 5184) (by norm_num : 5184 ≤ 5248)).symm
    _ = (7588 : ℕ) + (7113 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_5120_5184 squarefreeInitUpper_5184_5248
    _ = (14701 : ℕ) := by norm_num

private theorem squarefreeInitUpper_5248_5312 : (∑ n ∈ Ico 5248 5312, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (7598 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_5312_5376 : (∑ n ∈ Ico 5312 5376, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (7132 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_5248_5376 : (∑ n ∈ Ico 5248 5376, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (14730 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 5248 5312, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 5312 5376, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 5248 ≤ 5312) (by norm_num : 5312 ≤ 5376)).symm
    _ = (7598 : ℕ) + (7132 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_5248_5312 squarefreeInitUpper_5312_5376
    _ = (14730 : ℕ) := by norm_num

private theorem squarefreeInitUpper_5120_5376 : (∑ n ∈ Ico 5120 5376, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (29431 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 5120 5248, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 5248 5376, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 5120 ≤ 5248) (by norm_num : 5248 ≤ 5376)).symm
    _ = (14701 : ℕ) + (14730 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_5120_5248 squarefreeInitUpper_5248_5376
    _ = (29431 : ℕ) := by norm_num

private theorem squarefreeInitUpper_5376_5440 : (∑ n ∈ Ico 5376 5440, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (7231 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_5440_5504 : (∑ n ∈ Ico 5440 5504, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (7145 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_5376_5504 : (∑ n ∈ Ico 5376 5504, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (14376 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 5376 5440, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 5440 5504, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 5376 ≤ 5440) (by norm_num : 5440 ≤ 5504)).symm
    _ = (7231 : ℕ) + (7145 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_5376_5440 squarefreeInitUpper_5440_5504
    _ = (14376 : ℕ) := by norm_num

private theorem squarefreeInitUpper_5504_5568 : (∑ n ∈ Ico 5504 5568, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (6885 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_5568_5632 : (∑ n ∈ Ico 5568 5632, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (6982 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_5504_5632 : (∑ n ∈ Ico 5504 5632, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (13867 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 5504 5568, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 5568 5632, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 5504 ≤ 5568) (by norm_num : 5568 ≤ 5632)).symm
    _ = (6885 : ℕ) + (6982 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_5504_5568 squarefreeInitUpper_5568_5632
    _ = (13867 : ℕ) := by norm_num

private theorem squarefreeInitUpper_5376_5632 : (∑ n ∈ Ico 5376 5632, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (28243 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 5376 5504, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 5504 5632, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 5376 ≤ 5504) (by norm_num : 5504 ≤ 5632)).symm
    _ = (14376 : ℕ) + (13867 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_5376_5504 squarefreeInitUpper_5504_5632
    _ = (28243 : ℕ) := by norm_num

theorem squarefreeInitUpper_5120_5632 : (∑ n ∈ Ico 5120 5632, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (57674 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 5120 5376, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 5376 5632, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 5120 ≤ 5376) (by norm_num : 5376 ≤ 5632)).symm
    _ = (29431 : ℕ) + (28243 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_5120_5376 squarefreeInitUpper_5376_5632
    _ = (57674 : ℕ) := by norm_num

end Helfgott
end

section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
open Finset Nat
open scoped BigOperators
namespace Helfgott

private theorem squarefreeInitCount_5632_5696 : (∑ n ∈ Ico 5632 5696, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (39 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_5696_5760 : (∑ n ∈ Ico 5696 5760, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (39 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_5632_5760 : (∑ n ∈ Ico 5632 5760, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (78 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 5632 5696, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 5696 5760, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 5632 ≤ 5696) (by norm_num : 5696 ≤ 5760)).symm
    _ = (39 : ℤ) + (39 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_5632_5696 squarefreeInitCount_5696_5760
    _ = (78 : ℤ) := by norm_num

private theorem squarefreeInitCount_5760_5824 : (∑ n ∈ Ico 5760 5824, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (38 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_5824_5888 : (∑ n ∈ Ico 5824 5888, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (39 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_5760_5888 : (∑ n ∈ Ico 5760 5888, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (77 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 5760 5824, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 5824 5888, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 5760 ≤ 5824) (by norm_num : 5824 ≤ 5888)).symm
    _ = (38 : ℤ) + (39 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_5760_5824 squarefreeInitCount_5824_5888
    _ = (77 : ℤ) := by norm_num

private theorem squarefreeInitCount_5632_5888 : (∑ n ∈ Ico 5632 5888, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (155 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 5632 5760, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 5760 5888, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 5632 ≤ 5760) (by norm_num : 5760 ≤ 5888)).symm
    _ = (78 : ℤ) + (77 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_5632_5760 squarefreeInitCount_5760_5888
    _ = (155 : ℤ) := by norm_num

private theorem squarefreeInitCount_5888_5952 : (∑ n ∈ Ico 5888 5952, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (39 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_5952_6016 : (∑ n ∈ Ico 5952 6016, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (41 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_5888_6016 : (∑ n ∈ Ico 5888 6016, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (80 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 5888 5952, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 5952 6016, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 5888 ≤ 5952) (by norm_num : 5952 ≤ 6016)).symm
    _ = (39 : ℤ) + (41 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_5888_5952 squarefreeInitCount_5952_6016
    _ = (80 : ℤ) := by norm_num

private theorem squarefreeInitCount_6016_6080 : (∑ n ∈ Ico 6016 6080, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (38 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_6080_6144 : (∑ n ∈ Ico 6080 6144, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (41 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_6016_6144 : (∑ n ∈ Ico 6016 6144, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (79 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 6016 6080, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 6080 6144, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 6016 ≤ 6080) (by norm_num : 6080 ≤ 6144)).symm
    _ = (38 : ℤ) + (41 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_6016_6080 squarefreeInitCount_6080_6144
    _ = (79 : ℤ) := by norm_num

private theorem squarefreeInitCount_5888_6144 : (∑ n ∈ Ico 5888 6144, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (159 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 5888 6016, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 6016 6144, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 5888 ≤ 6016) (by norm_num : 6016 ≤ 6144)).symm
    _ = (80 : ℤ) + (79 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_5888_6016 squarefreeInitCount_6016_6144
    _ = (159 : ℤ) := by norm_num

theorem squarefreeInitCount_5632_6144 : (∑ n ∈ Ico 5632 6144, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (314 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 5632 5888, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 5888 6144, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 5632 ≤ 5888) (by norm_num : 5888 ≤ 6144)).symm
    _ = (155 : ℤ) + (159 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_5632_5888 squarefreeInitCount_5888_6144
    _ = (314 : ℤ) := by norm_num

private theorem squarefreeInitUpper_5632_5696 : (∑ n ∈ Ico 5632 5696, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (6903 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_5696_5760 : (∑ n ∈ Ico 5696 5760, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (6830 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_5632_5760 : (∑ n ∈ Ico 5632 5760, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (13733 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 5632 5696, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 5696 5760, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 5632 ≤ 5696) (by norm_num : 5696 ≤ 5760)).symm
    _ = (6903 : ℕ) + (6830 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_5632_5696 squarefreeInitUpper_5696_5760
    _ = (13733 : ℕ) := by norm_num

private theorem squarefreeInitUpper_5760_5824 : (∑ n ∈ Ico 5760 5824, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (6580 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_5824_5888 : (∑ n ∈ Ico 5824 5888, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (6682 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_5760_5888 : (∑ n ∈ Ico 5760 5888, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (13262 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 5760 5824, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 5824 5888, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 5760 ≤ 5824) (by norm_num : 5824 ≤ 5888)).symm
    _ = (6580 : ℕ) + (6682 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_5760_5824 squarefreeInitUpper_5824_5888
    _ = (13262 : ℕ) := by norm_num

private theorem squarefreeInitUpper_5632_5888 : (∑ n ∈ Ico 5632 5888, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (26995 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 5632 5760, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 5760 5888, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 5632 ≤ 5760) (by norm_num : 5760 ≤ 5888)).symm
    _ = (13733 : ℕ) + (13262 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_5632_5760 squarefreeInitUpper_5760_5888
    _ = (26995 : ℕ) := by norm_num

private theorem squarefreeInitUpper_5888_5952 : (∑ n ∈ Ico 5888 5952, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (6610 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_5952_6016 : (∑ n ∈ Ico 5952 6016, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (6869 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_5888_6016 : (∑ n ∈ Ico 5888 6016, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (13479 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 5888 5952, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 5952 6016, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 5888 ≤ 5952) (by norm_num : 5952 ≤ 6016)).symm
    _ = (6610 : ℕ) + (6869 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_5888_5952 squarefreeInitUpper_5952_6016
    _ = (13479 : ℕ) := by norm_num

private theorem squarefreeInitUpper_6016_6080 : (∑ n ∈ Ico 6016 6080, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (6301 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_6080_6144 : (∑ n ∈ Ico 6080 6144, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (6731 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_6016_6144 : (∑ n ∈ Ico 6016 6144, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (13032 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 6016 6080, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 6080 6144, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 6016 ≤ 6080) (by norm_num : 6080 ≤ 6144)).symm
    _ = (6301 : ℕ) + (6731 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_6016_6080 squarefreeInitUpper_6080_6144
    _ = (13032 : ℕ) := by norm_num

private theorem squarefreeInitUpper_5888_6144 : (∑ n ∈ Ico 5888 6144, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (26511 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 5888 6016, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 6016 6144, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 5888 ≤ 6016) (by norm_num : 6016 ≤ 6144)).symm
    _ = (13479 : ℕ) + (13032 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_5888_6016 squarefreeInitUpper_6016_6144
    _ = (26511 : ℕ) := by norm_num

theorem squarefreeInitUpper_5632_6144 : (∑ n ∈ Ico 5632 6144, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (53506 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 5632 5888, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 5888 6144, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 5632 ≤ 5888) (by norm_num : 5888 ≤ 6144)).symm
    _ = (26995 : ℕ) + (26511 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_5632_5888 squarefreeInitUpper_5888_6144
    _ = (53506 : ℕ) := by norm_num

end Helfgott
end

section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
open Finset Nat
open scoped BigOperators
namespace Helfgott

private theorem squarefreeInitCount_6144_6208 : (∑ n ∈ Ico 6144 6208, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (40 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_6208_6272 : (∑ n ∈ Ico 6208 6272, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (38 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_6144_6272 : (∑ n ∈ Ico 6144 6272, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (78 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 6144 6208, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 6208 6272, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 6144 ≤ 6208) (by norm_num : 6208 ≤ 6272)).symm
    _ = (40 : ℤ) + (38 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_6144_6208 squarefreeInitCount_6208_6272
    _ = (78 : ℤ) := by norm_num

private theorem squarefreeInitCount_6272_6336 : (∑ n ∈ Ico 6272 6336, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (39 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_6336_6400 : (∑ n ∈ Ico 6336 6400, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (38 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_6272_6400 : (∑ n ∈ Ico 6272 6400, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (77 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 6272 6336, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 6336 6400, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 6272 ≤ 6336) (by norm_num : 6336 ≤ 6400)).symm
    _ = (39 : ℤ) + (38 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_6272_6336 squarefreeInitCount_6336_6400
    _ = (77 : ℤ) := by norm_num

private theorem squarefreeInitCount_6144_6400 : (∑ n ∈ Ico 6144 6400, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (155 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 6144 6272, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 6272 6400, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 6144 ≤ 6272) (by norm_num : 6272 ≤ 6400)).symm
    _ = (78 : ℤ) + (77 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_6144_6272 squarefreeInitCount_6272_6400
    _ = (155 : ℤ) := by norm_num

private theorem squarefreeInitCount_6400_6464 : (∑ n ∈ Ico 6400 6464, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (38 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_6464_6528 : (∑ n ∈ Ico 6464 6528, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (41 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_6400_6528 : (∑ n ∈ Ico 6400 6528, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (79 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 6400 6464, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 6464 6528, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 6400 ≤ 6464) (by norm_num : 6464 ≤ 6528)).symm
    _ = (38 : ℤ) + (41 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_6400_6464 squarefreeInitCount_6464_6528
    _ = (79 : ℤ) := by norm_num

private theorem squarefreeInitCount_6528_6592 : (∑ n ∈ Ico 6528 6592, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (39 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_6592_6656 : (∑ n ∈ Ico 6592 6656, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (37 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_6528_6656 : (∑ n ∈ Ico 6528 6656, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (76 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 6528 6592, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 6592 6656, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 6528 ≤ 6592) (by norm_num : 6592 ≤ 6656)).symm
    _ = (39 : ℤ) + (37 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_6528_6592 squarefreeInitCount_6592_6656
    _ = (76 : ℤ) := by norm_num

private theorem squarefreeInitCount_6400_6656 : (∑ n ∈ Ico 6400 6656, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (155 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 6400 6528, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 6528 6656, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 6400 ≤ 6528) (by norm_num : 6528 ≤ 6656)).symm
    _ = (79 : ℤ) + (76 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_6400_6528 squarefreeInitCount_6528_6656
    _ = (155 : ℤ) := by norm_num

theorem squarefreeInitCount_6144_6656 : (∑ n ∈ Ico 6144 6656, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (310 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 6144 6400, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 6400 6656, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 6144 ≤ 6400) (by norm_num : 6400 ≤ 6656)).symm
    _ = (155 : ℤ) + (155 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_6144_6400 squarefreeInitCount_6400_6656
    _ = (310 : ℤ) := by norm_num

private theorem squarefreeInitUpper_6144_6208 : (∑ n ∈ Ico 6144 6208, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (6497 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_6208_6272 : (∑ n ∈ Ico 6208 6272, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (6106 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_6144_6272 : (∑ n ∈ Ico 6144 6272, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (12603 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 6144 6208, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 6208 6272, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 6144 ≤ 6208) (by norm_num : 6208 ≤ 6272)).symm
    _ = (6497 : ℕ) + (6106 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_6144_6208 squarefreeInitUpper_6208_6272
    _ = (12603 : ℕ) := by norm_num

private theorem squarefreeInitUpper_6272_6336 : (∑ n ∈ Ico 6272 6336, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (6206 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_6336_6400 : (∑ n ∈ Ico 6336 6400, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (5986 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_6272_6400 : (∑ n ∈ Ico 6272 6400, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (12192 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 6272 6336, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 6336 6400, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 6272 ≤ 6336) (by norm_num : 6336 ≤ 6400)).symm
    _ = (6206 : ℕ) + (5986 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_6272_6336 squarefreeInitUpper_6336_6400
    _ = (12192 : ℕ) := by norm_num

private theorem squarefreeInitUpper_6144_6400 : (∑ n ∈ Ico 6144 6400, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (24795 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 6144 6272, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 6272 6400, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 6144 ≤ 6272) (by norm_num : 6272 ≤ 6400)).symm
    _ = (12603 : ℕ) + (12192 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_6144_6272 squarefreeInitUpper_6272_6400
    _ = (24795 : ℕ) := by norm_num

private theorem squarefreeInitUpper_6400_6464 : (∑ n ∈ Ico 6400 6464, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (5929 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_6464_6528 : (∑ n ∈ Ico 6464 6528, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (6333 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_6400_6528 : (∑ n ∈ Ico 6400 6528, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (12262 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 6400 6464, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 6464 6528, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 6400 ≤ 6464) (by norm_num : 6464 ≤ 6528)).symm
    _ = (5929 : ℕ) + (6333 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_6400_6464 squarefreeInitUpper_6464_6528
    _ = (12262 : ℕ) := by norm_num

private theorem squarefreeInitUpper_6528_6592 : (∑ n ∈ Ico 6528 6592, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (5964 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_6592_6656 : (∑ n ∈ Ico 6592 6656, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (5607 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_6528_6656 : (∑ n ∈ Ico 6528 6656, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (11571 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 6528 6592, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 6592 6656, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 6528 ≤ 6592) (by norm_num : 6592 ≤ 6656)).symm
    _ = (5964 : ℕ) + (5607 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_6528_6592 squarefreeInitUpper_6592_6656
    _ = (11571 : ℕ) := by norm_num

private theorem squarefreeInitUpper_6400_6656 : (∑ n ∈ Ico 6400 6656, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (23833 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 6400 6528, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 6528 6656, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 6400 ≤ 6528) (by norm_num : 6528 ≤ 6656)).symm
    _ = (12262 : ℕ) + (11571 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_6400_6528 squarefreeInitUpper_6528_6656
    _ = (23833 : ℕ) := by norm_num

theorem squarefreeInitUpper_6144_6656 : (∑ n ∈ Ico 6144 6656, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (48628 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 6144 6400, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 6400 6656, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 6144 ≤ 6400) (by norm_num : 6400 ≤ 6656)).symm
    _ = (24795 : ℕ) + (23833 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_6144_6400 squarefreeInitUpper_6400_6656
    _ = (48628 : ℕ) := by norm_num

end Helfgott
end

section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
open Finset Nat
open scoped BigOperators
namespace Helfgott

private theorem squarefreeInitCount_6656_6720 : (∑ n ∈ Ico 6656 6720, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (41 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_6720_6784 : (∑ n ∈ Ico 6720 6784, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (39 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_6656_6784 : (∑ n ∈ Ico 6656 6784, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (80 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 6656 6720, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 6720 6784, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 6656 ≤ 6720) (by norm_num : 6720 ≤ 6784)).symm
    _ = (41 : ℤ) + (39 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_6656_6720 squarefreeInitCount_6720_6784
    _ = (80 : ℤ) := by norm_num

private theorem squarefreeInitCount_6784_6848 : (∑ n ∈ Ico 6784 6848, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (40 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_6848_6912 : (∑ n ∈ Ico 6848 6912, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (35 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_6784_6912 : (∑ n ∈ Ico 6784 6912, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (75 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 6784 6848, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 6848 6912, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 6784 ≤ 6848) (by norm_num : 6848 ≤ 6912)).symm
    _ = (40 : ℤ) + (35 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_6784_6848 squarefreeInitCount_6848_6912
    _ = (75 : ℤ) := by norm_num

private theorem squarefreeInitCount_6656_6912 : (∑ n ∈ Ico 6656 6912, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (155 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 6656 6784, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 6784 6912, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 6656 ≤ 6784) (by norm_num : 6784 ≤ 6912)).symm
    _ = (80 : ℤ) + (75 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_6656_6784 squarefreeInitCount_6784_6912
    _ = (155 : ℤ) := by norm_num

private theorem squarefreeInitCount_6912_6976 : (∑ n ∈ Ico 6912 6976, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (37 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_6976_7040 : (∑ n ∈ Ico 6976 7040, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (40 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_6912_7040 : (∑ n ∈ Ico 6912 7040, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (77 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 6912 6976, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 6976 7040, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 6912 ≤ 6976) (by norm_num : 6976 ≤ 7040)).symm
    _ = (37 : ℤ) + (40 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_6912_6976 squarefreeInitCount_6976_7040
    _ = (77 : ℤ) := by norm_num

private theorem squarefreeInitCount_7040_7104 : (∑ n ∈ Ico 7040 7104, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (40 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_7104_7168 : (∑ n ∈ Ico 7104 7168, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (38 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_7040_7168 : (∑ n ∈ Ico 7040 7168, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (78 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 7040 7104, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 7104 7168, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 7040 ≤ 7104) (by norm_num : 7104 ≤ 7168)).symm
    _ = (40 : ℤ) + (38 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_7040_7104 squarefreeInitCount_7104_7168
    _ = (78 : ℤ) := by norm_num

private theorem squarefreeInitCount_6912_7168 : (∑ n ∈ Ico 6912 7168, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (155 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 6912 7040, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 7040 7168, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 6912 ≤ 7040) (by norm_num : 7040 ≤ 7168)).symm
    _ = (77 : ℤ) + (78 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_6912_7040 squarefreeInitCount_7040_7168
    _ = (155 : ℤ) := by norm_num

theorem squarefreeInitCount_6656_7168 : (∑ n ∈ Ico 6656 7168, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (310 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 6656 6912, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 6912 7168, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 6656 ≤ 6912) (by norm_num : 6912 ≤ 7168)).symm
    _ = (155 : ℤ) + (155 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_6656_6912 squarefreeInitCount_6912_7168
    _ = (310 : ℤ) := by norm_num

private theorem squarefreeInitUpper_6656_6720 : (∑ n ∈ Ico 6656 6720, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (6154 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_6720_6784 : (∑ n ∈ Ico 6720 6784, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (5794 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_6656_6784 : (∑ n ∈ Ico 6656 6784, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (11948 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 6656 6720, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 6720 6784, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 6656 ≤ 6720) (by norm_num : 6720 ≤ 6784)).symm
    _ = (6154 : ℕ) + (5794 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_6656_6720 squarefreeInitUpper_6720_6784
    _ = (11948 : ℕ) := by norm_num

private theorem squarefreeInitUpper_6784_6848 : (∑ n ∈ Ico 6784 6848, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (5892 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_6848_6912 : (∑ n ∈ Ico 6848 6912, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (5101 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_6784_6912 : (∑ n ∈ Ico 6784 6912, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (10993 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 6784 6848, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 6848 6912, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 6784 ≤ 6848) (by norm_num : 6848 ≤ 6912)).symm
    _ = (5892 : ℕ) + (5101 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_6784_6848 squarefreeInitUpper_6848_6912
    _ = (10993 : ℕ) := by norm_num

private theorem squarefreeInitUpper_6656_6912 : (∑ n ∈ Ico 6656 6912, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (22941 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 6656 6784, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 6784 6912, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 6656 ≤ 6784) (by norm_num : 6784 ≤ 6912)).symm
    _ = (11948 : ℕ) + (10993 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_6656_6784 squarefreeInitUpper_6784_6912
    _ = (22941 : ℕ) := by norm_num

private theorem squarefreeInitUpper_6912_6976 : (∑ n ∈ Ico 6912 6976, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (5347 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_6976_7040 : (∑ n ∈ Ico 6976 7040, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (5732 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_6912_7040 : (∑ n ∈ Ico 6912 7040, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (11079 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 6912 6976, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 6976 7040, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 6912 ≤ 6976) (by norm_num : 6976 ≤ 7040)).symm
    _ = (5347 : ℕ) + (5732 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_6912_6976 squarefreeInitUpper_6976_7040
    _ = (11079 : ℕ) := by norm_num

private theorem squarefreeInitUpper_7040_7104 : (∑ n ∈ Ico 7040 7104, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (5675 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_7104_7168 : (∑ n ∈ Ico 7104 7168, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (5343 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_7040_7168 : (∑ n ∈ Ico 7040 7168, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (11018 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 7040 7104, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 7104 7168, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 7040 ≤ 7104) (by norm_num : 7104 ≤ 7168)).symm
    _ = (5675 : ℕ) + (5343 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_7040_7104 squarefreeInitUpper_7104_7168
    _ = (11018 : ℕ) := by norm_num

private theorem squarefreeInitUpper_6912_7168 : (∑ n ∈ Ico 6912 7168, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (22097 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 6912 7040, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 7040 7168, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 6912 ≤ 7040) (by norm_num : 7040 ≤ 7168)).symm
    _ = (11079 : ℕ) + (11018 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_6912_7040 squarefreeInitUpper_7040_7168
    _ = (22097 : ℕ) := by norm_num

theorem squarefreeInitUpper_6656_7168 : (∑ n ∈ Ico 6656 7168, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (45038 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 6656 6912, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 6912 7168, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 6656 ≤ 6912) (by norm_num : 6912 ≤ 7168)).symm
    _ = (22941 : ℕ) + (22097 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_6656_6912 squarefreeInitUpper_6912_7168
    _ = (45038 : ℕ) := by norm_num

end Helfgott
end

section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
open Finset Nat
open scoped BigOperators
namespace Helfgott

private theorem squarefreeInitCount_7168_7232 : (∑ n ∈ Ico 7168 7232, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (39 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_7232_7296 : (∑ n ∈ Ico 7232 7296, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (40 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_7168_7296 : (∑ n ∈ Ico 7168 7296, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (79 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 7168 7232, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 7232 7296, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 7168 ≤ 7232) (by norm_num : 7232 ≤ 7296)).symm
    _ = (39 : ℤ) + (40 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_7168_7232 squarefreeInitCount_7232_7296
    _ = (79 : ℤ) := by norm_num

private theorem squarefreeInitCount_7296_7360 : (∑ n ∈ Ico 7296 7360, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (40 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_7360_7424 : (∑ n ∈ Ico 7360 7424, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (39 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_7296_7424 : (∑ n ∈ Ico 7296 7424, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (79 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 7296 7360, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 7360 7424, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 7296 ≤ 7360) (by norm_num : 7360 ≤ 7424)).symm
    _ = (40 : ℤ) + (39 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_7296_7360 squarefreeInitCount_7360_7424
    _ = (79 : ℤ) := by norm_num

private theorem squarefreeInitCount_7168_7424 : (∑ n ∈ Ico 7168 7424, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (158 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 7168 7296, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 7296 7424, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 7168 ≤ 7296) (by norm_num : 7296 ≤ 7424)).symm
    _ = (79 : ℤ) + (79 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_7168_7296 squarefreeInitCount_7296_7424
    _ = (158 : ℤ) := by norm_num

private theorem squarefreeInitCount_7424_7488 : (∑ n ∈ Ico 7424 7488, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (39 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_7488_7552 : (∑ n ∈ Ico 7488 7552, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (37 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_7424_7552 : (∑ n ∈ Ico 7424 7552, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (76 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 7424 7488, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 7488 7552, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 7424 ≤ 7488) (by norm_num : 7488 ≤ 7552)).symm
    _ = (39 : ℤ) + (37 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_7424_7488 squarefreeInitCount_7488_7552
    _ = (76 : ℤ) := by norm_num

private theorem squarefreeInitCount_7552_7616 : (∑ n ∈ Ico 7552 7616, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (40 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_7616_7680 : (∑ n ∈ Ico 7616 7680, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (41 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_7552_7680 : (∑ n ∈ Ico 7552 7680, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (81 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 7552 7616, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 7616 7680, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 7552 ≤ 7616) (by norm_num : 7616 ≤ 7680)).symm
    _ = (40 : ℤ) + (41 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_7552_7616 squarefreeInitCount_7616_7680
    _ = (81 : ℤ) := by norm_num

private theorem squarefreeInitCount_7424_7680 : (∑ n ∈ Ico 7424 7680, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (157 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 7424 7552, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 7552 7680, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 7424 ≤ 7552) (by norm_num : 7552 ≤ 7680)).symm
    _ = (76 : ℤ) + (81 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_7424_7552 squarefreeInitCount_7552_7680
    _ = (157 : ℤ) := by norm_num

theorem squarefreeInitCount_7168_7680 : (∑ n ∈ Ico 7168 7680, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (315 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 7168 7424, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 7424 7680, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 7168 ≤ 7424) (by norm_num : 7424 ≤ 7680)).symm
    _ = (158 : ℤ) + (157 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_7168_7424 squarefreeInitCount_7424_7680
    _ = (315 : ℤ) := by norm_num

private theorem squarefreeInitUpper_7168_7232 : (∑ n ∈ Ico 7168 7232, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (5437 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_7232_7296 : (∑ n ∈ Ico 7232 7296, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (5530 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_7168_7296 : (∑ n ∈ Ico 7168 7296, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (10967 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 7168 7232, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 7232 7296, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 7168 ≤ 7232) (by norm_num : 7232 ≤ 7296)).symm
    _ = (5437 : ℕ) + (5530 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_7168_7232 squarefreeInitUpper_7232_7296
    _ = (10967 : ℕ) := by norm_num

private theorem squarefreeInitUpper_7296_7360 : (∑ n ∈ Ico 7296 7360, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (5477 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_7360_7424 : (∑ n ∈ Ico 7360 7424, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (5292 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_7296_7424 : (∑ n ∈ Ico 7296 7424, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (10769 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 7296 7360, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 7360 7424, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 7296 ≤ 7360) (by norm_num : 7360 ≤ 7424)).symm
    _ = (5477 : ℕ) + (5292 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_7296_7360 squarefreeInitUpper_7360_7424
    _ = (10769 : ℕ) := by norm_num

private theorem squarefreeInitUpper_7168_7424 : (∑ n ∈ Ico 7168 7424, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (21736 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 7168 7296, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 7296 7424, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 7168 ≤ 7296) (by norm_num : 7296 ≤ 7424)).symm
    _ = (10967 : ℕ) + (10769 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_7168_7296 squarefreeInitUpper_7296_7424
    _ = (21736 : ℕ) := by norm_num

private theorem squarefreeInitUpper_7424_7488 : (∑ n ∈ Ico 7424 7488, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (5249 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_7488_7552 : (∑ n ∈ Ico 7488 7552, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (4939 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_7424_7552 : (∑ n ∈ Ico 7424 7552, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (10188 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 7424 7488, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 7488 7552, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 7424 ≤ 7488) (by norm_num : 7488 ≤ 7552)).symm
    _ = (5249 : ℕ) + (4939 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_7424_7488 squarefreeInitUpper_7488_7552
    _ = (10188 : ℕ) := by norm_num

private theorem squarefreeInitUpper_7552_7616 : (∑ n ∈ Ico 7552 7616, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (5296 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_7616_7680 : (∑ n ∈ Ico 7616 7680, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (5382 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_7552_7680 : (∑ n ∈ Ico 7552 7680, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (10678 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 7552 7616, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 7616 7680, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 7552 ≤ 7616) (by norm_num : 7616 ≤ 7680)).symm
    _ = (5296 : ℕ) + (5382 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_7552_7616 squarefreeInitUpper_7616_7680
    _ = (10678 : ℕ) := by norm_num

private theorem squarefreeInitUpper_7424_7680 : (∑ n ∈ Ico 7424 7680, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (20866 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 7424 7552, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 7552 7680, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 7424 ≤ 7552) (by norm_num : 7552 ≤ 7680)).symm
    _ = (10188 : ℕ) + (10678 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_7424_7552 squarefreeInitUpper_7552_7680
    _ = (20866 : ℕ) := by norm_num

theorem squarefreeInitUpper_7168_7680 : (∑ n ∈ Ico 7168 7680, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (42602 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 7168 7424, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 7424 7680, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 7168 ≤ 7424) (by norm_num : 7424 ≤ 7680)).symm
    _ = (21736 : ℕ) + (20866 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_7168_7424 squarefreeInitUpper_7424_7680
    _ = (42602 : ℕ) := by norm_num

end Helfgott
end

section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
open Finset Nat
open scoped BigOperators
namespace Helfgott

private theorem squarefreeInitCount_7680_7744 : (∑ n ∈ Ico 7680 7744, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (40 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_7744_7808 : (∑ n ∈ Ico 7744 7808, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (38 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_7680_7808 : (∑ n ∈ Ico 7680 7808, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (78 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 7680 7744, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 7744 7808, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 7680 ≤ 7744) (by norm_num : 7744 ≤ 7808)).symm
    _ = (40 : ℤ) + (38 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_7680_7744 squarefreeInitCount_7744_7808
    _ = (78 : ℤ) := by norm_num

private theorem squarefreeInitCount_7808_7872 : (∑ n ∈ Ico 7808 7872, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (40 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_7872_7936 : (∑ n ∈ Ico 7872 7936, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (39 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_7808_7936 : (∑ n ∈ Ico 7808 7936, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (79 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 7808 7872, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 7872 7936, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 7808 ≤ 7872) (by norm_num : 7872 ≤ 7936)).symm
    _ = (40 : ℤ) + (39 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_7808_7872 squarefreeInitCount_7872_7936
    _ = (79 : ℤ) := by norm_num

private theorem squarefreeInitCount_7680_7936 : (∑ n ∈ Ico 7680 7936, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (157 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 7680 7808, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 7808 7936, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 7680 ≤ 7808) (by norm_num : 7808 ≤ 7936)).symm
    _ = (78 : ℤ) + (79 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_7680_7808 squarefreeInitCount_7808_7936
    _ = (157 : ℤ) := by norm_num

private theorem squarefreeInitCount_7936_8000 : (∑ n ∈ Ico 7936 8000, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (37 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_8000_8064 : (∑ n ∈ Ico 8000 8064, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (40 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_7936_8064 : (∑ n ∈ Ico 7936 8064, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (77 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 7936 8000, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 8000 8064, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 7936 ≤ 8000) (by norm_num : 8000 ≤ 8064)).symm
    _ = (37 : ℤ) + (40 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_7936_8000 squarefreeInitCount_8000_8064
    _ = (77 : ℤ) := by norm_num

private theorem squarefreeInitCount_8064_8128 : (∑ n ∈ Ico 8064 8128, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (38 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_8128_8192 : (∑ n ∈ Ico 8128 8192, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (39 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_8064_8192 : (∑ n ∈ Ico 8064 8192, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (77 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 8064 8128, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 8128 8192, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 8064 ≤ 8128) (by norm_num : 8128 ≤ 8192)).symm
    _ = (38 : ℤ) + (39 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_8064_8128 squarefreeInitCount_8128_8192
    _ = (77 : ℤ) := by norm_num

private theorem squarefreeInitCount_7936_8192 : (∑ n ∈ Ico 7936 8192, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (154 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 7936 8064, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 8064 8192, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 7936 ≤ 8064) (by norm_num : 8064 ≤ 8192)).symm
    _ = (77 : ℤ) + (77 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_7936_8064 squarefreeInitCount_8064_8192
    _ = (154 : ℤ) := by norm_num

theorem squarefreeInitCount_7680_8192 : (∑ n ∈ Ico 7680 8192, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (311 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 7680 7936, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 7936 8192, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 7680 ≤ 7936) (by norm_num : 7936 ≤ 8192)).symm
    _ = (157 : ℤ) + (154 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_7680_7936 squarefreeInitCount_7936_8192
    _ = (311 : ℤ) := by norm_num

private theorem squarefreeInitUpper_7680_7744 : (∑ n ∈ Ico 7680 7744, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (5208 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_7744_7808 : (∑ n ∈ Ico 7744 7808, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (4906 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_7680_7808 : (∑ n ∈ Ico 7680 7808, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (10114 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 7680 7744, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 7744 7808, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 7680 ≤ 7744) (by norm_num : 7744 ≤ 7808)).symm
    _ = (5208 : ℕ) + (4906 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_7680_7744 squarefreeInitUpper_7744_7808
    _ = (10114 : ℕ) := by norm_num

private theorem squarefreeInitUpper_7808_7872 : (∑ n ∈ Ico 7808 7872, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (5123 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_7872_7936 : (∑ n ∈ Ico 7872 7936, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (4955 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_7808_7936 : (∑ n ∈ Ico 7808 7936, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (10078 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 7808 7872, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 7872 7936, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 7808 ≤ 7872) (by norm_num : 7872 ≤ 7936)).symm
    _ = (5123 : ℕ) + (4955 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_7808_7872 squarefreeInitUpper_7872_7936
    _ = (10078 : ℕ) := by norm_num

private theorem squarefreeInitUpper_7680_7936 : (∑ n ∈ Ico 7680 7936, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (20192 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 7680 7808, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 7808 7936, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 7680 ≤ 7808) (by norm_num : 7808 ≤ 7936)).symm
    _ = (10114 : ℕ) + (10078 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_7680_7808 squarefreeInitUpper_7808_7936
    _ = (20192 : ℕ) := by norm_num

private theorem squarefreeInitUpper_7936_8000 : (∑ n ∈ Ico 7936 8000, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (4662 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_8000_8064 : (∑ n ∈ Ico 8000 8064, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (5000 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_7936_8064 : (∑ n ∈ Ico 7936 8064, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (9662 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 7936 8000, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 8000 8064, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 7936 ≤ 8000) (by norm_num : 8000 ≤ 8064)).symm
    _ = (4662 : ℕ) + (5000 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_7936_8000 squarefreeInitUpper_8000_8064
    _ = (9662 : ℕ) := by norm_num

private theorem squarefreeInitUpper_8064_8128 : (∑ n ∈ Ico 8064 8128, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (4712 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_8128_8192 : (∑ n ∈ Ico 8128 8192, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (4799 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_8064_8192 : (∑ n ∈ Ico 8064 8192, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (9511 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 8064 8128, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 8128 8192, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 8064 ≤ 8128) (by norm_num : 8128 ≤ 8192)).symm
    _ = (4712 : ℕ) + (4799 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_8064_8128 squarefreeInitUpper_8128_8192
    _ = (9511 : ℕ) := by norm_num

private theorem squarefreeInitUpper_7936_8192 : (∑ n ∈ Ico 7936 8192, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (19173 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 7936 8064, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 8064 8192, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 7936 ≤ 8064) (by norm_num : 8064 ≤ 8192)).symm
    _ = (9662 : ℕ) + (9511 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_7936_8064 squarefreeInitUpper_8064_8192
    _ = (19173 : ℕ) := by norm_num

theorem squarefreeInitUpper_7680_8192 : (∑ n ∈ Ico 7680 8192, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (39365 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 7680 7936, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 7936 8192, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 7680 ≤ 7936) (by norm_num : 7936 ≤ 8192)).symm
    _ = (20192 : ℕ) + (19173 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_7680_7936 squarefreeInitUpper_7936_8192
    _ = (39365 : ℕ) := by norm_num

end Helfgott
end

section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
open Finset Nat
open scoped BigOperators
namespace Helfgott

private theorem squarefreeInitCount_8192_8256 : (∑ n ∈ Ico 8192 8256, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (40 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_8256_8320 : (∑ n ∈ Ico 8256 8320, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (40 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_8192_8320 : (∑ n ∈ Ico 8192 8320, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (80 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 8192 8256, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 8256 8320, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 8192 ≤ 8256) (by norm_num : 8256 ≤ 8320)).symm
    _ = (40 : ℤ) + (40 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_8192_8256 squarefreeInitCount_8256_8320
    _ = (80 : ℤ) := by norm_num

private theorem squarefreeInitCount_8320_8384 : (∑ n ∈ Ico 8320 8384, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (37 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_8384_8448 : (∑ n ∈ Ico 8384 8448, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (39 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_8320_8448 : (∑ n ∈ Ico 8320 8448, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (76 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 8320 8384, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 8384 8448, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 8320 ≤ 8384) (by norm_num : 8384 ≤ 8448)).symm
    _ = (37 : ℤ) + (39 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_8320_8384 squarefreeInitCount_8384_8448
    _ = (76 : ℤ) := by norm_num

private theorem squarefreeInitCount_8192_8448 : (∑ n ∈ Ico 8192 8448, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (156 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 8192 8320, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 8320 8448, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 8192 ≤ 8320) (by norm_num : 8320 ≤ 8448)).symm
    _ = (80 : ℤ) + (76 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_8192_8320 squarefreeInitCount_8320_8448
    _ = (156 : ℤ) := by norm_num

private theorem squarefreeInitCount_8448_8512 : (∑ n ∈ Ico 8448 8512, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (39 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_8512_8576 : (∑ n ∈ Ico 8512 8576, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (40 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_8448_8576 : (∑ n ∈ Ico 8448 8576, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (79 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 8448 8512, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 8512 8576, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 8448 ≤ 8512) (by norm_num : 8512 ≤ 8576)).symm
    _ = (39 : ℤ) + (40 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_8448_8512 squarefreeInitCount_8512_8576
    _ = (79 : ℤ) := by norm_num

private theorem squarefreeInitCount_8576_8640 : (∑ n ∈ Ico 8576 8640, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (39 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_8640_8704 : (∑ n ∈ Ico 8640 8704, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (38 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_8576_8704 : (∑ n ∈ Ico 8576 8704, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (77 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 8576 8640, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 8640 8704, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 8576 ≤ 8640) (by norm_num : 8640 ≤ 8704)).symm
    _ = (39 : ℤ) + (38 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_8576_8640 squarefreeInitCount_8640_8704
    _ = (77 : ℤ) := by norm_num

private theorem squarefreeInitCount_8448_8704 : (∑ n ∈ Ico 8448 8704, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (156 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 8448 8576, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 8576 8704, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 8448 ≤ 8576) (by norm_num : 8576 ≤ 8704)).symm
    _ = (79 : ℤ) + (77 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_8448_8576 squarefreeInitCount_8576_8704
    _ = (156 : ℤ) := by norm_num

theorem squarefreeInitCount_8192_8704 : (∑ n ∈ Ico 8192 8704, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (312 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 8192 8448, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 8448 8704, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 8192 ≤ 8448) (by norm_num : 8448 ≤ 8704)).symm
    _ = (156 : ℤ) + (156 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_8192_8448 squarefreeInitCount_8448_8704
    _ = (312 : ℤ) := by norm_num

private theorem squarefreeInitUpper_8192_8256 : (∑ n ∈ Ico 8192 8256, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (4883 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_8256_8320 : (∑ n ∈ Ico 8256 8320, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (4845 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_8192_8320 : (∑ n ∈ Ico 8192 8320, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (9728 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 8192 8256, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 8256 8320, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 8192 ≤ 8256) (by norm_num : 8256 ≤ 8320)).symm
    _ = (4883 : ℕ) + (4845 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_8192_8256 squarefreeInitUpper_8256_8320
    _ = (9728 : ℕ) := by norm_num

private theorem squarefreeInitUpper_8320_8384 : (∑ n ∈ Ico 8320 8384, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (4448 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_8384_8448 : (∑ n ∈ Ico 8384 8448, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (4655 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_8320_8448 : (∑ n ∈ Ico 8320 8448, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (9103 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 8320 8384, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 8384 8448, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 8320 ≤ 8384) (by norm_num : 8384 ≤ 8448)).symm
    _ = (4448 : ℕ) + (4655 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_8320_8384 squarefreeInitUpper_8384_8448
    _ = (9103 : ℕ) := by norm_num

private theorem squarefreeInitUpper_8192_8448 : (∑ n ∈ Ico 8192 8448, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (18831 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 8192 8320, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 8320 8448, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 8192 ≤ 8320) (by norm_num : 8320 ≤ 8448)).symm
    _ = (9728 : ℕ) + (9103 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_8192_8320 squarefreeInitUpper_8320_8448
    _ = (18831 : ℕ) := by norm_num

private theorem squarefreeInitUpper_8448_8512 : (∑ n ∈ Ico 8448 8512, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (4618 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_8512_8576 : (∑ n ∈ Ico 8512 8576, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (4702 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_8448_8576 : (∑ n ∈ Ico 8448 8576, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (9320 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 8448 8512, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 8512 8576, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 8448 ≤ 8512) (by norm_num : 8512 ≤ 8576)).symm
    _ = (4618 : ℕ) + (4702 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_8448_8512 squarefreeInitUpper_8512_8576
    _ = (9320 : ℕ) := by norm_num

private theorem squarefreeInitUpper_8576_8640 : (∑ n ∈ Ico 8576 8640, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (4551 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_8640_8704 : (∑ n ∈ Ico 8640 8704, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (4403 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_8576_8704 : (∑ n ∈ Ico 8576 8704, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (8954 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 8576 8640, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 8640 8704, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 8576 ≤ 8640) (by norm_num : 8640 ≤ 8704)).symm
    _ = (4551 : ℕ) + (4403 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_8576_8640 squarefreeInitUpper_8640_8704
    _ = (8954 : ℕ) := by norm_num

private theorem squarefreeInitUpper_8448_8704 : (∑ n ∈ Ico 8448 8704, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (18274 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 8448 8576, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 8576 8704, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 8448 ≤ 8576) (by norm_num : 8576 ≤ 8704)).symm
    _ = (9320 : ℕ) + (8954 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_8448_8576 squarefreeInitUpper_8576_8704
    _ = (18274 : ℕ) := by norm_num

theorem squarefreeInitUpper_8192_8704 : (∑ n ∈ Ico 8192 8704, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (37105 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 8192 8448, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 8448 8704, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 8192 ≤ 8448) (by norm_num : 8448 ≤ 8704)).symm
    _ = (18831 : ℕ) + (18274 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_8192_8448 squarefreeInitUpper_8448_8704
    _ = (37105 : ℕ) := by norm_num

end Helfgott
end

section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
open Finset Nat
open scoped BigOperators
namespace Helfgott

private theorem squarefreeInitCount_8704_8768 : (∑ n ∈ Ico 8704 8768, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (40 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_8768_8832 : (∑ n ∈ Ico 8768 8832, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (41 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_8704_8832 : (∑ n ∈ Ico 8704 8832, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (81 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 8704 8768, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 8768 8832, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 8704 ≤ 8768) (by norm_num : 8768 ≤ 8832)).symm
    _ = (40 : ℤ) + (41 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_8704_8768 squarefreeInitCount_8768_8832
    _ = (81 : ℤ) := by norm_num

private theorem squarefreeInitCount_8832_8896 : (∑ n ∈ Ico 8832 8896, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (39 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_8896_8960 : (∑ n ∈ Ico 8896 8960, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (36 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_8832_8960 : (∑ n ∈ Ico 8832 8960, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (75 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 8832 8896, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 8896 8960, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 8832 ≤ 8896) (by norm_num : 8896 ≤ 8960)).symm
    _ = (39 : ℤ) + (36 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_8832_8896 squarefreeInitCount_8896_8960
    _ = (75 : ℤ) := by norm_num

private theorem squarefreeInitCount_8704_8960 : (∑ n ∈ Ico 8704 8960, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (156 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 8704 8832, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 8832 8960, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 8704 ≤ 8832) (by norm_num : 8832 ≤ 8960)).symm
    _ = (81 : ℤ) + (75 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_8704_8832 squarefreeInitCount_8832_8960
    _ = (156 : ℤ) := by norm_num

private theorem squarefreeInitCount_8960_9024 : (∑ n ∈ Ico 8960 9024, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (39 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_9024_9088 : (∑ n ∈ Ico 9024 9088, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (39 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_8960_9088 : (∑ n ∈ Ico 8960 9088, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (78 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 8960 9024, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 9024 9088, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 8960 ≤ 9024) (by norm_num : 9024 ≤ 9088)).symm
    _ = (39 : ℤ) + (39 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_8960_9024 squarefreeInitCount_9024_9088
    _ = (78 : ℤ) := by norm_num

private theorem squarefreeInitCount_9088_9152 : (∑ n ∈ Ico 9088 9152, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (40 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_9152_9216 : (∑ n ∈ Ico 9152 9216, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (40 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_9088_9216 : (∑ n ∈ Ico 9088 9216, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (80 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 9088 9152, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 9152 9216, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 9088 ≤ 9152) (by norm_num : 9152 ≤ 9216)).symm
    _ = (40 : ℤ) + (40 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_9088_9152 squarefreeInitCount_9152_9216
    _ = (80 : ℤ) := by norm_num

private theorem squarefreeInitCount_8960_9216 : (∑ n ∈ Ico 8960 9216, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (158 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 8960 9088, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 9088 9216, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 8960 ≤ 9088) (by norm_num : 9088 ≤ 9216)).symm
    _ = (78 : ℤ) + (80 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_8960_9088 squarefreeInitCount_9088_9216
    _ = (158 : ℤ) := by norm_num

theorem squarefreeInitCount_8704_9216 : (∑ n ∈ Ico 8704 9216, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (314 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 8704 8960, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 8960 9216, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 8704 ≤ 8960) (by norm_num : 8960 ≤ 9216)).symm
    _ = (156 : ℤ) + (158 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_8704_8960 squarefreeInitCount_8960_9216
    _ = (314 : ℤ) := by norm_num

private theorem squarefreeInitUpper_8704_8768 : (∑ n ∈ Ico 8704 8768, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (4600 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_8768_8832 : (∑ n ∈ Ico 8768 8832, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (4676 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_8704_8832 : (∑ n ∈ Ico 8704 8832, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (9276 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 8704 8768, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 8768 8832, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 8704 ≤ 8768) (by norm_num : 8768 ≤ 8832)).symm
    _ = (4600 : ℕ) + (4676 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_8704_8768 squarefreeInitUpper_8768_8832
    _ = (9276 : ℕ) := by norm_num

private theorem squarefreeInitUpper_8832_8896 : (∑ n ∈ Ico 8832 8896, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (4417 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_8896_8960 : (∑ n ∈ Ico 8896 8960, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (4051 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_8832_8960 : (∑ n ∈ Ico 8832 8960, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (8468 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 8832 8896, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 8896 8960, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 8832 ≤ 8896) (by norm_num : 8896 ≤ 8960)).symm
    _ = (4417 : ℕ) + (4051 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_8832_8896 squarefreeInitUpper_8896_8960
    _ = (8468 : ℕ) := by norm_num

private theorem squarefreeInitUpper_8704_8960 : (∑ n ∈ Ico 8704 8960, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (17744 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 8704 8832, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 8832 8960, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 8704 ≤ 8832) (by norm_num : 8832 ≤ 8960)).symm
    _ = (9276 : ℕ) + (8468 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_8704_8832 squarefreeInitUpper_8832_8960
    _ = (17744 : ℕ) := by norm_num

private theorem squarefreeInitUpper_8960_9024 : (∑ n ∈ Ico 8960 9024, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (4358 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_9024_9088 : (∑ n ∈ Ico 9024 9088, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (4329 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_8960_9088 : (∑ n ∈ Ico 8960 9088, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (8687 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 8960 9024, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 9024 9088, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 8960 ≤ 9024) (by norm_num : 9024 ≤ 9088)).symm
    _ = (4358 : ℕ) + (4329 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_8960_9024 squarefreeInitUpper_9024_9088
    _ = (8687 : ℕ) := by norm_num

private theorem squarefreeInitUpper_9088_9152 : (∑ n ∈ Ico 9088 9152, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (4401 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_9152_9216 : (∑ n ∈ Ico 9152 9216, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (4373 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_9088_9216 : (∑ n ∈ Ico 9088 9216, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (8774 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 9088 9152, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 9152 9216, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 9088 ≤ 9152) (by norm_num : 9152 ≤ 9216)).symm
    _ = (4401 : ℕ) + (4373 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_9088_9152 squarefreeInitUpper_9152_9216
    _ = (8774 : ℕ) := by norm_num

private theorem squarefreeInitUpper_8960_9216 : (∑ n ∈ Ico 8960 9216, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (17461 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 8960 9088, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 9088 9216, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 8960 ≤ 9088) (by norm_num : 9088 ≤ 9216)).symm
    _ = (8687 : ℕ) + (8774 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_8960_9088 squarefreeInitUpper_9088_9216
    _ = (17461 : ℕ) := by norm_num

theorem squarefreeInitUpper_8704_9216 : (∑ n ∈ Ico 8704 9216, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (35205 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 8704 8960, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 8960 9216, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 8704 ≤ 8960) (by norm_num : 8960 ≤ 9216)).symm
    _ = (17744 : ℕ) + (17461 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_8704_8960 squarefreeInitUpper_8960_9216
    _ = (35205 : ℕ) := by norm_num

end Helfgott
end

section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
open Finset Nat
open scoped BigOperators
namespace Helfgott

private theorem squarefreeInitCount_9216_9280 : (∑ n ∈ Ico 9216 9280, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (38 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_9280_9344 : (∑ n ∈ Ico 9280 9344, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (39 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_9216_9344 : (∑ n ∈ Ico 9216 9344, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (77 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 9216 9280, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 9280 9344, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 9216 ≤ 9280) (by norm_num : 9280 ≤ 9344)).symm
    _ = (38 : ℤ) + (39 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_9216_9280 squarefreeInitCount_9280_9344
    _ = (77 : ℤ) := by norm_num

private theorem squarefreeInitCount_9344_9408 : (∑ n ∈ Ico 9344 9408, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (39 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_9408_9472 : (∑ n ∈ Ico 9408 9472, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (39 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_9344_9472 : (∑ n ∈ Ico 9344 9472, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (78 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 9344 9408, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 9408 9472, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 9344 ≤ 9408) (by norm_num : 9408 ≤ 9472)).symm
    _ = (39 : ℤ) + (39 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_9344_9408 squarefreeInitCount_9408_9472
    _ = (78 : ℤ) := by norm_num

private theorem squarefreeInitCount_9216_9472 : (∑ n ∈ Ico 9216 9472, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (155 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 9216 9344, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 9344 9472, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 9216 ≤ 9344) (by norm_num : 9344 ≤ 9472)).symm
    _ = (77 : ℤ) + (78 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_9216_9344 squarefreeInitCount_9344_9472
    _ = (155 : ℤ) := by norm_num

private theorem squarefreeInitCount_9472_9536 : (∑ n ∈ Ico 9472 9536, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (39 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_9536_9600 : (∑ n ∈ Ico 9536 9600, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (37 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_9472_9600 : (∑ n ∈ Ico 9472 9600, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (76 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 9472 9536, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 9536 9600, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 9472 ≤ 9536) (by norm_num : 9536 ≤ 9600)).symm
    _ = (39 : ℤ) + (37 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_9472_9536 squarefreeInitCount_9536_9600
    _ = (76 : ℤ) := by norm_num

private theorem squarefreeInitCount_9600_9664 : (∑ n ∈ Ico 9600 9664, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (38 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_9664_9728 : (∑ n ∈ Ico 9664 9728, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (42 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_9600_9728 : (∑ n ∈ Ico 9600 9728, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (80 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 9600 9664, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 9664 9728, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 9600 ≤ 9664) (by norm_num : 9664 ≤ 9728)).symm
    _ = (38 : ℤ) + (42 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_9600_9664 squarefreeInitCount_9664_9728
    _ = (80 : ℤ) := by norm_num

private theorem squarefreeInitCount_9472_9728 : (∑ n ∈ Ico 9472 9728, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (156 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 9472 9600, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 9600 9728, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 9472 ≤ 9600) (by norm_num : 9600 ≤ 9728)).symm
    _ = (76 : ℤ) + (80 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_9472_9600 squarefreeInitCount_9600_9728
    _ = (156 : ℤ) := by norm_num

theorem squarefreeInitCount_9216_9728 : (∑ n ∈ Ico 9216 9728, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (311 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 9216 9472, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 9472 9728, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 9216 ≤ 9472) (by norm_num : 9472 ≤ 9728)).symm
    _ = (155 : ℤ) + (156 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_9216_9472 squarefreeInitCount_9472_9728
    _ = (311 : ℤ) := by norm_num

private theorem squarefreeInitUpper_9216_9280 : (∑ n ∈ Ico 9216 9280, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (4131 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_9280_9344 : (∑ n ∈ Ico 9280 9344, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (4212 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_9216_9344 : (∑ n ∈ Ico 9216 9344, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (8343 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 9216 9280, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 9280 9344, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 9216 ≤ 9280) (by norm_num : 9280 ≤ 9344)).symm
    _ = (4131 : ℕ) + (4212 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_9216_9280 squarefreeInitUpper_9280_9344
    _ = (8343 : ℕ) := by norm_num

private theorem squarefreeInitUpper_9344_9408 : (∑ n ∈ Ico 9344 9408, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (4174 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_9408_9472 : (∑ n ∈ Ico 9408 9472, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (4149 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_9344_9472 : (∑ n ∈ Ico 9344 9472, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (8323 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 9344 9408, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 9408 9472, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 9344 ≤ 9408) (by norm_num : 9408 ≤ 9472)).symm
    _ = (4174 : ℕ) + (4149 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_9344_9408 squarefreeInitUpper_9408_9472
    _ = (8323 : ℕ) := by norm_num

private theorem squarefreeInitUpper_9216_9472 : (∑ n ∈ Ico 9216 9472, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (16666 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 9216 9344, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 9344 9472, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 9216 ≤ 9344) (by norm_num : 9344 ≤ 9472)).symm
    _ = (8343 : ℕ) + (8323 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_9216_9344 squarefreeInitUpper_9344_9472
    _ = (16666 : ℕ) := by norm_num

private theorem squarefreeInitUpper_9472_9536 : (∑ n ∈ Ico 9472 9536, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (4127 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_9536_9600 : (∑ n ∈ Ico 9536 9600, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (3885 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_9472_9600 : (∑ n ∈ Ico 9472 9600, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (8012 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 9472 9536, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 9536 9600, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 9472 ≤ 9536) (by norm_num : 9536 ≤ 9600)).symm
    _ = (4127 : ℕ) + (3885 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_9472_9536 squarefreeInitUpper_9536_9600
    _ = (8012 : ℕ) := by norm_num

private theorem squarefreeInitUpper_9600_9664 : (∑ n ∈ Ico 9600 9664, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (3962 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_9664_9728 : (∑ n ∈ Ico 9664 9728, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (4355 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_9600_9728 : (∑ n ∈ Ico 9600 9728, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (8317 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 9600 9664, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 9664 9728, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 9600 ≤ 9664) (by norm_num : 9664 ≤ 9728)).symm
    _ = (3962 : ℕ) + (4355 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_9600_9664 squarefreeInitUpper_9664_9728
    _ = (8317 : ℕ) := by norm_num

private theorem squarefreeInitUpper_9472_9728 : (∑ n ∈ Ico 9472 9728, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (16329 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 9472 9600, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 9600 9728, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 9472 ≤ 9600) (by norm_num : 9600 ≤ 9728)).symm
    _ = (8012 : ℕ) + (8317 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_9472_9600 squarefreeInitUpper_9600_9728
    _ = (16329 : ℕ) := by norm_num

theorem squarefreeInitUpper_9216_9728 : (∑ n ∈ Ico 9216 9728, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (32995 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 9216 9472, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 9472 9728, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 9216 ≤ 9472) (by norm_num : 9472 ≤ 9728)).symm
    _ = (16666 : ℕ) + (16329 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_9216_9472 squarefreeInitUpper_9472_9728
    _ = (32995 : ℕ) := by norm_num

end Helfgott
end

section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
open Finset Nat
open scoped BigOperators
namespace Helfgott

private theorem squarefreeInitCount_9728_9792 : (∑ n ∈ Ico 9728 9792, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (39 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_9792_9856 : (∑ n ∈ Ico 9792 9856, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (37 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_9728_9856 : (∑ n ∈ Ico 9728 9856, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (76 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 9728 9792, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 9792 9856, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 9728 ≤ 9792) (by norm_num : 9792 ≤ 9856)).symm
    _ = (39 : ℤ) + (37 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_9728_9792 squarefreeInitCount_9792_9856
    _ = (76 : ℤ) := by norm_num

private theorem squarefreeInitCount_9856_9920 : (∑ n ∈ Ico 9856 9920, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (41 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_9920_9984 : (∑ n ∈ Ico 9920 9984, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (37 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_9984_10001 : (∑ n ∈ Ico 9984 10001, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (10 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_9920_10001 : (∑ n ∈ Ico 9920 10001, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (47 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 9920 9984, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 9984 10001, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 9920 ≤ 9984) (by norm_num : 9984 ≤ 10001)).symm
    _ = (37 : ℤ) + (10 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_9920_9984 squarefreeInitCount_9984_10001
    _ = (47 : ℤ) := by norm_num

private theorem squarefreeInitCount_9856_10001 : (∑ n ∈ Ico 9856 10001, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (88 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 9856 9920, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 9920 10001, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 9856 ≤ 9920) (by norm_num : 9920 ≤ 10001)).symm
    _ = (41 : ℤ) + (47 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_9856_9920 squarefreeInitCount_9920_10001
    _ = (88 : ℤ) := by norm_num

theorem squarefreeInitCount_9728_10001 : (∑ n ∈ Ico 9728 10001, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (164 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 9728 9856, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 9856 10001, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 9728 ≤ 9856) (by norm_num : 9856 ≤ 10001)).symm
    _ = (76 : ℤ) + (88 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_9728_9856 squarefreeInitCount_9856_10001
    _ = (164 : ℤ) := by norm_num

private theorem squarefreeInitUpper_9728_9792 : (∑ n ∈ Ico 9728 9792, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (4017 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_9792_9856 : (∑ n ∈ Ico 9792 9856, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (3781 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_9728_9856 : (∑ n ∈ Ico 9728 9856, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (7798 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 9728 9792, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 9792 9856, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 9728 ≤ 9792) (by norm_num : 9792 ≤ 9856)).symm
    _ = (4017 : ℕ) + (3781 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_9728_9792 squarefreeInitUpper_9792_9856
    _ = (7798 : ℕ) := by norm_num

private theorem squarefreeInitUpper_9856_9920 : (∑ n ∈ Ico 9856 9920, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (4169 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_9920_9984 : (∑ n ∈ Ico 9920 9984, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (3737 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_9984_10001 : (∑ n ∈ Ico 9984 10001, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (1010 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_9920_10001 : (∑ n ∈ Ico 9920 10001, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (4747 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 9920 9984, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 9984 10001, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 9920 ≤ 9984) (by norm_num : 9984 ≤ 10001)).symm
    _ = (3737 : ℕ) + (1010 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_9920_9984 squarefreeInitUpper_9984_10001
    _ = (4747 : ℕ) := by norm_num

private theorem squarefreeInitUpper_9856_10001 : (∑ n ∈ Ico 9856 10001, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (8916 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 9856 9920, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 9920 10001, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 9856 ≤ 9920) (by norm_num : 9920 ≤ 10001)).symm
    _ = (4169 : ℕ) + (4747 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_9856_9920 squarefreeInitUpper_9920_10001
    _ = (8916 : ℕ) := by norm_num

theorem squarefreeInitUpper_9728_10001 : (∑ n ∈ Ico 9728 10001, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (16714 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 9728 9856, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 9856 10001, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 9728 ≤ 9856) (by norm_num : 9856 ≤ 10001)).symm
    _ = (7798 : ℕ) + (8916 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_9728_9856 squarefreeInitUpper_9856_10001
    _ = (16714 : ℕ) := by norm_num

end Helfgott
end

section
set_option autoImplicit false
set_option Elab.async false
open Finset Nat
open scoped BigOperators
namespace Helfgott
theorem squarefree_harmonic_numeric_group001_checked_native :
  ((∑ n ∈ Ico 5120 5632, ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) = (309 : ℤ) ∧
    (∑ n ∈ Ico 5120 5632, mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) = (57674 : ℕ)) ∧
  ((∑ n ∈ Ico 5632 6144, ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) = (314 : ℤ) ∧
    (∑ n ∈ Ico 5632 6144, mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) = (53506 : ℕ)) ∧
  ((∑ n ∈ Ico 6144 6656, ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) = (310 : ℤ) ∧
    (∑ n ∈ Ico 6144 6656, mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) = (48628 : ℕ)) ∧
  ((∑ n ∈ Ico 6656 7168, ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) = (310 : ℤ) ∧
    (∑ n ∈ Ico 6656 7168, mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) = (45038 : ℕ)) ∧
  ((∑ n ∈ Ico 7168 7680, ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) = (315 : ℤ) ∧
    (∑ n ∈ Ico 7168 7680, mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) = (42602 : ℕ)) ∧
  ((∑ n ∈ Ico 7680 8192, ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) = (311 : ℤ) ∧
    (∑ n ∈ Ico 7680 8192, mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) = (39365 : ℕ)) ∧
  ((∑ n ∈ Ico 8192 8704, ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) = (312 : ℤ) ∧
    (∑ n ∈ Ico 8192 8704, mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) = (37105 : ℕ)) ∧
  ((∑ n ∈ Ico 8704 9216, ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) = (314 : ℤ) ∧
    (∑ n ∈ Ico 8704 9216, mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) = (35205 : ℕ)) ∧
  ((∑ n ∈ Ico 9216 9728, ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) = (311 : ℤ) ∧
    (∑ n ∈ Ico 9216 9728, mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) = (32995 : ℕ)) ∧
  ((∑ n ∈ Ico 9728 10001, ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) = (164 : ℤ) ∧
    (∑ n ∈ Ico 9728 10001, mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) = (16714 : ℕ)) := ⟨⟨squarefreeInitCount_5120_5632, squarefreeInitUpper_5120_5632⟩, ⟨⟨squarefreeInitCount_5632_6144, squarefreeInitUpper_5632_6144⟩, ⟨⟨squarefreeInitCount_6144_6656, squarefreeInitUpper_6144_6656⟩, ⟨⟨squarefreeInitCount_6656_7168, squarefreeInitUpper_6656_7168⟩, ⟨⟨squarefreeInitCount_7168_7680, squarefreeInitUpper_7168_7680⟩, ⟨⟨squarefreeInitCount_7680_8192, squarefreeInitUpper_7680_8192⟩, ⟨⟨squarefreeInitCount_8192_8704, squarefreeInitUpper_8192_8704⟩, ⟨⟨squarefreeInitCount_8704_9216, squarefreeInitUpper_8704_9216⟩, ⟨⟨squarefreeInitCount_9216_9728, squarefreeInitUpper_9216_9728⟩, ⟨squarefreeInitCount_9728_10001, squarefreeInitUpper_9728_10001⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Helfgott
end

open Helfgott Finset Nat
open scoped BigOperators
theorem solution :
  ((∑ n ∈ Ico 5120 5632, ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) = (309 : ℤ) ∧
    (∑ n ∈ Ico 5120 5632, mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) = (57674 : ℕ)) ∧
  ((∑ n ∈ Ico 5632 6144, ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) = (314 : ℤ) ∧
    (∑ n ∈ Ico 5632 6144, mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) = (53506 : ℕ)) ∧
  ((∑ n ∈ Ico 6144 6656, ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) = (310 : ℤ) ∧
    (∑ n ∈ Ico 6144 6656, mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) = (48628 : ℕ)) ∧
  ((∑ n ∈ Ico 6656 7168, ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) = (310 : ℤ) ∧
    (∑ n ∈ Ico 6656 7168, mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) = (45038 : ℕ)) ∧
  ((∑ n ∈ Ico 7168 7680, ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) = (315 : ℤ) ∧
    (∑ n ∈ Ico 7168 7680, mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) = (42602 : ℕ)) ∧
  ((∑ n ∈ Ico 7680 8192, ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) = (311 : ℤ) ∧
    (∑ n ∈ Ico 7680 8192, mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) = (39365 : ℕ)) ∧
  ((∑ n ∈ Ico 8192 8704, ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) = (312 : ℤ) ∧
    (∑ n ∈ Ico 8192 8704, mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) = (37105 : ℕ)) ∧
  ((∑ n ∈ Ico 8704 9216, ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) = (314 : ℤ) ∧
    (∑ n ∈ Ico 8704 9216, mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) = (35205 : ℕ)) ∧
  ((∑ n ∈ Ico 9216 9728, ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) = (311 : ℤ) ∧
    (∑ n ∈ Ico 9216 9728, mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) = (32995 : ℕ)) ∧
  ((∑ n ∈ Ico 9728 10001, ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) = (164 : ℤ) ∧
    (∑ n ∈ Ico 9728 10001, mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) = (16714 : ℕ)) := Helfgott.squarefree_harmonic_numeric_group001_checked_native
#print axioms solution
