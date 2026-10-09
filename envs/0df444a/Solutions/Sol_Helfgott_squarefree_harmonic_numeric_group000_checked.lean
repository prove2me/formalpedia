-- Prove2me | solution 1 for Helfgott.squarefree_harmonic_numeric_group000_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-08T23:51:46.122535+00:00
-- url     : https://prove2.me/submissions/48e8906e-2ffa-4408-92b1-870e4bd3ee57

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

private theorem squarefreeInitCount_0_64 : (∑ n ∈ Ico 0 64, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (39 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_64_128 : (∑ n ∈ Ico 64 128, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (39 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_0_128 : (∑ n ∈ Ico 0 128, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (78 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 0 64, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 64 128, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 0 ≤ 64) (by norm_num : 64 ≤ 128)).symm
    _ = (39 : ℤ) + (39 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_0_64 squarefreeInitCount_64_128
    _ = (78 : ℤ) := by norm_num

private theorem squarefreeInitCount_128_192 : (∑ n ∈ Ico 128 192, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (39 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_192_256 : (∑ n ∈ Ico 192 256, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (40 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_128_256 : (∑ n ∈ Ico 128 256, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (79 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 128 192, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 192 256, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 128 ≤ 192) (by norm_num : 192 ≤ 256)).symm
    _ = (39 : ℤ) + (40 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_128_192 squarefreeInitCount_192_256
    _ = (79 : ℤ) := by norm_num

private theorem squarefreeInitCount_0_256 : (∑ n ∈ Ico 0 256, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (157 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 0 128, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 128 256, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 0 ≤ 128) (by norm_num : 128 ≤ 256)).symm
    _ = (78 : ℤ) + (79 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_0_128 squarefreeInitCount_128_256
    _ = (157 : ℤ) := by norm_num

private theorem squarefreeInitCount_256_320 : (∑ n ∈ Ico 256 320, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (39 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_320_384 : (∑ n ∈ Ico 320 384, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (36 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_256_384 : (∑ n ∈ Ico 256 384, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (75 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 256 320, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 320 384, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 256 ≤ 320) (by norm_num : 320 ≤ 384)).symm
    _ = (39 : ℤ) + (36 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_256_320 squarefreeInitCount_320_384
    _ = (75 : ℤ) := by norm_num

private theorem squarefreeInitCount_384_448 : (∑ n ∈ Ico 384 448, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (42 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_448_512 : (∑ n ∈ Ico 448 512, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (40 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_384_512 : (∑ n ∈ Ico 384 512, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (82 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 384 448, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 448 512, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 384 ≤ 448) (by norm_num : 448 ≤ 512)).symm
    _ = (42 : ℤ) + (40 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_384_448 squarefreeInitCount_448_512
    _ = (82 : ℤ) := by norm_num

private theorem squarefreeInitCount_256_512 : (∑ n ∈ Ico 256 512, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (157 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 256 384, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 384 512, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 256 ≤ 384) (by norm_num : 384 ≤ 512)).symm
    _ = (75 : ℤ) + (82 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_256_384 squarefreeInitCount_384_512
    _ = (157 : ℤ) := by norm_num

theorem squarefreeInitCount_0_512 : (∑ n ∈ Ico 0 512, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (314 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 0 256, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 256 512, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 0 ≤ 256) (by norm_num : 256 ≤ 512)).symm
    _ = (157 : ℤ) + (157 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_0_256 squarefreeInitCount_256_512
    _ = (314 : ℤ) := by norm_num

private theorem squarefreeInitUpper_0_64 : (∑ n ∈ Ico 0 64, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (3558003 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_64_128 : (∑ n ∈ Ico 64 128, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (429990 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_0_128 : (∑ n ∈ Ico 0 128, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (3987993 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 0 64, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 64 128, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 0 ≤ 64) (by norm_num : 64 ≤ 128)).symm
    _ = (3558003 : ℕ) + (429990 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_0_64 squarefreeInitUpper_64_128
    _ = (3987993 : ℕ) := by norm_num

private theorem squarefreeInitUpper_128_192 : (∑ n ∈ Ico 128 192, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (247756 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_192_256 : (∑ n ∈ Ico 192 256, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (180854 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_128_256 : (∑ n ∈ Ico 128 256, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (428610 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 128 192, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 192 256, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 128 ≤ 192) (by norm_num : 192 ≤ 256)).symm
    _ = (247756 : ℕ) + (180854 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_128_192 squarefreeInitUpper_192_256
    _ = (428610 : ℕ) := by norm_num

private theorem squarefreeInitUpper_0_256 : (∑ n ∈ Ico 0 256, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (4416603 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 0 128, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 128 256, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 0 ≤ 128) (by norm_num : 128 ≤ 256)).symm
    _ = (3987993 : ℕ) + (428610 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_0_128 squarefreeInitUpper_128_256
    _ = (4416603 : ℕ) := by norm_num

private theorem squarefreeInitUpper_256_320 : (∑ n ∈ Ico 256 320, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (135950 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_320_384 : (∑ n ∈ Ico 320 384, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (102626 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_256_384 : (∑ n ∈ Ico 256 384, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (238576 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 256 320, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 320 384, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 256 ≤ 320) (by norm_num : 320 ≤ 384)).symm
    _ = (135950 : ℕ) + (102626 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_256_320 squarefreeInitUpper_320_384
    _ = (238576 : ℕ) := by norm_num

private theorem squarefreeInitUpper_384_448 : (∑ n ∈ Ico 384 448, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (101184 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_448_512 : (∑ n ∈ Ico 448 512, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (83478 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_384_512 : (∑ n ∈ Ico 384 512, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (184662 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 384 448, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 448 512, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 384 ≤ 448) (by norm_num : 448 ≤ 512)).symm
    _ = (101184 : ℕ) + (83478 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_384_448 squarefreeInitUpper_448_512
    _ = (184662 : ℕ) := by norm_num

private theorem squarefreeInitUpper_256_512 : (∑ n ∈ Ico 256 512, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (423238 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 256 384, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 384 512, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 256 ≤ 384) (by norm_num : 384 ≤ 512)).symm
    _ = (238576 : ℕ) + (184662 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_256_384 squarefreeInitUpper_384_512
    _ = (423238 : ℕ) := by norm_num

theorem squarefreeInitUpper_0_512 : (∑ n ∈ Ico 0 512, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (4839841 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 0 256, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 256 512, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 0 ≤ 256) (by norm_num : 256 ≤ 512)).symm
    _ = (4416603 : ℕ) + (423238 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_0_256 squarefreeInitUpper_256_512
    _ = (4839841 : ℕ) := by norm_num

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

private theorem squarefreeInitCount_512_576 : (∑ n ∈ Ico 512 576, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (37 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_576_640 : (∑ n ∈ Ico 576 640, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (38 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_512_640 : (∑ n ∈ Ico 512 640, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (75 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 512 576, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 576 640, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 512 ≤ 576) (by norm_num : 576 ≤ 640)).symm
    _ = (37 : ℤ) + (38 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_512_576 squarefreeInitCount_576_640
    _ = (75 : ℤ) := by norm_num

private theorem squarefreeInitCount_640_704 : (∑ n ∈ Ico 640 704, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (41 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_704_768 : (∑ n ∈ Ico 704 768, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (38 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_640_768 : (∑ n ∈ Ico 640 768, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (79 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 640 704, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 704 768, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 640 ≤ 704) (by norm_num : 704 ≤ 768)).symm
    _ = (41 : ℤ) + (38 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_640_704 squarefreeInitCount_704_768
    _ = (79 : ℤ) := by norm_num

private theorem squarefreeInitCount_512_768 : (∑ n ∈ Ico 512 768, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (154 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 512 640, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 640 768, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 512 ≤ 640) (by norm_num : 640 ≤ 768)).symm
    _ = (75 : ℤ) + (79 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_512_640 squarefreeInitCount_640_768
    _ = (154 : ℤ) := by norm_num

private theorem squarefreeInitCount_768_832 : (∑ n ∈ Ico 768 832, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (41 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_832_896 : (∑ n ∈ Ico 832 896, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (35 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_768_896 : (∑ n ∈ Ico 768 896, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (76 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 768 832, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 832 896, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 768 ≤ 832) (by norm_num : 832 ≤ 896)).symm
    _ = (41 : ℤ) + (35 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_768_832 squarefreeInitCount_832_896
    _ = (76 : ℤ) := by norm_num

private theorem squarefreeInitCount_896_960 : (∑ n ∈ Ico 896 960, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (40 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_960_1024 : (∑ n ∈ Ico 960 1024, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (40 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_896_1024 : (∑ n ∈ Ico 896 1024, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (80 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 896 960, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 960 1024, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 896 ≤ 960) (by norm_num : 960 ≤ 1024)).symm
    _ = (40 : ℤ) + (40 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_896_960 squarefreeInitCount_960_1024
    _ = (80 : ℤ) := by norm_num

private theorem squarefreeInitCount_768_1024 : (∑ n ∈ Ico 768 1024, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (156 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 768 896, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 896 1024, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 768 ≤ 896) (by norm_num : 896 ≤ 1024)).symm
    _ = (76 : ℤ) + (80 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_768_896 squarefreeInitCount_896_1024
    _ = (156 : ℤ) := by norm_num

theorem squarefreeInitCount_512_1024 : (∑ n ∈ Ico 512 1024, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (310 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 512 768, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 768 1024, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 512 ≤ 768) (by norm_num : 768 ≤ 1024)).symm
    _ = (154 : ℤ) + (156 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_512_768 squarefreeInitCount_768_1024
    _ = (310 : ℤ) := by norm_num

private theorem squarefreeInitUpper_512_576 : (∑ n ∈ Ico 512 576, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (68024 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_576_640 : (∑ n ∈ Ico 576 640, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (62675 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_512_640 : (∑ n ∈ Ico 512 640, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (130699 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 512 576, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 576 640, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 512 ≤ 576) (by norm_num : 576 ≤ 640)).symm
    _ = (68024 : ℕ) + (62675 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_512_576 squarefreeInitUpper_576_640
    _ = (130699 : ℕ) := by norm_num

private theorem squarefreeInitUpper_640_704 : (∑ n ∈ Ico 640 704, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (61133 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_704_768 : (∑ n ∈ Ico 704 768, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (51663 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_640_768 : (∑ n ∈ Ico 640 768, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (112796 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 640 704, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 704 768, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 640 ≤ 704) (by norm_num : 704 ≤ 768)).symm
    _ = (61133 : ℕ) + (51663 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_640_704 squarefreeInitUpper_704_768
    _ = (112796 : ℕ) := by norm_num

private theorem squarefreeInitUpper_512_768 : (∑ n ∈ Ico 512 768, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (243495 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 512 640, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 640 768, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 512 ≤ 640) (by norm_num : 640 ≤ 768)).symm
    _ = (130699 : ℕ) + (112796 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_512_640 squarefreeInitUpper_640_768
    _ = (243495 : ℕ) := by norm_num

private theorem squarefreeInitUpper_768_832 : (∑ n ∈ Ico 768 832, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (51279 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_832_896 : (∑ n ∈ Ico 832 896, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (40424 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_768_896 : (∑ n ∈ Ico 768 896, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (91703 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 768 832, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 832 896, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 768 ≤ 832) (by norm_num : 832 ≤ 896)).symm
    _ = (51279 : ℕ) + (40424 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_768_832 squarefreeInitUpper_832_896
    _ = (91703 : ℕ) := by norm_num

private theorem squarefreeInitUpper_896_960 : (∑ n ∈ Ico 896 960, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (43179 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_960_1024 : (∑ n ∈ Ico 960 1024, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (40328 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_896_1024 : (∑ n ∈ Ico 896 1024, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (83507 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 896 960, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 960 1024, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 896 ≤ 960) (by norm_num : 960 ≤ 1024)).symm
    _ = (43179 : ℕ) + (40328 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_896_960 squarefreeInitUpper_960_1024
    _ = (83507 : ℕ) := by norm_num

private theorem squarefreeInitUpper_768_1024 : (∑ n ∈ Ico 768 1024, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (175210 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 768 896, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 896 1024, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 768 ≤ 896) (by norm_num : 896 ≤ 1024)).symm
    _ = (91703 : ℕ) + (83507 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_768_896 squarefreeInitUpper_896_1024
    _ = (175210 : ℕ) := by norm_num

theorem squarefreeInitUpper_512_1024 : (∑ n ∈ Ico 512 1024, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (418705 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 512 768, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 768 1024, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 512 ≤ 768) (by norm_num : 768 ≤ 1024)).symm
    _ = (243495 : ℕ) + (175210 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_512_768 squarefreeInitUpper_768_1024
    _ = (418705 : ℕ) := by norm_num

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

private theorem squarefreeInitCount_1024_1088 : (∑ n ∈ Ico 1024 1088, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (36 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_1088_1152 : (∑ n ∈ Ico 1088 1152, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (40 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_1024_1152 : (∑ n ∈ Ico 1024 1152, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (76 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 1024 1088, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 1088 1152, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 1024 ≤ 1088) (by norm_num : 1088 ≤ 1152)).symm
    _ = (36 : ℤ) + (40 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_1024_1088 squarefreeInitCount_1088_1152
    _ = (76 : ℤ) := by norm_num

private theorem squarefreeInitCount_1152_1216 : (∑ n ∈ Ico 1152 1216, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (39 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_1216_1280 : (∑ n ∈ Ico 1216 1280, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (39 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_1152_1280 : (∑ n ∈ Ico 1152 1280, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (78 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 1152 1216, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 1216 1280, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 1152 ≤ 1216) (by norm_num : 1216 ≤ 1280)).symm
    _ = (39 : ℤ) + (39 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_1152_1216 squarefreeInitCount_1216_1280
    _ = (78 : ℤ) := by norm_num

private theorem squarefreeInitCount_1024_1280 : (∑ n ∈ Ico 1024 1280, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (154 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 1024 1152, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 1152 1280, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 1024 ≤ 1152) (by norm_num : 1152 ≤ 1280)).symm
    _ = (76 : ℤ) + (78 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_1024_1152 squarefreeInitCount_1152_1280
    _ = (154 : ℤ) := by norm_num

private theorem squarefreeInitCount_1280_1344 : (∑ n ∈ Ico 1280 1344, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (41 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_1344_1408 : (∑ n ∈ Ico 1344 1408, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (41 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_1280_1408 : (∑ n ∈ Ico 1280 1408, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (82 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 1280 1344, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 1344 1408, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 1280 ≤ 1344) (by norm_num : 1344 ≤ 1408)).symm
    _ = (41 : ℤ) + (41 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_1280_1344 squarefreeInitCount_1344_1408
    _ = (82 : ℤ) := by norm_num

private theorem squarefreeInitCount_1408_1472 : (∑ n ∈ Ico 1408 1472, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (37 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_1472_1536 : (∑ n ∈ Ico 1472 1536, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (40 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_1408_1536 : (∑ n ∈ Ico 1408 1536, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (77 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 1408 1472, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 1472 1536, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 1408 ≤ 1472) (by norm_num : 1472 ≤ 1536)).symm
    _ = (37 : ℤ) + (40 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_1408_1472 squarefreeInitCount_1472_1536
    _ = (77 : ℤ) := by norm_num

private theorem squarefreeInitCount_1280_1536 : (∑ n ∈ Ico 1280 1536, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (159 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 1280 1408, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 1408 1536, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 1280 ≤ 1408) (by norm_num : 1408 ≤ 1536)).symm
    _ = (82 : ℤ) + (77 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_1280_1408 squarefreeInitCount_1408_1536
    _ = (159 : ℤ) := by norm_num

theorem squarefreeInitCount_1024_1536 : (∑ n ∈ Ico 1024 1536, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (313 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 1024 1280, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 1280 1536, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 1024 ≤ 1280) (by norm_num : 1280 ≤ 1536)).symm
    _ = (154 : ℤ) + (159 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_1024_1280 squarefreeInitCount_1280_1536
    _ = (313 : ℤ) := by norm_num

private theorem squarefreeInitUpper_1024_1088 : (∑ n ∈ Ico 1024 1088, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (34094 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_1088_1152 : (∑ n ∈ Ico 1088 1152, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (35753 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_1024_1152 : (∑ n ∈ Ico 1024 1152, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (69847 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 1024 1088, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 1088 1152, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 1024 ≤ 1088) (by norm_num : 1088 ≤ 1152)).symm
    _ = (34094 : ℕ) + (35753 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_1024_1088 squarefreeInitUpper_1088_1152
    _ = (69847 : ℕ) := by norm_num

private theorem squarefreeInitUpper_1152_1216 : (∑ n ∈ Ico 1152 1216, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (32993 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_1216_1280 : (∑ n ∈ Ico 1216 1280, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (31318 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_1152_1280 : (∑ n ∈ Ico 1152 1280, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (64311 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 1152 1216, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 1216 1280, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 1152 ≤ 1216) (by norm_num : 1216 ≤ 1280)).symm
    _ = (32993 : ℕ) + (31318 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_1152_1216 squarefreeInitUpper_1216_1280
    _ = (64311 : ℕ) := by norm_num

private theorem squarefreeInitUpper_1024_1280 : (∑ n ∈ Ico 1024 1280, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (134158 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 1024 1152, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 1152 1280, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 1024 ≤ 1152) (by norm_num : 1152 ≤ 1280)).symm
    _ = (69847 : ℕ) + (64311 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_1024_1152 squarefreeInitUpper_1152_1280
    _ = (134158 : ℕ) := by norm_num

private theorem squarefreeInitUpper_1280_1344 : (∑ n ∈ Ico 1280 1344, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (31303 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_1344_1408 : (∑ n ∈ Ico 1344 1408, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (29811 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_1280_1408 : (∑ n ∈ Ico 1280 1408, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (61114 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 1280 1344, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 1344 1408, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 1280 ≤ 1344) (by norm_num : 1344 ≤ 1408)).symm
    _ = (31303 : ℕ) + (29811 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_1280_1344 squarefreeInitUpper_1344_1408
    _ = (61114 : ℕ) := by norm_num

private theorem squarefreeInitUpper_1408_1472 : (∑ n ∈ Ico 1408 1472, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (25721 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_1472_1536 : (∑ n ∈ Ico 1472 1536, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (26630 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_1408_1536 : (∑ n ∈ Ico 1408 1536, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (52351 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 1408 1472, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 1472 1536, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 1408 ≤ 1472) (by norm_num : 1472 ≤ 1536)).symm
    _ = (25721 : ℕ) + (26630 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_1408_1472 squarefreeInitUpper_1472_1536
    _ = (52351 : ℕ) := by norm_num

private theorem squarefreeInitUpper_1280_1536 : (∑ n ∈ Ico 1280 1536, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (113465 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 1280 1408, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 1408 1536, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 1280 ≤ 1408) (by norm_num : 1408 ≤ 1536)).symm
    _ = (61114 : ℕ) + (52351 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_1280_1408 squarefreeInitUpper_1408_1536
    _ = (113465 : ℕ) := by norm_num

theorem squarefreeInitUpper_1024_1536 : (∑ n ∈ Ico 1024 1536, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (247623 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 1024 1280, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 1280 1536, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 1024 ≤ 1280) (by norm_num : 1280 ≤ 1536)).symm
    _ = (134158 : ℕ) + (113465 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_1024_1280 squarefreeInitUpper_1280_1536
    _ = (247623 : ℕ) := by norm_num

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

private theorem squarefreeInitCount_1536_1600 : (∑ n ∈ Ico 1536 1600, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (40 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_1600_1664 : (∑ n ∈ Ico 1600 1664, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (40 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_1536_1664 : (∑ n ∈ Ico 1536 1664, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (80 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 1536 1600, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 1600 1664, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 1536 ≤ 1600) (by norm_num : 1600 ≤ 1664)).symm
    _ = (40 : ℤ) + (40 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_1536_1600 squarefreeInitCount_1600_1664
    _ = (80 : ℤ) := by norm_num

private theorem squarefreeInitCount_1664_1728 : (∑ n ∈ Ico 1664 1728, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (34 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_1728_1792 : (∑ n ∈ Ico 1728 1792, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (39 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_1664_1792 : (∑ n ∈ Ico 1664 1792, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (73 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 1664 1728, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 1728 1792, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 1664 ≤ 1728) (by norm_num : 1728 ≤ 1792)).symm
    _ = (34 : ℤ) + (39 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_1664_1728 squarefreeInitCount_1728_1792
    _ = (73 : ℤ) := by norm_num

private theorem squarefreeInitCount_1536_1792 : (∑ n ∈ Ico 1536 1792, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (153 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 1536 1664, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 1664 1792, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 1536 ≤ 1664) (by norm_num : 1664 ≤ 1792)).symm
    _ = (80 : ℤ) + (73 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_1536_1664 squarefreeInitCount_1664_1792
    _ = (153 : ℤ) := by norm_num

private theorem squarefreeInitCount_1792_1856 : (∑ n ∈ Ico 1792 1856, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (37 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_1856_1920 : (∑ n ∈ Ico 1856 1920, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (39 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_1792_1920 : (∑ n ∈ Ico 1792 1920, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (76 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 1792 1856, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 1856 1920, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 1792 ≤ 1856) (by norm_num : 1856 ≤ 1920)).symm
    _ = (37 : ℤ) + (39 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_1792_1856 squarefreeInitCount_1856_1920
    _ = (76 : ℤ) := by norm_num

private theorem squarefreeInitCount_1920_1984 : (∑ n ∈ Ico 1920 1984, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (39 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_1984_2048 : (∑ n ∈ Ico 1984 2048, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (40 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_1920_2048 : (∑ n ∈ Ico 1920 2048, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (79 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 1920 1984, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 1984 2048, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 1920 ≤ 1984) (by norm_num : 1984 ≤ 2048)).symm
    _ = (39 : ℤ) + (40 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_1920_1984 squarefreeInitCount_1984_2048
    _ = (79 : ℤ) := by norm_num

private theorem squarefreeInitCount_1792_2048 : (∑ n ∈ Ico 1792 2048, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (155 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 1792 1920, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 1920 2048, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 1792 ≤ 1920) (by norm_num : 1920 ≤ 2048)).symm
    _ = (76 : ℤ) + (79 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_1792_1920 squarefreeInitCount_1920_2048
    _ = (155 : ℤ) := by norm_num

theorem squarefreeInitCount_1536_2048 : (∑ n ∈ Ico 1536 2048, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (308 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 1536 1792, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 1792 2048, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 1536 ≤ 1792) (by norm_num : 1792 ≤ 2048)).symm
    _ = (153 : ℤ) + (155 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_1536_1792 squarefreeInitCount_1792_2048
    _ = (308 : ℤ) := by norm_num

private theorem squarefreeInitUpper_1536_1600 : (∑ n ∈ Ico 1536 1600, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (25531 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_1600_1664 : (∑ n ∈ Ico 1600 1664, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (24520 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_1536_1664 : (∑ n ∈ Ico 1536 1664, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (50051 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 1536 1600, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 1600 1664, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 1536 ≤ 1600) (by norm_num : 1600 ≤ 1664)).symm
    _ = (25531 : ℕ) + (24520 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_1536_1600 squarefreeInitUpper_1600_1664
    _ = (50051 : ℕ) := by norm_num

private theorem squarefreeInitUpper_1664_1728 : (∑ n ∈ Ico 1664 1728, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (20045 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_1728_1792 : (∑ n ∈ Ico 1728 1792, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (22183 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_1664_1792 : (∑ n ∈ Ico 1664 1792, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (42228 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 1664 1728, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 1728 1792, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 1664 ≤ 1728) (by norm_num : 1728 ≤ 1792)).symm
    _ = (20045 : ℕ) + (22183 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_1664_1728 squarefreeInitUpper_1728_1792
    _ = (42228 : ℕ) := by norm_num

private theorem squarefreeInitUpper_1536_1792 : (∑ n ∈ Ico 1536 1792, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (92279 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 1536 1664, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 1664 1792, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 1536 ≤ 1664) (by norm_num : 1664 ≤ 1792)).symm
    _ = (50051 : ℕ) + (42228 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_1536_1664 squarefreeInitUpper_1664_1792
    _ = (92279 : ℕ) := by norm_num

private theorem squarefreeInitUpper_1792_1856 : (∑ n ∈ Ico 1792 1856, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (20320 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_1856_1920 : (∑ n ∈ Ico 1856 1920, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (20668 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_1792_1920 : (∑ n ∈ Ico 1792 1920, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (40988 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 1792 1856, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 1856 1920, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 1792 ≤ 1856) (by norm_num : 1856 ≤ 1920)).symm
    _ = (20320 : ℕ) + (20668 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_1792_1856 squarefreeInitUpper_1856_1920
    _ = (40988 : ℕ) := by norm_num

private theorem squarefreeInitUpper_1920_1984 : (∑ n ∈ Ico 1920 1984, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (19985 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_1984_2048 : (∑ n ∈ Ico 1984 2048, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (19860 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_1920_2048 : (∑ n ∈ Ico 1920 2048, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (39845 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 1920 1984, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 1984 2048, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 1920 ≤ 1984) (by norm_num : 1984 ≤ 2048)).symm
    _ = (19985 : ℕ) + (19860 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_1920_1984 squarefreeInitUpper_1984_2048
    _ = (39845 : ℕ) := by norm_num

private theorem squarefreeInitUpper_1792_2048 : (∑ n ∈ Ico 1792 2048, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (80833 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 1792 1920, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 1920 2048, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 1792 ≤ 1920) (by norm_num : 1920 ≤ 2048)).symm
    _ = (40988 : ℕ) + (39845 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_1792_1920 squarefreeInitUpper_1920_2048
    _ = (80833 : ℕ) := by norm_num

theorem squarefreeInitUpper_1536_2048 : (∑ n ∈ Ico 1536 2048, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (173112 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 1536 1792, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 1792 2048, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 1536 ≤ 1792) (by norm_num : 1792 ≤ 2048)).symm
    _ = (92279 : ℕ) + (80833 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_1536_1792 squarefreeInitUpper_1792_2048
    _ = (173112 : ℕ) := by norm_num

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

private theorem squarefreeInitCount_2048_2112 : (∑ n ∈ Ico 2048 2112, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (38 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_2112_2176 : (∑ n ∈ Ico 2112 2176, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (39 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_2048_2176 : (∑ n ∈ Ico 2048 2176, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (77 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 2048 2112, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 2112 2176, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 2048 ≤ 2112) (by norm_num : 2112 ≤ 2176)).symm
    _ = (38 : ℤ) + (39 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_2048_2112 squarefreeInitCount_2112_2176
    _ = (77 : ℤ) := by norm_num

private theorem squarefreeInitCount_2176_2240 : (∑ n ∈ Ico 2176 2240, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (40 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_2240_2304 : (∑ n ∈ Ico 2240 2304, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (38 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_2176_2304 : (∑ n ∈ Ico 2176 2304, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (78 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 2176 2240, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 2240 2304, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 2176 ≤ 2240) (by norm_num : 2240 ≤ 2304)).symm
    _ = (40 : ℤ) + (38 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_2176_2240 squarefreeInitCount_2240_2304
    _ = (78 : ℤ) := by norm_num

private theorem squarefreeInitCount_2048_2304 : (∑ n ∈ Ico 2048 2304, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (155 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 2048 2176, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 2176 2304, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 2048 ≤ 2176) (by norm_num : 2176 ≤ 2304)).symm
    _ = (77 : ℤ) + (78 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_2048_2176 squarefreeInitCount_2176_2304
    _ = (155 : ℤ) := by norm_num

private theorem squarefreeInitCount_2304_2368 : (∑ n ∈ Ico 2304 2368, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (39 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_2368_2432 : (∑ n ∈ Ico 2368 2432, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (40 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_2304_2432 : (∑ n ∈ Ico 2304 2432, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (79 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 2304 2368, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 2368 2432, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 2304 ≤ 2368) (by norm_num : 2368 ≤ 2432)).symm
    _ = (39 : ℤ) + (40 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_2304_2368 squarefreeInitCount_2368_2432
    _ = (79 : ℤ) := by norm_num

private theorem squarefreeInitCount_2432_2496 : (∑ n ∈ Ico 2432 2496, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (42 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_2496_2560 : (∑ n ∈ Ico 2496 2560, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (36 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_2432_2560 : (∑ n ∈ Ico 2432 2560, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (78 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 2432 2496, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 2496 2560, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 2432 ≤ 2496) (by norm_num : 2496 ≤ 2560)).symm
    _ = (42 : ℤ) + (36 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_2432_2496 squarefreeInitCount_2496_2560
    _ = (78 : ℤ) := by norm_num

private theorem squarefreeInitCount_2304_2560 : (∑ n ∈ Ico 2304 2560, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (157 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 2304 2432, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 2432 2560, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 2304 ≤ 2432) (by norm_num : 2432 ≤ 2560)).symm
    _ = (79 : ℤ) + (78 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_2304_2432 squarefreeInitCount_2432_2560
    _ = (157 : ℤ) := by norm_num

theorem squarefreeInitCount_2048_2560 : (∑ n ∈ Ico 2048 2560, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (312 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 2048 2304, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 2304 2560, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 2048 ≤ 2304) (by norm_num : 2304 ≤ 2560)).symm
    _ = (155 : ℤ) + (157 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_2048_2304 squarefreeInitCount_2304_2560
    _ = (312 : ℤ) := by norm_num

private theorem squarefreeInitUpper_2048_2112 : (∑ n ∈ Ico 2048 2112, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (18281 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_2112_2176 : (∑ n ∈ Ico 2112 2176, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (18219 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_2048_2176 : (∑ n ∈ Ico 2048 2176, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (36500 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 2048 2112, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 2112 2176, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 2048 ≤ 2112) (by norm_num : 2112 ≤ 2176)).symm
    _ = (18281 : ℕ) + (18219 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_2048_2112 squarefreeInitUpper_2112_2176
    _ = (36500 : ℕ) := by norm_num

private theorem squarefreeInitUpper_2176_2240 : (∑ n ∈ Ico 2176 2240, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (18132 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_2240_2304 : (∑ n ∈ Ico 2240 2304, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (16750 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_2176_2304 : (∑ n ∈ Ico 2176 2304, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (34882 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 2176 2240, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 2240 2304, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 2176 ≤ 2240) (by norm_num : 2240 ≤ 2304)).symm
    _ = (18132 : ℕ) + (16750 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_2176_2240 squarefreeInitUpper_2240_2304
    _ = (34882 : ℕ) := by norm_num

private theorem squarefreeInitUpper_2048_2304 : (∑ n ∈ Ico 2048 2304, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (71382 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 2048 2176, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 2176 2304, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 2048 ≤ 2176) (by norm_num : 2176 ≤ 2304)).symm
    _ = (36500 : ℕ) + (34882 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_2048_2176 squarefreeInitUpper_2176_2304
    _ = (71382 : ℕ) := by norm_num

private theorem squarefreeInitUpper_2304_2368 : (∑ n ∈ Ico 2304 2368, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (16724 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_2368_2432 : (∑ n ∈ Ico 2368 2432, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (16693 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_2304_2432 : (∑ n ∈ Ico 2304 2432, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (33417 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 2304 2368, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 2368 2432, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 2304 ≤ 2368) (by norm_num : 2368 ≤ 2432)).symm
    _ = (16724 : ℕ) + (16693 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_2304_2368 squarefreeInitUpper_2368_2432
    _ = (33417 : ℕ) := by norm_num

private theorem squarefreeInitUpper_2432_2496 : (∑ n ∈ Ico 2432 2496, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (17066 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_2496_2560 : (∑ n ∈ Ico 2496 2560, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (14257 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_2432_2560 : (∑ n ∈ Ico 2432 2560, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (31323 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 2432 2496, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 2496 2560, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 2432 ≤ 2496) (by norm_num : 2496 ≤ 2560)).symm
    _ = (17066 : ℕ) + (14257 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_2432_2496 squarefreeInitUpper_2496_2560
    _ = (31323 : ℕ) := by norm_num

private theorem squarefreeInitUpper_2304_2560 : (∑ n ∈ Ico 2304 2560, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (64740 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 2304 2432, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 2432 2560, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 2304 ≤ 2432) (by norm_num : 2432 ≤ 2560)).symm
    _ = (33417 : ℕ) + (31323 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_2304_2432 squarefreeInitUpper_2432_2560
    _ = (64740 : ℕ) := by norm_num

theorem squarefreeInitUpper_2048_2560 : (∑ n ∈ Ico 2048 2560, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (136122 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 2048 2304, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 2304 2560, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 2048 ≤ 2304) (by norm_num : 2304 ≤ 2560)).symm
    _ = (71382 : ℕ) + (64740 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_2048_2304 squarefreeInitUpper_2304_2560
    _ = (136122 : ℕ) := by norm_num

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

private theorem squarefreeInitCount_2560_2624 : (∑ n ∈ Ico 2560 2624, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (40 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_2624_2688 : (∑ n ∈ Ico 2624 2688, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (38 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_2560_2688 : (∑ n ∈ Ico 2560 2688, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (78 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 2560 2624, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 2624 2688, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 2560 ≤ 2624) (by norm_num : 2624 ≤ 2688)).symm
    _ = (40 : ℤ) + (38 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_2560_2624 squarefreeInitCount_2624_2688
    _ = (78 : ℤ) := by norm_num

private theorem squarefreeInitCount_2688_2752 : (∑ n ∈ Ico 2688 2752, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (39 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_2752_2816 : (∑ n ∈ Ico 2752 2816, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (39 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_2688_2816 : (∑ n ∈ Ico 2688 2816, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (78 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 2688 2752, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 2752 2816, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 2688 ≤ 2752) (by norm_num : 2752 ≤ 2816)).symm
    _ = (39 : ℤ) + (39 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_2688_2752 squarefreeInitCount_2752_2816
    _ = (78 : ℤ) := by norm_num

private theorem squarefreeInitCount_2560_2816 : (∑ n ∈ Ico 2560 2816, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (156 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 2560 2688, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 2688 2816, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 2560 ≤ 2688) (by norm_num : 2688 ≤ 2816)).symm
    _ = (78 : ℤ) + (78 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_2560_2688 squarefreeInitCount_2688_2816
    _ = (156 : ℤ) := by norm_num

private theorem squarefreeInitCount_2816_2880 : (∑ n ∈ Ico 2816 2880, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (37 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_2880_2944 : (∑ n ∈ Ico 2880 2944, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (39 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_2816_2944 : (∑ n ∈ Ico 2816 2944, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (76 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 2816 2880, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 2880 2944, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 2816 ≤ 2880) (by norm_num : 2880 ≤ 2944)).symm
    _ = (37 : ℤ) + (39 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_2816_2880 squarefreeInitCount_2880_2944
    _ = (76 : ℤ) := by norm_num

private theorem squarefreeInitCount_2944_3008 : (∑ n ∈ Ico 2944 3008, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (40 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_3008_3072 : (∑ n ∈ Ico 3008 3072, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (40 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_2944_3072 : (∑ n ∈ Ico 2944 3072, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (80 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 2944 3008, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 3008 3072, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 2944 ≤ 3008) (by norm_num : 3008 ≤ 3072)).symm
    _ = (40 : ℤ) + (40 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_2944_3008 squarefreeInitCount_3008_3072
    _ = (80 : ℤ) := by norm_num

private theorem squarefreeInitCount_2816_3072 : (∑ n ∈ Ico 2816 3072, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (156 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 2816 2944, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 2944 3072, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 2816 ≤ 2944) (by norm_num : 2944 ≤ 3072)).symm
    _ = (76 : ℤ) + (80 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_2816_2944 squarefreeInitCount_2944_3072
    _ = (156 : ℤ) := by norm_num

theorem squarefreeInitCount_2560_3072 : (∑ n ∈ Ico 2560 3072, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (312 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 2560 2816, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 2816 3072, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 2560 ≤ 2816) (by norm_num : 2816 ≤ 3072)).symm
    _ = (156 : ℤ) + (156 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_2560_2816 squarefreeInitCount_2816_3072
    _ = (312 : ℤ) := by norm_num

private theorem squarefreeInitUpper_2560_2624 : (∑ n ∈ Ico 2560 2624, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (15450 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_2624_2688 : (∑ n ∈ Ico 2624 2688, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (14325 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_2560_2688 : (∑ n ∈ Ico 2560 2688, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (29775 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 2560 2624, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 2624 2688, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 2560 ≤ 2624) (by norm_num : 2624 ≤ 2688)).symm
    _ = (15450 : ℕ) + (14325 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_2560_2624 squarefreeInitUpper_2624_2688
    _ = (29775 : ℕ) := by norm_num

private theorem squarefreeInitUpper_2688_2752 : (∑ n ∈ Ico 2688 2752, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (14361 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_2752_2816 : (∑ n ∈ Ico 2752 2816, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (14027 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_2688_2816 : (∑ n ∈ Ico 2688 2816, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (28388 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 2688 2752, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 2752 2816, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 2688 ≤ 2752) (by norm_num : 2752 ≤ 2816)).symm
    _ = (14361 : ℕ) + (14027 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_2688_2752 squarefreeInitUpper_2752_2816
    _ = (28388 : ℕ) := by norm_num

private theorem squarefreeInitUpper_2560_2816 : (∑ n ∈ Ico 2560 2816, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (58163 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 2560 2688, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 2688 2816, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 2560 ≤ 2688) (by norm_num : 2688 ≤ 2816)).symm
    _ = (29775 : ℕ) + (28388 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_2560_2688 squarefreeInitUpper_2688_2816
    _ = (58163 : ℕ) := by norm_num

private theorem squarefreeInitUpper_2816_2880 : (∑ n ∈ Ico 2816 2880, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (13010 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_2880_2944 : (∑ n ∈ Ico 2880 2944, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (13408 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_2816_2944 : (∑ n ∈ Ico 2816 2944, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (26418 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 2816 2880, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 2880 2944, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 2816 ≤ 2880) (by norm_num : 2880 ≤ 2944)).symm
    _ = (13010 : ℕ) + (13408 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_2816_2880 squarefreeInitUpper_2880_2944
    _ = (26418 : ℕ) := by norm_num

private theorem squarefreeInitUpper_2944_3008 : (∑ n ∈ Ico 2944 3008, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (13466 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_3008_3072 : (∑ n ∈ Ico 3008 3072, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (13181 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_2944_3072 : (∑ n ∈ Ico 2944 3072, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (26647 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 2944 3008, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 3008 3072, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 2944 ≤ 3008) (by norm_num : 3008 ≤ 3072)).symm
    _ = (13466 : ℕ) + (13181 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_2944_3008 squarefreeInitUpper_3008_3072
    _ = (26647 : ℕ) := by norm_num

private theorem squarefreeInitUpper_2816_3072 : (∑ n ∈ Ico 2816 3072, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (53065 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 2816 2944, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 2944 3072, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 2816 ≤ 2944) (by norm_num : 2944 ≤ 3072)).symm
    _ = (26418 : ℕ) + (26647 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_2816_2944 squarefreeInitUpper_2944_3072
    _ = (53065 : ℕ) := by norm_num

theorem squarefreeInitUpper_2560_3072 : (∑ n ∈ Ico 2560 3072, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (111228 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 2560 2816, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 2816 3072, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 2560 ≤ 2816) (by norm_num : 2816 ≤ 3072)).symm
    _ = (58163 : ℕ) + (53065 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_2560_2816 squarefreeInitUpper_2816_3072
    _ = (111228 : ℕ) := by norm_num

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

private theorem squarefreeInitCount_3072_3136 : (∑ n ∈ Ico 3072 3136, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (41 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_3136_3200 : (∑ n ∈ Ico 3136 3200, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (37 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_3072_3200 : (∑ n ∈ Ico 3072 3200, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (78 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 3072 3136, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 3136 3200, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 3072 ≤ 3136) (by norm_num : 3136 ≤ 3200)).symm
    _ = (41 : ℤ) + (37 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_3072_3136 squarefreeInitCount_3136_3200
    _ = (78 : ℤ) := by norm_num

private theorem squarefreeInitCount_3200_3264 : (∑ n ∈ Ico 3200 3264, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (39 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_3264_3328 : (∑ n ∈ Ico 3264 3328, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (40 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_3200_3328 : (∑ n ∈ Ico 3200 3328, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (79 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 3200 3264, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 3264 3328, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 3200 ≤ 3264) (by norm_num : 3264 ≤ 3328)).symm
    _ = (39 : ℤ) + (40 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_3200_3264 squarefreeInitCount_3264_3328
    _ = (79 : ℤ) := by norm_num

private theorem squarefreeInitCount_3072_3328 : (∑ n ∈ Ico 3072 3328, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (157 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 3072 3200, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 3200 3328, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 3072 ≤ 3200) (by norm_num : 3200 ≤ 3328)).symm
    _ = (78 : ℤ) + (79 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_3072_3200 squarefreeInitCount_3200_3328
    _ = (157 : ℤ) := by norm_num

private theorem squarefreeInitCount_3328_3392 : (∑ n ∈ Ico 3328 3392, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (40 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_3392_3456 : (∑ n ∈ Ico 3392 3456, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (39 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_3328_3456 : (∑ n ∈ Ico 3328 3456, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (79 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 3328 3392, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 3392 3456, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 3328 ≤ 3392) (by norm_num : 3392 ≤ 3456)).symm
    _ = (40 : ℤ) + (39 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_3328_3392 squarefreeInitCount_3392_3456
    _ = (79 : ℤ) := by norm_num

private theorem squarefreeInitCount_3456_3520 : (∑ n ∈ Ico 3456 3520, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (38 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_3520_3584 : (∑ n ∈ Ico 3520 3584, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (38 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_3456_3584 : (∑ n ∈ Ico 3456 3584, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (76 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 3456 3520, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 3520 3584, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 3456 ≤ 3520) (by norm_num : 3520 ≤ 3584)).symm
    _ = (38 : ℤ) + (38 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_3456_3520 squarefreeInitCount_3520_3584
    _ = (76 : ℤ) := by norm_num

private theorem squarefreeInitCount_3328_3584 : (∑ n ∈ Ico 3328 3584, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (155 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 3328 3456, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 3456 3584, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 3328 ≤ 3456) (by norm_num : 3456 ≤ 3584)).symm
    _ = (79 : ℤ) + (76 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_3328_3456 squarefreeInitCount_3456_3584
    _ = (155 : ℤ) := by norm_num

theorem squarefreeInitCount_3072_3584 : (∑ n ∈ Ico 3072 3584, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (312 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 3072 3328, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 3328 3584, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 3072 ≤ 3328) (by norm_num : 3328 ≤ 3584)).symm
    _ = (157 : ℤ) + (155 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_3072_3328 squarefreeInitCount_3328_3584
    _ = (312 : ℤ) := by norm_num

private theorem squarefreeInitUpper_3072_3136 : (∑ n ∈ Ico 3072 3136, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (13227 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_3136_3200 : (∑ n ∈ Ico 3136 3200, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (11700 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_3072_3200 : (∑ n ∈ Ico 3072 3200, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (24927 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 3072 3136, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 3136 3200, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 3072 ≤ 3136) (by norm_num : 3136 ≤ 3200)).symm
    _ = (13227 : ℕ) + (11700 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_3072_3136 squarefreeInitUpper_3136_3200
    _ = (24927 : ℕ) := by norm_num

private theorem squarefreeInitUpper_3200_3264 : (∑ n ∈ Ico 3200 3264, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (12087 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_3264_3328 : (∑ n ∈ Ico 3264 3328, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (12155 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_3200_3328 : (∑ n ∈ Ico 3200 3328, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (24242 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 3200 3264, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 3264 3328, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 3200 ≤ 3264) (by norm_num : 3264 ≤ 3328)).symm
    _ = (12087 : ℕ) + (12155 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_3200_3264 squarefreeInitUpper_3264_3328
    _ = (24242 : ℕ) := by norm_num

private theorem squarefreeInitUpper_3072_3328 : (∑ n ∈ Ico 3072 3328, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (49169 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 3072 3200, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 3200 3328, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 3072 ≤ 3200) (by norm_num : 3200 ≤ 3328)).symm
    _ = (24927 : ℕ) + (24242 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_3072_3200 squarefreeInitUpper_3200_3328
    _ = (49169 : ℕ) := by norm_num

private theorem squarefreeInitUpper_3328_3392 : (∑ n ∈ Ico 3328 3392, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (11924 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_3392_3456 : (∑ n ∈ Ico 3392 3456, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (11410 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_3328_3456 : (∑ n ∈ Ico 3328 3456, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (23334 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 3328 3392, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 3392 3456, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 3328 ≤ 3392) (by norm_num : 3392 ≤ 3456)).symm
    _ = (11924 : ℕ) + (11410 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_3328_3392 squarefreeInitUpper_3392_3456
    _ = (23334 : ℕ) := by norm_num

private theorem squarefreeInitUpper_3456_3520 : (∑ n ∈ Ico 3456 3520, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (10915 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_3520_3584 : (∑ n ∈ Ico 3520 3584, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (10723 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_3456_3584 : (∑ n ∈ Ico 3456 3584, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (21638 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 3456 3520, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 3520 3584, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 3456 ≤ 3520) (by norm_num : 3520 ≤ 3584)).symm
    _ = (10915 : ℕ) + (10723 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_3456_3520 squarefreeInitUpper_3520_3584
    _ = (21638 : ℕ) := by norm_num

private theorem squarefreeInitUpper_3328_3584 : (∑ n ∈ Ico 3328 3584, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (44972 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 3328 3456, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 3456 3584, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 3328 ≤ 3456) (by norm_num : 3456 ≤ 3584)).symm
    _ = (23334 : ℕ) + (21638 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_3328_3456 squarefreeInitUpper_3456_3584
    _ = (44972 : ℕ) := by norm_num

theorem squarefreeInitUpper_3072_3584 : (∑ n ∈ Ico 3072 3584, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (94141 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 3072 3328, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 3328 3584, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 3072 ≤ 3328) (by norm_num : 3328 ≤ 3584)).symm
    _ = (49169 : ℕ) + (44972 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_3072_3328 squarefreeInitUpper_3328_3584
    _ = (94141 : ℕ) := by norm_num

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

private theorem squarefreeInitCount_3584_3648 : (∑ n ∈ Ico 3584 3648, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (39 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_3648_3712 : (∑ n ∈ Ico 3648 3712, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (39 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_3584_3712 : (∑ n ∈ Ico 3584 3712, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (78 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 3584 3648, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 3648 3712, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 3584 ≤ 3648) (by norm_num : 3648 ≤ 3712)).symm
    _ = (39 : ℤ) + (39 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_3584_3648 squarefreeInitCount_3648_3712
    _ = (78 : ℤ) := by norm_num

private theorem squarefreeInitCount_3712_3776 : (∑ n ∈ Ico 3712 3776, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (34 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_3776_3840 : (∑ n ∈ Ico 3776 3840, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (42 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_3712_3840 : (∑ n ∈ Ico 3712 3840, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (76 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 3712 3776, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 3776 3840, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 3712 ≤ 3776) (by norm_num : 3776 ≤ 3840)).symm
    _ = (34 : ℤ) + (42 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_3712_3776 squarefreeInitCount_3776_3840
    _ = (76 : ℤ) := by norm_num

private theorem squarefreeInitCount_3584_3840 : (∑ n ∈ Ico 3584 3840, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (154 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 3584 3712, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 3712 3840, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 3584 ≤ 3712) (by norm_num : 3712 ≤ 3840)).symm
    _ = (78 : ℤ) + (76 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_3584_3712 squarefreeInitCount_3712_3840
    _ = (154 : ℤ) := by norm_num

private theorem squarefreeInitCount_3840_3904 : (∑ n ∈ Ico 3840 3904, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (39 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_3904_3968 : (∑ n ∈ Ico 3904 3968, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (41 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_3840_3968 : (∑ n ∈ Ico 3840 3968, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (80 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 3840 3904, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 3904 3968, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 3840 ≤ 3904) (by norm_num : 3904 ≤ 3968)).symm
    _ = (39 : ℤ) + (41 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_3840_3904 squarefreeInitCount_3904_3968
    _ = (80 : ℤ) := by norm_num

private theorem squarefreeInitCount_3968_4032 : (∑ n ∈ Ico 3968 4032, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (37 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_4032_4096 : (∑ n ∈ Ico 4032 4096, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (39 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_3968_4096 : (∑ n ∈ Ico 3968 4096, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (76 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 3968 4032, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 4032 4096, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 3968 ≤ 4032) (by norm_num : 4032 ≤ 4096)).symm
    _ = (37 : ℤ) + (39 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_3968_4032 squarefreeInitCount_4032_4096
    _ = (76 : ℤ) := by norm_num

private theorem squarefreeInitCount_3840_4096 : (∑ n ∈ Ico 3840 4096, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (156 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 3840 3968, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 3968 4096, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 3840 ≤ 3968) (by norm_num : 3968 ≤ 4096)).symm
    _ = (80 : ℤ) + (76 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_3840_3968 squarefreeInitCount_3968_4096
    _ = (156 : ℤ) := by norm_num

theorem squarefreeInitCount_3584_4096 : (∑ n ∈ Ico 3584 4096, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (310 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 3584 3840, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 3840 4096, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 3584 ≤ 3840) (by norm_num : 3840 ≤ 4096)).symm
    _ = (154 : ℤ) + (156 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_3584_3840 squarefreeInitCount_3840_4096
    _ = (310 : ℤ) := by norm_num

private theorem squarefreeInitUpper_3584_3648 : (∑ n ∈ Ico 3584 3648, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (10808 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_3648_3712 : (∑ n ∈ Ico 3648 3712, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (10616 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_3584_3712 : (∑ n ∈ Ico 3584 3712, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (21424 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 3584 3648, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 3648 3712, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 3584 ≤ 3648) (by norm_num : 3648 ≤ 3712)).symm
    _ = (10808 : ℕ) + (10616 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_3584_3648 squarefreeInitUpper_3648_3712
    _ = (21424 : ℕ) := by norm_num

private theorem squarefreeInitUpper_3712_3776 : (∑ n ∈ Ico 3712 3776, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (9101 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_3776_3840 : (∑ n ∈ Ico 3776 3840, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (11053 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_3712_3840 : (∑ n ∈ Ico 3712 3840, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (20154 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 3712 3776, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 3776 3840, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 3712 ≤ 3776) (by norm_num : 3776 ≤ 3840)).symm
    _ = (9101 : ℕ) + (11053 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_3712_3776 squarefreeInitUpper_3776_3840
    _ = (20154 : ℕ) := by norm_num

private theorem squarefreeInitUpper_3584_3840 : (∑ n ∈ Ico 3584 3840, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (41578 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 3584 3712, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 3712 3840, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 3584 ≤ 3712) (by norm_num : 3712 ≤ 3840)).symm
    _ = (21424 : ℕ) + (20154 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_3584_3712 squarefreeInitUpper_3712_3840
    _ = (41578 : ℕ) := by norm_num

private theorem squarefreeInitUpper_3840_3904 : (∑ n ∈ Ico 3840 3904, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (10092 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_3904_3968 : (∑ n ∈ Ico 3904 3968, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (10435 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_3840_3968 : (∑ n ∈ Ico 3840 3968, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (20527 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 3840 3904, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 3904 3968, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 3840 ≤ 3904) (by norm_num : 3904 ≤ 3968)).symm
    _ = (10092 : ℕ) + (10435 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_3840_3904 squarefreeInitUpper_3904_3968
    _ = (20527 : ℕ) := by norm_num

private theorem squarefreeInitUpper_3968_4032 : (∑ n ∈ Ico 3968 4032, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (9267 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_4032_4096 : (∑ n ∈ Ico 4032 4096, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (9616 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_3968_4096 : (∑ n ∈ Ico 3968 4096, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (18883 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 3968 4032, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 4032 4096, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 3968 ≤ 4032) (by norm_num : 4032 ≤ 4096)).symm
    _ = (9267 : ℕ) + (9616 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_3968_4032 squarefreeInitUpper_4032_4096
    _ = (18883 : ℕ) := by norm_num

private theorem squarefreeInitUpper_3840_4096 : (∑ n ∈ Ico 3840 4096, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (39410 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 3840 3968, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 3968 4096, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 3840 ≤ 3968) (by norm_num : 3968 ≤ 4096)).symm
    _ = (20527 : ℕ) + (18883 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_3840_3968 squarefreeInitUpper_3968_4096
    _ = (39410 : ℕ) := by norm_num

theorem squarefreeInitUpper_3584_4096 : (∑ n ∈ Ico 3584 4096, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (80988 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 3584 3840, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 3840 4096, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 3584 ≤ 3840) (by norm_num : 3840 ≤ 4096)).symm
    _ = (41578 : ℕ) + (39410 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_3584_3840 squarefreeInitUpper_3840_4096
    _ = (80988 : ℕ) := by norm_num

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

private theorem squarefreeInitCount_4096_4160 : (∑ n ∈ Ico 4096 4160, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (39 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_4160_4224 : (∑ n ∈ Ico 4160 4224, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (39 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_4096_4224 : (∑ n ∈ Ico 4096 4224, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (78 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 4096 4160, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 4160 4224, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 4096 ≤ 4160) (by norm_num : 4160 ≤ 4224)).symm
    _ = (39 : ℤ) + (39 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_4096_4160 squarefreeInitCount_4160_4224
    _ = (78 : ℤ) := by norm_num

private theorem squarefreeInitCount_4224_4288 : (∑ n ∈ Ico 4224 4288, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (39 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_4288_4352 : (∑ n ∈ Ico 4288 4352, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (39 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_4224_4352 : (∑ n ∈ Ico 4224 4352, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (78 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 4224 4288, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 4288 4352, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 4224 ≤ 4288) (by norm_num : 4288 ≤ 4352)).symm
    _ = (39 : ℤ) + (39 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_4224_4288 squarefreeInitCount_4288_4352
    _ = (78 : ℤ) := by norm_num

private theorem squarefreeInitCount_4096_4352 : (∑ n ∈ Ico 4096 4352, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (156 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 4096 4224, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 4224 4352, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 4096 ≤ 4224) (by norm_num : 4224 ≤ 4352)).symm
    _ = (78 : ℤ) + (78 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_4096_4224 squarefreeInitCount_4224_4352
    _ = (156 : ℤ) := by norm_num

private theorem squarefreeInitCount_4352_4416 : (∑ n ∈ Ico 4352 4416, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (40 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_4416_4480 : (∑ n ∈ Ico 4416 4480, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (37 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_4352_4480 : (∑ n ∈ Ico 4352 4480, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (77 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 4352 4416, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 4416 4480, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 4352 ≤ 4416) (by norm_num : 4416 ≤ 4480)).symm
    _ = (40 : ℤ) + (37 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_4352_4416 squarefreeInitCount_4416_4480
    _ = (77 : ℤ) := by norm_num

private theorem squarefreeInitCount_4480_4544 : (∑ n ∈ Ico 4480 4544, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (41 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_4544_4608 : (∑ n ∈ Ico 4544 4608, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (37 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_4480_4608 : (∑ n ∈ Ico 4480 4608, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (78 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 4480 4544, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 4544 4608, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 4480 ≤ 4544) (by norm_num : 4544 ≤ 4608)).symm
    _ = (41 : ℤ) + (37 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_4480_4544 squarefreeInitCount_4544_4608
    _ = (78 : ℤ) := by norm_num

private theorem squarefreeInitCount_4352_4608 : (∑ n ∈ Ico 4352 4608, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (155 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 4352 4480, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 4480 4608, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 4352 ≤ 4480) (by norm_num : 4480 ≤ 4608)).symm
    _ = (77 : ℤ) + (78 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_4352_4480 squarefreeInitCount_4480_4608
    _ = (155 : ℤ) := by norm_num

theorem squarefreeInitCount_4096_4608 : (∑ n ∈ Ico 4096 4608, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (311 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 4096 4352, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 4352 4608, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 4096 ≤ 4352) (by norm_num : 4352 ≤ 4608)).symm
    _ = (156 : ℤ) + (155 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_4096_4352 squarefreeInitCount_4352_4608
    _ = (311 : ℤ) := by norm_num

private theorem squarefreeInitUpper_4096_4160 : (∑ n ∈ Ico 4096 4160, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (9467 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_4160_4224 : (∑ n ∈ Ico 4160 4224, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (9325 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_4096_4224 : (∑ n ∈ Ico 4096 4224, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (18792 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 4096 4160, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 4160 4224, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 4096 ≤ 4160) (by norm_num : 4160 ≤ 4224)).symm
    _ = (9467 : ℕ) + (9325 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_4096_4160 squarefreeInitUpper_4160_4224
    _ = (18792 : ℕ) := by norm_num

private theorem squarefreeInitUpper_4224_4288 : (∑ n ∈ Ico 4224 4288, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (9181 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_4288_4352 : (∑ n ∈ Ico 4288 4352, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (9051 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_4224_4352 : (∑ n ∈ Ico 4224 4352, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (18232 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 4224 4288, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 4288 4352, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 4224 ≤ 4288) (by norm_num : 4288 ≤ 4352)).symm
    _ = (9181 : ℕ) + (9051 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_4224_4288 squarefreeInitUpper_4288_4352
    _ = (18232 : ℕ) := by norm_num

private theorem squarefreeInitUpper_4096_4352 : (∑ n ∈ Ico 4096 4352, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (37024 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 4096 4224, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 4224 4352, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 4096 ≤ 4224) (by norm_num : 4224 ≤ 4352)).symm
    _ = (18792 : ℕ) + (18232 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_4096_4224 squarefreeInitUpper_4224_4352
    _ = (37024 : ℕ) := by norm_num

private theorem squarefreeInitUpper_4352_4416 : (∑ n ∈ Ico 4352 4416, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (9142 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_4416_4480 : (∑ n ∈ Ico 4416 4480, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (8337 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_4352_4480 : (∑ n ∈ Ico 4352 4480, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (17479 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 4352 4416, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 4416 4480, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 4352 ≤ 4416) (by norm_num : 4416 ≤ 4480)).symm
    _ = (9142 : ℕ) + (8337 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_4352_4416 squarefreeInitUpper_4416_4480
    _ = (17479 : ℕ) := by norm_num

private theorem squarefreeInitUpper_4480_4544 : (∑ n ∈ Ico 4480 4544, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (9106 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_4544_4608 : (∑ n ∈ Ico 4544 4608, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (8104 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_4480_4608 : (∑ n ∈ Ico 4480 4608, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (17210 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 4480 4544, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 4544 4608, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 4480 ≤ 4544) (by norm_num : 4544 ≤ 4608)).symm
    _ = (9106 : ℕ) + (8104 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_4480_4544 squarefreeInitUpper_4544_4608
    _ = (17210 : ℕ) := by norm_num

private theorem squarefreeInitUpper_4352_4608 : (∑ n ∈ Ico 4352 4608, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (34689 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 4352 4480, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 4480 4608, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 4352 ≤ 4480) (by norm_num : 4480 ≤ 4608)).symm
    _ = (17479 : ℕ) + (17210 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_4352_4480 squarefreeInitUpper_4480_4608
    _ = (34689 : ℕ) := by norm_num

theorem squarefreeInitUpper_4096_4608 : (∑ n ∈ Ico 4096 4608, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (71713 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 4096 4352, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 4352 4608, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 4096 ≤ 4352) (by norm_num : 4352 ≤ 4608)).symm
    _ = (37024 : ℕ) + (34689 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_4096_4352 squarefreeInitUpper_4352_4608
    _ = (71713 : ℕ) := by norm_num

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

private theorem squarefreeInitCount_4608_4672 : (∑ n ∈ Ico 4608 4672, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (39 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_4672_4736 : (∑ n ∈ Ico 4672 4736, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (40 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_4608_4736 : (∑ n ∈ Ico 4608 4736, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (79 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 4608 4672, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 4672 4736, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 4608 ≤ 4672) (by norm_num : 4672 ≤ 4736)).symm
    _ = (39 : ℤ) + (40 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_4608_4672 squarefreeInitCount_4672_4736
    _ = (79 : ℤ) := by norm_num

private theorem squarefreeInitCount_4736_4800 : (∑ n ∈ Ico 4736 4800, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (40 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_4800_4864 : (∑ n ∈ Ico 4800 4864, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (39 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_4736_4864 : (∑ n ∈ Ico 4736 4864, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (79 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 4736 4800, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 4800 4864, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 4736 ≤ 4800) (by norm_num : 4800 ≤ 4864)).symm
    _ = (40 : ℤ) + (39 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_4736_4800 squarefreeInitCount_4800_4864
    _ = (79 : ℤ) := by norm_num

private theorem squarefreeInitCount_4608_4864 : (∑ n ∈ Ico 4608 4864, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (158 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 4608 4736, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 4736 4864, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 4608 ≤ 4736) (by norm_num : 4736 ≤ 4864)).symm
    _ = (79 : ℤ) + (79 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_4608_4736 squarefreeInitCount_4736_4864
    _ = (158 : ℤ) := by norm_num

private theorem squarefreeInitCount_4864_4928 : (∑ n ∈ Ico 4864 4928, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (38 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_4928_4992 : (∑ n ∈ Ico 4928 4992, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (40 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_4864_4992 : (∑ n ∈ Ico 4864 4992, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (78 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 4864 4928, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 4928 4992, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 4864 ≤ 4928) (by norm_num : 4928 ≤ 4992)).symm
    _ = (38 : ℤ) + (40 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_4864_4928 squarefreeInitCount_4928_4992
    _ = (78 : ℤ) := by norm_num

private theorem squarefreeInitCount_4992_5056 : (∑ n ∈ Ico 4992 5056, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (35 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_5056_5120 : (∑ n ∈ Ico 5056 5120, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (40 : ℤ) := by decide +kernel

private theorem squarefreeInitCount_4992_5120 : (∑ n ∈ Ico 4992 5120, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (75 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 4992 5056, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 5056 5120, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 4992 ≤ 5056) (by norm_num : 5056 ≤ 5120)).symm
    _ = (35 : ℤ) + (40 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_4992_5056 squarefreeInitCount_5056_5120
    _ = (75 : ℤ) := by norm_num

private theorem squarefreeInitCount_4864_5120 : (∑ n ∈ Ico 4864 5120, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (153 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 4864 4992, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 4992 5120, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 4864 ≤ 4992) (by norm_num : 4992 ≤ 5120)).symm
    _ = (78 : ℤ) + (75 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_4864_4992 squarefreeInitCount_4992_5120
    _ = (153 : ℤ) := by norm_num

theorem squarefreeInitCount_4608_5120 : (∑ n ∈ Ico 4608 5120, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (311 : ℤ) := by
  calc
    _ = (∑ n ∈ Ico 4608 4864, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) + (∑ n ∈ Ico 4864 5120, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) (by norm_num : 4608 ≤ 4864) (by norm_num : 4864 ≤ 5120)).symm
    _ = (158 : ℤ) + (153 : ℤ) := congrArg₂ (· + ·) squarefreeInitCount_4608_4864 squarefreeInitCount_4864_5120
    _ = (311 : ℤ) := by norm_num

private theorem squarefreeInitUpper_4608_4672 : (∑ n ∈ Ico 4608 4672, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (8426 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_4672_4736 : (∑ n ∈ Ico 4672 4736, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (8522 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_4608_4736 : (∑ n ∈ Ico 4608 4736, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (16948 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 4608 4672, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 4672 4736, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 4608 ≤ 4672) (by norm_num : 4672 ≤ 4736)).symm
    _ = (8426 : ℕ) + (8522 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_4608_4672 squarefreeInitUpper_4672_4736
    _ = (16948 : ℕ) := by norm_num

private theorem squarefreeInitUpper_4736_4800 : (∑ n ∈ Ico 4736 4800, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (8407 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_4800_4864 : (∑ n ∈ Ico 4800 4864, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (8087 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_4736_4864 : (∑ n ∈ Ico 4736 4864, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (16494 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 4736 4800, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 4800 4864, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 4736 ≤ 4800) (by norm_num : 4800 ≤ 4864)).symm
    _ = (8407 : ℕ) + (8087 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_4736_4800 squarefreeInitUpper_4800_4864
    _ = (16494 : ℕ) := by norm_num

private theorem squarefreeInitUpper_4608_4864 : (∑ n ∈ Ico 4608 4864, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (33442 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 4608 4736, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 4736 4864, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 4608 ≤ 4736) (by norm_num : 4736 ≤ 4864)).symm
    _ = (16948 : ℕ) + (16494 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_4608_4736 squarefreeInitUpper_4736_4864
    _ = (33442 : ℕ) := by norm_num

private theorem squarefreeInitUpper_4864_4928 : (∑ n ∈ Ico 4864 4928, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (7782 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_4928_4992 : (∑ n ∈ Ico 4928 4992, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (8084 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_4864_4992 : (∑ n ∈ Ico 4864 4992, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (15866 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 4864 4928, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 4928 4992, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 4864 ≤ 4928) (by norm_num : 4928 ≤ 4992)).symm
    _ = (7782 : ℕ) + (8084 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_4864_4928 squarefreeInitUpper_4928_4992
    _ = (15866 : ℕ) := by norm_num

private theorem squarefreeInitUpper_4992_5056 : (∑ n ∈ Ico 4992 5056, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (6986 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_5056_5120 : (∑ n ∈ Ico 5056 5120, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (7879 : ℕ) := by decide +kernel

private theorem squarefreeInitUpper_4992_5120 : (∑ n ∈ Ico 4992 5120, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (14865 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 4992 5056, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 5056 5120, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 4992 ≤ 5056) (by norm_num : 5056 ≤ 5120)).symm
    _ = (6986 : ℕ) + (7879 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_4992_5056 squarefreeInitUpper_5056_5120
    _ = (14865 : ℕ) := by norm_num

private theorem squarefreeInitUpper_4864_5120 : (∑ n ∈ Ico 4864 5120, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (30731 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 4864 4992, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 4992 5120, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 4864 ≤ 4992) (by norm_num : 4992 ≤ 5120)).symm
    _ = (15866 : ℕ) + (14865 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_4864_4992 squarefreeInitUpper_4992_5120
    _ = (30731 : ℕ) := by norm_num

theorem squarefreeInitUpper_4608_5120 : (∑ n ∈ Ico 4608 5120, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (64173 : ℕ) := by
  calc
    _ = (∑ n ∈ Ico 4608 4864, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) + (∑ n ∈ Ico 4864 5120, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) :=
      (Finset.sum_Ico_consecutive (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) (by norm_num : 4608 ≤ 4864) (by norm_num : 4864 ≤ 5120)).symm
    _ = (33442 : ℕ) + (30731 : ℕ) := congrArg₂ (· + ·) squarefreeInitUpper_4608_4864 squarefreeInitUpper_4864_5120
    _ = (64173 : ℕ) := by norm_num

end Helfgott
end

section
set_option autoImplicit false
set_option Elab.async false
open Finset Nat
open scoped BigOperators
namespace Helfgott
theorem squarefree_harmonic_numeric_group000_checked_native :
  ((∑ n ∈ Ico 0 512, ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) = (314 : ℤ) ∧
    (∑ n ∈ Ico 0 512, mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) = (4839841 : ℕ)) ∧
  ((∑ n ∈ Ico 512 1024, ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) = (310 : ℤ) ∧
    (∑ n ∈ Ico 512 1024, mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) = (418705 : ℕ)) ∧
  ((∑ n ∈ Ico 1024 1536, ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) = (313 : ℤ) ∧
    (∑ n ∈ Ico 1024 1536, mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) = (247623 : ℕ)) ∧
  ((∑ n ∈ Ico 1536 2048, ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) = (308 : ℤ) ∧
    (∑ n ∈ Ico 1536 2048, mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) = (173112 : ℕ)) ∧
  ((∑ n ∈ Ico 2048 2560, ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) = (312 : ℤ) ∧
    (∑ n ∈ Ico 2048 2560, mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) = (136122 : ℕ)) ∧
  ((∑ n ∈ Ico 2560 3072, ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) = (312 : ℤ) ∧
    (∑ n ∈ Ico 2560 3072, mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) = (111228 : ℕ)) ∧
  ((∑ n ∈ Ico 3072 3584, ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) = (312 : ℤ) ∧
    (∑ n ∈ Ico 3072 3584, mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) = (94141 : ℕ)) ∧
  ((∑ n ∈ Ico 3584 4096, ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) = (310 : ℤ) ∧
    (∑ n ∈ Ico 3584 4096, mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) = (80988 : ℕ)) ∧
  ((∑ n ∈ Ico 4096 4608, ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) = (311 : ℤ) ∧
    (∑ n ∈ Ico 4096 4608, mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) = (71713 : ℕ)) ∧
  ((∑ n ∈ Ico 4608 5120, ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) = (311 : ℤ) ∧
    (∑ n ∈ Ico 4608 5120, mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) = (64173 : ℕ)) := ⟨⟨squarefreeInitCount_0_512, squarefreeInitUpper_0_512⟩, ⟨⟨squarefreeInitCount_512_1024, squarefreeInitUpper_512_1024⟩, ⟨⟨squarefreeInitCount_1024_1536, squarefreeInitUpper_1024_1536⟩, ⟨⟨squarefreeInitCount_1536_2048, squarefreeInitUpper_1536_2048⟩, ⟨⟨squarefreeInitCount_2048_2560, squarefreeInitUpper_2048_2560⟩, ⟨⟨squarefreeInitCount_2560_3072, squarefreeInitUpper_2560_3072⟩, ⟨⟨squarefreeInitCount_3072_3584, squarefreeInitUpper_3072_3584⟩, ⟨⟨squarefreeInitCount_3584_4096, squarefreeInitUpper_3584_4096⟩, ⟨⟨squarefreeInitCount_4096_4608, squarefreeInitUpper_4096_4608⟩, ⟨squarefreeInitCount_4608_5120, squarefreeInitUpper_4608_5120⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Helfgott
end

open Helfgott Finset Nat
open scoped BigOperators
theorem solution :
  ((∑ n ∈ Ico 0 512, ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) = (314 : ℤ) ∧
    (∑ n ∈ Ico 0 512, mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) = (4839841 : ℕ)) ∧
  ((∑ n ∈ Ico 512 1024, ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) = (310 : ℤ) ∧
    (∑ n ∈ Ico 512 1024, mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) = (418705 : ℕ)) ∧
  ((∑ n ∈ Ico 1024 1536, ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) = (313 : ℤ) ∧
    (∑ n ∈ Ico 1024 1536, mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) = (247623 : ℕ)) ∧
  ((∑ n ∈ Ico 1536 2048, ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) = (308 : ℤ) ∧
    (∑ n ∈ Ico 1536 2048, mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) = (173112 : ℕ)) ∧
  ((∑ n ∈ Ico 2048 2560, ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) = (312 : ℤ) ∧
    (∑ n ∈ Ico 2048 2560, mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) = (136122 : ℕ)) ∧
  ((∑ n ∈ Ico 2560 3072, ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) = (312 : ℤ) ∧
    (∑ n ∈ Ico 2560 3072, mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) = (111228 : ℕ)) ∧
  ((∑ n ∈ Ico 3072 3584, ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) = (312 : ℤ) ∧
    (∑ n ∈ Ico 3072 3584, mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) = (94141 : ℕ)) ∧
  ((∑ n ∈ Ico 3584 4096, ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) = (310 : ℤ) ∧
    (∑ n ∈ Ico 3584 4096, mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) = (80988 : ℕ)) ∧
  ((∑ n ∈ Ico 4096 4608, ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) = (311 : ℤ) ∧
    (∑ n ∈ Ico 4096 4608, mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) = (71713 : ℕ)) ∧
  ((∑ n ∈ Ico 4608 5120, ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) = (311 : ℤ) ∧
    (∑ n ∈ Ico 4608 5120, mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) = (64173 : ℕ)) := Helfgott.squarefree_harmonic_numeric_group000_checked_native
#print axioms solution
