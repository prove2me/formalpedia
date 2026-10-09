-- Prove2me | solution 1 for Helfgott.cdemPrefixGroup034_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T02:27:39.375984+00:00
-- url     : https://prove2.me/submissions/0c48b1b8-6b7c-4062-b7ef-74f74201fc01

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset
open scoped BigOperators
namespace Helfgott
private theorem cdemPrefixStats_139264_139328 :
    (∑ n ∈ Ico 139264 139328, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 139264 139328, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 139264 139328, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-251300 : ℤ) ∧
    (∑ n ∈ Ico 139264 139328, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5026022329772607763982871199 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_139328_139392 :
    (∑ n ∈ Ico 139328 139392, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 139328 139392, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 139328 139392, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-215265 : ℤ) ∧
    (∑ n ∈ Ico 139328 139392, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4305354880945206107675204881 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_139264_139392 :
    (∑ n ∈ Ico 139264 139392, mobiusTreeValue 16 mobiusTable1200001 n) = (-13 : ℤ) ∧
    (∑ n ∈ Ico 139264 139392, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 139264 139392, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-466565 : ℤ) ∧
    (∑ n ∈ Ico 139264 139392, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9331377210717813871658076080 : ℤ) := by
  rcases cdemPrefixStats_139264_139328 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_139328_139392 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 139264 ≤ 139328) (by norm_num : 139328 ≤ 139392), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 139264 ≤ 139328) (by norm_num : 139328 ≤ 139392), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 139264 ≤ 139328) (by norm_num : 139328 ≤ 139392), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 139264 ≤ 139328) (by norm_num : 139328 ≤ 139392), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_139392_139456 :
    (∑ n ∈ Ico 139392 139456, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 139392 139456, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 139392 139456, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (35865 : ℤ) ∧
    (∑ n ∈ Ico 139392 139456, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (717231427275520567182808728 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_139456_139520 :
    (∑ n ∈ Ico 139456 139520, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 139456 139520, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 139456 139520, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (71717 : ℤ) ∧
    (∑ n ∈ Ico 139456 139520, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1434329033155295030350720879 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_139392_139520 :
    (∑ n ∈ Ico 139392 139520, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 139392 139520, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 139392 139520, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (107582 : ℤ) ∧
    (∑ n ∈ Ico 139392 139520, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2151560460430815597533529607 : ℤ) := by
  rcases cdemPrefixStats_139392_139456 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_139456_139520 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 139392 ≤ 139456) (by norm_num : 139456 ≤ 139520), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 139392 ≤ 139456) (by norm_num : 139456 ≤ 139520), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 139392 ≤ 139456) (by norm_num : 139456 ≤ 139520), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 139392 ≤ 139456) (by norm_num : 139456 ≤ 139520), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_139264_139520 :
    (∑ n ∈ Ico 139264 139520, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 139264 139520, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (154 : ℕ) ∧
    (∑ n ∈ Ico 139264 139520, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-358983 : ℤ) ∧
    (∑ n ∈ Ico 139264 139520, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7179816750286998274124546473 : ℤ) := by
  rcases cdemPrefixStats_139264_139392 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_139392_139520 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 139264 ≤ 139392) (by norm_num : 139392 ≤ 139520), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 139264 ≤ 139392) (by norm_num : 139392 ≤ 139520), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 139264 ≤ 139392) (by norm_num : 139392 ≤ 139520), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 139264 ≤ 139392) (by norm_num : 139392 ≤ 139520), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_139520_139584 :
    (∑ n ∈ Ico 139520 139584, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 139520 139584, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 139520 139584, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (394128 : ℤ) ∧
    (∑ n ∈ Ico 139520 139584, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7882700396078687910868296931 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_139584_139648 :
    (∑ n ∈ Ico 139584 139648, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 139584 139648, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 139584 139648, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-19 : ℤ) ∧
    (∑ n ∈ Ico 139584 139648, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-379558419682980117462461 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_139520_139648 :
    (∑ n ∈ Ico 139520 139648, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 139520 139648, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (75 : ℕ) ∧
    (∑ n ∈ Ico 139520 139648, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (394109 : ℤ) ∧
    (∑ n ∈ Ico 139520 139648, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7882320837659004930750834470 : ℤ) := by
  rcases cdemPrefixStats_139520_139584 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_139584_139648 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 139520 ≤ 139584) (by norm_num : 139584 ≤ 139648), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 139520 ≤ 139584) (by norm_num : 139584 ≤ 139648), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 139520 ≤ 139584) (by norm_num : 139584 ≤ 139648), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 139520 ≤ 139584) (by norm_num : 139584 ≤ 139648), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_139648_139712 :
    (∑ n ∈ Ico 139648 139712, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 139648 139712, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 139648 139712, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (322164 : ℤ) ∧
    (∑ n ∈ Ico 139648 139712, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6443391322498506337453162872 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_139712_139776 :
    (∑ n ∈ Ico 139712 139776, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 139712 139776, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 139712 139776, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-178864 : ℤ) ∧
    (∑ n ∈ Ico 139712 139776, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3577377096934820992907978345 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_139648_139776 :
    (∑ n ∈ Ico 139648 139776, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 139648 139776, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 139648 139776, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (143300 : ℤ) ∧
    (∑ n ∈ Ico 139648 139776, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2866014225563685344545184527 : ℤ) := by
  rcases cdemPrefixStats_139648_139712 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_139712_139776 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 139648 ≤ 139712) (by norm_num : 139712 ≤ 139776), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 139648 ≤ 139712) (by norm_num : 139712 ≤ 139776), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 139648 ≤ 139712) (by norm_num : 139712 ≤ 139776), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 139648 ≤ 139712) (by norm_num : 139712 ≤ 139776), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_139520_139776 :
    (∑ n ∈ Ico 139520 139776, mobiusTreeValue 16 mobiusTable1200001 n) = (15 : ℤ) ∧
    (∑ n ∈ Ico 139520 139776, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (153 : ℕ) ∧
    (∑ n ∈ Ico 139520 139776, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (537409 : ℤ) ∧
    (∑ n ∈ Ico 139520 139776, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (10748335063222690275296018997 : ℤ) := by
  rcases cdemPrefixStats_139520_139648 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_139648_139776 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 139520 ≤ 139648) (by norm_num : 139648 ≤ 139776), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 139520 ≤ 139648) (by norm_num : 139648 ≤ 139776), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 139520 ≤ 139648) (by norm_num : 139648 ≤ 139776), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 139520 ≤ 139648) (by norm_num : 139648 ≤ 139776), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_139264_139776 :
    (∑ n ∈ Ico 139264 139776, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 139264 139776, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (307 : ℕ) ∧
    (∑ n ∈ Ico 139264 139776, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (178426 : ℤ) ∧
    (∑ n ∈ Ico 139264 139776, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3568518312935692001171472524 : ℤ) := by
  rcases cdemPrefixStats_139264_139520 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_139520_139776 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 139264 ≤ 139520) (by norm_num : 139520 ≤ 139776), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 139264 ≤ 139520) (by norm_num : 139520 ≤ 139776), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 139264 ≤ 139520) (by norm_num : 139520 ≤ 139776), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 139264 ≤ 139520) (by norm_num : 139520 ≤ 139776), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_139776_139840 :
    (∑ n ∈ Ico 139776 139840, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 139776 139840, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (42 : ℕ) ∧
    (∑ n ∈ Ico 139776 139840, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-143055 : ℤ) ∧
    (∑ n ∈ Ico 139776 139840, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2861153808119260520778708891 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_139840_139904 :
    (∑ n ∈ Ico 139840 139904, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 139840 139904, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 139840 139904, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (35747 : ℤ) ∧
    (∑ n ∈ Ico 139840 139904, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (714944499685881534500418528 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_139776_139904 :
    (∑ n ∈ Ico 139776 139904, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 139776 139904, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (81 : ℕ) ∧
    (∑ n ∈ Ico 139776 139904, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-107308 : ℤ) ∧
    (∑ n ∈ Ico 139776 139904, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2146209308433378986278290363 : ℤ) := by
  rcases cdemPrefixStats_139776_139840 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_139840_139904 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 139776 ≤ 139840) (by norm_num : 139840 ≤ 139904), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 139776 ≤ 139840) (by norm_num : 139840 ≤ 139904), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 139776 ≤ 139840) (by norm_num : 139840 ≤ 139904), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 139776 ≤ 139840) (by norm_num : 139840 ≤ 139904), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_139904_139968 :
    (∑ n ∈ Ico 139904 139968, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 139904 139968, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 139904 139968, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (178666 : ℤ) ∧
    (∑ n ∈ Ico 139904 139968, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3573363227198513554570148254 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_139968_140032 :
    (∑ n ∈ Ico 139968 140032, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 139968 140032, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 139968 140032, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (71416 : ℤ) ∧
    (∑ n ∈ Ico 139968 140032, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1428357139935044077529669898 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_139904_140032 :
    (∑ n ∈ Ico 139904 140032, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 139904 140032, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 139904 140032, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (250082 : ℤ) ∧
    (∑ n ∈ Ico 139904 140032, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5001720367133557632099818152 : ℤ) := by
  rcases cdemPrefixStats_139904_139968 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_139968_140032 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 139904 ≤ 139968) (by norm_num : 139968 ≤ 140032), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 139904 ≤ 139968) (by norm_num : 139968 ≤ 140032), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 139904 ≤ 139968) (by norm_num : 139968 ≤ 140032), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 139904 ≤ 139968) (by norm_num : 139968 ≤ 140032), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_139776_140032 :
    (∑ n ∈ Ico 139776 140032, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 139776 140032, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (160 : ℕ) ∧
    (∑ n ∈ Ico 139776 140032, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (142774 : ℤ) ∧
    (∑ n ∈ Ico 139776 140032, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2855511058700178645821527789 : ℤ) := by
  rcases cdemPrefixStats_139776_139904 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_139904_140032 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 139776 ≤ 139904) (by norm_num : 139904 ≤ 140032), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 139776 ≤ 139904) (by norm_num : 139904 ≤ 140032), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 139776 ≤ 139904) (by norm_num : 139904 ≤ 140032), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 139776 ≤ 139904) (by norm_num : 139904 ≤ 140032), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_140032_140096 :
    (∑ n ∈ Ico 140032 140096, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 140032 140096, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 140032 140096, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (107087 : ℤ) ∧
    (∑ n ∈ Ico 140032 140096, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2141760870009640258677152856 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_140096_140160 :
    (∑ n ∈ Ico 140096 140160, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 140096 140160, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 140096 140160, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (107041 : ℤ) ∧
    (∑ n ∈ Ico 140096 140160, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2140828533236693184825371703 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_140032_140160 :
    (∑ n ∈ Ico 140032 140160, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 140032 140160, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 140032 140160, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (214128 : ℤ) ∧
    (∑ n ∈ Ico 140032 140160, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4282589403246333443502524559 : ℤ) := by
  rcases cdemPrefixStats_140032_140096 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_140096_140160 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 140032 ≤ 140096) (by norm_num : 140096 ≤ 140160), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 140032 ≤ 140096) (by norm_num : 140096 ≤ 140160), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 140032 ≤ 140096) (by norm_num : 140096 ≤ 140160), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 140032 ≤ 140096) (by norm_num : 140096 ≤ 140160), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_140160_140224 :
    (∑ n ∈ Ico 140160 140224, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 140160 140224, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 140160 140224, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-142646 : ℤ) ∧
    (∑ n ∈ Ico 140160 140224, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2853046670809133877339866897 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_140224_140288 :
    (∑ n ∈ Ico 140224 140288, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 140224 140288, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 140224 140288, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (142568 : ℤ) ∧
    (∑ n ∈ Ico 140224 140288, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2851378972426926715768964270 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_140160_140288 :
    (∑ n ∈ Ico 140160 140288, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 140160 140288, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 140160 140288, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-78 : ℤ) ∧
    (∑ n ∈ Ico 140160 140288, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1667698382207161570902627 : ℤ) := by
  rcases cdemPrefixStats_140160_140224 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_140224_140288 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 140160 ≤ 140224) (by norm_num : 140224 ≤ 140288), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 140160 ≤ 140224) (by norm_num : 140224 ≤ 140288), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 140160 ≤ 140224) (by norm_num : 140224 ≤ 140288), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 140160 ≤ 140224) (by norm_num : 140224 ≤ 140288), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_140032_140288 :
    (∑ n ∈ Ico 140032 140288, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 140032 140288, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (154 : ℕ) ∧
    (∑ n ∈ Ico 140032 140288, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (214050 : ℤ) ∧
    (∑ n ∈ Ico 140032 140288, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4280921704864126281931621932 : ℤ) := by
  rcases cdemPrefixStats_140032_140160 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_140160_140288 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 140032 ≤ 140160) (by norm_num : 140160 ≤ 140288), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 140032 ≤ 140160) (by norm_num : 140160 ≤ 140288), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 140032 ≤ 140160) (by norm_num : 140160 ≤ 140288), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 140032 ≤ 140160) (by norm_num : 140160 ≤ 140288), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_139776_140288 :
    (∑ n ∈ Ico 139776 140288, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 139776 140288, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (314 : ℕ) ∧
    (∑ n ∈ Ico 139776 140288, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (356824 : ℤ) ∧
    (∑ n ∈ Ico 139776 140288, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7136432763564304927753149721 : ℤ) := by
  rcases cdemPrefixStats_139776_140032 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_140032_140288 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 139776 ≤ 140032) (by norm_num : 140032 ≤ 140288), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 139776 ≤ 140032) (by norm_num : 140032 ≤ 140288), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 139776 ≤ 140032) (by norm_num : 140032 ≤ 140288), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 139776 ≤ 140032) (by norm_num : 140032 ≤ 140288), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_139264_140288 :
    (∑ n ∈ Ico 139264 140288, mobiusTreeValue 16 mobiusTable1200001 n) = (15 : ℤ) ∧
    (∑ n ∈ Ico 139264 140288, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (621 : ℕ) ∧
    (∑ n ∈ Ico 139264 140288, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (535250 : ℤ) ∧
    (∑ n ∈ Ico 139264 140288, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (10704951076499996928924622245 : ℤ) := by
  rcases cdemPrefixStats_139264_139776 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_139776_140288 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 139264 ≤ 139776) (by norm_num : 139776 ≤ 140288), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 139264 ≤ 139776) (by norm_num : 139776 ≤ 140288), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 139264 ≤ 139776) (by norm_num : 139776 ≤ 140288), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 139264 ≤ 139776) (by norm_num : 139776 ≤ 140288), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_140288_140352 :
    (∑ n ∈ Ico 140288 140352, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 140288 140352, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 140288 140352, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (213826 : ℤ) ∧
    (∑ n ∈ Ico 140288 140352, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4276529904383155629296529955 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_140352_140416 :
    (∑ n ∈ Ico 140352 140416, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 140352 140416, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 140352 140416, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-35583 : ℤ) ∧
    (∑ n ∈ Ico 140352 140416, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-711733110378612440329194984 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_140288_140416 :
    (∑ n ∈ Ico 140288 140416, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 140288 140416, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (81 : ℕ) ∧
    (∑ n ∈ Ico 140288 140416, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (178243 : ℤ) ∧
    (∑ n ∈ Ico 140288 140416, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3564796794004543188967334971 : ℤ) := by
  rcases cdemPrefixStats_140288_140352 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_140352_140416 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 140288 ≤ 140352) (by norm_num : 140352 ≤ 140416), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 140288 ≤ 140352) (by norm_num : 140352 ≤ 140416), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 140288 ≤ 140352) (by norm_num : 140352 ≤ 140416), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 140288 ≤ 140352) (by norm_num : 140352 ≤ 140416), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_140416_140480 :
    (∑ n ∈ Ico 140416 140480, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 140416 140480, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (35 : ℕ) ∧
    (∑ n ∈ Ico 140416 140480, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (177966 : ℤ) ∧
    (∑ n ∈ Ico 140416 140480, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3559463621307192032998289320 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_140480_140544 :
    (∑ n ∈ Ico 140480 140544, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 140480 140544, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 140480 140544, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-213456 : ℤ) ∧
    (∑ n ∈ Ico 140480 140544, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4269145713321023219978467021 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_140416_140544 :
    (∑ n ∈ Ico 140416 140544, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 140416 140544, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (75 : ℕ) ∧
    (∑ n ∈ Ico 140416 140544, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-35490 : ℤ) ∧
    (∑ n ∈ Ico 140416 140544, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-709682092013831186980177701 : ℤ) := by
  rcases cdemPrefixStats_140416_140480 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_140480_140544 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 140416 ≤ 140480) (by norm_num : 140480 ≤ 140544), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 140416 ≤ 140480) (by norm_num : 140480 ≤ 140544), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 140416 ≤ 140480) (by norm_num : 140480 ≤ 140544), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 140416 ≤ 140480) (by norm_num : 140480 ≤ 140544), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_140288_140544 :
    (∑ n ∈ Ico 140288 140544, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 140288 140544, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 140288 140544, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (142753 : ℤ) ∧
    (∑ n ∈ Ico 140288 140544, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2855114701990712001987157270 : ℤ) := by
  rcases cdemPrefixStats_140288_140416 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_140416_140544 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 140288 ≤ 140416) (by norm_num : 140416 ≤ 140544), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 140288 ≤ 140416) (by norm_num : 140416 ≤ 140544), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 140288 ≤ 140416) (by norm_num : 140416 ≤ 140544), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 140288 ≤ 140416) (by norm_num : 140416 ≤ 140544), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_140544_140608 :
    (∑ n ∈ Ico 140544 140608, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 140544 140608, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 140544 140608, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-284566 : ℤ) ∧
    (∑ n ∈ Ico 140544 140608, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5691408377185092032837055954 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_140608_140672 :
    (∑ n ∈ Ico 140608 140672, mobiusTreeValue 16 mobiusTable1200001 n) = (-11 : ℤ) ∧
    (∑ n ∈ Ico 140608 140672, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 140608 140672, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-391059 : ℤ) ∧
    (∑ n ∈ Ico 140608 140672, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7821322449367429933907863756 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_140544_140672 :
    (∑ n ∈ Ico 140544 140672, mobiusTreeValue 16 mobiusTable1200001 n) = (-19 : ℤ) ∧
    (∑ n ∈ Ico 140544 140672, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 140544 140672, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-675625 : ℤ) ∧
    (∑ n ∈ Ico 140544 140672, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-13512730826552521966744919710 : ℤ) := by
  rcases cdemPrefixStats_140544_140608 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_140608_140672 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 140544 ≤ 140608) (by norm_num : 140608 ≤ 140672), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 140544 ≤ 140608) (by norm_num : 140608 ≤ 140672), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 140544 ≤ 140608) (by norm_num : 140608 ≤ 140672), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 140544 ≤ 140608) (by norm_num : 140608 ≤ 140672), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_140672_140736 :
    (∑ n ∈ Ico 140672 140736, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 140672 140736, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 140672 140736, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-319822 : ℤ) ∧
    (∑ n ∈ Ico 140672 140736, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6396512997120873446759477037 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_140736_140800 :
    (∑ n ∈ Ico 140736 140800, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 140736 140800, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 140736 140800, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-71049 : ℤ) ∧
    (∑ n ∈ Ico 140736 140800, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1420928855912369142880528742 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_140672_140800 :
    (∑ n ∈ Ico 140672 140800, mobiusTreeValue 16 mobiusTable1200001 n) = (-11 : ℤ) ∧
    (∑ n ∈ Ico 140672 140800, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 140672 140800, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-390871 : ℤ) ∧
    (∑ n ∈ Ico 140672 140800, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7817441853033242589640005779 : ℤ) := by
  rcases cdemPrefixStats_140672_140736 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_140736_140800 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 140672 ≤ 140736) (by norm_num : 140736 ≤ 140800), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 140672 ≤ 140736) (by norm_num : 140736 ≤ 140800), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 140672 ≤ 140736) (by norm_num : 140736 ≤ 140800), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 140672 ≤ 140736) (by norm_num : 140736 ≤ 140800), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_140544_140800 :
    (∑ n ∈ Ico 140544 140800, mobiusTreeValue 16 mobiusTable1200001 n) = (-30 : ℤ) ∧
    (∑ n ∈ Ico 140544 140800, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 140544 140800, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1066496 : ℤ) ∧
    (∑ n ∈ Ico 140544 140800, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-21330172679585764556384925489 : ℤ) := by
  rcases cdemPrefixStats_140544_140672 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_140672_140800 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 140544 ≤ 140672) (by norm_num : 140672 ≤ 140800), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 140544 ≤ 140672) (by norm_num : 140672 ≤ 140800), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 140544 ≤ 140672) (by norm_num : 140672 ≤ 140800), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 140544 ≤ 140672) (by norm_num : 140672 ≤ 140800), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_140288_140800 :
    (∑ n ∈ Ico 140288 140800, mobiusTreeValue 16 mobiusTable1200001 n) = (-26 : ℤ) ∧
    (∑ n ∈ Ico 140288 140800, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (312 : ℕ) ∧
    (∑ n ∈ Ico 140288 140800, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-923743 : ℤ) ∧
    (∑ n ∈ Ico 140288 140800, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-18475057977595052554397768219 : ℤ) := by
  rcases cdemPrefixStats_140288_140544 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_140544_140800 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 140288 ≤ 140544) (by norm_num : 140544 ≤ 140800), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 140288 ≤ 140544) (by norm_num : 140544 ≤ 140800), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 140288 ≤ 140544) (by norm_num : 140544 ≤ 140800), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 140288 ≤ 140544) (by norm_num : 140544 ≤ 140800), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_140800_140864 :
    (∑ n ∈ Ico 140800 140864, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 140800 140864, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 140800 140864, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (213020 : ℤ) ∧
    (∑ n ∈ Ico 140800 140864, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4260461107375037928197231316 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_140864_140928 :
    (∑ n ∈ Ico 140864 140928, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 140864 140928, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 140864 140928, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (35494 : ℤ) ∧
    (∑ n ∈ Ico 140864 140928, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (709849148538408412406507723 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_140800_140928 :
    (∑ n ∈ Ico 140800 140928, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 140800 140928, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (81 : ℕ) ∧
    (∑ n ∈ Ico 140800 140928, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (248514 : ℤ) ∧
    (∑ n ∈ Ico 140800 140928, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4970310255913446340603739039 : ℤ) := by
  rcases cdemPrefixStats_140800_140864 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_140864_140928 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 140800 ≤ 140864) (by norm_num : 140864 ≤ 140928), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 140800 ≤ 140864) (by norm_num : 140864 ≤ 140928), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 140800 ≤ 140864) (by norm_num : 140864 ≤ 140928), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 140800 ≤ 140864) (by norm_num : 140864 ≤ 140928), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_140928_140992 :
    (∑ n ∈ Ico 140928 140992, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 140928 140992, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 140928 140992, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-70963 : ℤ) ∧
    (∑ n ∈ Ico 140928 140992, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1419290236679073726986574218 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_140992_141056 :
    (∑ n ∈ Ico 140992 141056, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 140992 141056, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 140992 141056, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (106367 : ℤ) ∧
    (∑ n ∈ Ico 140992 141056, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2127372969648489269956439011 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_140928_141056 :
    (∑ n ∈ Ico 140928 141056, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 140928 141056, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 140928 141056, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (35404 : ℤ) ∧
    (∑ n ∈ Ico 140928 141056, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (708082732969415542969864793 : ℤ) := by
  rcases cdemPrefixStats_140928_140992 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_140992_141056 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 140928 ≤ 140992) (by norm_num : 140992 ≤ 141056), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 140928 ≤ 140992) (by norm_num : 140992 ≤ 141056), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 140928 ≤ 140992) (by norm_num : 140992 ≤ 141056), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 140928 ≤ 140992) (by norm_num : 140992 ≤ 141056), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_140800_141056 :
    (∑ n ∈ Ico 140800 141056, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 140800 141056, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (158 : ℕ) ∧
    (∑ n ∈ Ico 140800 141056, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (283918 : ℤ) ∧
    (∑ n ∈ Ico 140800 141056, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5678392988882861883573603832 : ℤ) := by
  rcases cdemPrefixStats_140800_140928 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_140928_141056 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 140800 ≤ 140928) (by norm_num : 140928 ≤ 141056), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 140800 ≤ 140928) (by norm_num : 140928 ≤ 141056), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 140800 ≤ 140928) (by norm_num : 140928 ≤ 141056), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 140800 ≤ 140928) (by norm_num : 140928 ≤ 141056), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_141056_141120 :
    (∑ n ∈ Ico 141056 141120, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 141056 141120, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 141056 141120, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-35463 : ℤ) ∧
    (∑ n ∈ Ico 141056 141120, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-709269889451820695356671683 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_141120_141184 :
    (∑ n ∈ Ico 141120 141184, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 141120 141184, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 141120 141184, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (354240 : ℤ) ∧
    (∑ n ∈ Ico 141120 141184, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7084867545130635470950938385 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_141056_141184 :
    (∑ n ∈ Ico 141056 141184, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 141056 141184, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (75 : ℕ) ∧
    (∑ n ∈ Ico 141056 141184, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (318777 : ℤ) ∧
    (∑ n ∈ Ico 141056 141184, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6375597655678814775594266702 : ℤ) := by
  rcases cdemPrefixStats_141056_141120 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_141120_141184 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 141056 ≤ 141120) (by norm_num : 141120 ≤ 141184), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 141056 ≤ 141120) (by norm_num : 141120 ≤ 141184), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 141056 ≤ 141120) (by norm_num : 141120 ≤ 141184), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 141056 ≤ 141120) (by norm_num : 141120 ≤ 141184), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_141184_141248 :
    (∑ n ∈ Ico 141184 141248, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 141184 141248, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 141184 141248, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-177039 : ℤ) ∧
    (∑ n ∈ Ico 141184 141248, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3540835669419351815807966175 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_141248_141312 :
    (∑ n ∈ Ico 141248 141312, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 141248 141312, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 141248 141312, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 141248 141312, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-90202100010825244539376 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_141184_141312 :
    (∑ n ∈ Ico 141184 141312, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 141184 141312, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 141184 141312, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-177045 : ℤ) ∧
    (∑ n ∈ Ico 141184 141312, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3540925871519362641052505551 : ℤ) := by
  rcases cdemPrefixStats_141184_141248 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_141248_141312 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 141184 ≤ 141248) (by norm_num : 141248 ≤ 141312), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 141184 ≤ 141248) (by norm_num : 141248 ≤ 141312), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 141184 ≤ 141248) (by norm_num : 141248 ≤ 141312), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 141184 ≤ 141248) (by norm_num : 141248 ≤ 141312), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_141056_141312 :
    (∑ n ∈ Ico 141056 141312, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 141056 141312, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (154 : ℕ) ∧
    (∑ n ∈ Ico 141056 141312, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (141732 : ℤ) ∧
    (∑ n ∈ Ico 141056 141312, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2834671784159452134541761151 : ℤ) := by
  rcases cdemPrefixStats_141056_141184 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_141184_141312 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 141056 ≤ 141184) (by norm_num : 141184 ≤ 141312), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 141056 ≤ 141184) (by norm_num : 141184 ≤ 141312), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 141056 ≤ 141184) (by norm_num : 141184 ≤ 141312), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 141056 ≤ 141184) (by norm_num : 141184 ≤ 141312), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_140800_141312 :
    (∑ n ∈ Ico 140800 141312, mobiusTreeValue 16 mobiusTable1200001 n) = (12 : ℤ) ∧
    (∑ n ∈ Ico 140800 141312, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (312 : ℕ) ∧
    (∑ n ∈ Ico 140800 141312, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (425650 : ℤ) ∧
    (∑ n ∈ Ico 140800 141312, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8513064773042314018115364983 : ℤ) := by
  rcases cdemPrefixStats_140800_141056 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_141056_141312 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 140800 ≤ 141056) (by norm_num : 141056 ≤ 141312), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 140800 ≤ 141056) (by norm_num : 141056 ≤ 141312), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 140800 ≤ 141056) (by norm_num : 141056 ≤ 141312), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 140800 ≤ 141056) (by norm_num : 141056 ≤ 141312), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_140288_141312 :
    (∑ n ∈ Ico 140288 141312, mobiusTreeValue 16 mobiusTable1200001 n) = (-14 : ℤ) ∧
    (∑ n ∈ Ico 140288 141312, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (624 : ℕ) ∧
    (∑ n ∈ Ico 140288 141312, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-498093 : ℤ) ∧
    (∑ n ∈ Ico 140288 141312, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9961993204552738536282403236 : ℤ) := by
  rcases cdemPrefixStats_140288_140800 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_140800_141312 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 140288 ≤ 140800) (by norm_num : 140800 ≤ 141312), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 140288 ≤ 140800) (by norm_num : 140800 ≤ 141312), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 140288 ≤ 140800) (by norm_num : 140800 ≤ 141312), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 140288 ≤ 140800) (by norm_num : 140800 ≤ 141312), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_139264_141312 :
    (∑ n ∈ Ico 139264 141312, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 139264 141312, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (1245 : ℕ) ∧
    (∑ n ∈ Ico 139264 141312, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (37157 : ℤ) ∧
    (∑ n ∈ Ico 139264 141312, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (742957871947258392642219009 : ℤ) := by
  rcases cdemPrefixStats_139264_140288 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_140288_141312 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 139264 ≤ 140288) (by norm_num : 140288 ≤ 141312), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 139264 ≤ 140288) (by norm_num : 140288 ≤ 141312), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 139264 ≤ 140288) (by norm_num : 140288 ≤ 141312), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 139264 ≤ 140288) (by norm_num : 140288 ≤ 141312), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_141312_141376 :
    (∑ n ∈ Ico 141312 141376, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 141312 141376, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 141312 141376, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-212273 : ℤ) ∧
    (∑ n ∈ Ico 141312 141376, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4245538254674518261617927712 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_141376_141440 :
    (∑ n ∈ Ico 141376 141440, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 141376 141440, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 141376 141440, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (247465 : ℤ) ∧
    (∑ n ∈ Ico 141376 141440, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4949459939791262634378554819 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_141312_141440 :
    (∑ n ∈ Ico 141312 141440, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 141312 141440, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 141312 141440, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (35192 : ℤ) ∧
    (∑ n ∈ Ico 141312 141440, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (703921685116744372760627107 : ℤ) := by
  rcases cdemPrefixStats_141312_141376 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_141376_141440 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 141312 ≤ 141376) (by norm_num : 141376 ≤ 141440), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 141312 ≤ 141376) (by norm_num : 141376 ≤ 141440), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 141312 ≤ 141376) (by norm_num : 141376 ≤ 141440), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 141312 ≤ 141376) (by norm_num : 141376 ≤ 141440), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_141440_141504 :
    (∑ n ∈ Ico 141440 141504, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 141440 141504, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 141440 141504, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-318065 : ℤ) ∧
    (∑ n ∈ Ico 141440 141504, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6361303286062958014681895831 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_141504_141568 :
    (∑ n ∈ Ico 141504 141568, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 141504 141568, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (42 : ℕ) ∧
    (∑ n ∈ Ico 141504 141568, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (141318 : ℤ) ∧
    (∑ n ∈ Ico 141504 141568, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2826415657955156901420879924 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_141440_141568 :
    (∑ n ∈ Ico 141440 141568, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 141440 141568, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (81 : ℕ) ∧
    (∑ n ∈ Ico 141440 141568, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-176747 : ℤ) ∧
    (∑ n ∈ Ico 141440 141568, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3534887628107801113261015907 : ℤ) := by
  rcases cdemPrefixStats_141440_141504 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_141504_141568 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 141440 ≤ 141504) (by norm_num : 141504 ≤ 141568), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 141440 ≤ 141504) (by norm_num : 141504 ≤ 141568), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 141440 ≤ 141504) (by norm_num : 141504 ≤ 141568), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 141440 ≤ 141504) (by norm_num : 141504 ≤ 141568), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_141312_141568 :
    (∑ n ∈ Ico 141312 141568, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 141312 141568, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (158 : ℕ) ∧
    (∑ n ∈ Ico 141312 141568, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-141555 : ℤ) ∧
    (∑ n ∈ Ico 141312 141568, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2830965942991056740500388800 : ℤ) := by
  rcases cdemPrefixStats_141312_141440 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_141440_141568 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 141312 ≤ 141440) (by norm_num : 141440 ≤ 141568), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 141312 ≤ 141440) (by norm_num : 141440 ≤ 141568), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 141312 ≤ 141440) (by norm_num : 141440 ≤ 141568), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 141312 ≤ 141440) (by norm_num : 141440 ≤ 141568), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_141568_141632 :
    (∑ n ∈ Ico 141568 141632, mobiusTreeValue 16 mobiusTable1200001 n) = (-11 : ℤ) ∧
    (∑ n ∈ Ico 141568 141632, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 141568 141632, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-388398 : ℤ) ∧
    (∑ n ∈ Ico 141568 141632, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7768077331817261916863406788 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_141632_141696 :
    (∑ n ∈ Ico 141632 141696, mobiusTreeValue 16 mobiusTable1200001 n) = (-12 : ℤ) ∧
    (∑ n ∈ Ico 141632 141696, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 141632 141696, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-423545 : ℤ) ∧
    (∑ n ∈ Ico 141632 141696, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8471001929120402917127038654 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_141568_141696 :
    (∑ n ∈ Ico 141568 141696, mobiusTreeValue 16 mobiusTable1200001 n) = (-23 : ℤ) ∧
    (∑ n ∈ Ico 141568 141696, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 141568 141696, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-811943 : ℤ) ∧
    (∑ n ∈ Ico 141568 141696, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-16239079260937664833990445442 : ℤ) := by
  rcases cdemPrefixStats_141568_141632 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_141632_141696 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 141568 ≤ 141632) (by norm_num : 141632 ≤ 141696), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 141568 ≤ 141632) (by norm_num : 141632 ≤ 141696), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 141568 ≤ 141632) (by norm_num : 141632 ≤ 141696), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 141568 ≤ 141632) (by norm_num : 141632 ≤ 141696), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_141696_141760 :
    (∑ n ∈ Ico 141696 141760, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 141696 141760, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 141696 141760, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (141031 : ℤ) ∧
    (∑ n ∈ Ico 141696 141760, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2820664690453563608479764598 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_141760_141824 :
    (∑ n ∈ Ico 141760 141824, mobiusTreeValue 16 mobiusTable1200001 n) = (-12 : ℤ) ∧
    (∑ n ∈ Ico 141760 141824, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 141760 141824, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-423187 : ℤ) ∧
    (∑ n ∈ Ico 141760 141824, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8463842131696267280953600595 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_141696_141824 :
    (∑ n ∈ Ico 141696 141824, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 141696 141824, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 141696 141824, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-282156 : ℤ) ∧
    (∑ n ∈ Ico 141696 141824, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5643177441242703672473835997 : ℤ) := by
  rcases cdemPrefixStats_141696_141760 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_141760_141824 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 141696 ≤ 141760) (by norm_num : 141760 ≤ 141824), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 141696 ≤ 141760) (by norm_num : 141760 ≤ 141824), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 141696 ≤ 141760) (by norm_num : 141760 ≤ 141824), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 141696 ≤ 141760) (by norm_num : 141760 ≤ 141824), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_141568_141824 :
    (∑ n ∈ Ico 141568 141824, mobiusTreeValue 16 mobiusTable1200001 n) = (-31 : ℤ) ∧
    (∑ n ∈ Ico 141568 141824, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 141568 141824, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1094099 : ℤ) ∧
    (∑ n ∈ Ico 141568 141824, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-21882256702180368506464281439 : ℤ) := by
  rcases cdemPrefixStats_141568_141696 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_141696_141824 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 141568 ≤ 141696) (by norm_num : 141696 ≤ 141824), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 141568 ≤ 141696) (by norm_num : 141696 ≤ 141824), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 141568 ≤ 141696) (by norm_num : 141696 ≤ 141824), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 141568 ≤ 141696) (by norm_num : 141696 ≤ 141824), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_141312_141824 :
    (∑ n ∈ Ico 141312 141824, mobiusTreeValue 16 mobiusTable1200001 n) = (-35 : ℤ) ∧
    (∑ n ∈ Ico 141312 141824, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (315 : ℕ) ∧
    (∑ n ∈ Ico 141312 141824, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1235654 : ℤ) ∧
    (∑ n ∈ Ico 141312 141824, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-24713222645171425246964670239 : ℤ) := by
  rcases cdemPrefixStats_141312_141568 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_141568_141824 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 141312 ≤ 141568) (by norm_num : 141568 ≤ 141824), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 141312 ≤ 141568) (by norm_num : 141568 ≤ 141824), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 141312 ≤ 141568) (by norm_num : 141568 ≤ 141824), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 141312 ≤ 141568) (by norm_num : 141568 ≤ 141824), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_141824_141888 :
    (∑ n ∈ Ico 141824 141888, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 141824 141888, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 141824 141888, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-140979 : ℤ) ∧
    (∑ n ∈ Ico 141824 141888, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2819621753055345438541070727 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_141888_141952 :
    (∑ n ∈ Ico 141888 141952, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 141888 141952, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 141888 141952, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (387603 : ℤ) ∧
    (∑ n ∈ Ico 141888 141952, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7752166392183099203879860875 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_141824_141952 :
    (∑ n ∈ Ico 141824 141952, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 141824 141952, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 141824 141952, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (246624 : ℤ) ∧
    (∑ n ∈ Ico 141824 141952, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4932544639127753765338790148 : ℤ) := by
  rcases cdemPrefixStats_141824_141888 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_141888_141952 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 141824 ≤ 141888) (by norm_num : 141888 ≤ 141952), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 141824 ≤ 141888) (by norm_num : 141888 ≤ 141952), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 141824 ≤ 141888) (by norm_num : 141888 ≤ 141952), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 141824 ≤ 141888) (by norm_num : 141888 ≤ 141952), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_141952_142016 :
    (∑ n ∈ Ico 141952 142016, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 141952 142016, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 141952 142016, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (176048 : ℤ) ∧
    (∑ n ∈ Ico 141952 142016, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3521012691120049533905713247 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_142016_142080 :
    (∑ n ∈ Ico 142016 142080, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 142016 142080, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 142016 142080, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 142016 142080, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-89186755943668103075920 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_141952_142080 :
    (∑ n ∈ Ico 141952 142080, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 141952 142080, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 141952 142080, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (176043 : ℤ) ∧
    (∑ n ∈ Ico 141952 142080, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3520923504364105865802637327 : ℤ) := by
  rcases cdemPrefixStats_141952_142016 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_142016_142080 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 141952 ≤ 142016) (by norm_num : 142016 ≤ 142080), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 141952 ≤ 142016) (by norm_num : 142016 ≤ 142080), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 141952 ≤ 142016) (by norm_num : 142016 ≤ 142080), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 141952 ≤ 142016) (by norm_num : 142016 ≤ 142080), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_141824_142080 :
    (∑ n ∈ Ico 141824 142080, mobiusTreeValue 16 mobiusTable1200001 n) = (12 : ℤ) ∧
    (∑ n ∈ Ico 141824 142080, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 141824 142080, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (422667 : ℤ) ∧
    (∑ n ∈ Ico 141824 142080, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8453468143491859631141427475 : ℤ) := by
  rcases cdemPrefixStats_141824_141952 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_141952_142080 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 141824 ≤ 141952) (by norm_num : 141952 ≤ 142080), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 141824 ≤ 141952) (by norm_num : 141952 ≤ 142080), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 141824 ≤ 141952) (by norm_num : 141952 ≤ 142080), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 141824 ≤ 141952) (by norm_num : 141952 ≤ 142080), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_142080_142144 :
    (∑ n ∈ Ico 142080 142144, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 142080 142144, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 142080 142144, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-175957 : ℤ) ∧
    (∑ n ∈ Ico 142080 142144, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3519153780552446896235379052 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_142144_142208 :
    (∑ n ∈ Ico 142144 142208, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 142144 142208, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 142144 142208, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (175813 : ℤ) ∧
    (∑ n ∈ Ico 142144 142208, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3516308044315715673329393197 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_142080_142208 :
    (∑ n ∈ Ico 142080 142208, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 142080 142208, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 142080 142208, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-144 : ℤ) ∧
    (∑ n ∈ Ico 142080 142208, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2845736236731222905985855 : ℤ) := by
  rcases cdemPrefixStats_142080_142144 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_142144_142208 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 142080 ≤ 142144) (by norm_num : 142144 ≤ 142208), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 142080 ≤ 142144) (by norm_num : 142144 ≤ 142208), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 142080 ≤ 142144) (by norm_num : 142144 ≤ 142208), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 142080 ≤ 142144) (by norm_num : 142144 ≤ 142208), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_142208_142272 :
    (∑ n ∈ Ico 142208 142272, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 142208 142272, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 142208 142272, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-26 : ℤ) ∧
    (∑ n ∈ Ico 142208 142272, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-484432133805143947750168 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_142272_142336 :
    (∑ n ∈ Ico 142272 142336, mobiusTreeValue 16 mobiusTable1200001 n) = (16 : ℤ) ∧
    (∑ n ∈ Ico 142272 142336, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 142272 142336, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (562175 : ℤ) ∧
    (∑ n ∈ Ico 142272 142336, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (11243717980201405095591594217 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_142208_142336 :
    (∑ n ∈ Ico 142208 142336, mobiusTreeValue 16 mobiusTable1200001 n) = (16 : ℤ) ∧
    (∑ n ∈ Ico 142208 142336, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 142208 142336, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (562149 : ℤ) ∧
    (∑ n ∈ Ico 142208 142336, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (11243233548067599951643844049 : ℤ) := by
  rcases cdemPrefixStats_142208_142272 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_142272_142336 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 142208 ≤ 142272) (by norm_num : 142272 ≤ 142336), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 142208 ≤ 142272) (by norm_num : 142272 ≤ 142336), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 142208 ≤ 142272) (by norm_num : 142272 ≤ 142336), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 142208 ≤ 142272) (by norm_num : 142272 ≤ 142336), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_142080_142336 :
    (∑ n ∈ Ico 142080 142336, mobiusTreeValue 16 mobiusTable1200001 n) = (16 : ℤ) ∧
    (∑ n ∈ Ico 142080 142336, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 142080 142336, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (562005 : ℤ) ∧
    (∑ n ∈ Ico 142080 142336, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (11240387811830868728737858194 : ℤ) := by
  rcases cdemPrefixStats_142080_142208 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_142208_142336 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 142080 ≤ 142208) (by norm_num : 142208 ≤ 142336), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 142080 ≤ 142208) (by norm_num : 142208 ≤ 142336), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 142080 ≤ 142208) (by norm_num : 142208 ≤ 142336), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 142080 ≤ 142208) (by norm_num : 142208 ≤ 142336), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_141824_142336 :
    (∑ n ∈ Ico 141824 142336, mobiusTreeValue 16 mobiusTable1200001 n) = (28 : ℤ) ∧
    (∑ n ∈ Ico 141824 142336, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (312 : ℕ) ∧
    (∑ n ∈ Ico 141824 142336, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (984672 : ℤ) ∧
    (∑ n ∈ Ico 141824 142336, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (19693855955322728359879285669 : ℤ) := by
  rcases cdemPrefixStats_141824_142080 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_142080_142336 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 141824 ≤ 142080) (by norm_num : 142080 ≤ 142336), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 141824 ≤ 142080) (by norm_num : 142080 ≤ 142336), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 141824 ≤ 142080) (by norm_num : 142080 ≤ 142336), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 141824 ≤ 142080) (by norm_num : 142080 ≤ 142336), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_141312_142336 :
    (∑ n ∈ Ico 141312 142336, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 141312 142336, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (627 : ℕ) ∧
    (∑ n ∈ Ico 141312 142336, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-250982 : ℤ) ∧
    (∑ n ∈ Ico 141312 142336, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5019366689848696887085384570 : ℤ) := by
  rcases cdemPrefixStats_141312_141824 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_141824_142336 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 141312 ≤ 141824) (by norm_num : 141824 ≤ 142336), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 141312 ≤ 141824) (by norm_num : 141824 ≤ 142336), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 141312 ≤ 141824) (by norm_num : 141824 ≤ 142336), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 141312 ≤ 141824) (by norm_num : 141824 ≤ 142336), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_142336_142400 :
    (∑ n ∈ Ico 142336 142400, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 142336 142400, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 142336 142400, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (140465 : ℤ) ∧
    (∑ n ∈ Ico 142336 142400, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2809363769849264949632045396 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_142400_142464 :
    (∑ n ∈ Ico 142400 142464, mobiusTreeValue 16 mobiusTable1200001 n) = (-13 : ℤ) ∧
    (∑ n ∈ Ico 142400 142464, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 142400 142464, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-456371 : ℤ) ∧
    (∑ n ∈ Ico 142400 142464, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9127502705193110868830811459 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_142336_142464 :
    (∑ n ∈ Ico 142336 142464, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 142336 142464, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 142336 142464, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-315906 : ℤ) ∧
    (∑ n ∈ Ico 142336 142464, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6318138935343845919198766063 : ℤ) := by
  rcases cdemPrefixStats_142336_142400 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_142400_142464 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 142336 ≤ 142400) (by norm_num : 142400 ≤ 142464), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 142336 ≤ 142400) (by norm_num : 142400 ≤ 142464), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 142336 ≤ 142400) (by norm_num : 142400 ≤ 142464), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 142336 ≤ 142400) (by norm_num : 142400 ≤ 142464), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_142464_142528 :
    (∑ n ∈ Ico 142464 142528, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 142464 142528, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 142464 142528, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (245608 : ℤ) ∧
    (∑ n ∈ Ico 142464 142528, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4912315376319322971804557075 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_142528_142592 :
    (∑ n ∈ Ico 142528 142592, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 142528 142592, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 142528 142592, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-35105 : ℤ) ∧
    (∑ n ∈ Ico 142528 142592, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-702079039037825997502158716 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_142464_142592 :
    (∑ n ∈ Ico 142464 142592, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 142464 142592, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 142464 142592, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (210503 : ℤ) ∧
    (∑ n ∈ Ico 142464 142592, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4210236337281496974302398359 : ℤ) := by
  rcases cdemPrefixStats_142464_142528 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_142528_142592 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 142464 ≤ 142528) (by norm_num : 142528 ≤ 142592), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 142464 ≤ 142528) (by norm_num : 142528 ≤ 142592), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 142464 ≤ 142528) (by norm_num : 142528 ≤ 142592), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 142464 ≤ 142528) (by norm_num : 142528 ≤ 142592), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_142336_142592 :
    (∑ n ∈ Ico 142336 142592, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 142336 142592, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 142336 142592, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-105403 : ℤ) ∧
    (∑ n ∈ Ico 142336 142592, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2107902598062348944896367704 : ℤ) := by
  rcases cdemPrefixStats_142336_142464 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_142464_142592 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 142336 ≤ 142464) (by norm_num : 142464 ≤ 142592), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 142336 ≤ 142464) (by norm_num : 142464 ≤ 142592), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 142336 ≤ 142464) (by norm_num : 142464 ≤ 142592), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 142336 ≤ 142464) (by norm_num : 142464 ≤ 142592), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_142592_142656 :
    (∑ n ∈ Ico 142592 142656, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 142592 142656, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 142592 142656, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (70091 : ℤ) ∧
    (∑ n ∈ Ico 142592 142656, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1401846076764665083863050063 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_142656_142720 :
    (∑ n ∈ Ico 142656 142720, mobiusTreeValue 16 mobiusTable1200001 n) = (12 : ℤ) ∧
    (∑ n ∈ Ico 142656 142720, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (42 : ℕ) ∧
    (∑ n ∈ Ico 142656 142720, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (420472 : ℤ) ∧
    (∑ n ∈ Ico 142656 142720, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8409559643595734375644519274 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_142592_142720 :
    (∑ n ∈ Ico 142592 142720, mobiusTreeValue 16 mobiusTable1200001 n) = (14 : ℤ) ∧
    (∑ n ∈ Ico 142592 142720, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (82 : ℕ) ∧
    (∑ n ∈ Ico 142592 142720, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (490563 : ℤ) ∧
    (∑ n ∈ Ico 142592 142720, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (9811405720360399459507569337 : ℤ) := by
  rcases cdemPrefixStats_142592_142656 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_142656_142720 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 142592 ≤ 142656) (by norm_num : 142656 ≤ 142720), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 142592 ≤ 142656) (by norm_num : 142656 ≤ 142720), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 142592 ≤ 142656) (by norm_num : 142656 ≤ 142720), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 142592 ≤ 142656) (by norm_num : 142656 ≤ 142720), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_142720_142784 :
    (∑ n ∈ Ico 142720 142784, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 142720 142784, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 142720 142784, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (385281 : ℤ) ∧
    (∑ n ∈ Ico 142720 142784, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7705764851093644794458801602 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_142784_142848 :
    (∑ n ∈ Ico 142784 142848, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 142784 142848, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 142784 142848, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (104998 : ℤ) ∧
    (∑ n ∈ Ico 142784 142848, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2100001990932570659456282085 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_142720_142848 :
    (∑ n ∈ Ico 142720 142848, mobiusTreeValue 16 mobiusTable1200001 n) = (14 : ℤ) ∧
    (∑ n ∈ Ico 142720 142848, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (74 : ℕ) ∧
    (∑ n ∈ Ico 142720 142848, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (490279 : ℤ) ∧
    (∑ n ∈ Ico 142720 142848, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (9805766842026215453915083687 : ℤ) := by
  rcases cdemPrefixStats_142720_142784 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_142784_142848 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 142720 ≤ 142784) (by norm_num : 142784 ≤ 142848), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 142720 ≤ 142784) (by norm_num : 142784 ≤ 142848), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 142720 ≤ 142784) (by norm_num : 142784 ≤ 142848), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 142720 ≤ 142784) (by norm_num : 142784 ≤ 142848), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_142592_142848 :
    (∑ n ∈ Ico 142592 142848, mobiusTreeValue 16 mobiusTable1200001 n) = (28 : ℤ) ∧
    (∑ n ∈ Ico 142592 142848, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 142592 142848, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (980842 : ℤ) ∧
    (∑ n ∈ Ico 142592 142848, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (19617172562386614913422653024 : ℤ) := by
  rcases cdemPrefixStats_142592_142720 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_142720_142848 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 142592 ≤ 142720) (by norm_num : 142720 ≤ 142848), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 142592 ≤ 142720) (by norm_num : 142720 ≤ 142848), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 142592 ≤ 142720) (by norm_num : 142720 ≤ 142848), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 142592 ≤ 142720) (by norm_num : 142720 ≤ 142848), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_142336_142848 :
    (∑ n ∈ Ico 142336 142848, mobiusTreeValue 16 mobiusTable1200001 n) = (25 : ℤ) ∧
    (∑ n ∈ Ico 142336 142848, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (311 : ℕ) ∧
    (∑ n ∈ Ico 142336 142848, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (875439 : ℤ) ∧
    (∑ n ∈ Ico 142336 142848, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (17509269964324265968526285320 : ℤ) := by
  rcases cdemPrefixStats_142336_142592 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_142592_142848 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 142336 ≤ 142592) (by norm_num : 142592 ≤ 142848), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 142336 ≤ 142592) (by norm_num : 142592 ≤ 142848), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 142336 ≤ 142592) (by norm_num : 142592 ≤ 142848), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 142336 ≤ 142592) (by norm_num : 142592 ≤ 142848), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_142848_142912 :
    (∑ n ∈ Ico 142848 142912, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 142848 142912, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 142848 142912, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (34993 : ℤ) ∧
    (∑ n ∈ Ico 142848 142912, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (699819584814970151527151347 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_142912_142976 :
    (∑ n ∈ Ico 142912 142976, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 142912 142976, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 142912 142976, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (209890 : ℤ) ∧
    (∑ n ∈ Ico 142912 142976, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4197849231393937636951209487 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_142848_142976 :
    (∑ n ∈ Ico 142848 142976, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 142848 142976, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 142848 142976, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (244883 : ℤ) ∧
    (∑ n ∈ Ico 142848 142976, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4897668816208907788478360834 : ℤ) := by
  rcases cdemPrefixStats_142848_142912 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_142912_142976 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 142848 ≤ 142912) (by norm_num : 142912 ≤ 142976), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 142848 ≤ 142912) (by norm_num : 142912 ≤ 142976), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 142848 ≤ 142912) (by norm_num : 142912 ≤ 142976), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 142848 ≤ 142912) (by norm_num : 142912 ≤ 142976), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_142976_143040 :
    (∑ n ∈ Ico 142976 143040, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 142976 143040, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 142976 143040, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (244705 : ℤ) ∧
    (∑ n ∈ Ico 142976 143040, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4894205340811679875497408871 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_143040_143104 :
    (∑ n ∈ Ico 143040 143104, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 143040 143104, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 143040 143104, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (384388 : ℤ) ∧
    (∑ n ∈ Ico 143040 143104, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7687850611886812534608390925 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_142976_143104 :
    (∑ n ∈ Ico 142976 143104, mobiusTreeValue 16 mobiusTable1200001 n) = (18 : ℤ) ∧
    (∑ n ∈ Ico 142976 143104, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 142976 143104, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (629093 : ℤ) ∧
    (∑ n ∈ Ico 142976 143104, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (12582055952698492410105799796 : ℤ) := by
  rcases cdemPrefixStats_142976_143040 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_143040_143104 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 142976 ≤ 143040) (by norm_num : 143040 ≤ 143104), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 142976 ≤ 143040) (by norm_num : 143040 ≤ 143104), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 142976 ≤ 143040) (by norm_num : 143040 ≤ 143104), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 142976 ≤ 143040) (by norm_num : 143040 ≤ 143104), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_142848_143104 :
    (∑ n ∈ Ico 142848 143104, mobiusTreeValue 16 mobiusTable1200001 n) = (25 : ℤ) ∧
    (∑ n ∈ Ico 142848 143104, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 142848 143104, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (873976 : ℤ) ∧
    (∑ n ∈ Ico 142848 143104, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (17479724768907400198584160630 : ℤ) := by
  rcases cdemPrefixStats_142848_142976 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_142976_143104 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 142848 ≤ 142976) (by norm_num : 142976 ≤ 143104), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 142848 ≤ 142976) (by norm_num : 142976 ≤ 143104), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 142848 ≤ 142976) (by norm_num : 142976 ≤ 143104), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 142848 ≤ 142976) (by norm_num : 142976 ≤ 143104), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_143104_143168 :
    (∑ n ∈ Ico 143104 143168, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 143104 143168, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 143104 143168, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-45 : ℤ) ∧
    (∑ n ∈ Ico 143104 143168, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-922491514730956300093739 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_143168_143232 :
    (∑ n ∈ Ico 143168 143232, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 143168 143232, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 143168 143232, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-69827 : ℤ) ∧
    (∑ n ∈ Ico 143168 143232, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1396584739154274754077984175 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_143104_143232 :
    (∑ n ∈ Ico 143104 143232, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 143104 143232, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 143104 143232, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-69872 : ℤ) ∧
    (∑ n ∈ Ico 143104 143232, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1397507230669005710378077914 : ℤ) := by
  rcases cdemPrefixStats_143104_143168 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_143168_143232 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 143104 ≤ 143168) (by norm_num : 143168 ≤ 143232), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 143104 ≤ 143168) (by norm_num : 143168 ≤ 143232), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 143104 ≤ 143168) (by norm_num : 143168 ≤ 143232), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 143104 ≤ 143168) (by norm_num : 143168 ≤ 143232), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_143232_143296 :
    (∑ n ∈ Ico 143232 143296, mobiusTreeValue 16 mobiusTable1200001 n) = (-12 : ℤ) ∧
    (∑ n ∈ Ico 143232 143296, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 143232 143296, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-418782 : ℤ) ∧
    (∑ n ∈ Ico 143232 143296, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8375725707473018176378480883 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_143296_143360 :
    (∑ n ∈ Ico 143296 143360, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 143296 143360, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 143296 143360, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (209282 : ℤ) ∧
    (∑ n ∈ Ico 143296 143360, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4185681345095617322774011537 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_143232_143360 :
    (∑ n ∈ Ico 143232 143360, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 143232 143360, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 143232 143360, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-209500 : ℤ) ∧
    (∑ n ∈ Ico 143232 143360, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4190044362377400853604469346 : ℤ) := by
  rcases cdemPrefixStats_143232_143296 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_143296_143360 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 143232 ≤ 143296) (by norm_num : 143296 ≤ 143360), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 143232 ≤ 143296) (by norm_num : 143296 ≤ 143360), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 143232 ≤ 143296) (by norm_num : 143296 ≤ 143360), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 143232 ≤ 143296) (by norm_num : 143296 ≤ 143360), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_143104_143360 :
    (∑ n ∈ Ico 143104 143360, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 143104 143360, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 143104 143360, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-279372 : ℤ) ∧
    (∑ n ∈ Ico 143104 143360, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5587551593046406563982547260 : ℤ) := by
  rcases cdemPrefixStats_143104_143232 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_143232_143360 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 143104 ≤ 143232) (by norm_num : 143232 ≤ 143360), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 143104 ≤ 143232) (by norm_num : 143232 ≤ 143360), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 143104 ≤ 143232) (by norm_num : 143232 ≤ 143360), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 143104 ≤ 143232) (by norm_num : 143232 ≤ 143360), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_142848_143360 :
    (∑ n ∈ Ico 142848 143360, mobiusTreeValue 16 mobiusTable1200001 n) = (17 : ℤ) ∧
    (∑ n ∈ Ico 142848 143360, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (313 : ℕ) ∧
    (∑ n ∈ Ico 142848 143360, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (594604 : ℤ) ∧
    (∑ n ∈ Ico 142848 143360, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (11892173175860993634601613370 : ℤ) := by
  rcases cdemPrefixStats_142848_143104 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_143104_143360 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 142848 ≤ 143104) (by norm_num : 143104 ≤ 143360), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 142848 ≤ 143104) (by norm_num : 143104 ≤ 143360), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 142848 ≤ 143104) (by norm_num : 143104 ≤ 143360), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 142848 ≤ 143104) (by norm_num : 143104 ≤ 143360), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_142336_143360 :
    (∑ n ∈ Ico 142336 143360, mobiusTreeValue 16 mobiusTable1200001 n) = (42 : ℤ) ∧
    (∑ n ∈ Ico 142336 143360, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (624 : ℕ) ∧
    (∑ n ∈ Ico 142336 143360, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1470043 : ℤ) ∧
    (∑ n ∈ Ico 142336 143360, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (29401443140185259603127898690 : ℤ) := by
  rcases cdemPrefixStats_142336_142848 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_142848_143360 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 142336 ≤ 142848) (by norm_num : 142848 ≤ 143360), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 142336 ≤ 142848) (by norm_num : 142848 ≤ 143360), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 142336 ≤ 142848) (by norm_num : 142848 ≤ 143360), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 142336 ≤ 142848) (by norm_num : 142848 ≤ 143360), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_141312_143360 :
    (∑ n ∈ Ico 141312 143360, mobiusTreeValue 16 mobiusTable1200001 n) = (35 : ℤ) ∧
    (∑ n ∈ Ico 141312 143360, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (1251 : ℕ) ∧
    (∑ n ∈ Ico 141312 143360, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1219061 : ℤ) ∧
    (∑ n ∈ Ico 141312 143360, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (24382076450336562716042514120 : ℤ) := by
  rcases cdemPrefixStats_141312_142336 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_142336_143360 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 141312 ≤ 142336) (by norm_num : 142336 ≤ 143360), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 141312 ≤ 142336) (by norm_num : 142336 ≤ 143360), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 141312 ≤ 142336) (by norm_num : 142336 ≤ 143360), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 141312 ≤ 142336) (by norm_num : 142336 ≤ 143360), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_139264_143360 :
    (∑ n ∈ Ico 139264 143360, mobiusTreeValue 16 mobiusTable1200001 n) = (36 : ℤ) ∧
    (∑ n ∈ Ico 139264 143360, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2496 : ℕ) ∧
    (∑ n ∈ Ico 139264 143360, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1256218 : ℤ) ∧
    (∑ n ∈ Ico 139264 143360, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (25125034322283821108684733129 : ℤ) := by
  rcases cdemPrefixStats_139264_141312 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_141312_143360 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 139264 ≤ 141312) (by norm_num : 141312 ≤ 143360), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 139264 ≤ 141312) (by norm_num : 141312 ≤ 143360), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 139264 ≤ 141312) (by norm_num : 141312 ≤ 143360), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 139264 ≤ 141312) (by norm_num : 141312 ≤ 143360), hR1, hR2] <;> norm_num

theorem cdemPrefixGroup034_checked_complete :
    (∑ n ∈ Ico 139264 143360, mobiusTreeValue 16 mobiusTable1200001 n) = (36 : ℤ) ∧
    (∑ n ∈ Ico 139264 143360, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2496 : ℕ) ∧
    (∑ n ∈ Ico 139264 143360, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1256218 : ℤ) ∧
    (∑ n ∈ Ico 139264 143360, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (25125034322283821108684733129 : ℤ) := cdemPrefixStats_139264_143360
end Helfgott
#print axioms Helfgott.cdemPrefixGroup034_checked_complete

open Helfgott Finset
open scoped BigOperators

theorem solution :
    (∑ n ∈ Ico 139264 143360, mobiusTreeValue 16 mobiusTable1200001 n) = (36 : ℤ) ∧
    (∑ n ∈ Ico 139264 143360, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2496 : ℕ) ∧
    (∑ n ∈ Ico 139264 143360, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1256218 : ℤ) ∧
    (∑ n ∈ Ico 139264 143360, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (25125034322283821108684733129 : ℤ) := Helfgott.cdemPrefixGroup034_checked_complete
#print axioms solution
