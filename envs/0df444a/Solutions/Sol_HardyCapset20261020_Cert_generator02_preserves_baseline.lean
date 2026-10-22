-- Prove2me | solution 1 for HardyCapset20261020.Cert.generator02_preserves_baseline
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-20T16:02:25.981057+00:00
-- url     : https://prove2.me/submissions/91bb2d3a-1ebf-470c-8d89-6f06c1eee4f3

import Definitions.Def_HardyCapsetSymmetryData20261020
import Mathlib.Data.List.Sort
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
namespace HardyCapset20261020.Cert
private theorem action_preserves_from_lists (g : Point ≃+ Point) (l : List ℕ)
    (hp : l.Perm baselineIds)
    (hm : (baselineIds.map decode).map g = l.map decode) : PreservesBaseline g := by
  unfold PreservesBaseline
  calc
    baseline.image g = ((baselineIds.map decode).map g).toFinset := by
      ext x
      simp [baseline]
    _ = (l.map decode).toFinset := congrArg List.toFinset hm
    _ = baseline := by
      ext x
      change x ∈ (l.map decode).toFinset ↔ x ∈ (baselineIds.map decode).toFinset
      simp only [List.mem_toFinset]
      exact (hp.map decode).mem_iff

private theorem image_list :
    (baselineIds.map decode).map generator02 = permutedBaselineIds[2]!.map decode := by decide_cbv
private theorem sorted_ids :
    permutedBaselineIds[2]!.mergeSort (· ≤ ·) = baselineIds := by decide_cbv
end HardyCapset20261020.Cert
open HardyCapset20261020 HardyCapset20261020.Cert
theorem solution : PreservesBaseline generator02 := by
  apply action_preserves_from_lists generator02 permutedBaselineIds[2]!
  · rw [← sorted_ids]
    exact (List.mergeSort_perm _ _).symm
  · exact image_list
#print axioms solution
