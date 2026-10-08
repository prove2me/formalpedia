-- Prove2me | solution 1 for OAI.Erdos3.normalizedMesh_scale_large
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T10:21:02.056416+00:00
-- url     : https://prove2.me/submissions/8384b5a1-d65d-4da2-8894-bc906f7517a9

import Mathlib
import Definitions.Def_ErdosReciprocal

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NormalizedMeshLengths
namespace OAI

section

namespace Erdos3

theorem normalizedMesh_scale_lower {delta scale inverseLog lengthLog : ℝ}
    (hdelta : 0 < delta) (hinv : delta⁻¹ ≤ Real.exp inverseLog)
    (hscale : 4 * Real.exp (inverseLog + lengthLog) ≤ scale) :
    Real.exp lengthLog ≤ delta * scale / 4 := by
  have hinv' := mul_le_mul_of_nonneg_left hinv hdelta.le
  rw [mul_inv_cancel₀ hdelta.ne'] at hinv'
  have hprod := mul_le_mul_of_nonneg_right hinv' (by positivity : 0 ≤ 4 * Real.exp lengthLog)
  have hsize := mul_le_mul_of_nonneg_left hscale hdelta.le
  rw [Real.exp_add] at hsize
  nlinarith

theorem normalizedMesh_scale_large {delta scale inverseLog lengthLog : ℝ}
    (hdelta : 0 < delta) (hinv : delta⁻¹ ≤ Real.exp inverseLog)
    (hlength : 0 ≤ lengthLog) (hscale : 4 * Real.exp (inverseLog + lengthLog) ≤ scale) :
    4 ≤ delta * scale := by
  have h := normalizedMesh_scale_lower hdelta hinv hscale
  have hone := Real.one_le_exp_iff.mpr hlength
  linarith

end Erdos3

end

end OAI

end

theorem solution : type_of% @OAI.Erdos3.normalizedMesh_scale_large := @OAI.Erdos3.normalizedMesh_scale_large
