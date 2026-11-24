-- Prove2me | solution 1 for GlobalTheory.SW.LinChange.det_mul_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:27:19.250213+00:00
-- url     : https://prove2.me/submissions/3c44089a-e52f-4a36-ac94-4852a912d8d5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatInvariantIntegralMatrixMul
import Theorems.Thm_GlobalTheory_SW_LinChange_det_mul_right

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.LinChange
variable {K : Type} [Field K] [NumberField K] {κ ι : Type} [Fintype κ] [Fintype ι]
namespace GlobalTheory.SW.LinChange
theorem _root_.solution [DecidableEq κ] (A : Matrix κ κ K) :
    LinearMap.det (mulLeftLinearMap ι K A) = A.det ^ Fintype.card ι := by
  rw [← Matrix.det_transpose, ← det_mul_right, ← LinearMap.det_conj (mulRightLinearMap ι K Aᵀ)
    (Matrix.transposeLinearEquiv ι κ K K)]
  congr 1
  refine LinearMap.ext fun x => ?_
  simp [Matrix.transpose_mul]
end GlobalTheory.SW.LinChange
