-- Prove2me | solution 1 for GlobalTheory.SW.LinChange.det_mul_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:09:11.777878+00:00
-- url     : https://prove2.me/submissions/7c6da33a-fd69-415e-8eed-0b671184615d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatInvariantIntegralMatrixMul

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
theorem _root_.solution [DecidableEq ι] (A : Matrix ι ι K) :
    LinearMap.det (mulRightLinearMap κ K A) = A.det ^ Fintype.card κ := by
  have h := LinearMap.det_pi (fun _ : κ => Matrix.toLin' Aᵀ)
  rw [Finset.prod_const, LinearMap.det_toLin', Matrix.det_transpose, Finset.card_univ] at h
  rw [← h]
  congr 1
  refine LinearMap.ext fun x => ?_
  funext k i
  change (x * A) k i = (Aᵀ *ᵥ x k) i
  rw [Matrix.mulVec_transpose]
  rfl
end GlobalTheory.SW.LinChange
