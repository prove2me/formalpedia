-- Prove2me | solution 1 for GlobalTheory.SW.LinChange.haar_comp_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:48:29.125661+00:00
-- url     : https://prove2.me/submissions/2bec385c-af0f-4161-a27a-bcd85fea4b77

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatInvariantIntegralMatrixMul
import Theorems.Thm_GlobalTheory_SW_LinChange_haar_comp

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
theorem _root_.solution (f : Matrix κ ι K →ₗ[K] Matrix κ ι K) (hf : LinearMap.det f ≠ 0)
    (φ : Matrix κ ι K → ℂ) (hφ : IsSB φ) :
    IsSB (fun x => φ (f x)) ∧
      haar (fun x => φ (f x)) = ((|Algebra.norm ℚ (LinearMap.det f)| : ℚ) : ℂ) * haar φ := by
  have h := haar_comp ((f.equivOfDetNeZero hf).restrictScalars ℚ) φ hφ
  rw [← LinearMap.det_restrictScalars]
  exact h
end GlobalTheory.SW.LinChange
