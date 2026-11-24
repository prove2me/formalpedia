-- Prove2me | solution 1 for GlobalTheory.SW.LinChange.haar_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:59:07.287924+00:00
-- url     : https://prove2.me/submissions/688a7047-20db-4b3f-89aa-57c23842af37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatInvariantIntegralMatrixMul
import Theorems.Thm_GlobalTheory_SW_LinChange_haar_comp_field
import Theorems.Thm_GlobalTheory_SW_LinChange_det_mul_right
import Theorems.Thm_GlobalTheory_SW_LinChange_det_mul_left

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
theorem _root_.solution : ∀ (K κ ι : Type) [Field K] [NumberField K] [Fintype κ] [Fintype ι] [DecidableEq ι] [DecidableEq κ] (φ : Matrix κ ι K → ℂ), IsSB φ → (∀ A : Matrix ι ι K, A.det ≠ 0 → IsSB (fun x : Matrix κ ι K => φ (x * A)) ∧ haar (fun x : Matrix κ ι K => φ (x * A)) = ((|Algebra.norm ℚ A.det| : ℚ) : ℂ) ^ Fintype.card κ * haar φ) ∧ ∀ A : Matrix κ κ K, A.det ≠ 0 → IsSB (fun x : Matrix κ ι K => φ (A * x)) ∧ haar (fun x : Matrix κ ι K => φ (A * x)) = ((|Algebra.norm ℚ A.det| : ℚ) : ℂ) ^ Fintype.card ι * haar φ := by
  intro K κ ι _ _ _ _ _ _ φ hφ
  refine ⟨fun A hA => ?_, fun A hA => ?_⟩
  · have h := haar_comp_field (mulRightLinearMap κ K A)
      (by rw [det_mul_right]; exact pow_ne_zero _ hA) φ hφ
    rw [det_mul_right, map_pow, abs_pow, Rat.cast_pow] at h
    exact h
  · have h := haar_comp_field (mulLeftLinearMap ι K A)
      (by rw [det_mul_left]; exact pow_ne_zero _ hA) φ hφ
    rw [det_mul_left, map_pow, abs_pow, Rat.cast_pow] at h
    exact h
end GlobalTheory.SW.LinChange
