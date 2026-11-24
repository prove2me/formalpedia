-- Prove2me | solution 1 for GlobalTheory.T.schwartzBruhatInvariantIntegral_matrix_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:09:32.695417+00:00
-- url     : https://prove2.me/submissions/bb477b0a-6c8b-4636-91a3-67cc6591062a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatInvariantIntegralMatrixMul
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatInvariantIntegralMatrixMulStatement
import Theorems.Thm_GlobalTheory_SW_LinChange_haar_mul


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
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K κ ι : Type) [Field K] [NumberField K] [Fintype κ] [Fintype ι] [DecidableEq ι] [DecidableEq κ] (φ : Matrix κ ι K → ℂ), IsSB φ → (∀ A : Matrix ι ι K, A.det ≠ 0 → IsSB (fun x : Matrix κ ι K => φ (x * A)) ∧ haar (fun x : Matrix κ ι K => φ (x * A)) = ((|Algebra.norm ℚ A.det| : ℚ) : ℂ) ^ Fintype.card κ * haar φ) ∧ ∀ A : Matrix κ κ K, A.det ≠ 0 → IsSB (fun x : Matrix κ ι K => φ (A * x)) ∧ haar (fun x : Matrix κ ι K => φ (A * x)) = ((|Algebra.norm ℚ A.det| : ℚ) : ℂ) ^ Fintype.card ι * haar φ := by
  first | exact @GlobalTheory.SW.LinChange.haar_mul | exact GlobalTheory.SW.LinChange.haar_mul | (intros; apply GlobalTheory.SW.LinChange.haar_mul <;> assumption)
end _root_.GlobalTheory.T
