-- Prove2me | solution 1 for GlobalTheory.SmoothForms.filt_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:28:15.7298+00:00
-- url     : https://prove2.me/submissions/549fcfff-a07b-4e94-8c11-9d4c5e11c319

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_RightDerivativeAlongLieSmoothAndLinearStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_RightDerivativeAlongLieCommutatorEqBracketStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_CommutatorGlGeneratorTensorWordMapMatrixUnitsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_MemAdjoinGlActionOfCommuteTensorPermStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_BicommutantTensorFactorPermMemSpanStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_CommutantLiftModStableSelfAdjointStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_PermutationWordGelfandPolynomialModShorterStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_CommuteGelfandInvariantMatrixUnitsOfGlRelStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_PolarConjTranspose
import Theorems.Thm_GlobalTheory_SmoothForms_range_le_filt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ContDiff Topology
open Matrix
open GlobalTheory GlobalTheory.SmoothForms
variable {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} {E : Fin n → Fin n → A}
namespace GlobalTheory.SmoothForms
theorem _root_.solution (d : ℕ) : filt E (d + 1) ≤ LinearMap.range (wordMap E d) ⊔ filt E d :=
  iSup₂_le fun k hk => by
    rcases (Nat.lt_succ_iff.1 hk).eq_or_lt with rfl | h
    · exact le_sup_left
    · exact (range_le_filt h).trans le_sup_right
end GlobalTheory.SmoothForms
