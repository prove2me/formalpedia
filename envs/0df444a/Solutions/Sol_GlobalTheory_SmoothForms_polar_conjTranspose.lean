-- Prove2me | solution 1 for GlobalTheory.SmoothForms.polar_conjTranspose
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:17:49.596464+00:00
-- url     : https://prove2.me/submissions/16638bd0-6c39-4f83-a778-77d6e1fd86be

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
theorem _root_.solution (d : ℕ) (a b : Fin n) : (polar n d a b)ᴴ = polar n d b a := by
  ext I K
  simp only [polar, conjTranspose_apply, of_apply, star_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  have : (K p = a ∧ I p = b ∧ ∀ q, q ≠ p → K q = I q) ↔ (I p = b ∧ K p = a ∧ ∀ q, q ≠ p → I q = K q) :=
    ⟨fun h => ⟨h.2.1, h.1, fun q hq => (h.2.2 q hq).symm⟩, fun h => ⟨h.2.1, h.1, fun q hq => (h.2.2 q hq).symm⟩⟩
  simp only [this]
  split_ifs <;> simp
end GlobalTheory.SmoothForms
