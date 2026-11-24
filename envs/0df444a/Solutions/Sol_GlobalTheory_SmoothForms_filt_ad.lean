-- Prove2me | solution 1 for GlobalTheory.SmoothForms.filt_ad
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:28:14.891703+00:00
-- url     : https://prove2.me/submissions/d684e2e2-510f-4b6c-81f8-ffbad4374d4a

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
import Theorems.Thm_GlobalTheory_T_commutator_glGenerator_tensorWordMapMatrixUnits


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
theorem _root_.solution (hE : Formalism.REAL.GlRel E) (d : ℕ) (a b : Fin n) {y : A} (hy : y ∈ filt E d) :
    E a b * y - y * E a b ∈ filt E d := by
  have : filt E d ≤ (filt E d).comap (LinearMap.mulLeft ℂ (E a b) - LinearMap.mulRight ℂ (E a b)) :=
    iSup₂_le fun k hk => by
      rintro _ ⟨M, rfl⟩
      change E a b * wordMap E k M - wordMap E k M * E a b ∈ filt E d
      rw [GlobalTheory.T.commutator_glGenerator_tensorWordMapMatrixUnits A n E hE]
      exact range_le_filt hk ⟨_, rfl⟩
  exact this hy
end GlobalTheory.SmoothForms
