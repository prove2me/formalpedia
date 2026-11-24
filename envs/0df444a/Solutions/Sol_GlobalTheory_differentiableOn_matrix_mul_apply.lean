-- Prove2me | solution 1 for GlobalTheory.differentiableOn_matrix_mul_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:34:52.29933+00:00
-- url     : https://prove2.me/submissions/a7faea93-5ef5-4463-9a9f-959b18fe820f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsEqTransposeMulDiagonalMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRepresentativesQuotientRangeMulVecLin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_HasSumLocallyUniformlyOnIteratedFDerivRiemannThe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenMain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_SemistableReduction_ShareDetA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FromBlocksMapIntCastMemSymplecticGroup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix
open scoped Real
noncomputable section
open GlobalTheory
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi
variable {g : ℕ} {γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ}
namespace GlobalTheory
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {n : Type*} [Fintype n] {M N : E → Matrix n n ℂ} {U : Set E}
    (hM : ∀ i j, DifferentiableOn ℂ (fun x => M x i j) U)
    (hN : ∀ i j, DifferentiableOn ℂ (fun x => N x i j) U) (i j : n) :
    DifferentiableOn ℂ (fun x => (M x * N x) i j) U :=
  DifferentiableOn.fun_sum fun k _ => (hM i k).mul (hN k j)
end GlobalTheory
