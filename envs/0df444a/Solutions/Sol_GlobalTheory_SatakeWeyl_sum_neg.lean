-- Prove2me | solution 1 for GlobalTheory.SatakeWeyl.sum_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:54:04.268697+00:00
-- url     : https://prove2.me/submissions/e94b7082-3a96-4f5c-a972-c86028627d0b

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CellSumTwoStageDescentUnipotentStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CellSumLeftRightInvarianceNormaliserStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteIndexLeftRightCosetSumsEqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexCosetSumUnimodularityOfFiniteIndexStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContractingAutomorphismSubgroupChainIndexStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContractingAutChainCosetSumScalingOfUnimodularitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CellSumRankOneReflectionSymmetryOfStepsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSmallerUnitaryGroupEmbeddingStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SmallerUnitaryEmbeddingPreservesIntegralPartsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryDiagonalFactorizationAlongEmbeddingStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryLeviNormalizesUnipotentRadicalStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryBlockTriangularLeviPartUnitaryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryUnipotentRadicalSplittingOfLeviPartStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryDominantDiagonalConjugationContractsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryLeviCentreDiagonalConjugationEqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryCellSumLeviReductionOfStepsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TraceZeroIntegersModUniformizerCardOfCardSqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardIntegersModUniformizerEqQSqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryRankTwoRootIndexOfTraceZeroCardStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryRankThreeRootIndexOfCardsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryFourLeviGL2RootIndexOfCardSqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryFourLeviGL2CartanDoubleCosetsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitarySatakeCoeffAdjacentSwapOfLeviReductionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitarySatakeCoeffLastSignChangeOfLeviReductionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitarySatakeWeylInvariant
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open Formalism.UG
open GlobalTheory GlobalTheory.SatakeWeyl
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {ϖ : L} {q n m : ℕ}
namespace GlobalTheory.SatakeWeyl
theorem _root_.solution (S : (Fin m → ℤ) → ℂ) (j : Fin m) (hS : ∀ a, S (Function.update a j (-a j)) = S a) (α : Fin m → ℂ) :
    ∑ᶠ a : Fin m → ℤ, (∏ i, Function.update α j (α j)⁻¹ i ^ a i) * S a =
      ∑ᶠ a : Fin m → ℤ, (∏ i, α i ^ a i) * S a := by
  have hinv : Function.Involutive fun a : Fin m → ℤ => Function.update a j (-a j) := fun a => by simp
  rw [← finsum_comp_equiv hinv.toPerm]
  refine finsum_congr fun a => ?_
  rw [Function.Involutive.coe_toPerm, hS]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases hi : i = j
  · subst hi
    simp
  · rw [Function.update_of_ne hi, Function.update_of_ne hi]
end GlobalTheory.SatakeWeyl
