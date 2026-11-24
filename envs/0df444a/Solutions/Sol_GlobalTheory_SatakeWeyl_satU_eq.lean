-- Prove2me | solution 1 for GlobalTheory.SatakeWeyl.satU_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:50:20.803609+00:00
-- url     : https://prove2.me/submissions/457bf261-a971-4eb5-aeed-2254a909bff3

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
import Theorems.Thm_GlobalTheory_SatakeWeyl_mem_radU_iff
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
import Theorems.Thm_GlobalTheory_SatakeWeyl_mat_injective


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.UG
open GlobalTheory GlobalTheory.SatakeWeyl
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {ϖ : L} {q n m : ℕ}
namespace GlobalTheory.SatakeWeyl
theorem _root_.solution (T : (Fin m → ℤ) → GU σ n) (hT : ∀ a, mat (T a) = tMat ϖ n m a) (h : GU σ n → ℂ) (α : Fin m → ℂ) :
    SatU ϖ q h α = ∑ᶠ a : Fin m → ℤ, (∏ i, α i ^ a i) *
      ((q : ℂ) ^ 0 * (∏ i : Fin m, (q : ℂ) ^ (-(a i) * ((n : ℤ) - 1 - 2 * (i.val : ℤ)))) *
        cellSum (KU σ n) (radU σ Fin.val) h (T a)) := by
  unfold SatU cellSum
  refine finsum_congr fun a => ?_
  rw [Finset.prod_mul_distrib, pow_zero, one_mul, mul_assoc]
  congr 2
  refine finsum_congr fun x => ?_
  congr 1
  refine propext ⟨?_, ?_⟩
  · rintro ⟨u, hu, k, hk, e⟩
    exact ⟨u, (mem_radU_iff u).2 hu, k, hk, mat_injective (by rw [mat_mul, mat_mul, hT]; exact e)⟩
  · rintro ⟨u, hu, k, hk, e⟩
    refine ⟨u, (mem_radU_iff u).1 hu, k, hk, ?_⟩
    have := congrArg mat e
    rw [mat_mul, mat_mul, hT] at this
    exact this
end GlobalTheory.SatakeWeyl
