-- Prove2me | solution 1 for GlobalTheory.SatakeWeyl.perm_of_swap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:36:15.079227+00:00
-- url     : https://prove2.me/submissions/0e476675-7005-49ac-b8be-204a65799c34

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
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_mul
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_one
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
theorem _root_.solution (S : (Fin m → ℤ) → ℂ)
    (hS : ∀ (i j : Fin m), j.val = i.val + 1 → ∀ a, S (a ∘ Equiv.swap i j) = S a) (π : Equiv.Perm (Fin m)) :
    ∀ a, S (a ∘ π) = S a := by
  cases m with
  | zero => intro a; congr 1; funext i; exact i.elim0
  | succ m =>
    have hπ : π ∈ Submonoid.closure (Set.range fun i : Fin m => Equiv.swap i.castSucc i.succ) := by
      rw [Equiv.Perm.mclosure_swap_castSucc_succ]; trivial
    induction hπ using Submonoid.closure_induction with
    | mem x hx => obtain ⟨i, rfl⟩ := hx; exact hS _ _ (by simp)
    | one => intro a; rfl
    | mul x y _ _ hx hy => intro a; rw [← hx a, ← hy (a ∘ x)]; rfl
end GlobalTheory.SatakeWeyl
