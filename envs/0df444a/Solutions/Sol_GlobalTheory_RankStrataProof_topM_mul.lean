-- Prove2me | solution 1 for GlobalTheory.RankStrataProof.topM_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:11:36.98792+00:00
-- url     : https://prove2.me/submissions/3bd532dc-2850-48f0-8fc6-76eeb5853c91

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_OpenClosedSequences
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SchwartzBruhatSweepSmoothlyInducedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsGLMulRightColumnsEqZeroOfRankStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeftColumnsMulVecInjectiveOfRankEqCardStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsOpenNormalisedSubgroupSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RankFiltrationExists
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClosedEmbeddingTopEmb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences Matrix Topology
open scoped TensorProduct
open GlobalTheory GlobalTheory.RankStrataProof
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {a b c : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [DecidableEq a]
  [DecidableEq b] [DecidableEq c] [Fintype c] [Fintype b]
namespace GlobalTheory.RankStrataProof
theorem _root_.solution (e : a ⊕ c ≃ b) (y g : Matrix a a k) : topM e (y * g) = topM e y * g := by
  ext i l
  obtain ⟨i | i, rfl⟩ := e.surjective i <;> simp [mul_apply]
end GlobalTheory.RankStrataProof
