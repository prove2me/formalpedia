-- Prove2me | solution 1 for GlobalTheory.RankStrataProof.isSmoothChar_omChar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:32:41.519424+00:00
-- url     : https://prove2.me/submissions/fec05307-2bb0-4c06-90e9-d62825fccd24

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
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_inv
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_mul
import Theorems.Thm_GlobalTheory_SmGL_isSmoothChar_of_isUnram
import Theorems.Thm_GlobalTheory_SmGL_isUnram_absPow


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
variable {a b c d : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]
  [Fintype d] [DecidableEq d]
open Matrix Topology Module
open scoped TensorProduct
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {a b c d : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]
  [Fintype d] [DecidableEq d]
namespace GlobalTheory.RankStrataProof
namespace _root_.GlobalTheory.RankStrataProof
theorem _root_.solution {μ : kˣ →* ℂˣ} (hμ : _root_.GlobalTheory.SmGL.IsSmoothChar μ) : _root_.GlobalTheory.SmGL.IsSmoothChar (_root_.GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.omChar a b μ) := by
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.omChar
  apply _root_.GlobalTheory.SmGL.IsSmoothChar.mul
  · refine _root_.GlobalTheory.SmGL.IsSmoothChar.comp ?_ _ continuous_fst
    apply _root_.GlobalTheory.SmGL.IsSmoothChar.detChar
    exact _root_.GlobalTheory.SmGL.IsSmoothChar.mul
      (_root_.GlobalTheory.SmGL.IsSmoothChar.inv hμ)
      (_root_.GlobalTheory.SmGL.isSmoothChar_of_isUnram (_root_.GlobalTheory.SmGL.isUnram_absPow k _))
  · refine _root_.GlobalTheory.SmGL.IsSmoothChar.comp ?_ _ continuous_snd
    apply _root_.GlobalTheory.SmGL.IsSmoothChar.detChar
    exact _root_.GlobalTheory.SmGL.IsSmoothChar.mul hμ
      (_root_.GlobalTheory.SmGL.isSmoothChar_of_isUnram (_root_.GlobalTheory.SmGL.isUnram_absPow k _))
end _root_.GlobalTheory.RankStrataProof
end GlobalTheory.RankStrataProof
