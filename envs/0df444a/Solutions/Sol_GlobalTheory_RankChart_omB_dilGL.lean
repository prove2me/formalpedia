-- Prove2me | solution 1 for GlobalTheory.RankChart.omB_dilGL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:10:21.492797+00:00
-- url     : https://prove2.me/submissions/9e2620e5-9b1d-4208-8162-59b920cd3479

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SubMemNsp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IsBicharPairing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SchwartzBruhatMatrixExistsOpenAddSubgroupInvaria
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ShearGLTransposeMul
import Theorems.Thm_P2M_GlobalTheory_RankChart_toRows__shear_d5dffcf9ff0a
import Theorems.Thm_P2M_GlobalTheory_RankChart_toRows__dil_a78c4f6a5c7f
import Theorems.Thm_P2M_GlobalTheory_RankChart_toRows__stack_b71dac95216e
import Theorems.Thm_GlobalTheory_RankChart_dilGL_transpose_mul
import Theorems.Thm_GlobalTheory_RankChart_gdet_dilGL
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.RankChart.toRows₁_shear
attribute [local simp] GlobalTheory.RankChart.toRows₁_dil
attribute [local simp] GlobalTheory.RankChart.toRows₁_stack

set_option autoImplicit false
open GlobalTheory.WeilM Matrix
noncomputable section
open GlobalTheory GlobalTheory.RankChart
open GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.SplitWeil.Model
variable {k : Type} [Field k] {R T D : Type} [Fintype R] [DecidableEq R] [Fintype T] [DecidableEq T]
  [Fintype D] [DecidableEq D]
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.RankChart
theorem _root_.solution (ν : kˣ →* ℂˣ) (t : kˣ) (Ψ : Matrix (R ⊕ T) D k → ℂ) (Y : Matrix (R ⊕ T) D k) :
    omB ν ν (dilGL t : GL (R ⊕ T) k) 1 Ψ Y =
      (ν t : ℂ) ^ Fintype.card T * apow (t ^ Fintype.card T) ((Fintype.card D : ℂ) / 2) * Ψ (dil (t : k) Y) := by
  simp [omB, gdet_dilGL, dilGL_transpose_mul]
end GlobalTheory.RankChart
