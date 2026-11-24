-- Prove2me | solution 1 for GlobalTheory.SplitDict.glueFun_mul_glueRows
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:53:44.511922+00:00
-- url     : https://prove2.me/submissions/82f5c708-edbe-44ec-828a-bc4c9085bbf3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_GL2CharacterZeros
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierTransformInversionLocalFieldPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsBoxInvariantSnd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi GlobalTheory.IndefiniteRowSideFullHecke.GLMatrixJoining
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.SplitDict
variable {k : Type} [Field k]
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]
variable (ψ : AddChar k Circle) (m : Measure k) [m.IsAddHaarMeasure] (μ : kˣ →* ℂˣ) (s₁ s₂ : ℤˣ)
variable {ρ v τ w W : Type} [Fintype ρ] [DecidableEq ρ] [Fintype v] [DecidableEq v]
  [Fintype τ] [DecidableEq τ] [Fintype w] [DecidableEq w] [Fintype W] [DecidableEq W]
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
  [Fintype ρ] [DecidableEq ρ] [Fintype v] [DecidableEq v] [DecidableEq τ] [DecidableEq w]
namespace GlobalTheory.SplitDict
theorem _root_.solution (η' : Matrix ρ τ k) (η₀ : Matrix ρ w k) (ηd : Matrix ρ τ k)
    (r : Matrix τ v k) (x : Matrix w v k) (ys : Matrix τ v k) :
    glueFun η' η₀ ηd * glueRows r x ys = η' * r + (η₀ * x + ηd * ys) := by
  simp only [glueFun, glueRows, Matrix.fromCols_mul_fromRows]
end GlobalTheory.SplitDict
