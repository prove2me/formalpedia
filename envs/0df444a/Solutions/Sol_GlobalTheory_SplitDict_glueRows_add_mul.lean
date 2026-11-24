-- Prove2me | solution 1 for GlobalTheory.SplitDict.glueRows_add_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:53:45.936318+00:00
-- url     : https://prove2.me/submissions/82f1ece6-a6bd-464a-b3f2-e925c342e49d

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
  [DecidableEq ρ] [Fintype v] [DecidableEq v] [Fintype τ] [DecidableEq τ] [Fintype w] [DecidableEq w]
namespace GlobalTheory.SplitDict
theorem _root_.solution (r : Matrix τ v k) (x : Matrix w v k) (ys : Matrix τ v k)
    (ξ' : Matrix τ ρ k) (ξ₀ : Matrix w ρ k) (ν' : Matrix ρ v k) :
    glueRows r x ys + glueRows ξ' ξ₀ 0 * ν' = glueRows (r + ξ' * ν') (x + ξ₀ * ν') ys := by
  ext (i | i | i) j <;> simp [glueRows, Matrix.fromRows_mul]
end GlobalTheory.SplitDict
