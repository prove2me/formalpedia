-- Prove2me | solution 1 for GlobalTheory.LastSteps.latInd_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:54:26.532989+00:00
-- url     : https://prove2.me/submissions/588623b7-fb3b-444e-bbe4-2174e6de2fdf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_DualLiftInvariance
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PairOperatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactMapsPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactQLat
import Theorems.Thm_GlobalTheory_LatPair_latInd_smul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix IsLocalRing
open scoped Pointwise
open GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData
noncomputable section
open GlobalTheory GlobalTheory.LastSteps
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' n'' : Type}
variable [Fintype n'] {L : Submodule 𝒪[k] (n' → k)} {LY : Submodule 𝒪[k] (n → k)} {x₀ : Matrix n n' k}
variable (q : Unif k) (χ : AddChar 𝓀[k] ℂ) (ε : 𝓀[k]ˣ) (P : Pair k n')
variable [LY.IsLattice k] (fW : {f : Module.Dual 𝓀[k] (Red LY) // f ≠ 0})
variable {M A : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup A] [Module ℂ A]
variable [DecidableEq n'] [Fintype n]
namespace GlobalTheory.LastSteps
theorem _root_.solution {g : GL n' k} (hg : g ∈ latStab L) (L₁ : Submodule 𝒪[k] (n → k)) (x₀ : Matrix n n' k) :
    latInd L L₁ (x₀ * g.val) = latInd L L₁ x₀ := by
  classical
  have := latInd_smul (x := x₀) g 1 L L₁
  rw [MulAction.mem_stabilizer_iff.1 hg, one_smul] at this
  simpa using this.symm
end GlobalTheory.LastSteps
