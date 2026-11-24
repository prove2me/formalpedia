-- Prove2me | solution 1 for GlobalTheory.LastSteps.lift_latInd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:49:04.321602+00:00
-- url     : https://prove2.me/submissions/52ee5696-c312-4336-aaf3-a84476fc9bd3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_DualLiftInvariance
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PairOperatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactMapsPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactQLat
import Theorems.Thm_GlobalTheory_LastSteps_latInd_mul
import Theorems.Thm_GlobalTheory_LatPair_latInd_mem_SB
import Theorems.Thm_GlobalTheory_PairOp_vanishing


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
variable {π : Representation ℂ (GL n' k) M} {θ : M →ₗ[ℂ] (Matrix n n' k → ℂ) →ₗ[ℂ] A} {φ : Form k n' M}
namespace GlobalTheory.LastSteps
theorem _root_.solution (hφ : φ ∈ Mram k n' M) (he : φ ∈ EqForm π) (hθ : IsLiftInv π θ P.ker)
    (L₁ : Submodule 𝒪[k] (n → k)) [L₁.IsLattice k] : θ (φ P) (latInd P.ker L₁) = 0 := by
  obtain ⟨q⟩ : Nonempty (Unif k) := inferInstance
  have hv : formOf π P (evalEquiv π P ⟨φ, he⟩) = φ := congrArg Subtype.val ((evalEquiv π P).left_inv ⟨φ, he⟩)
  refine (PairOp.vanishing q).invariant_eq_zero π P (evalEquiv π P ⟨φ, he⟩) (hv.symm ▸ hφ) A
    (θ.flip (latInd P.ker L₁)) (Or.inr fun g hg w => ?_)
  have := hθ g hg w _ (latInd_mem_SB P.ker L₁)
  simp only [latInd_mul hg] at this
  exact this
end GlobalTheory.LastSteps
