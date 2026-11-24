-- Prove2me | solution 1 for GlobalTheory.LastSteps.sum_latInd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:49:05.186039+00:00
-- url     : https://prove2.me/submissions/a65ffbde-9ee3-481f-8ce4-22ca0c976658

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_DualLiftInvariance
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PairOperatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactMapsPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactQLat
import Theorems.Thm_GlobalTheory_LatPair_trKer_apply
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
omit [Fintype n]
namespace GlobalTheory.LastSteps
theorem _root_.solution {φ : Form k n' M} (hφ : φ ∈ Mram k n' M) (L : Submodule 𝒪[k] (n' → k)) [L.IsLattice k]
    (L₁ : Submodule 𝒪[k] (n → k)) (x₀ : Matrix n n' k) : ∑ P₁ ∈ withKer L, latInd P₁.ker L₁ x₀ • φ P₁ = 0 := by
  obtain ⟨q⟩ : Nonempty (Unif k) := inferInstance
  rw [Finset.sum_congr rfl fun P₁ h => by rw [mem_withKer.1 h], ← Finset.smul_sum, ← trKer_apply,
    (PairOp.vanishing q).trKer_eq_zero φ hφ L, smul_zero]
end GlobalTheory.LastSteps
