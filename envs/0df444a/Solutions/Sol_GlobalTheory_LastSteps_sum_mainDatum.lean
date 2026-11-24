-- Prove2me | solution 1 for GlobalTheory.LastSteps.sum_mainDatum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:56:45.710189+00:00
-- url     : https://prove2.me/submissions/4911063e-b68f-4712-990e-ff87c9792538

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_DualLiftInvariance
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PairOperatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactMapsPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactQLat
import Theorems.Thm_GlobalTheory_LastSteps_mainDatum_eq
import Theorems.Thm_GlobalTheory_LastSteps_dia_FFStar

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
namespace GlobalTheory.LastSteps
theorem _root_.solution (L : Submodule 𝒪[k] (n' → k)) (Q : Pair k n) (φ : Form k n' M) (x₀ : Matrix n n' k) :
    ∑ P ∈ withKer L, mainDatum q χ ε P Q x₀ • φ P =
      ∑ P' ∈ withLat L, phiOne P' Q x₀ • dia ε (FFStar q χ φ) P' := by
  calc _ = ∑ P ∈ withKer L, ∑ P' ∈ withLat L, phiOne P' Q x₀ • χ (-((ε : 𝓀[k]) * cross q P P')) • φ P := by
        refine Finset.sum_congr rfl fun P hP => ?_
        rw [mainDatum_eq, mem_withKer.1 hP, Finset.sum_apply, Finset.sum_smul]
        exact Finset.sum_congr rfl fun P' _ => by rw [Pi.smul_apply, smul_eq_mul, mul_comm, mul_smul]
    _ = _ := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun P' hP' => by rw [dia_FFStar, mem_withLat.1 hP', Finset.smul_sum]
end GlobalTheory.LastSteps
