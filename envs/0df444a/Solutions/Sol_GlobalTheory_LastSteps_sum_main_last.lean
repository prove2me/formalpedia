-- Prove2me | solution 1 for GlobalTheory.LastSteps.sum_main_last
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:25:59.539994+00:00
-- url     : https://prove2.me/submissions/a25c2a3b-2f96-4c72-95fe-d6b0867e3458

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_DualLiftInvariance
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PairOperatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactMapsPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactQLat
import Theorems.Thm_GlobalTheory_LastSteps_finsum_ofDual
import Theorems.Thm_GlobalTheory_LastSteps_sum_mainDatum
import Theorems.Thm_P2M_GlobalTheory_LastSteps_phiOne_last__fde6c3287ccb

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
variable [Fintype n] [Fintype n'] (q : Unif k) (LY : Submodule 𝒪[k] (n → k)) [LY.IsLattice k]
  (L'' : Submodule 𝒪[k] (n'' → k)) [L''.IsLattice k] {M A : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup A]
  [Module ℂ A] (x' : Matrix n'' n k) (η : n → k)
namespace GlobalTheory.LastSteps
theorem _root_.solution (χ : AddChar 𝓀[k] ℂ) (ε : 𝓀[k]ˣ) (L : Submodule 𝒪[k] (n' → k)) (φ : Form k n' M)
    (x₀ : Matrix n n' k) :
    ∑ P ∈ withKer L, (∑ᶠ fW : {f : Module.Dual 𝓀[k] (Red LY) // f ≠ 0},
        mainDatum q χ ε P (ofDual LY fW) x₀ * (latInd LY L'' x' * cosetInd q LY fW.1 η)) • φ P =
      ∑ Q ∈ withLat LY, ∑ P' ∈ withLat L,
        (phiOne Q (lastPair q L'') (withRow x' η) * phiOne P' Q x₀) • dia ε (FFStar q χ φ) P' := by
  simp only [← phiOne_last']
  simp only [fun P => finsum_ofDual LY fun Q => mainDatum q χ ε P Q x₀ * phiOne Q (lastPair q L'') (withRow x' η),
    Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun Q _ => ?_
  simp only [mul_comm _ (phiOne Q (lastPair q L'') (withRow x' η)), mul_smul, ← Finset.smul_sum, sum_mainDatum]
end GlobalTheory.LastSteps
