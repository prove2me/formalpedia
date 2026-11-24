-- Prove2me | solution 1 for GlobalTheory.LastSteps.lift_datumHat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:07:13.451063+00:00
-- url     : https://prove2.me/submissions/61096d2c-f261-4240-8d30-f406d9d51899

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_DualLiftInvariance
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PairOperatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactMapsPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactQLat
import Theorems.Thm_GlobalTheory_LastSteps_lift_latInd
import Theorems.Thm_GlobalTheory_LastSteps_lift_mainDatum
import Theorems.Thm_GlobalTheory_LastSteps_datumHat_mul

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
variable [MeasurableSpace k] [BorelSpace k] {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) (ε : 𝒪[k]ˣ)
  (μ : Measure (n → k)) [μ.IsAddHaarMeasure]
variable [DecidableEq n'] {L : Submodule 𝒪[k] (n' → k)} [L.IsLattice k] {φ : Form k n' M}
namespace GlobalTheory.LastSteps
theorem _root_.solution {π : Representation ℂ (GL n' k) M} {θ : M →ₗ[ℂ] (Matrix n n' k → ℂ) →ₗ[ℂ] A}
    (hφ : φ ∈ Mram k n' M) (he : φ ∈ EqForm π) (hθ : IsLiftInv π θ L) {P P' : Pair k n'} (hP : P.ker = L)
    (hP' : P'.lat = L) :
    latInd LY L'' x' • θ (φ P) (fun x₀ => datumHat ψ ε μ q P LY x₀ η) =
      (volQ μ q LY : ℂ) • ∑ Q ∈ withLat LY, phiOne Q (lastPair q L'') (withRow x' η) •
        θ (dia (resUnit ε) (FFStar q (resChar ψ hψ q) φ) P') (phiOne P' Q) := by
  have h0 := lift_latInd P hφ he (hP.symm ▸ hθ)
  rw [← map_smul, datumHat_mul q LY L'' x' η hψ]
  simp only [map_smul, map_add, map_sum, h0 LY, fun Q : Pair k n => h0 Q.ker, smul_zero, zero_add,
    fun Q => lift_mainDatum q (resChar ψ hψ q) (resUnit ε) he hθ Q hP hP']
end GlobalTheory.LastSteps
