-- Prove2me | solution 1 for GlobalTheory.LastSteps.sum_datumHat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:07:14.270919+00:00
-- url     : https://prove2.me/submissions/8f99f432-16a4-4e63-8d6a-82794972a4e5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_DualLiftInvariance
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PairOperatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactMapsPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactQLat
import Theorems.Thm_GlobalTheory_LastSteps_sum_mainDatum
import Theorems.Thm_GlobalTheory_LastSteps_sum_latInd
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
theorem _root_.solution (hφ : φ ∈ Mram k n' M) (x₀ : Matrix n n' k) :
    ∑ P ∈ withKer L, (datumHat ψ ε μ q P LY x₀ η * latInd LY L'' x') • φ P =
      (volQ μ q LY : ℂ) • ∑ Q ∈ withLat LY, ∑ P' ∈ withLat L,
        (phiOne Q (lastPair q L'') (withRow x' η) * phiOne P' Q x₀) •
          dia (resUnit ε) (FFStar q (resChar ψ hψ q) φ) P' := by
  have h := fun P => congrFun (datumHat_mul q LY L'' x' η hψ ε μ P) x₀
  simp only [Pi.smul_apply, Pi.add_apply, Finset.sum_apply, smul_eq_mul] at h
  simp only [mul_comm _ (latInd LY L'' x'), h]
  simp only [mul_smul, add_smul, Finset.sum_smul, ← Finset.smul_sum, Finset.sum_add_distrib, sum_latInd hφ,
    smul_zero, zero_add]
  rw [Finset.sum_comm]
  simp only [← Finset.smul_sum, Finset.sum_add_distrib, sum_latInd hφ, zero_add, sum_mainDatum]
end GlobalTheory.LastSteps
