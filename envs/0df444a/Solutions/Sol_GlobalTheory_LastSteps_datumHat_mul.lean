-- Prove2me | solution 1 for GlobalTheory.LastSteps.datumHat_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:25:27.352356+00:00
-- url     : https://prove2.me/submissions/a1e996e2-4107-47b1-a1c6-def3194c33a6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_DualLiftInvariance
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PairOperatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactMapsPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactQLat
import Theorems.Thm_GlobalTheory_LastSteps_finsum_split
import Theorems.Thm_GlobalTheory_LastSteps_term_zero
import Theorems.Thm_GlobalTheory_LastSteps_term_ne_zero
import Theorems.Thm_GlobalTheory_LastSteps_datumHat_eq
import Theorems.Thm_P2M_GlobalTheory_LastSteps_phiOne_last__fde6c3287ccb
import Theorems.Thm_GlobalTheory_LatPair_sum_withLat


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
namespace GlobalTheory.LastSteps
theorem _root_.solution (P : Pair k n') :
    latInd LY L'' x' • (fun x₀ => datumHat ψ ε μ q P LY x₀ η) = (volQ μ q LY : ℂ) •
      ((latInd LY L'' x' * cosetInd q LY 0 η) • latInd P.ker LY +
        ∑ Q ∈ withLat LY, phiOne Q (lastPair q L'') (withRow x' η) •
          (latInd P.ker Q.ker + mainDatum q (resChar ψ hψ q) (resUnit ε) P Q)) := by
  letI := Fintype.ofFinite {f : Module.Dual 𝓀[k] (Red LY) // f ≠ 0}
  ext x₀
  simp only [Pi.smul_apply, Pi.add_apply, Finset.sum_apply, smul_eq_mul]
  rw [(datumHat_eq q hψ μ LY ε P x₀ η).2, finsum_split, finsum_eq_sum_of_fintype, sum_withLat, term_zero,
    mul_left_comm, mul_add, Finset.mul_sum]
  congr 2
  · ring
  · refine Finset.sum_congr rfl fun f _ => ?_
    rw [term_ne_zero, phiOne_last', Pi.add_apply]
    ring
end GlobalTheory.LastSteps
