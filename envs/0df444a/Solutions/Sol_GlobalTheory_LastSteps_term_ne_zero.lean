-- Prove2me | solution 1 for GlobalTheory.LastSteps.term_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:05:35.123828+00:00
-- url     : https://prove2.me/submissions/ccb57886-71a1-45d5-bc66-d20f0a4af803

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_DualLiftInvariance
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PairOperatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactMapsPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactQLat
import Theorems.Thm_GlobalTheory_LastSteps_finsum_split
import Theorems.Thm_GlobalTheory_LastSteps_term_eq_finsum
import Theorems.Thm_GlobalTheory_LastSteps_compInd_zero
import Theorems.Thm_GlobalTheory_LastSteps_compInd_eq_phiOne

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
namespace GlobalTheory.LastSteps
theorem _root_.solution : term q χ ε P LY fW.1 =
    latInd P.ker (ofDual LY fW).ker + mainDatum q χ ε P (ofDual LY fW) := by
  ext x₀
  rw [term_eq_finsum, finsum_split, compInd_zero, Pi.add_apply]
  simp only [LinearMap.zero_apply, mul_zero, neg_zero, AddChar.map_zero_eq_one, one_mul,
    compInd_eq_phiOne]
  rfl
end GlobalTheory.LastSteps
