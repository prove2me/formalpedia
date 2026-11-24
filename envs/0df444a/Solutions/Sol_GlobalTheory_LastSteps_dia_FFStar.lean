-- Prove2me | solution 1 for GlobalTheory.LastSteps.dia_FFStar
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:43:46.671687+00:00
-- url     : https://prove2.me/submissions/acdeb02f-5f77-4389-a7cd-e5ef2684421d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_DualLiftInvariance
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PairOperatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactMapsPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactQLat
import Theorems.Thm_GlobalTheory_LatPair_FFStar_apply
import Theorems.Thm_GlobalTheory_LatPair_cross_dia_right


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
theorem _root_.solution (φ : Form k n' M) (P' : Pair k n') :
    dia ε (FFStar q χ φ) P' = ∑ P ∈ withKer P'.lat, χ (-((ε : 𝓀[k]) * cross q P P')) • φ P := by
  rw [dia_apply, FFStar_apply]
  exact Finset.sum_congr rfl fun P hP => by rw [cross_dia_right q (mem_withKer.1 hP).symm]
end GlobalTheory.LastSteps
