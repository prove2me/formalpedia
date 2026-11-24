-- Prove2me | solution 1 for GlobalTheory.LastSteps.mainDatum_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:51:40.701124+00:00
-- url     : https://prove2.me/submissions/01c54711-334a-4f2e-ab88-a5b257b965fd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_DualLiftInvariance
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PairOperatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactMapsPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactQLat
import Theorems.Thm_GlobalTheory_LastSteps_finsum_ofDual
import Theorems.Thm_GlobalTheory_LatPair_cross_hasVal


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
theorem _root_.solution (Q : Pair k n) : mainDatum q χ ε P Q =
    ∑ P' ∈ withLat P.ker, χ (-((ε : 𝓀[k]) * cross q P P')) • phiOne P' Q := by
  ext x₀
  rw [Finset.sum_apply, ← finsum_ofDual]
  refine finsum_congr fun f' => ?_
  rw [(cross_hasVal q (P := ofDual P.ker f') rfl P.hasVal_vec).unique (ofDual_hasVal P.ker f' ⟨_, _⟩)]
  rfl
end GlobalTheory.LastSteps
