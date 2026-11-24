-- Prove2me | solution 1 for GlobalTheory.PairOp.FF_FFStar_ram
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:49:39.677577+00:00
-- url     : https://prove2.me/submissions/dfda5065-e4b5-48d9-902a-a63b73a4f30d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_AdjointOperatorIdentities
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ExistsFFNeZeroThree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PairOperatorStatement
import Theorems.Thm_GlobalTheory_PairOp_FF_FFStar
import Theorems.Thm_GlobalTheory_LatPair_Model_tr_eq_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix IsLocalRing
open GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.AdjointOperatorIdentities
noncomputable section
open GlobalTheory GlobalTheory.PairOp
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : Type}
  {M : Type} [AddCommGroup M] [Module ℂ M]
variable (q : Unif k) (χ : AddChar 𝓀[k] ℂ)
variable {χ}
namespace GlobalTheory.PairOp
theorem _root_.solution [Fintype n] (hχ : χ ≠ 1) {φ : Form k n M} (h : φ ∈ Mram k n M) :
    FF q χ (FFStar q χ φ) = ((resCard k : ℂ) ^ Fintype.card n) • φ := by
  rw [FF_FFStar q hχ φ, (Model.tr_eq_zero h).2, sub_zero]
end GlobalTheory.PairOp
