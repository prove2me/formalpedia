-- Prove2me | solution 1 for GlobalTheory.PairOp.eq_zpow_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:51:41.243783+00:00
-- url     : https://prove2.me/submissions/c16ff292-c362-41a2-913b-36fd547dad60

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_AdjointOperatorIdentities
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ExistsFFNeZeroThree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PairOperatorStatement
import Theorems.Thm_GlobalTheory_PairOp_resCard_ne_zero

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
theorem _root_.solution {φ φ' : Form k n M} {r : ℕ} (h : (resCard k : ℂ) • φ' = ((resCard k : ℂ) ^ r) • φ) :
    φ' = ((resCard k : ℂ) ^ ((r : ℤ) - 1)) • φ := by
  have hq := resCard_ne_zero (k := k)
  have e : φ' = ((resCard k : ℂ)⁻¹ * (resCard k : ℂ) ^ r) • φ := by
    rw [mul_smul, ← h, smul_smul, inv_mul_cancel₀ hq, one_smul]
  rw [e, zpow_sub₀ hq, zpow_natCast, zpow_one, div_eq_inv_mul]
end GlobalTheory.PairOp
