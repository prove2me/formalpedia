-- Prove2me | solution 1 for GlobalTheory.PairOp.unit_FF_FFStar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:40:02.476303+00:00
-- url     : https://prove2.me/submissions/1ee76cfa-03c5-497c-b7ff-474c06ac318e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_AdjointOperatorIdentities
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ExistsFFNeZeroThree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PairOperatorStatement
import Theorems.Thm_GlobalTheory_PairOp_FF_dia
import Theorems.Thm_GlobalTheory_LatPair_Model_FF_dia


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
variable (χ)
namespace GlobalTheory.PairOp
theorem _root_.solution (c : 𝓀[k]ˣ) :
    (dia c⁻¹ * FF q χ * (dia c * FFStar q χ) : Module.End ℂ (Form k n M)) = FF q χ * FFStar q χ := by
  rw [← FF_dia q χ c⁻¹, mul_assoc, ← mul_assoc (dia c⁻¹), ← map_mul, inv_mul_cancel, map_one, one_mul]
end GlobalTheory.PairOp
