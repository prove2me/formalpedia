-- Prove2me | solution 1 for GlobalTheory.PairOp.unit_FFStar_FF
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:56:51.846491+00:00
-- url     : https://prove2.me/submissions/3ba5a0ab-4673-41ec-b232-a1f67abccc39

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_AdjointOperatorIdentities
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ExistsFFNeZeroThree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PairOperatorStatement
import Theorems.Thm_GlobalTheory_PairOp_FFStar_dia

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
    (dia c * FFStar q χ * (dia c⁻¹ * FF q χ) : Module.End ℂ (Form k n M)) = FFStar q χ * FF q χ := by
  rw [← FFStar_dia q χ c, mul_assoc, ← mul_assoc (dia c), ← map_mul, mul_inv_cancel, map_one, one_mul]
end GlobalTheory.PairOp
