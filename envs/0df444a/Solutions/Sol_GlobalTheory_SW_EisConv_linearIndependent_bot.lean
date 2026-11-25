-- Prove2me | solution 1 for GlobalTheory.SW.EisConv.linearIndependent_bot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:29:32.251995+00:00
-- url     : https://prove2.me/submissions/70ca5505-a265-4f34-b533-2bed88598b0a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_PosSemidefSubMulConjTranspose
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsLinearIndependentOfRatIndependent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SummableEisMajorant
import Theorems.Thm_GlobalTheory_SW_HAct_group_part


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.EisConv
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}
namespace GlobalTheory.SW.EisConv
theorem _root_.solution {γ : M2 E N} (h : γ ∈ UU E N) :
    LinearIndependent E fun i => γ.submatrix Sum.inr id i := by
  have h1 : LinearIndependent E γ.row := linearIndependent_rows_iff_isUnit.2
    ((Matrix.isUnit_iff_isUnit_det _).2 (HAct.group_part h).1)
  exact h1.comp Sum.inr Sum.inr_injective
end GlobalTheory.SW.EisConv
