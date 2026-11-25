-- Prove2me | solution 1 for GlobalTheory.SW.EisConv.embAll_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:29:31.466458+00:00
-- url     : https://prove2.me/submissions/f1fd9984-e180-48cb-b008-50fc2116fb9f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_PosSemidefSubMulConjTranspose
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsLinearIndependentOfRatIndependent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SummableEisMajorant

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
namespace GlobalTheory.SW.EisConv
theorem _root_.solution {E m : Type} [Field E] [NumberField E] (w : m → 𝓞 E) (j : m)
    (σ : E →+* ℂ) : embAll E m w j σ = σ (w j : E) := rfl
end GlobalTheory.SW.EisConv
