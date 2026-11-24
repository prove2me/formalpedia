-- Prove2me | solution 1 for GlobalTheory.SW.star_dotProduct_self_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:31:21.540549+00:00
-- url     : https://prove2.me/submissions/51786452-a041-48c6-b80d-1b8cd14d473e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_NormDetDenomLeRankOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_PosSemidefSubMulConjTranspose

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
open GlobalTheory GlobalTheory.SW
variable {N : ℕ}
namespace GlobalTheory.SW
theorem _root_.solution (x : Fin N → ℂ) :
    star x ⬝ᵥ x = ((∑ a, ‖x a‖ ^ 2 : ℝ) : ℂ) := by
  simp [dotProduct, Complex.conj_mul']
end GlobalTheory.SW
