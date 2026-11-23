-- Prove2me | solution 1 for GlobalTheory.SW.Nbr.int_move
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:01:38.846694+00:00
-- url     : https://prove2.me/submissions/74c251ad-f8f5-4a8e-bbb3-9f7699282c73

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_CycOfPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_NeBotOfNorm
import Theorems.Thm_GlobalTheory_SW_Nbr_coe_co
import Theorems.Thm_GlobalTheory_SW_Nbr_cc_cc
import Theorems.Thm_GlobalTheory_SW_Nbr_herm_sr

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
open scoped ComplexConjugate ComplexOrder Real Classical nonZeroDivisors
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Nbr
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
namespace GlobalTheory.SW.Nbr
theorem _root_.solution (c : 𝓞 E) (x y : Fin n → E) : Int' (c • x) y ↔ Int' x (co c • y) := by
  unfold Int'
  rw [osmul, osmul, herm_sl, herm_sr, coe_co, cc_cc]
end GlobalTheory.SW.Nbr
