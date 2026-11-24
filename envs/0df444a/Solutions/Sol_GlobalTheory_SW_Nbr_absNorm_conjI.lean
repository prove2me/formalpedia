-- Prove2me | solution 1 for GlobalTheory.SW.Nbr.absNorm_conjI
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:28:24.981858+00:00
-- url     : https://prove2.me/submissions/eaf73c1e-ae1f-4292-a24b-68ecfdd20b92

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_CycOfPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_NeBotOfNorm
import Theorems.Thm_GlobalTheory_SW_Nbr_conjI_eq

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
theorem _root_.solution (P : Ideal (𝓞 E)) : Ideal.absNorm (conjI P) = Ideal.absNorm P := by
  rw [conjI_eq, Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply,
    Submodule.cardQuot_apply]
  exact (Nat.card_congr (Ideal.quotientEquiv P (P.map (co (E := E))) co rfl).toEquiv).symm
end GlobalTheory.SW.Nbr
