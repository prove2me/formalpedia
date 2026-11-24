-- Prove2me | solution 1 for GlobalTheory.EtaCard.card_quot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:41:06.101946+00:00
-- url     : https://prove2.me/submissions/b5c7aae7-4b8a-4f49-ab69-dadea669ddb1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_IsNullVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_TwoMulPowFourDvdCardGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CardLevGrpAndSpan

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.EtaForm
attribute [local instance] Over.cartesianMonoidalCategory
open scoped TensorProduct
open GlobalTheory GlobalTheory.EtaCard
variable (E : Type) [Field E] [NumberField E]
namespace GlobalTheory.EtaCard
theorem _root_.solution (k : ℕ) : Nat.card (𝓞 E ⧸ Ideal.span {(k : 𝓞 E)}) = k ^ Module.finrank ℚ E := by
  rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, Ideal.absNorm_span_natCast, RingOfIntegers.rank]
end GlobalTheory.EtaCard
