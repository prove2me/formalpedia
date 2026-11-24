-- Prove2me | solution 1 for GlobalTheory.DatumInverseCharacter.bar_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:12:40.197437+00:00
-- url     : https://prove2.me/submissions/4f609ad3-1c4b-42f6-9388-cec0dabf6bdc

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsLevMove
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndBC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsQuotEquiv
import Theorems.Thm_GlobalTheory_DatumInverseCharacter_bar_bar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.DatumInverseCharacter
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
namespace GlobalTheory.DatumInverseCharacter
theorem _root_.solution {I : Ideal (𝓞 E)} {j : 𝓞 E} (hj : j ∈ I.map (H.bar : 𝓞 E →+* 𝓞 E)) : H.bar j ∈ I := by
  have hc : (H.bar : 𝓞 E →+* 𝓞 E).comp (H.bar : 𝓞 E →+* 𝓞 E) = RingHom.id _ :=
    RingHom.ext fun a => bar_bar H a
  have h2 := Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) hj
  rw [Ideal.map_map, hc, Ideal.map_id] at h2
  exact h2
end GlobalTheory.DatumInverseCharacter
