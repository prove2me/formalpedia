-- Prove2me | solution 1 for GlobalTheory.DatumInverseCharacter.dvd_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:28:58.404743+00:00
-- url     : https://prove2.me/submissions/7591e183-1cdf-4802-a4ce-5d1b9e934ae6

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsLevMove
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndBC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsQuotEquiv
import Theorems.Thm_GlobalTheory_DatumInverseCharacter_bar_mem
import Theorems.Thm_GlobalTheory_DatumInverseCharacter_dvd_EF_smul

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
theorem _root_.solution (D : Datum H) {N : ℕ} {I : Ideal (𝓞 E)}
    (hI : I * I.map (H.bar : 𝓞 E →+* 𝓞 E) = Ideal.span {(N : 𝓞 E)}) {c : 𝓞 E}
    (hc : c ∈ I.map (H.bar : 𝓞 E →+* 𝓞 E)) (v : D.La) {w : D.La}
    (hw : w ∈ (I.map (H.bar : 𝓞 E →+* 𝓞 E) • ⊤ : Submodule (𝓞 E) D.La)) : (N : ℤ) ∣ D.EF w (c • v) := by
  refine Submodule.smul_induction_on (p := fun w => (N : ℤ) ∣ D.EF w (c • v)) hw ?_ ?_
  · intro a ha x _
    rw [D.adj, smul_smul]
    apply dvd_EF_smul D
    rw [← hI]
    exact Ideal.mul_mem_mul (bar_mem ha) hc
  · intro x y hx hy
    rw [map_add, LinearMap.add_apply]
    exact dvd_add hx hy
end GlobalTheory.DatumInverseCharacter
