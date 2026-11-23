-- Prove2me | solution 1 for GlobalTheory.DatumInverseCharacter.dvd_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:51:26.983602+00:00
-- url     : https://prove2.me/submissions/e67f80e6-bb33-4dd1-bf9a-a2d88a6272cc

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsLevMove
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndBC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsQuotEquiv
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
    (hc : c ∈ I.map (H.bar : 𝓞 E →+* 𝓞 E)) (u : D.La) {w : D.La}
    (hw : w ∈ (I • ⊤ : Submodule (𝓞 E) D.La)) : (N : ℤ) ∣ D.EF u (c • w) := by
  refine Submodule.smul_induction_on (p := fun w => (N : ℤ) ∣ D.EF u (c • w)) hw ?_ ?_
  · intro a ha x _
    rw [smul_smul]
    apply dvd_EF_smul D
    rw [← hI, _root_.mul_comm c a]
    exact Ideal.mul_mem_mul ha hc
  · intro x y hx hy
    rw [smul_add, map_add]
    exact dvd_add hx hy
end GlobalTheory.DatumInverseCharacter
