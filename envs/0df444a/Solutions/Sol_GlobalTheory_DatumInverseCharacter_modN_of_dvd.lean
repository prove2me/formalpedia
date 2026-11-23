-- Prove2me | solution 1 for GlobalTheory.DatumInverseCharacter.modN_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:44:08.185056+00:00
-- url     : https://prove2.me/submissions/ba88031e-5b0a-4c9b-a69c-1b45853e4548

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsLevMove
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndBC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsQuotEquiv

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
theorem _root_.solution (D : Datum H) {n : ℕ} (hn : 0 < n) {w : D.La} (h : ∀ v, (n : ℤ) ∣ D.EF w v) :
    D.ModN n w := by
  obtain ⟨b, hb⟩ := D.unimod.2
    ({ toFun := fun v => D.EF w v / n
       map_add' := fun x y => by
         simp only [map_add]
         exact Int.add_ediv_of_dvd_left (h x)
       map_smul' := fun m x => by
         simp only [map_zsmul, smul_eq_mul, RingHom.id_apply]
         exact Int.mul_ediv_assoc m (h x) } : D.La →ₗ[ℤ] ℤ)
  refine ⟨b, D.unimod.1 ?_⟩
  ext v
  rw [map_nsmul, LinearMap.smul_apply, hb]
  simp only [LinearMap.coe_mk, AddHom.coe_mk, nsmul_eq_mul]
  exact (Int.mul_ediv_cancel' (h v)).symm
end GlobalTheory.DatumInverseCharacter
