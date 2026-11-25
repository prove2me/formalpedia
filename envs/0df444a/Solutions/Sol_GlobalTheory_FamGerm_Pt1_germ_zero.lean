-- Prove2me | solution 1 for GlobalTheory.FamGerm.Pt1.germ_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:01:18.463567+00:00
-- url     : https://prove2.me/submissions/62350503-f3a2-4dc8-8d54-1c0ca8724e95

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExistsWeightBasisFiltration
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_OneCHyp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExpF
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_ThmASt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_ColValMonomial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS FB ev Dof)
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.FamGerm
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {F : Type} [Field F] [Algebra (FractionRing V) F] (y : Pt1 E H V F)
namespace GlobalTheory.FamGerm
namespace Pt1
theorem _root_.solution (q : ℕ) {r : PS V 1 y.d} (hr : JetSer.IsSer1 y.x _ (y.ρ.s (fun _ => y.j)).val r) :
    y.Germ q 0 0 := by
  refine ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, Fin.elim0, r, fun i => i.elim0, fun α j₁ j₂ _ => ?_, hr,
    fun i => i.elim0, by simp⟩
  rw [Finset.univ_eq_empty, Finset.sum_empty]
  exact map_zero _
end Pt1
end GlobalTheory.FamGerm
