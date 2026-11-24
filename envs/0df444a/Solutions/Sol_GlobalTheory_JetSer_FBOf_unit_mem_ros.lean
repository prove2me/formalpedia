-- Prove2me | solution 1 for GlobalTheory.JetSer.FBOf.unit_mem_ros
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:23:26.959928+00:00
-- url     : https://prove2.me/submissions/d59c7234-b31f-4cbf-ba73-46a0e24f3a65

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsGoodConst
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isCub_cubV
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (gm gm_val val val_of Good cubV val₂ IsCub isCub_cubV exists_chart psum_hom preHom)
open ReciprocityTheory.ChartRestriction.G.Out (rosatiφ rosatiε zero2)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.JetSer GlobalTheory.JetSer.FBOf
variable {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
namespace GlobalTheory.JetSer.FBOf
theorem _root_.solution (L : LB G.left) (j : L.ι) (hj : ⊤ ≤ η[G].left ⁻¹ᵁ L.U j) (f g : G ⟶ G) [IsMonHom f] [IsMonHom g] :
    ⊤ ≤ (lift η[G] η[G]).left ⁻¹ᵁ LB.wchart L (rosatiφ G f g) (fun _ => j) := by
  intro s _
  refine Set.mem_iInter.2 fun a => ?_
  have one : zero2 G ≫ rosatiφ G f g a = η[G].left := by
    have e : ∀ q : G ⊗ G ⟶ G, lift η[G] η[G] ≫ q = η[G] → zero2 G ≫ q.left = η[G].left := fun q hq =>
      congrArg (fun m => m.left) hq
    have o : lift η[G] η[G] ≫ μ[G] = η[G] := by simpa [Hom.one_def, Hom.mul_def] using
      (_root_.mul_one (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G))
    fin_cases a <;> refine e _ ?_ <;> simp [padd, comp_lift_assoc, o]
  exact (congrArg (fun q => q s ∈ L.U j) one).mpr (hj (trivial : s ∈ ⊤))
end GlobalTheory.JetSer.FBOf
