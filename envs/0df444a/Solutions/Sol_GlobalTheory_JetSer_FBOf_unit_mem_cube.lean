-- Prove2me | solution 1 for GlobalTheory.JetSer.FBOf.unit_mem_cube
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:23:25.962804+00:00
-- url     : https://prove2.me/submissions/817a88c5-c3c4-4b17-ac8c-6faa0a40253a

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
theorem _root_.solution (L : LB G.left) (j : L.ι) (hj : ⊤ ≤ η[G].left ⁻¹ᵁ L.U j) :
    ⊤ ≤ (lift η[G] (lift η[G] η[G])).left ⁻¹ᵁ LB.wchart L (thφ G (x3 G)) (fun _ => j) := by
  intro s _
  refine Set.mem_iInter.2 fun I => ?_
  have h1 : (η[G] : 𝟙_ _ ⟶ G) = 1 := by simp [Hom.one_def]
  have e : lift η[G] (lift η[G] η[G]) ≫ psum G (x3 G) I.down = η[G] := by
    refine (psum_hom (preHom (lift η[G] (lift η[G] η[G]))) (x3 G) I.down).trans ?_
    have : (fun i => preHom (lift η[G] (lift η[G] η[G])) (x3 G i)) = fun _ => 1 :=
      funext fun i => by fin_cases i <;> simp [preHom, x3, Hom.one_def]
    refine (congrArg (fun q => psum G q I.down) this).trans ?_
    rw [h1]
    unfold psum
    induction ((List.finRange 3).filter (· ∈ I.down)) with
    | nil => rfl
    | cons k l ih => rw [List.foldr_cons, ih]; exact _root_.mul_one (1 : 𝟙_ _ ⟶ G)
  exact (congrArg (fun q => q.left s ∈ L.U j) e).mpr (hj (trivial : s ∈ ⊤))
end GlobalTheory.JetSer.FBOf
