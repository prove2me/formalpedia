-- Prove2me | solution 1 for GlobalTheory.NormRos.exists_gen_rosati
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:01:05.745343+00:00
-- url     : https://prove2.me/submissions/e2274110-7f11-4439-aa8a-1ebc0cd8e618

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsGenRosati
import Theorems.Thm_GlobalTheory_NormRos_exists_gen_of_lbIso
import Theorems.Thm_GlobalTheory_NormRos_prod_square
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_prod_sum__19c72914c5cb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_invGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_prod_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_gen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_prod_ros


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
open ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.JetSer
open ReciprocityTheory.ChartRestriction.G.Out (rosatiφ rosatiε zero2)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (LBIso)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.NormRos
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]
namespace GlobalTheory.NormRos
theorem _root_.solution {L : LB G.left} (hL : L.IsLB) (f g : G ⟶ G)
    (H : LBIso (cubeLB G ![fst G G ≫ f, snd G G] L) (cubeLB G ![fst G G, snd G G ≫ g] L)) :
    ∃ t : LB.Gen (LB.LinComb L (rosatiφ G f g) rosatiε), t.IsGen := by
  obtain ⟨t, ht⟩ := exists_gen_of_lbIso H
  obtain ⟨u, hu, -⟩ := exists_gen hL (φ' := rosatiφ G f g) (ε' := rosatiε) (fun V _ k => by
      have p := prod_ros f g (fst G G) (snd G G) k
      rw [lift_fst_snd] at p
      simp only [Over.id_left, Category.id_comp] at p
      rw [p]
      refine (DVR.prod_neg _ _ (DVR.prod_sum₂ (K := ULift.{0} (Finset (Fin 2))) (K' := ULift.{0} (Finset (Fin 2)))
        (U := V) _ (prod_square (fst G G) (snd G G ≫ g) k)
        (DVR.prod_neg _ _ (prod_square (fst G G ≫ f) (snd G G) k)))).trans ?_
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
    (LB.invGen L _ _ t) (DVR.invGen_isGen _ _ _ _ ht)
  exact ⟨u, hu⟩
end GlobalTheory.NormRos
