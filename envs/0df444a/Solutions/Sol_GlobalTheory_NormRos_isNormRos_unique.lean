-- Prove2me | solution 1 for GlobalTheory.NormRos.isNormRos_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:23:44.476102+00:00
-- url     : https://prove2.me/submissions/7ffcf426-d57a-486a-aa9c-8ee27bcec1ae

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsGenRosati
import Theorems.Thm_GlobalTheory_NormRos_gen_s_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gen_unique
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_corr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull


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
omit [IsCommMonObj G]
namespace GlobalTheory.NormRos
theorem _root_.solution {L : LB G.left} (hL : L.IsLB) (f g : G ⟶ G)
    (hs : Function.Surjective (G ⊗ G).hom.appTop.hom) {u u' : LB.Gen (LB.LinComb L (rosatiφ G f g) rosatiε)}
    (h : IsNormRos L f g u) (h' : IsNormRos L f g u') : u.s = u'.s := by
  have z2 : zero2 G ≫ (G ⊗ G).hom = 𝟙 S := Over.w (lift η[G] η[G])
  refine gen_s_ext hL h.1 h'.1 fun y J hJ =>
    gen_unique hL (S₀ := S) (G ⊗ G).hom (zero2 G) z2 hs h.1 h'.1 (fun s I hI => ?_) _ _ y J hJ
  have a := val_corr hI h.2 (𝟙 _)
  have b := val_corr hI h'.2 (𝟙 _)
  rw [val_pull hI, Category.id_comp, val_one] at a b
  exact a.trans b.symm
end GlobalTheory.NormRos
