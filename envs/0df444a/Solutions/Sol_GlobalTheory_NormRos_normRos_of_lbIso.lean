-- Prove2me | solution 1 for GlobalTheory.NormRos.normRos_of_lbIso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:42:44.758863+00:00
-- url     : https://prove2.me/submissions/e7c9b106-7a5e-415b-bd63-04e74c25be07

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsGenRosati
import Theorems.Thm_GlobalTheory_NormRos_exists_gen_rosati
import Theorems.Thm_GlobalTheory_NormRos_exists_isNormRos
import Theorems.Thm_GlobalTheory_NormRos_isNormRos_unique

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
theorem _root_.solution : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left), L.IsLB →
    ∀ (f g : G ⟶ G) [IsMonHom f] [IsMonHom g],
    LBIso (cubeLB G ![fst G G ≫ f, snd G G] L) (cubeLB G ![fst G G, snd G G ≫ g] L) →
    (∃ u, IsNormRos L f g u) ∧ (Function.Surjective (G ⊗ G).hom.appTop.hom →
      ∀ u u', IsNormRos L f g u → IsNormRos L f g u' → u.s = u'.s) := by
  intro S G _ _ L hL f g _ _ H
  obtain ⟨t, ht⟩ := exists_gen_rosati hL f g H
  exact ⟨exists_isNormRos hL f g t ht, fun hs u u' h h' => isNormRos_unique hL f g hs h h'⟩
end GlobalTheory.NormRos
