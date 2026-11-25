-- Prove2me | solution 1 for GlobalTheory.JetSer.exists_intChart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:58:44.401838+00:00
-- url     : https://prove2.me/submissions/dd28a24f-1743-4880-b586-6ff3a4e9e7f0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsIndexOfLocal
import Theorems.Thm_GlobalTheory_JetSer_exists_index_of_local
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_univChartLoc


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.JetSer
open ReciprocityTheory.ChartRestriction.G.Out (rosatiφ rosatiε zero2)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (LBIso)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.JetSer
namespace GlobalTheory.JetSer
theorem _root_.solution : (∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left), L.IsLB → ∀ (f g : G ⟶ G) [IsMonHom f] [IsMonHom g], LBIso (cubeLB G ![fst G G ≫ f, snd G G] L) (cubeLB G ![fst G G, snd G G ≫ g] L) → (∃ u, IsNormRos L f g u) ∧ (Function.Surjective (G ⊗ G).hom.appTop.hom → ∀ u u', IsNormRos L f g u → IsNormRos L f g u' → u.s = u'.s)) → FBOfSt → ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [Smooth G.hom], Function.Surjective (G ⊗ G).hom.appTop.hom → Function.Surjective (G ⊗ G ⊗ G).hom.appTop.hom → ∀ (Lr : RigLB G) (c : CubicalStr G Lr) (O : Type) [CommRing O] [StarRing O] (act : ReciprocityTheory.ChartRestriction.G.Geo.Tor.OAct O G), (∀ a, LBIso (cubeLB G ![fst G G ≫ act.act a, snd G G] Lr.L) (cubeLB G ![fst G G, snd G G ≫ act.act (star a)] Lr.L)) → ∃ (d : ℕ) (x : Fam G (Fin d)) (j : Lr.L.ι) (u : ∀ a : O, LB.Gen (LB.LinComb Lr.L (rosatiφ G (act.act a) (act.act (star a))) rosatiε)) (B : FB R d O), IsUnivChart G d x ∧ ⊤ ≤ η[G].left ⁻¹ᵁ Lr.L.U j ∧ (∀ a, IsNormRos Lr.L _ _ (u a)) ∧ IsFBOf Lr c act u x j B := by
  intro hRos hFB R _ _ G _ _ _ h2 h3 Lr c O _ _ act hiso
  obtain ⟨d, x, hx⟩ := univChartLoc G
  obtain ⟨j, hj⟩ := exists_index_of_local Lr.L Lr.isLB η[G].left
  have hu : ∀ a : O, ∃ u, IsNormRos Lr.L (act.act a) (act.act (star a)) u := fun a => by
    have := act.hom a
    have := act.hom (star a)
    exact (hRos _ G Lr.L Lr.isLB _ _ (hiso a)).1
  choose u hu using hu
  obtain ⟨B, hB⟩ := hFB R G h2 h3 Lr c O act u hu d x hx j hj
  exact ⟨d, x, j, u, B, hx, hj, hu, hB⟩
end GlobalTheory.JetSer
