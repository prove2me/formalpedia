-- Prove2me | solution 1 for GlobalTheory.ChartCmp.PushAd.exists_carried
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:39:27.400019+00:00
-- url     : https://prove2.me/submissions/c8915a57-a090-4b1c-91f1-b0722a5895e5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsGroupIsoCubicalIsoOfTripleMapId
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThetaSwapFirstTwo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_AdjointnessSeriesTransportFrames
import Theorems.Thm_GlobalTheory_ChartCmp_PushAd_carried_trans
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermFun_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_HasGen_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_glue_unit
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_trF_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_unit_ext


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
open GlobalTheory GlobalTheory.ChartCmp GlobalTheory.ChartCmp.PushAd
variable {X X' Y : Scheme.{0}} {L' : LB X'} {L : LB X} {F : X' ⟶ X} (w : LB.Iso L' (L.pull F))
  {K : Type} [Fintype K] {φ : K → (Y ⟶ X')} {ε : K → ℤ}
namespace GlobalTheory.ChartCmp.PushAd
theorem _root_.solution (hL' : L'.IsLB) (hL : L.IsLB) (hw : w.IsGen) {g : LB.Gen (LB.LinComb L' φ ε)} (hg : g.IsGen) :
    ∃ g' : LB.Gen (LB.LinComb L (fun k => φ k ≫ F) ε), g'.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) (J' : (Z ⟶ X') → L'.ι), Good L z J → Good L' z J' →
        val g' r z J = (∏ k, wv w z J J' (r ≫ φ k) ^ ε k) * val g r z J' := by
  have glue : ∀ p : K → L.ι, ∃ a : Γ(Y, LB.wchart L (fun k => φ k ≫ F) p)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z)
      (q : K → L'.ι), r z ∈ LB.wchart L (fun k => φ k ≫ F) p → r z ∈ LB.wchart L' φ q →
      gm r z _ a = (∏ k, gw w (r ≫ φ k) z (p k) (q k) ^ ε k) * gm r z (LB.wchart L' φ q) (g.s q) := by
    intro p
    let W : (K → L'.ι) → Y.Opens := fun q => LB.wchart L (fun k => φ k ≫ F) p ⊓ LB.wchart L' φ q
    have le : ∀ q k, W q ≤ φ k ⁻¹ᵁ ((L.pull F).U (fun _ => p k) ⊓ L'.U (q k)) := fun q k y hy =>
      ⟨mem_pull.2 (Set.mem_iInter.1 hy.1 k), Set.mem_iInter.1 hy.2 k⟩
    obtain ⟨u, hu⟩ : ∃ u : ∀ q, Γ(Y, W q)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) q, r z ∈ W q →
        gm r z (W q) (u q) = (∏ k, gw w (r ≫ φ k) z (p k) (q k) ^ ε k) * gm r z (LB.wchart L' φ q) (g.s q) :=
      ⟨fun q => (∏ k, res (le q k) (pullU (φ k) _ (w.s (fun _ => p k, q k))) ^ ε k) *
          res (inf_le_right : W q ≤ LB.wchart L' φ q) (g.s q), fun Z r z q hz =>
        (map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_prod _ _ _).trans (Finset.prod_congr rfl fun k _ =>
          (map_zpow _ _ _).trans (congrArg (· ^ ε k) ((gm_res r z _ hz _).trans
            (gm_pull r (φ k) z ((L.pull F).U (fun _ => p k) ⊓ L'.U (q k)) (le q k hz) _))))) (gm_res r z _ hz _))⟩
    obtain ⟨a, ha⟩ := glue_unit (LB.wchart L (fun k => φ k ≫ F) p) W (fun q => inf_le_left) (fun y hy => by
        choose q hq using fun k => exists_chart hL' (φ k y)
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨q, hy, Set.mem_iInter.2 hq⟩) u (fun q q' y hy => by
        rw [hu _ _ y q hy.1, hu _ _ y q' hy.2, carried_trans w hw hg (𝟙 Y) y p p q q' hy.1.1 hy.1.1 hy.1.2 hy.2.2,
          mul_eq_left.1 (trF_trans hL _ ε (𝟙 Y) y hy.1.1 hy.1.1 hy.1.1), _root_.one_mul])
    refine ⟨a, fun Z r z q h₁ h₂ => ?_⟩
    have hz : r z ∈ W q := ⟨h₁, h₂⟩
    exact (gm_res r z inf_le_left hz a).symm.trans ((congrArg (gm r z (W q)) (ha q)).trans (hu Z r z q hz))
  choose a ha using glue
  refine ⟨⟨a⟩, fun p p' => unit_ext fun y hy => ?_, fun Z r z J J' hJ hJ' => ?_⟩
  · choose q hq using fun k => exists_chart hL' (φ k y)
    have m : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L' φ q := Set.mem_iInter.2 hq
    refine (gm_res (𝟙 Y) y _ hy _).trans (Eq.trans ?_ ((map_mul _ _ _).trans (congrArg₂ (· * ·)
      (gm_linComb L _ ε (𝟙 Y) y p p' hy.1 hy.2) ((gm_res (𝟙 Y) y _ hy _).trans (ha p' _ (𝟙 Y) y q hy.2 m)))).symm)
    exact (ha p _ (𝟙 Y) y q hy.1 m).trans (carried_trans w hw hg (𝟙 Y) y p p' q q hy.1 hy.2 m m)
  · refine (ha _ Z r z _ (hJ.mem _ r) (hJ'.mem φ r)).trans ?_
    simp only [wv, Category.assoc]
    rfl
end GlobalTheory.ChartCmp.PushAd
