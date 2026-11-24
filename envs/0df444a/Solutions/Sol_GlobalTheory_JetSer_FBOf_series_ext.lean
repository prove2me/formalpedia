-- Prove2me | solution 1 for GlobalTheory.JetSer.FBOf.series_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:23:24.757463+00:00
-- url     : https://prove2.me/submissions/d61251c4-69e0-453a-a5eb-7cf6d33f0bb9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsGoodConst
import Theorems.Thm_GlobalTheory_JetSer_FBOf_gm_eq_germ_fnVal
import Theorems.Thm_GlobalTheory_JetSer_FBOf_eq_of_germ
import Theorems.Thm_GlobalTheory_JetSer_FBOf_exists_good_const
import Theorems.Thm_GlobalTheory_JetSer_FBOf_val_const
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_zero__bb72846b09b6
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isCub_cubV
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_of
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_addOf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_comp1


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
theorem _root_.solution (hJet : JetAlgSt) (hRep : RepSt) (Lr : RigLB G) (c : CubicalStr G Lr) {O : Type} [CommRing O]
    [StarRing O] (act : ReciprocityTheory.ChartRestriction.G.Geo.Tor.OAct O G)
    (u : ∀ a : O, LB.Gen (LB.LinComb Lr.L (rosatiφ G (act.act a) (act.act (star a))) rosatiε))
    {d : ℕ} (x : Fam G (Fin d)) (hx : IsUnivChart G d x) (j : Lr.L.ι)
    (F : Fin d → PS R 2 d) (hF : IsLawOf x F) (α : O → Pt R 1 d) (hα : ∀ a, IsMapOf x x (act.act a) (α a))
    (ph : PS R 3 d) (hph : IsSer3 x _ (c.t.s (fun _ => j)).val ph)
    (ad : O → PS R 2 d) (had : ∀ a, IsSer2 x _ ((u a).s (fun _ => j))⁻¹.val (ad a))
    (n : ℕ) (g g' : PS R n d)
    (H : ∀ (T : Over (Spec (CommRingCat.of R))) (z : T.left) (J : (T.left ⟶ G.left) → Lr.L.ι), Good Lr.L z J →
      ∀ (Φ : PS R n d →+* T.left.presheaf.stalk z) (y : Pt R n d → (T ⟶ G)), y 0 = 1 →
      (∀ a b, GP a → GP b → y (addOf F a b) = y a * y b) →
      (∀ o a, GP a → y (comp1 (α o) a) = y a ≫ act.act o) →
      (∀ a b e, GP a → GP b → GP e → Φ (ev ![a, b, e] ph) = (cubV c z J (y a) (y b) (y e)).val) →
      (∀ o a b, GP a → GP b → Φ (ev ![a, b] (ad o)) = (val₂ (u o) z J (y a) (y b))⁻¹.val) → Φ g = Φ g') :
    g = g' := by
  classical
  obtain ⟨j1, -, j3, -⟩ := hJet R (Fin n × Fin d)
  obtain ⟨r1, -, -, r4, -⟩ := hRep R G d x hx (Fin n × Fin d)
  have ex : ∀ a : Pt R n d, ∃ Y : Fam G (Fin n × Fin d), GP a → Rep x a Y ∧ ∀ Y', Rep x a Y' → Y' = Y := fun a => by
    by_cases h : GP a
    · obtain ⟨Y, h1, h2⟩ := r1 a h
      exact ⟨Y, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨fun _ => 1, fun h' => absurd h' h⟩
  choose Y hY using ex
  refine j3 g g' fun m => ?_
  obtain ⟨τ, hτ, -⟩ := j1 m
  refine eq_of_germ fun z => ?_
  obtain ⟨J, hJ, hJ'⟩ := exists_good_const Lr.L Lr.isLB j z
  rw [← hτ, ← hτ]
  refine H (sp (R₀ := R) (JetR R (Fin n × Fin d) m)) z J hJ
    ((((Spec (CommRingCat.of (JetR R (Fin n × Fin d) m))).presheaf.germ ⊤ z trivial).hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of (JetR R (Fin n × Fin d) m))).inv.hom).comp τ.toRingHom)
    (fun a => Y a m) ?_ (fun a b ha hb => ?_) (fun o a ha => ?_) (fun a b e ha hb he => ?_) (fun o a b ha hb => ?_)
  · exact (congrFun ((hY 0 gp_zero₂).2 _ r4) m).symm
  · exact (congrFun ((hY _ (gp_addOf F hF.1 a b ha hb)).2 _ (hF.2 n a b _ _ (hY a ha).1 (hY b hb).1)) m).symm
  · exact (congrFun ((hY _ (gp_comp1 _ a (hα o).1 ha)).2 _ ((hα o).2 n a _ (hY a ha).1)) m).symm
  · obtain ⟨h1, h2⟩ := hph n a b e _ _ _ (hY a ha).1 (hY b hb).1 (hY e he).1 m
    refine Eq.trans ?_ (congrArg Units.val (val_const (L := Lr.L) (φ := thφ G (x3 G)) (ε := thε) hJ' c.t _ h1)).symm
    refine Eq.trans ?_ (gm_eq_germ_fnVal _ _ h1 _ z).symm
    exact congrArg _ (congrArg _ ((hτ _).trans h2.symm))
  · obtain ⟨h1, h2⟩ := had o n a b _ _ (hY a ha).1 (hY b hb).1 m
    refine Eq.trans ?_ (congrArg (fun q => q⁻¹.val) (val_const hJ' (u o) _ h1)).symm
    refine Eq.trans ?_ (congrArg Units.val (map_inv _ _))
    refine Eq.trans ?_ (gm_eq_germ_fnVal _ _ h1 _ z).symm
    exact congrArg _ (congrArg _ ((hτ _).trans h2.symm))
end GlobalTheory.JetSer.FBOf
