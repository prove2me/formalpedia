-- Prove2me | solution 1 for GlobalTheory.FrameGeo.series_ext_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:28:18.155187+00:00
-- url     : https://prove2.me/submissions/537c4a2a-5bc8-4dc8-aacc-90cebfdb6c54

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaPt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsGoodConst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsUniqueNormPrim
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_PowerSeriesExpIntegralCanonGaugeAdditiveSecond
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ThreePointSeriesExponentialOfDefect
import Theorems.Thm_GlobalTheory_JetSer_FBOf_eq_of_germ
import Theorems.Thm_GlobalTheory_JetSer_FBOf_exists_good_const
import Theorems.Thm_GlobalTheory_JetSer_FBOf_gm_eq_germ_fnVal
import Theorems.Thm_GlobalTheory_JetSer_FBOf_val_const
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_comp1_pt_right


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.JetSer
open ReciprocityTheory.ChartRestriction.G.Out (rosatiφ rosatiε LPow ThetaGrp IsActOf WeilIs translT GlobalFnsSt)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Good val sval gs)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.FrameGeo
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing GlobalTheory.JetSer.FBOf
variable {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
namespace GlobalTheory.FrameGeo
theorem _root_.solution (hJet : JetAlgSt) (hRep : RepSt) (Lr : RigLB G) (c : CubicalStr G Lr) {O : Type} [CommRing O]
    [StarRing O] (act : ReciprocityTheory.ChartRestriction.G.Geo.Tor.OAct O G)
    (u : ∀ a : O, LB.Gen (LB.LinComb Lr.L (rosatiφ G (act.act a) (act.act (star a))) rosatiε))
    {d : ℕ} (x : Fam G (Fin d)) (hx : IsUnivChart G d x) (j : Lr.L.ι) (B : FB R d O) (hB : IsFBOf Lr c act u x j B)
    (g g' : PS R 1 d)
    (H : ∀ (T : Over (Spec (CommRingCat.of R))) (z : T.left) (J : (T.left ⟶ G.left) → Lr.L.ι), Good Lr.L z J →
      ∀ (Φ : PS R 1 d →+* T.left.presheaf.stalk z) (y : T ⟶ G),
      (∀ r : R, Φ (C r) = gs T.hom z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) →
      (∀ (K : Type) [Fintype K] (φ : K → (G.left ⟶ G.left)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb Lr.L φ ε))
        (s : PS R 1 d), IsSer1 x _ (t.s (fun _ => j)).val s → ∀ a,
          Φ (ev ![B.A.act a] s) = (val t (y ≫ act.act a).left z J).val) →
      (∀ a b e, Φ (ev ![B.A.act a, B.A.act b, B.A.act e] B.ph2) =
        (cubV c z J (y ≫ act.act a) (y ≫ act.act b) (y ≫ act.act e)).val) →
      (∀ o a b, Φ (ev ![B.A.act a, B.A.act b] (B.ad o)) =
        (val₂ (u o) z J (y ≫ act.act a) (y ≫ act.act b))⁻¹.val) → Φ g = Φ g') :
    g = g' := by
  classical
  obtain ⟨j1, -, j3, -⟩ := hJet R (Fin 1 × Fin d)
  obtain ⟨r1, -⟩ := hRep R G d x hx (Fin 1 × Fin d)
  obtain ⟨Y, hY, -⟩ := r1 (pt R (n := 1) d 0) (gp_pt 0)
  have hA : ∀ a, Rep x (B.A.act a) (fun m => Y m ≫ act.act a) := fun a => by
    have := (hB.map a).2 1 _ _ hY
    rwa [gt_comp1_pt_right] at this
  refine j3 g g' fun m => ?_
  obtain ⟨τ, hτ, -⟩ := j1 m
  refine eq_of_germ fun z => ?_
  obtain ⟨J, hJ, hJ'⟩ := exists_good_const Lr.L Lr.isLB j z
  rw [← hτ, ← hτ]
  refine H (sp (R₀ := R) (JetR R (Fin 1 × Fin d) m)) z J hJ
    ((((Spec (CommRingCat.of (JetR R (Fin 1 × Fin d) m))).presheaf.germ ⊤ z trivial).hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of (JetR R (Fin 1 × Fin d) m))).inv.hom).comp τ.toRingHom)
    (Y m) (fun r => ?_) (fun K _ φ ε t s hs a => ?_) (fun a b e => ?_) (fun o a b => ?_)
  · rw [gs_eq _ z ⊤ trivial]
    have e₁ : τ (C r) = algebraMap R _ r := τ.commutes r
    have e₂ := congrArg (fun q => q.hom r) (Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom (algebraMap R (JetR R (Fin 1 × Fin d) m))))
    exact congrArg _ ((congrArg _ e₁).trans e₂)
  · obtain ⟨h1, h2⟩ := hs 1 _ _ (hA a) m
    refine Eq.trans ?_ (congrArg Units.val (val_const hJ' t _ h1)).symm
    refine Eq.trans ?_ (gm_eq_germ_fnVal _ _ h1 _ z).symm
    exact congrArg _ (congrArg _ ((hτ _).trans h2.symm))
  · obtain ⟨h1, h2⟩ := hB.ph1 1 _ _ _ _ _ _ (hA a) (hA b) (hA e) m
    rw [hB.ph2]
    refine Eq.trans ?_ (congrArg Units.val (val_const (L := Lr.L) (φ := thφ G (x3 G)) (ε := thε) hJ' c.t _ h1)).symm
    refine Eq.trans ?_ (gm_eq_germ_fnVal _ _ h1 _ z).symm
    exact congrArg _ (congrArg _ ((hτ _).trans h2.symm))
  · obtain ⟨h1, h2⟩ := hB.ad o 1 _ _ _ _ (hA a) (hA b) m
    refine Eq.trans ?_ (congrArg (fun q => q⁻¹.val) (val_const hJ' (u o) _ h1)).symm
    refine Eq.trans ?_ (congrArg Units.val (map_inv _ _))
    refine Eq.trans ?_ (gm_eq_germ_fnVal _ _ h1 _ z).symm
    exact congrArg _ (congrArg _ ((hτ _).trans h2.symm))
end GlobalTheory.FrameGeo
