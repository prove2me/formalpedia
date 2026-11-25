-- Prove2me | solution 1 for GlobalTheory.PowGerm.exists_frames_eL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:14:11.708739+00:00
-- url     : https://prove2.me/submissions/b68c7a24-4b3d-48b5-9b39-247b48764d02

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_JetsOnCopiesCompatibleFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermDPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsFramesEL
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermD_formEq_eL
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermD_val_eL_trunc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_mulGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_gen


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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
open GlobalTheory GlobalTheory.PowGerm
namespace GlobalTheory.PowGerm
theorem _root_.solution {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {V : Type} [CommRing V]
    (t : SAB H (Sp V)) (L' : LB t.G.left) (h : t.PP.L = L')
    (d : ℕ) (FT : Fin d → PS V 2 d) (act : 𝓞 E → Fin d → PS V 1 d) (ph1 ph2 : PS V 3 d) (sy : PS V 2 d) (ad : 𝓞 E → PS V 2 d)
    (tg : Fin d → (Sp (DualNumber V) ⟶ t.G.left)) (uv : Fin d → Fin d → V) (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G)
    (e : ∀ m, FrTyG t (𝟙 (Sp V)) d x m) (wP : PrimTyG t)
    (hch : IsChartG t (𝟙 (Sp V)) d FT act tg uv x) (hfr : IsFrameG t (𝟙 (Sp V)) d x FT act ph1 ph2 sy ad e)
    (hpr : IsPrimG t wP) :
    ∃ τ : Frames L' (κ := Fin 1 × Fin d) x, τ.Gen ∧
      (∀ (m : ℕ) (y : Sp (Jet V (Fin 1 × Fin d) m)) (J : (Sp (Jet V (Fin 1 × Fin d) m) ⟶ t.G.left) → L'.ι), Good L' y J →
        val (τ m) (𝟙 _) y J = val (genCast h _ _ (eLG t (𝟙 (Sp V)) d x act e wP m)) (𝟙 _) y J) ∧
      (FrTrunc t (𝟙 (Sp V)) d x e → τ.Trunc) := by
  subst h
  have hL := t.PP.isLB
  have heL : ∀ m, (eLG t (𝟙 (Sp V)) d x act e wP m).IsGen := fun m =>
    ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen t.PP.L _ _ _ _ _ _ (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen t.PP.L _ _ _ hpr.1 _)
      (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen t.PP.L _ _ _ (hfr.gen m) _)
  have hτ : ∀ m, ∃ τ : LB.Gen (LB.LinComb t.PP.L (Y := (jOG (𝟙 (Sp V)) d m 1).left) (K := Fin 1) (fun _ => (x m).left)
      fun _ => (1 : ℤ)), τ.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (jOG (𝟙 (Sp V)) d m 1).left) (z : Z)
        (J : (Z ⟶ t.G.left) → t.PP.L.ι), Good t.PP.L z J →
          val τ r z J = val (eLG t (𝟙 (Sp V)) d x act e wP m) r z J := by
    intro m
    refine exists_gen hL ?_ _ (heL m)
    intro U _ hU
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_one, Category.comp_id,
      GermD.formEq_eL hch m]
    rw [_root_.mul_assoc, ← Finset.prod_mul_distrib]
    simp only [← zpow_add, neg_add_cancel, zpow_zero, Finset.prod_const_one, _root_.mul_one]
  choose τ hτg hτv using hτ
  refine ⟨τ, hτg, fun m y J hJ => hτv m _ (𝟙 _) y J hJ, fun htr m y J hJ => ?_⟩
  exact (hτv (m + 1) _ (GermD.ρT (𝟙 (Sp V)) d m).left y J hJ).trans
    ((GermD.val_eL_trunc hch e wP htr m y J hJ).trans (hτv m _ (𝟙 _) y J hJ).symm)
end GlobalTheory.PowGerm
