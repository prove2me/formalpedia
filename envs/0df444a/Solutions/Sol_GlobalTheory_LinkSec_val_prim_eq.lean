-- Prove2me | solution 1 for GlobalTheory.LinkSec.val_prim_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:31:48.871848+00:00
-- url     : https://prove2.me/submissions/3c2453bf-25ba-433e-b6a9-2b9138619b63

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_JetsOnCopiesCompatibleFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_CartesianLiftThreeCompProjection
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdJet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_IsLawOfOfMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ValSerGermFnVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsUniqueNormPrim
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_GsSpMapGermAt
import Theorems.Thm_GlobalTheory_JetSer_prod_lam
import Theorems.Thm_GlobalTheory_JetSer_prod_prim
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_prod_sum__19c72914c5cb
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gen_unique__84c95b4ccdb0
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_prod_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_corr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LinkSec
variable {V : Type} [CommRing V]
namespace GlobalTheory.LinkSec
theorem _root_.solution {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S : Scheme.{0}} (t : SAB H S)
    (hp : Function.Surjective t.G.hom.appTop.hom) (wP : PrimTyG t) (hw : IsPrimG t wP)
    (ρ : LB.Gen (LB.LinComb t.PP.L (JetSer.primφ (t.act.act H.w0)) JetSer.primε)) (hρ : ρ.IsGen)
    (hc : LB.Gen.Corr t.PP.L _ _ _ _ (LB.pullGen t.PP.L _ _ ρ (eSec t.G)) t.PP.rig)
    {Z : Scheme.{0}} (r : Z ⟶ t.G.left) (z : Z) (J) (hJ : Good t.PP.L z J) : val wP r z J = val ρ r z J := by
  have he : eSec t.G ≫ t.G.hom = 𝟙 S := Over.w η[t.G]
  refine gen_unique' t.PP.isLB (fun U _ k => ?_) t.G.hom (eSec t.G) he hp hw.1 hρ (fun y J hJ => ?_) Z r z J hJ
  · have P := JetSer.prod_prim (t.act.act H.w0) (𝟙 t.G) k
    simp only [Over.id_left, Category.id_comp] at P
    refine P.trans (Eq.symm ((DVR.prod_sum₂ (K := Fin 1) (U := U) _ (c := k (𝟙 _))
      (by rw [Fintype.prod_unique]; exact zpow_one _)
      (DVR.prod_neg _ _ (JetSer.prod_lam (𝟙 t.G) (t.act.act H.w0) k))).trans ?_))
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, Over.id_left]
    abel
  · have a := val_corr hJ hw.2 (𝟙 _)
    have b := val_corr hJ hc (𝟙 _)
    rw [val_pull hJ, Category.id_comp] at a b
    exact a.trans b.symm
end GlobalTheory.LinkSec
