-- Prove2me | solution 1 for GlobalTheory.FrameGeo.exists_gen_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:13:09.662723+00:00
-- url     : https://prove2.me/submissions/851747eb-54a6-440a-9ca6-af658d65646b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaPt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsGoodConst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsUniqueNormPrim
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_PowerSeriesExpIntegralCanonGaugeAdditiveSecond
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ThreePointSeriesExponentialOfDefect
import Theorems.Thm_GlobalTheory_FrameGeo_powGen_isGen
import Theorems.Thm_GlobalTheory_FrameGeo_val_powGen
import Theorems.Thm_GlobalTheory_FrameGeo_prod_nmul
import Theorems.Thm_GlobalTheory_FrameGeo_act_natCast_mul
import Theorems.Thm_GlobalTheory_JetSer_prod_prim
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_prod_sum__19c72914c5cb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_invGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_mulGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_powGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_prod_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_cubN
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_gen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isCub_cubV
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_prod_ros
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_inv
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
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.JetSer
open ReciprocityTheory.ChartRestriction.G.Out (rosatiφ rosatiε LPow ThetaGrp IsActOf WeilIs translT GlobalFnsSt)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Good val sval gs)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.FrameGeo
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]
namespace GlobalTheory.FrameGeo
theorem _root_.solution (Lr : RigLB G) (c : CubicalStr G Lr) {O : Type} [CommRing O] [StarRing O]
    (act : Geo.Tor.OAct O G) (a w0 : O) (N : ℕ) (hN : a * star a = (N : O))
    (u : LB.Gen (LB.LinComb Lr.L (rosatiφ G (act.act a) (act.act (star a))) rosatiε)) (hu : u.IsGen)
    (ρ : LB.Gen (LB.LinComb Lr.L (primφ (act.act w0)) primε)) (hρ : ρ.IsGen) :
    ∃ mu : LB.Gen (LB.LinComb Lr.L (K := Fin 2) ![𝟙 G.left, (act.act a).left] ![(N : ℤ), -1]), mu.IsGen ∧
      ∀ (T : Over S) (y : T ⟶ G) (z : T.left) (J), Good Lr.L z J →
        val mu y.left z J * val ρ (y ≫ act.act a).left z J *
          ∏ i ∈ Finset.range N, cubV c z J y (y ≫ act.act ((i : O) * w0)) (y ≫ act.act w0) =
        (val₂ u z J y (y ≫ act.act (w0 * a)))⁻¹ * val ρ y.left z J ^ N := by
  obtain ⟨t, ht, vt⟩ := exists_cubN c (1 : G ⟶ G) (act.act w0) (𝟙 G) N
  obtain ⟨mu, hmu, hv⟩ := exists_gen Lr.isLB (K' := Fin 2) (φ' := ![𝟙 G.left, (act.act a).left])
    (ε' := ![(N : ℤ), -1]) (fun U _ h => by
      have p₁ := prod_prim (act.act w0) (𝟙 G) h
      have p₂ := prod_prim (act.act w0) (act.act a) h
      have p₃ := prod_ros (act.act a) (act.act (star a)) (𝟙 G) (act.act (w0 * a)) h
      have e₁ : act.act (w0 * a) ≫ act.act (star a) = act.act w0 ^ N := by
        rw [← act.mul, _root_.mul_assoc, hN, mul_comm, act_natCast_mul]
      have e₂ : act.act a ≫ act.act w0 = act.act (w0 * a) := by rw [← act.mul, mul_comm]
      rw [e₁] at p₃
      rw [e₂] at p₂
      simp only [Over.id_left, Category.id_comp] at p₁ p₃
      refine (DVR.prod_sum₂ (K := Fin 5) (K' := Fin 5 ⊕ Fin 6 ⊕ Fin 8) (U := U) _ (prod_nmul _ _ N p₁)
        (DVR.prod_neg _ _ (DVR.prod_sum₂ (K := Fin 5) (K' := Fin 6 ⊕ Fin 8) (U := U) _ p₂
          (DVR.prod_sum₂ (K := Fin 6) (K' := Fin 8) (U := U) _ p₃ (Fin.prod_univ_eight _))))).trans ?_
      rw [Fin.prod_univ_two]
      simp only [Sum.elim_inr, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [_root_.one_mul (act.act w0 ^ N), _root_.one_mul (𝟙 G), mul_comm (act.act w0 ^ N) (𝟙 G),
        mul_comm (act.act w0) (𝟙 G)]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, Over.id_left]
      module)
    (LB.mulGen Lr.L _ _ _ _ (GeneratorPullback.powGen Lr.L _ _ ρ N) (LB.invGen Lr.L _ _
      (LB.mulGen Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ ρ (act.act a).left)
        (LB.mulGen Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ u (lift (𝟙 G) (act.act (w0 * a))).left) t))))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (powGen_isGen _ _ _ _ hρ N) (DVR.invGen_isGen _ _ _ _
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hρ _)
        (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hu _) ht))))
  refine ⟨mu, hmu, fun T y z J hJ => ?_⟩
  have C := isCub_cubV c hJ
  have e₁ : cubN (cubV c z J) N (y ≫ 1) (y ≫ act.act w0) (y ≫ 𝟙 G) =
      ∏ i ∈ Finset.range N, cubV c z J y (y ≫ act.act ((i : O) * w0)) (y ≫ act.act w0) := by
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [MonObj.comp_one, _root_.one_mul, Category.comp_id, act_natCast_mul, MonObj.comp_pow, C.s12, C.s01]
  have e₂ : val u (y.left ≫ (lift (𝟙 G) (act.act (w0 * a))).left) z J = val₂ u z J y (y ≫ act.act (w0 * a)) := by
    rw [← Over.comp_left, comp_lift, Category.comp_id]; rfl
  rw [hv _ _ z J hJ, val_mul hJ, val_inv, val_mul hJ, val_mul hJ, val_powGen, val_pull hJ, val_pull hJ,
    vt T y z J hJ, e₁, e₂, Over.comp_left]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel
end GlobalTheory.FrameGeo
