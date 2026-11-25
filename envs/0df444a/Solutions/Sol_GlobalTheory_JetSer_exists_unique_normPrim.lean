-- Prove2me | solution 1 for GlobalTheory.JetSer.exists_unique_normPrim
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:23:29.359824+00:00
-- url     : https://prove2.me/submissions/d919bf82-dde3-4d02-90dd-197351c6bc95

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsUniqueNormPrim
import Theorems.Thm_GlobalTheory_JetSer_exists_gen_of_lbIso
import Theorems.Thm_GlobalTheory_JetSer_gen_ext_val
import Theorems.Thm_GlobalTheory_JetSer_prod_lam
import Theorems.Thm_GlobalTheory_JetSer_prod_prim
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_prod_sum__19c72914c5cb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_invGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_mulGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_prod_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_corr_of_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_gen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gen_unique
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_corr
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
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.JetSer
open ReciprocityTheory.ChartRestriction.G.Out (rosatiφ rosatiε zero2)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (LBIso)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.JetSer
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.JetSer
theorem _root_.solution : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (Lr : RigLB G) (w : G ⟶ G) [IsMonHom w],
    LBIso Lr.L (cubeLB G ![𝟙 G, w] Lr.L) →
    (∃ ρ : LB.Gen (LB.LinComb Lr.L (primφ w) primε), ρ.IsGen ∧
      LB.Gen.Corr Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ ρ (eSec G)) Lr.rig) ∧
    (Function.Surjective G.hom.appTop.hom → ∀ ρ ρ' : LB.Gen (LB.LinComb Lr.L (primφ w) primε), ρ.IsGen → ρ'.IsGen →
      LB.Gen.Corr Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ ρ (eSec G)) Lr.rig →
      LB.Gen.Corr Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ ρ' (eSec G)) Lr.rig → ρ.s = ρ'.s) := by
  intro S G _ _ Lr w _ H
  have he : eSec G ≫ G.hom = 𝟙 S := Over.w η[G]
  refine ⟨?_, fun hp ρ ρ' h h' c c' => gen_ext_val Lr.isLB h h' fun y J hJ =>
    gen_unique Lr.isLB G.hom (eSec G) he hp h h' (fun y J hJ => ?_) _ _ y J hJ⟩
  · obtain ⟨t₀, ht₀⟩ := exists_gen_of_lbIso Lr.L _ _ H
    have P : ∀ (V : Type) [CommGroup V] (k : (G.left ⟶ G.left) → V), ∏ i, k (primφ w i) ^ primε i =
        k (𝟙 _) * (k (𝟙 G * w : G ⟶ G).left)⁻¹ * k (𝟙 _) * k w.left * (k (1 : G ⟶ G).left)⁻¹ := fun V _ k => by
      have := prod_prim w (𝟙 G) k
      simpa only [Over.id_left, Category.id_comp] using this
    obtain ⟨t, ht, -⟩ := exists_gen Lr.isLB (φ' := primφ w) (ε' := primε) (fun V _ k => by
      refine (DVR.prod_neg _ _ (DVR.prod_sum₂ (K' := PUnit) (U := V) _ (prod_lam (𝟙 G) w k)
        (c' := (k (𝟙 _))⁻¹) (by simp))).trans ?_
      rw [P]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, Over.id_left]
      abel) _ (DVR.invGen_isGen _ _ _ _ ht₀)
    have n : G.hom ≫ eSec G = (1 : G ⟶ G).left := rfl
    obtain ⟨ρ, hρ, hv⟩ := exists_gen Lr.isLB (φ' := primφ w) (ε' := primε) (fun V _ k => by
      have p := prod_prim w (1 : G ⟶ G) k
      rw [MonObj.one_comp, _root_.mul_one] at p
      refine Eq.trans (DVR.prod_sum₂ (K := Fin 5) (K' := Fin 5 ⊕ PUnit) (U := V) _
        (c := ∏ i, k (primφ w i) ^ primε i) rfl
        (DVR.prod_sum₂ (K := Fin 5) (K' := PUnit) (U := V) _ (DVR.prod_neg _ _ p) (c' := k (1 : G ⟶ G).left)
          (by rw [Fintype.prod_unique]; exact zpow_one _))) ?_
      simp)
      (LB.mulGen Lr.L _ _ _ _ t (LB.mulGen Lr.L _ _ _ _
        (LB.invGen Lr.L _ _ (LB.pullGen Lr.L _ _ t (1 : G ⟶ G).left)) (LB.pullGen Lr.L _ _ Lr.rig G.hom)))
      (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (DVR.mulGen_isGen _ _ _ _ _ _ _
        (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht _)) (DVR.pullGen_isGen _ _ _ _ Lr.rigGen _)))
    refine ⟨ρ, hρ, corr_of_val Lr.isLB fun y J hJ => ?_⟩
    have e₁ : eSec G ≫ (1 : G ⟶ G).left = eSec G := by
      rw [← n, ← Category.assoc, he]; exact Category.id_comp _
    rw [val_pull hJ, Category.id_comp, hv _ _ y J hJ, val_mul hJ, val_mul hJ, val_inv, val_pull hJ, val_pull hJ, e₁,
      mul_inv_cancel_left]
    exact congrArg (fun q => val Lr.rig q y J) he
  · have a := val_corr hJ c (𝟙 _)
    have b := val_corr hJ c' (𝟙 _)
    rw [val_pull hJ, Category.id_comp] at a b
    exact a.trans b.symm
end GlobalTheory.JetSer
