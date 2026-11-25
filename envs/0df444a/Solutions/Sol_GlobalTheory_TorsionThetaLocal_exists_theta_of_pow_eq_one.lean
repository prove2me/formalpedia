-- Prove2me | solution 1 for GlobalTheory.TorsionThetaLocal.exists_theta_of_pow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:52:54.884953+00:00
-- url     : https://prove2.me/submissions/2dfabf72-e7fa-46d4-980a-6e9344eb9cc6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifPowOf3
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrLem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigIsoCongr
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsThetaOfPowEqOne
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_exists_gen_of_local
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_mulGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_cubN
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_gen


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.TorsionThetaLocal
namespace GlobalTheory.TorsionThetaLocal
theorem _root_.solution : ∀ (S₀ : Scheme.{0}) (G : Over S₀) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (_ : CubicalStr G L) (S : Type) [CommRing S] [IsLocalRing S] (t : Spec (CommRingCat.of S) ⟶ S₀) (k : ℕ) (x : Over.mk t ⟶ G), x ^ k = 1 → ∃ θ : ThetaGrp G L.L (k : ℤ) (Over.mk t), θ.pt = x := by
  intro S₀ G _ _ L c S _ _ t k x hx
  obtain ⟨u, hu, -⟩ := Geo.Tor.exists_cubN c (T := Over.mk t ⊗ G) 1 (fst (Over.mk t) G ≫ x) (snd (Over.mk t) G) k
  obtain ⟨e, he⟩ := DVR.exists_gen_of_local (V := S) L.L L.isLB (K := Fin 2)
    ![x.left, (1 : Over.mk t ⟶ G).left] ![-(k : ℤ), k]
  have hm : (fst (Over.mk t) G ≫ x) ^ k = 1 := by
    rw [← MonObj.comp_pow, hx, MonObj.comp_one]
  have h1 : (fst (Over.mk t) G).left ≫ (1 : Over.mk t ⟶ G).left = (1 : Over.mk t ⊗ G ⟶ G).left := by
    rw [← Over.comp_left, MonObj.comp_one]
  have h2 : (fst (Over.mk t) G).left ≫ x.left = (fst (Over.mk t) G ≫ x).left := rfl
  have h3 : translPt G x = (fst (Over.mk t) G ≫ x) * snd (Over.mk t) G := rfl
  obtain ⟨w, hw, -⟩ := Geo.Tor.exists_gen L.isLB
    (φ' := ![(snd (Over.mk t) G).left, (translPt G x).left]) (ε' := ![(k : ℤ), -(k : ℤ)]) (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans ?_
      simp only [Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero,
        Matrix.cons_val_succ]
      erw [h1, h2]
      rw [hm, h3]
      simp only [_root_.one_mul, _root_.mul_one]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow]
      module)
    (LB.mulGen L.L _ _ _ _ u (LB.pullGen L.L _ _ e (fst (Over.mk t) G).left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hu (DVR.pullGen_isGen _ _ _ _ he _))
  exact ⟨⟨x, w, hw⟩, rfl⟩
end GlobalTheory.TorsionThetaLocal
