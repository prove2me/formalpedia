-- Prove2me | solution 1 for GlobalTheory.UU.IntGen.exists_genT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:02:18.495642+00:00
-- url     : https://prove2.me/submissions/5ac19dfc-ec2f-4c85-a110-96d308ba89c0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_SvalTwistOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsGenT
import Theorems.Thm_GlobalTheory_UU_IntGen_prod_famT
import Theorems.Thm_GlobalTheory_UU_IntGen_prod_base
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_prod_sum__19c72914c5cb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_cPoint_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_cPoint_nsmul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_comp_cP
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_invGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_mulGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_prod_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_cubN
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_gen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_prod_cub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_cub
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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open ReciprocityTheory.ChartRestriction.G.DVR
noncomputable section
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.IntGen
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)
namespace GlobalTheory.UU.IntGen
theorem _root_.solution (T S : Over (Spec (CommRingCat.of R))) (π : T ⊗ D.P.A ⟶ S) (k : ℕ) (α mu : D.X)
    (v : LB.Gen (LB.LinComb D.P.L (basePts D S α mu) (baseExp k))) (hv : v.IsGen) :
    ∃ u₀ : LB.Gen (LB.LinComb D.P.L (deltaφT D (α + k • mu) α (toUnit T ≫ D.c mu)) (DegPre.deltaε k)), u₀.IsGen ∧
      ∀ (T' : Over (Spec (CommRingCat.of R))) (ρ : T' ⟶ T ⊗ D.P.A) (z : T'.left) (J), Good D.P.L z J →
        val u₀ ρ.left z J = cubN (th D z J) k (cP D T' α) (cP D T' mu) (ρ ≫ snd _ _) *
          (th D z J (cP D T' α) (ρ ≫ snd _ _) (cP D T' mu))⁻¹ * val v (ρ ≫ π).left z J := by
  let a : T ⊗ D.P.A ⟶ D.P.A := cP D _ α
  let mm : T ⊗ D.P.A ⟶ D.P.A := cP D _ mu
  let x : T ⊗ D.P.A ⟶ D.P.A := snd _ _
  have hα' : cP D (T ⊗ D.P.A) (α + k • mu) = a * mm ^ k := by rw [cPoint_add, cPoint_nsmul]
  have htr : trT D (toUnit T ≫ D.c mu) ≫ snd _ _ = x * mm :=
    (lift_snd _ _).trans (congrArg (x * ·) (comp_cP D (fst T D.P.A) mu))
  obtain ⟨N, hN, vN⟩ := exists_cubN D.cub a mm x k
  obtain ⟨u₀, hu₀, vu₀⟩ := exists_gen D.P.isLB (φ' := deltaφT D (α + k • mu) α (toUnit T ≫ D.c mu))
      (ε' := DegPre.deltaε k) (fun U _ h => by
      have p₁ := prod_cub a x mm h
      have p₂ := prod_base D π α mu k h
      have p₃ := prod_famT D (𝟙 (T ⊗ D.P.A)) (α + k • mu) k h
      have p₄ := prod_famT D (trT D (toUnit T ≫ D.c mu)) α k h
      simp only [Over.id_left, Category.id_comp] at p₃
      rw [hα'] at p₃
      rw [htr] at p₄
      refine Eq.trans (prod_sum₂ (K := Fin 8 ⊕ thK) (K' := Fin 4) (U := U) _
        (prod_sum₂ (K := Fin 8) (K' := thK) (U := U) _ rfl (prod_neg _ _ p₁)) p₂)
        (Eq.trans ?_ (prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ p₃ (prod_neg _ _ p₄)).symm)
      rw [← _root_.mul_assoc (cP D _ α), mul_comm mm x]
      apply Additive.ofMul.injective
      simp [Fin.prod_univ_succ, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, a, mm, x]
      module)
    (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ N (LB.invGen D.P.L _ _
      (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (lift a (lift x mm)).left)))
      (LB.pullGen D.P.L _ _ v π.left))
    (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ hN (invGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ D.cub.isGen _)))
      (pullGen_isGen _ _ _ _ hv _))
  refine ⟨u₀, hu₀, fun T' ρ z J hJ => ?_⟩
  refine (vu₀ _ _ z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
    ((congrArg₂ (· * ·) (vN T' ρ z J hJ) ((val_inv _ _).trans (congrArg (·⁻¹) (val_cub D.cub ρ hJ _ _ _)))).trans ?_))
    (val_pull hJ _ _ _)))
  rw [← comp_cP D ρ α, ← comp_cP D ρ mu]
end GlobalTheory.UU.IntGen
