-- Prove2me | solution 1 for GlobalTheory.CubeLift.exists_defect
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:18:49.224815+00:00
-- url     : https://prove2.me/submissions/af75aa8d-b8dd-4955-bd1a-e6dd3a0a4da5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsNilpotentOfRd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_EvSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsGenLiftOfIsNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ThickenedPointToTorusExtensionGenerator
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsEvenCubicalTrivialisationLiftNilpotent
import Theorems.Thm_GlobalTheory_CubeLift_prod_triv
import Theorems.Thm_GlobalTheory_Descent_freeIso_hom
import Theorems.Thm_GlobalTheory_QCoh_germLinear_apply
import Theorems.Thm_GlobalTheory_QCoh_resBasicOpen_apply
import Theorems.Thm_GlobalTheory_QCoh_resLinear_apply
import Theorems.Thm_GlobalTheory_UU_TorusCompat_trans
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_prod_sum__19c72914c5cb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_mulGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_prod_cub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_cub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Descent.freeIso_hom
attribute [local simp] GlobalTheory.QCoh.germLinear_apply
attribute [local simp] GlobalTheory.QCoh.resBasicOpen_apply
attribute [local simp] GlobalTheory.QCoh.resLinear_apply



set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.CubeLift
open SplitTorus (bcMap)
variable {S : Scheme.{0}} {G H : Over S} [GrpObj G] {i : H ⟶ G}
variable [IsCommMonObj G] [GrpObj H] [IsMonHom i]
namespace GlobalTheory.CubeLift
theorem _root_.solution {L : RigLB G} (c : CubicalStr G L)
    (t : LB.Gen (LB.LinComb L.L (K := Fin 2) ![i.left, (1 : H ⟶ G).left] ![1, -1])) (ht : t.IsGen)
    {V : Over S} (a b d : V ⟶ H) : ∃ D : Γ(V.left, ⊤)ˣ, ∀ (T : Over S) (ρ : T ⟶ V) (z : T.left) (J), Good L.L z J →
      val t ((ρ ≫ a) * (ρ ≫ b) * (ρ ≫ d)).left z J * val t (ρ ≫ a).left z J * val t (ρ ≫ b).left z J *
        val t (ρ ≫ d).left z J = gm ρ.left z ⊤ D * (cubV c z J ((ρ ≫ a) ≫ i) ((ρ ≫ b) ≫ i) ((ρ ≫ d) ≫ i) *
          val t ((ρ ≫ a) * (ρ ≫ b)).left z J * val t ((ρ ≫ a) * (ρ ≫ d)).left z J *
          val t ((ρ ≫ b) * (ρ ≫ d)).left z J) := by
  let sy := fun p : V ⟶ H => LB.pullGen L.L _ _ t p.left
  have gs : ∀ p, (sy p).IsGen := fun p => DVR.pullGen_isGen _ _ _ _ ht _
  let cu := LB.pullGen L.L (thφ G (x3 G)) thε c.t (lift (a ≫ i) (lift (b ≫ i) (d ≫ i))).left
  have gc : cu.IsGen := DVR.pullGen_isGen _ _ _ _ c.isGen _
  obtain ⟨D, hD⟩ := TorusCoord.exists_ratio L.isLB (fun U _ k => by
      refine (DVR.prod_sum₂ (K := (Fin 2 ⊕ Fin 2) ⊕ Fin 2) (K' := Fin 2) (U := U) _
        (DVR.prod_sum₂ (K := Fin 2 ⊕ Fin 2) (K' := Fin 2) (U := U) _
          (DVR.prod_sum₂ (K := Fin 2) (K' := Fin 2) (U := U) _ (prod_triv (a * b * d) k) (prod_triv a k))
          (prod_triv b k)) (prod_triv d k)).trans (Eq.trans ?_
        (DVR.prod_sum₂ (K := (thK ⊕ Fin 2) ⊕ Fin 2) (K' := Fin 2) (U := U) _
          (DVR.prod_sum₂ (K := thK ⊕ Fin 2) (K' := Fin 2) (U := U) _
            (DVR.prod_sum₂ (K := thK) (K' := Fin 2) (U := U) _ (prod_cub (a ≫ i) (b ≫ i) (d ≫ i) k)
              (prod_triv (a * b) k)) (prod_triv (a * d) k)) (prod_triv (b * d) k)).symm)
      simp only [MonObj.mul_comp]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
    (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ (sy (a * b * d)) (sy a)) (sy b)) (sy d))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (gs _) (gs _))
      (gs _)) (gs _))
    (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ cu (sy (a * b))) (sy (a * d))) (sy (b * d)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ gc (gs _))
      (gs _)) (gs _))
  refine ⟨D, fun T ρ z J hJ => ?_⟩
  have vs : ∀ p, val (sy p) ρ.left z J = val t (ρ ≫ p).left z J := fun p => val_pull hJ _ _ _
  simp only [← MonObj.comp_mul, Category.assoc]
  refine Eq.trans ?_ ((hD _ ρ.left z J hJ).trans (congrArg (gm ρ.left z ⊤ D * ·) ?_))
  · exact ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
      ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (vs _) (vs _))) (vs _))) (vs _))).symm
  · exact (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
      ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_cub c ρ hJ _ _ _) (vs _))) (vs _))) (vs _))
end GlobalTheory.CubeLift
