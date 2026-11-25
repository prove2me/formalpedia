-- Prove2me | solution 1 for GlobalTheory.SymExtend.exists_sym
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:06:09.604708+00:00
-- url     : https://prove2.me/submissions/fbd0b6ba-2828-46fb-9fe3-58fabbfb999e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ForallGeometricallyIntegralOfSmoothOfGeometrical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsGenOfLocalOnBase
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueGeneratorExtendDiscreteValuationRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubicalExtendsAndExtendGen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_RigidifiedIsoRespectsCubeAndSymmetry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsCpOfGenericPolarisation
import Theorems.Thm_GlobalTheory_SymExtend_exists_normalised
import Theorems.Thm_GlobalTheory_SymExtend_prod_sym_unit
import Theorems.Thm_GlobalTheory_SymExtend_sym_comp
import Theorems.Thm_GlobalTheory_CubTransport_exists_pmaps
import Theorems.Thm_GlobalTheory_GenExtend_existsUnique_gen_extend
import Theorems.Thm_GlobalTheory_UU_pullIso_isGen
import Theorems.Thm_GlobalTheory_UU_toBase_mul_pullback
import Theorems.Thm_GlobalTheory_exists_gen_neg_of_sym
import Theorems.Thm_GlobalTheory_forall_geometricallyIntegral_of_smooth_of_geometricallyConnected
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_comm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_corr_of_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_gen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_up
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGen_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGrpPullback_pullback
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_pull_isLB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_isGen_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_isGen_oneGen


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory GlobalTheory.SymExtend
namespace GlobalTheory.SymExtend
theorem _root_.solution (hG : GlobalFnsSt) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G]
    [IsCommMonObj G] [Smooth G.hom] [GeometricallyConnected G.hom] (gen : (Over.pullback (jK V)).obj G ≅ A.A)
    [IsMonHom gen.hom] (L : LB G.left) (hL : L.IsLB)
    (w : LB.Iso (A.L.pull gen.hom.left) (L.pull (pullback.fst G.hom (jK V)))) (hw : w.IsGen) :
    ∃ s : LB.Gen (LB.LinComb L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1]), s.IsGen ∧
      LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ s (eSec G)) (LB.oneGen L) := by
  have := A.isAb.comm
  let G' : Over (Spec (CommRingCat.of (FractionRing V))) := (Over.pullback (jK V)).obj G
  let j : pullback G.hom (jK V) ⟶ G.left := pullback.fst G.hom (jK V)
  obtain ⟨u, hu⟩ := exists_gen_neg_of_sym hG A.isAb A.isLB A.sym
  obtain ⟨a, ha, -⟩ := CubTransport.exists_pmaps ((isGen_iff _).1 (pullIso_isGen A.isLB gen.hom.left)) A.isLB
    (pull_isLB A.isLB _) gen.hom.left
    (sym_comp (f := 𝟙 _) (hw := by simp) (toBase_mul_of_isMonHom gen.hom _)) u hu
  obtain ⟨t₀, ht₀, -⟩ := exists_up ((isGen_iff _).1 hw) hL (pull_isLB A.isLB _) a ha
  obtain ⟨t₁, ht₁, -⟩ := exists_gen hL (φ' := fun k => j ≫ (![(ι[G]).left, 𝟙 G.left] : Fin 2 → _) k) (ε' := ![1, -1])
    (fun U _ h => Finset.prod_congr rfl fun k _ =>
      congrArg (fun q => h q ^ _) (sym_comp (toBase_mul_pullback G (jK V)) k)) t₀ ht₀
  have e₂ : eSec G' ≫ j = jK V ≫ eSec G := (cubeMapOf (isGrpPullback_pullback G (jK V))).e_comm
  obtain ⟨t, ht, hv⟩ := exists_normalised hL G'.hom (eSec G') (Over.w η[G']) (fun U _ h => by
    refine Eq.trans (Finset.prod_congr rfl fun k _ => ?_) (prod_sym_unit G U fun q => h (jK V ≫ q))
    exact congrArg (fun q => h q ^ _) ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) e₂).trans
      (Category.assoc _ _ _)))) t₁ ht₁
  obtain ⟨ρ, hρ, hρv⟩ := exists_gen hL (φ' := fun k => eSec G ≫ (![(ι[G]).left, 𝟙 G.left] : Fin 2 → _) k)
    (ε' := ![1, -1]) (fun U _ h => (Fintype.prod_empty _).trans (prod_sym_unit G U h).symm)
    (LB.oneGen L) (LB.isGen_oneGen L)
  obtain ⟨s₀, ⟨hs₀, -⟩, -⟩ := GenExtend.existsUnique_gen_extend V (FractionRing V) G.left G.left G.hom (eSec G)
    inferInstance (forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ inferInstance inferInstance)
    (Over.w η[G]) (eSec G') e₂ L hL (Fin 2) _ _ t ρ ht hρ (corr_of_val hL fun y J hJ =>
      ((val_pull hJ t _ _).trans (hv _ _ y J hJ)).trans
        ((val_pull hJ ρ _ _).trans ((hρv _ _ y J hJ).trans (val_one _))).symm)
  obtain ⟨s, hs, hsv⟩ := exists_normalised hL G.hom (eSec G) (Over.w η[G]) (prod_sym_unit G) s₀ hs₀
  exact ⟨s, hs, corr_of_val hL fun y J hJ =>
    ((val_pull hJ s _ _).trans (hsv _ _ y J hJ)).trans (val_one _).symm⟩
end GlobalTheory.SymExtend
