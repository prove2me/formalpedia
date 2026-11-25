-- Prove2me | solution 1 for GlobalTheory.SymExtend.exists_normalised
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:20:18.28689+00:00
-- url     : https://prove2.me/submissions/4c96ed04-5434-4f27-929c-27c23a85180c

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
import Theorems.Thm_P2M_GlobalTheory_normal_domain_height_one__5612c3bf64ed
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_prod_sum__19c72914c5cb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_invGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_mulGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_prod_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_gen
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
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory GlobalTheory.SymExtend
namespace GlobalTheory.SymExtend
theorem _root_.solution {X Y S : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K]
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} (p : Y ⟶ S) (e : S ⟶ Y) (he : e ≫ p = 𝟙 S)
    (h0 : ∀ (U : Type) [CommGroup U] (h : (S ⟶ X) → U), ∏ k, h (e ≫ φ k) ^ ε k = 1)
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) :
    ∃ u : LB.Gen (LB.LinComb L φ ε), u.IsGen ∧
      ∀ (Z : Scheme.{0}) (b : Z ⟶ S) (z : Z) (J), Good L z J → val u (b ≫ e) z J = 1 := by
  obtain ⟨t', ht', hv⟩ := exists_gen hL (φ' := φ) (ε' := ε)
    (fun V _ k => by
      have q := h0 V (fun χ => k (p ≫ χ))
      refine Eq.trans (DVR.prod_sum₂ (K := K) (K' := K) (U := V) _
        (c := ∏ i, k (φ i) ^ ε i) rfl
        (DVR.prod_neg _ _ ((Finset.prod_congr rfl fun i _ => by
          show k ((p ≫ e) ≫ _) ^ _ = _
          rw [Category.assoc]).trans q))) ?_
      simp)
    (LB.mulGen L _ _ _ _ t (LB.invGen L _ _ (LB.pullGen L _ _ t (p ≫ e))))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht _)))
  refine ⟨t', ht', fun Z b z J hJ => ?_⟩
  have : (b ≫ e) ≫ p ≫ e = b ≫ e := by
    rw [Category.assoc, ← Category.assoc e, he, Category.id_comp]
  rw [hv Z _ z J hJ, val_mul hJ, val_inv, val_pull hJ, this, mul_inv_cancel]
end GlobalTheory.SymExtend
