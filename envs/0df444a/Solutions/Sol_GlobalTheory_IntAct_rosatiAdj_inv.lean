-- Prove2me | solution 1 for GlobalTheory.IntAct.rosatiAdj_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:12:17.185848+00:00
-- url     : https://prove2.me/submissions/8bd2dd55-7ef7-437b-92d1-152467f6480a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_RosatiAdjMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_RosatiAdjOfPoints
import Theorems.Thm_GlobalTheory_IntAct_rosatiAdj_of_points
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_prod_sum__19c72914c5cb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_invGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_mulGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_prod_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
open GlobalTheory
open GlobalTheory.IntAct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : LB A.left}
namespace GlobalTheory.IntAct
theorem _root_.solution (hL : L.IsLB) (hs : Out.Sym A L) : RosatiAdj A L (𝟙 A)⁻¹ (𝟙 A)⁻¹ := by
  refine rosatiAdj_of_points hL _ _ fun s => ?_
  obtain ⟨U, hU, t, ht⟩ := hs s
  refine ⟨U, hU, fun T x y hT => ?_⟩
  have lf : ∀ w : T ⟶ A, ∃ m : T.left ⟶ (A.hom ⁻¹ᵁ U).toScheme, m ≫ (A.hom ⁻¹ᵁ U).ι = w.left := fun w =>
    ⟨IsOpenImmersion.lift (A.hom ⁻¹ᵁ U).ι w.left (by
      rintro _ ⟨p, rfl⟩
      rw [Scheme.Opens.range_ι]
      have e := congrArg (fun q => q p) (Over.w w)
      exact (congrArg (· ∈ U) e).mpr (hT p)), IsOpenImmersion.lift_fac _ _ _⟩
  choose m hm using lf
  have pr : ∀ (w : T ⟶ A) (V : Type) [CommGroup V] (k : (T.left ⟶ A.left) → V),
      ∏ i : Fin 2, k (m w ≫ (![(A.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : A ⟶ A).left, (A.hom ⁻¹ᵁ U).ι] :
        Fin 2 → ((A.hom ⁻¹ᵁ U).toScheme ⟶ A.left)) i) ^ (![1, -1] : Fin 2 → ℤ) i =
        k (w⁻¹).left * (k w.left)⁻¹ := fun w V _ k => by
    rw [Fin.prod_univ_two]
    show k (m w ≫ (A.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : A ⟶ A).left) ^ (1 : ℤ) *
      k (m w ≫ (A.hom ⁻¹ᵁ U).ι) ^ (-1 : ℤ) = _
    rw [← Category.assoc, hm, zpow_one, zpow_neg_one]
    rfl
  refine ⟨(Fin 2 ⊕ Fin 2) ⊕ Fin 2, inferInstance, _, _,
    LB.mulGen L _ _ _ _ (LB.mulGen L _ _ _ _ (LB.pullGen L _ _ t (m (x * y⁻¹))) (LB.pullGen L _ _ t (m y)))
      (LB.invGen L _ _ (LB.pullGen L _ _ t (m x))),
    DVR.mulGen_isGen _ _ _ _ _ _ _
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht _) (DVR.pullGen_isGen _ _ _ _ ht _))
      (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht _)), fun V _ k => ?_⟩
  refine (DVR.prod_sum₂ (K := Fin 2 ⊕ Fin 2) (K' := Fin 2) (U := V) _
    (DVR.prod_sum₂ (K := Fin 2) (K' := Fin 2) (U := V) _ (pr (x * y⁻¹) V k) (pr y V k))
    (DVR.prod_neg _ _ (pr x V k))).trans ?_
  have e : ∀ w : T ⟶ A, w ≫ (𝟙 A)⁻¹ = w⁻¹ := fun w => by rw [GrpObj.comp_inv, Category.comp_id]
  rw [e, e, mul_inv, inv_inv]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, mul_inv, inv_inv]
  abel
end GlobalTheory.IntAct
