-- Prove2me | solution 1 for GlobalTheory.UU.BiTransport.exists_gen_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:05:41.698858+00:00
-- url     : https://prove2.me/submissions/d870960e-08fa-4da8-825d-a40f1d4806d2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsCompRedIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsUnitAddMonoidAlgebraIffOfTwoUniqueSums
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_BiTrivTransport
import Theorems.Thm_GlobalTheory_UU_BiTransport_lift_lam
import Theorems.Thm_GlobalTheory_UU_BiTransport_prod_lam
import Theorems.Thm_GlobalTheory_UU_BiTransport_toBase_surj
import Theorems.Thm_GlobalTheory_UU_BiTransport_toBase_comp
import Theorems.Thm_GlobalTheory_UU_IsWt_mul
import Theorems.Thm_GlobalTheory_UU_TorusCompat_trans
import Theorems.Thm_GlobalTheory_coe_unitsAddMonoidAlgebraEquiv
import Theorems.Thm_GlobalTheory_mem_coactionWeightSpace
import Theorems.Thm_GlobalTheory_trivialCoaction_apply
import Theorems.Thm_GlobalTheory_tupleCoface_last
import Theorems.Thm_GlobalTheory_tupleCoface_zero
import Theorems.Thm_GlobalTheory_tupleContraction_apply
import Theorems.Thm_P2M_GlobalTheory_hochschildD__trivialCoaction_d0af9f793cf0
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_up
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGen_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.coe_unitsAddMonoidAlgebraEquiv
attribute [local simp] GlobalTheory.mem_coactionWeightSpace
attribute [local simp] GlobalTheory.trivialCoaction_apply
attribute [local simp] GlobalTheory.tupleCoface_last
attribute [local simp] GlobalTheory.tupleCoface_zero
attribute [local simp] GlobalTheory.tupleContraction_apply
attribute [local simp] P2M_GlobalTheory_hochschildD__trivialCoaction_d0af9f793cf0



set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.BiTransport
variable {S S₀ : Scheme.{0}} {ρ : S₀ ⟶ S}
variable {G H : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj H] {G₀ H₀ : Over S₀} [GrpObj G₀] [IsCommMonObj G₀]
  [GrpObj H₀] {F : G₀.left ⟶ G.left} {hw : F ≫ G.hom = G₀.hom ≫ ρ} {E : H₀.left ⟶ H.left}
  {P : CP G} {P₀ : CP G₀} {w : LB.Iso P₀.L.L (P.L.L.pull F)} {i : H ⟶ G} {i₀ : H₀ ⟶ G₀}
namespace GlobalTheory.UU.BiTransport
theorem _root_.solution [Mono ρ] (hF : IsPullback F G₀.hom G.hom ρ) (hE : IsPullback E H₀.hom H.hom ρ)
    (hP : IsCPMap P₀ P ρ F hw w) (hi : E ≫ i.left = i₀.left ≫ F)
    (σ : LB.Gen (LB.LinComb P₀.L.L (lamφ i₀) Oε)) (hσ : σ.IsGen) :
    ∃ s : LB.Gen (LB.LinComb P.L.L (fun k => pullback.fst (H ⊗ G).hom ρ ≫ lamφ i k) Oε), s.IsGen ∧
      ∀ (T : Over S₀) (t : T ⟶ H₀) (x : T ⟶ G₀) (a : T.left ⟶ pullback (H ⊗ G).hom ρ),
        a ≫ pullback.fst _ _ = (lift (toBase hE.w t) (toBase hw x)).left →
        ∀ (z : T.left) (J' J), Good P₀.L.L z J' → Good P.L.L z J →
        ∀ W : (T ⟶ G₀) → (T.left.presheaf.stalk z)ˣ, (∀ y, W y = gw w y.left z (J (y.left ≫ F)) (J' y.left)) →
          val s a z J = W ((t ≫ i₀) * x) * (W (t ≫ i₀))⁻¹ * (W x)⁻¹ * W 1 * val σ (lift t x).left z J' := by
  let Y : Over S₀ := Over.mk (pullback.snd (H ⊗ G).hom ρ)
  let j : Over.mk (Y.hom ≫ ρ) ⟶ H ⊗ G := Over.homMk (pullback.fst (H ⊗ G).hom ρ) pullback.condition
  obtain ⟨t₀, ht₀⟩ := toBase_surj hE hE.w (j ≫ fst H G)
  obtain ⟨x₀, hx₀⟩ := toBase_surj hF hw (j ≫ snd H G)
  have hj : pullback.fst (H ⊗ G).hom ρ = (lift (toBase hE.w t₀) (toBase hw x₀)).left := by
    rw [ht₀, hx₀, ← comp_lift, lift_fst_snd, Category.comp_id]; rfl
  have hφ : (fun k => pullback.fst (H ⊗ G).hom ρ ≫ lamφ i k) = fun k => ((lift t₀ x₀).left ≫ lamφ i₀ k) ≫ F := by
    funext k
    refine ((congrArg (· ≫ lamφ i k) hj).trans (lift_lam i _ _ k)).trans
      (Eq.trans ?_ (congrArg (· ≫ F) (lift_lam i₀ t₀ x₀ k)).symm)
    rw [toBase_comp (hw := hw) hE.w hi]
    fin_cases k
    · exact (congrArg (fun q => q.left) (hP.mul Y (t₀ ≫ i₀) x₀)).symm
    · rfl
    · rfl
    · exact (congrArg (fun q => q.left) (map_one (toBaseHom hP.mul Y))).symm
  obtain ⟨s, hs, hv⟩ := exists_up ((isGen_iff w).1 hP.gen) P.L.isLB P₀.L.isLB
    (LB.pullGen P₀.L.L (lamφ i₀) Oε σ (lift t₀ x₀).left) (DVR.pullGen_isGen _ _ _ _ hσ _)
  rw [hφ]
  refine ⟨s, hs, fun T t x a ha z J' J hJ' hJ W hW => ?_⟩
  have e₀ : a ≫ pullback.snd (H ⊗ G).hom ρ = T.hom := by
    rw [← cancel_mono ρ, Category.assoc, ← pullback.condition, ← Category.assoc, ha]
    exact Over.w _
  let a' : T ⟶ Y := Over.homMk a e₀
  have e₁ : a' ≫ t₀ = t := Over.OverMorphism.ext (hE.hom_ext (by
    have := congrArg (fun q => a ≫ q.left) ht₀
    refine ((Category.assoc _ _ _).trans this).trans ?_
    refine ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ (fst H G).left) ha)).trans ?_
    exact congrArg (fun q => q.left) (lift_fst (toBase hE.w t) (toBase hw x))) ((Over.w _).trans (Over.w _).symm))
  have e₂ : a' ≫ x₀ = x := Over.OverMorphism.ext (hF.hom_ext (by
    have := congrArg (fun q => a ≫ q.left) hx₀
    refine ((Category.assoc _ _ _).trans this).trans ?_
    refine ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ (snd H G).left) ha)).trans ?_
    exact congrArg (fun q => q.left) (lift_snd (toBase hE.w t) (toBase hw x))) ((Over.w _).trans (Over.w _).symm))
  have e₃ : a ≫ (lift t₀ x₀).left = (lift t x).left :=
    congrArg (fun q => q.left) (show a' ≫ lift t₀ x₀ = lift t x by rw [comp_lift, e₁, e₂])
  have v := hv _ a z _ _ (hJ.mem (fun k => ((lift t₀ x₀).left ≫ lamφ i₀ k) ≫ F) a)
    (hJ'.mem (fun k => (lift t₀ x₀).left ≫ lamφ i₀ k) a)
  refine v.trans (congrArg₂ (· * ·) ?_ ((val_pull hJ' σ _ a).trans (congrArg (fun q => val σ q z J') e₃)))
  simp only [hW]
  refine Eq.trans ?_ (prod_lam i₀ t x (fun q => gw w q z (J (q ≫ F)) (J' q)))
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← e₃]
  simp only [Category.assoc]
end GlobalTheory.UU.BiTransport
