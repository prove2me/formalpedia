-- Prove2me | solution 1 for GlobalTheory.FieldBaseChange.isExtension_pullOver
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:35:01.923336+00:00
-- url     : https://prove2.me/submissions/5c98ee45-ec3e-4b8f-aa68-faf0750d6639

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExpF
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsExtensionOfIsPushout
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsExtensionPullOver
import Theorems.Thm_P2M_GlobalTheory_FieldBaseChange_gs_zero__47fb152d3439
import Theorems.Thm_GlobalTheory_FieldBaseChange_isExtension_pullFn
import Theorems.Thm_GlobalTheory_FieldBaseChange_IsCoord_natural
import Theorems.Thm_GlobalTheory_FieldBaseChange_IsExtension_of_proj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open GlobalTheory GlobalTheory.FieldBaseChange
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
variable {K F : Type} [Field K] [Field F] [Algebra K F] {X Y Y' : Scheme.{0}}
  {π : Y ⟶ Spec (CommRingCat.of K)} {π' : Y' ⟶ Spec (CommRingCat.of F)} {p : Y' ⟶ Y}
  (H : IsPullback p π' π (Spec.map (CommRingCat.ofHom (algebraMap K F)))) [NoetherianSpace Y]
variable {L : LB X} (hL : L.IsLB) {I : Type} [Fintype I] {φ : I → (Y ⟶ X)} (ε : I → ℤ) {φ' : I → (Y' ⟶ X)}
  (hφ : ∀ k, φ' k = p ≫ φ k)
include hL
namespace GlobalTheory.FieldBaseChange
theorem _root_.solution : IsExtension (pullOver L ε H.w hφ) := by
  obtain ⟨T, hT⟩ := (NoetherianSpace.isCompact (Set.univ : Set Y)).elim_finite_subcover
    (fun j : I → L.ι => (LB.wchart L φ j : Set Y)) (fun j => (LB.wchart L φ j).isOpen) (fun y _ => by
      choose j hj using fun k => exists_chart hL (φ k y)
      exact Set.mem_iUnion.2 ⟨j, Set.mem_iInter.2 hj⟩)
  refine IsExtension.of_proj (J := I → L.ι) _ (fun j => pullFn H.w (wchart_eq hφ j).le)
    (fun j => isExtension_pullFn H (wchart_eq hφ j)) (chartLin π (LB.LinComb L φ ε))
    (chartLin π' (LB.LinComb L φ' ε)) (fun _ _ => rfl) (fun x hx => SecOver.ext _ _ hx) T
    (fun v hv => SecOver.ext _ _ fun j => fn_ext fun y hy => ?_) fun ℓ Λ hΛ x => ?_
  · obtain ⟨t, ht, hy'⟩ := Set.mem_iUnion₂.1 (hT (Set.mem_univ y))
    refine (sec_trans v (𝟙 Y) y hy hy').trans ?_
    have z : gs (𝟙 Y) y (LB.wchart L φ t) (LB.Sec.f v t) = 0 :=
      (congrArg (gs (𝟙 Y) y (LB.wchart L φ t)) (hv t ht)).trans (gs_zero' _ y _ hy')
    exact ((congrArg _ z).trans (mul_zero _)).trans (gs_zero' _ y _ hy).symm
  · refine ⟨⟨fun j => Λ j (chartFun π' (LB.LinComb L φ' ε) j x), fun (i j : I → L.ι) => ?_⟩, fun j => rfl⟩
    have e : LB.wchart L φ' i ⊓ LB.wchart L φ' j = p ⁻¹ᵁ (LB.wchart L φ i ⊓ LB.wchart L φ j) := by
      rw [wchart_eq hφ, wchart_eq hφ]; rfl
    obtain ⟨Λ', hΛ'⟩ := (isExtension_pullFn H e).coord ℓ
    have e₁ := IsCoord.natural (isExtension_pullFn H (wchart_eq hφ i)).span (hΛ i) hΛ'
      (resFn π inf_le_left) (resFn π' inf_le_left) (fun v => fn_ext fun y hy =>
        ((gs_res _ y _ hy _).trans (gs_pullFn H.w _ _ _ y hy.1)).trans
          ((gs_pullFn H.w _ _ _ y hy).trans (gs_res (𝟙 Y' ≫ p) y _ (e.le hy) _)).symm) (chartFun π' (LB.LinComb L φ' ε) i x)
    have e₂ := IsCoord.natural (isExtension_pullFn H (wchart_eq hφ j)).span (hΛ j) hΛ'
      (LinearMap.mulLeft K (show FnOver π _ from ((LB.LinComb L φ ε).g i j).val) ∘ₗ resFn π inf_le_right)
      (LinearMap.mulLeft F (show FnOver π' _ from ((LB.LinComb L φ' ε).g i j).val) ∘ₗ resFn π' inf_le_right)
      (fun v => fn_ext fun y hy => by
        refine ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·) ((gs_unit _ y _ hy _).trans
            (congrArg Units.val (gm_linComb L φ' ε (𝟙 Y') y i j hy.1 hy.2)))
            ((gs_res _ y _ hy _).trans (gs_pullFn H.w _ _ _ y hy.2)))).trans (Eq.symm ?_)
        have hy' : (𝟙 Y' ≫ p) y ∈ LB.wchart L φ i ⊓ LB.wchart L φ j := e.le hy
        refine (gs_pullFn H.w _ _ _ y hy).trans ((gs_mul _ y _ hy' _ _).trans (congrArg₂ (· * ·)
          ((gs_unit _ y _ hy' _).trans (congrArg Units.val
            ((gm_linComb L φ ε (𝟙 Y' ≫ p) y i j hy'.1 hy'.2).trans (trF_comp hφ _ y i j).symm)))
          (gs_res _ y _ hy' _)))) (chartFun π' (LB.LinComb L φ' ε) j x)
    exact e₁.symm.trans ((congrArg Λ' (LB.Sec.compat x i j)).trans e₂)
end GlobalTheory.FieldBaseChange
