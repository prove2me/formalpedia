-- Prove2me | solution 1 for GlobalTheory.SectionsDescent.coord_mul_rs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:31:15.363262+00:00
-- url     : https://prove2.me/submissions/3de3b9a2-5d87-45f9-b27a-28b8d5edc3ef

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsExtensionPullOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsExtensionAffine
import Theorems.Thm_GlobalTheory_SectionsDescent_rs_self
import Theorems.Thm_GlobalTheory_SectionsDescent_app_rs
import Theorems.Thm_GlobalTheory_SectionsDescent_isExtension_affine
import Theorems.Thm_GlobalTheory_FieldBaseChange_IsCoord_natural


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.SectionsDescent
open GlobalTheory.FieldBaseChange
variable {K F : Type} [Field K] [Field F] [Algebra K F] {Y Y' : Scheme.{0}}
  {π : Y ⟶ Spec (CommRingCat.of K)} {π' : Y' ⟶ Spec (CommRingCat.of F)} {p : Y' ⟶ Y}
  (H : IsPullback p π' π (Spec.map (CommRingCat.ofHom (algebraMap K F))))
namespace GlobalTheory.SectionsDescent
theorem _root_.solution {V W : Y.Opens} (hV : IsAffineOpen V) (h : W ≤ V) {ℓ : F →ₗ[K] K}
    {Λ : FnOver π' (p ⁻¹ᵁ V) →+ FnOver π V} {Λ' : FnOver π' (p ⁻¹ᵁ W) →+ FnOver π W}
    (hΛ : IsCoord (pullFn H.w (le_refl (p ⁻¹ᵁ V))) ℓ Λ) (hΛ' : IsCoord (pullFn H.w (le_refl (p ⁻¹ᵁ W))) ℓ Λ')
    (u : Γ(Y, W)) (x : Γ(Y', p ⁻¹ᵁ V)) :
    Λ' ((p.app W).hom u * rs (pre_mono p h) x) = u * rs h (Λ x) :=
  IsCoord.natural (isExtension_affine H hV).span hΛ hΛ'
    (LinearMap.mulLeft K (show FnOver π W from u) ∘ₗ resFn π h)
    (LinearMap.mulLeft F (show FnOver π' (p ⁻¹ᵁ W) from (p.app W).hom u) ∘ₗ
      resFn π' (pre_mono p h))
    (fun v => by
      show (p.app W).hom u * rs _ (rs _ ((p.app V).hom v)) = rs _ ((p.app W).hom (u * rs h v))
      rw [rs_self, rs_self, map_mul]
      exact congrArg _ (app_rs p h v).symm) x
end GlobalTheory.SectionsDescent
