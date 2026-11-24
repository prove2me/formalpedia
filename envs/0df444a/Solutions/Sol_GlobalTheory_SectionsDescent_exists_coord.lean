-- Prove2me | solution 1 for GlobalTheory.SectionsDescent.exists_coord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:09:40.477632+00:00
-- url     : https://prove2.me/submissions/486e57b8-cb14-470c-9cf4-cb1a86a5bd68

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsExtensionPullOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsExtensionAffine
import Theorems.Thm_GlobalTheory_SectionsDescent_rs_rs
import Theorems.Thm_GlobalTheory_SectionsDescent_glue_affine
import Theorems.Thm_GlobalTheory_SectionsDescent_coord_mul_rs

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
theorem _root_.solution {ℓ : F →ₗ[K] K}
    (Λ : ∀ V : Y.Opens, IsAffineOpen V → FnOver π' (p ⁻¹ᵁ V) →+ FnOver π V)
    (hΛ : ∀ V hV, IsCoord (pullFn H.w (le_refl (p ⁻¹ᵁ V))) ℓ (Λ V hV)) (U : Y.Opens) (x : Γ(Y', p ⁻¹ᵁ U)) :
    ∃ y : Γ(Y, U), ∀ V hV (h : V ≤ U), rs h y = Λ V hV (rs (pre_mono p h) x) :=
  glue_affine U _ fun V W hV hW hVU h => by
    have := coord_mul_rs H hV h (hΛ V hV) (hΛ W hW) 1 (rs (pre_mono p hVU) x)
    rw [map_one, _root_.one_mul, _root_.one_mul, rs_rs] at this
    exact this.symm
end GlobalTheory.SectionsDescent
