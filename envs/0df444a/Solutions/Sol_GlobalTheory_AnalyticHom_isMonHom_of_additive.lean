-- Prove2me | solution 1 for GlobalTheory.AnalyticHom.isMonHom_of_additive
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:59:32.004788+00:00
-- url     : https://prove2.me/submissions/6946668a-255a-4a62-bbd8-454d7afab21d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SemicharacterSqEqOneOfSymmetric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SurjectiveOfComplexPointsLiftOfUniversallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniquePointOfRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsReducedSchemeOfSmoothOfIsIntegrallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_DenseClosedPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsHomOfLinearScalingHermForm
import Theorems.Thm_GlobalTheory_ComplexPoints_over_hom_ext_of_complexPoints
import Theorems.Thm_GlobalTheory_CubeValues_ex_zero
import Theorems.Thm_GlobalTheory_isReduced_of_smooth_complex


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory
open GlobalTheory.AnalyticHom
open CubeValues SymmetricSemicharacter ComplexPoints AffinePointValues
variable {A A' : Over (Sp ℂ)} [GrpObj A] [GrpObj A'] {L : LB A.left} {L' : LB A'.left} {g g' : ℕ}
  (u : HolUnif A L g) (u' : HolUnif A' L' g')
namespace GlobalTheory.AnalyticHom
theorem _root_.solution [Smooth A.hom] [IsSeparated A'.hom]
    (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) (f : A ⟶ A') (hf : ∀ z, u'.ex (F z) = u.ex z ≫ f) :
    IsMonHom f where
  one_hom := by
    have h := hf 0
    rw [map_zero, ex_zero, ex_zero, Hom.one_def, Hom.one_def, toUnit_unit, Category.id_comp,
      Category.id_comp] at h
    exact h.symm
  mul_hom := by
    haveI : Smooth (A ⊗ A).hom := by
      change Smooth (pullback.fst A.hom A.hom ≫ A.hom)
      infer_instance
    haveI := isReduced_of_smooth_complex _ (A ⊗ A).hom inferInstance
    refine over_hom_ext_of_complexPoints fun x => ?_
    obtain ⟨z, hz⟩ := u.ex_onto (x ≫ fst A A)
    obtain ⟨w, hw⟩ := u.ex_onto (x ≫ snd A A)
    have hx : x = lift (u.ex z) (u.ex w) := by
      rw [hz, hw, ← comp_lift, lift_fst_snd, Category.comp_id]
    rw [hx, lift_map_assoc, ← Category.assoc, ← Hom.mul_def, ← Hom.mul_def, ← u.ex_add, ← hf, ← hf,
      ← hf, map_add, u'.ex_add]
end GlobalTheory.AnalyticHom
