-- Prove2me | solution 1 for GlobalTheory.HomLinear.exists_linear_of_isMonHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:06:38.435655+00:00
-- url     : https://prove2.me/submissions/b7344322-8d94-4cb2-952c-c961ca61e432

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsUniqueLinearLiftOfHolomorphicAbelianVarietStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SurjectiveOfComplexPointsLiftOfUniversallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsReducedSchemeOfSmoothOfIsIntegrallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsLinearOfIsMonHom
import Theorems.Thm_GlobalTheory_HomLinear_isHolTo_ex_comp
import Theorems.Thm_GlobalTheory_HomLinear_isTangent_comp
import Theorems.Thm_GlobalTheory_HomLinear_isDiff_comp
import Theorems.Thm_GlobalTheory_ComplexPoints_over_hom_ext_of_complexPoints
import Theorems.Thm_GlobalTheory_T_existsUnique_linearLift_of_holomorphic_abelianVariety
import Theorems.Thm_GlobalTheory_coe_modNEquivTorsion_mk
import Theorems.Thm_GlobalTheory_isReduced_of_smooth_complex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.coe_modNEquivTorsion_mk



set_option autoImplicit false
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HomLinear
variable {A A' : Over (Sp ℂ)} [GrpObj A] [GrpObj A'] {L : LB A.left} {L' : LB A'.left} {g g' : ℕ}
namespace GlobalTheory.HomLinear
theorem _root_.solution :
    ∀ (A A' : Over (Sp ℂ)) [GrpObj A] [GrpObj A'], IsAbelianScheme A → IsAbelianScheme A' →
  ∀ (L : LB A.left) (L' : LB A'.left) (g g' : ℕ) (u : HolUnif A L g) (u' : HolUnif A' L' g'),
  (∀ v, IsTangent v → ∃! w, u'.IsDiff w v) → (∀ w, ∃! v, IsTangent v ∧ u'.IsDiff w v) →
  ∀ f : A ⟶ A', IsMonHom f → ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ), (∀ z, u'.ex (F z) = u.ex z ≫ f) ∧
    (∀ l ∈ u.Λ, F l ∈ u'.Λ) ∧ (∀ w v, IsTangent v → u.IsDiff w v → IsTangent (v ≫ f) ∧ u'.IsDiff (F w) (v ≫ f)) ∧
    ∀ f' : A ⟶ A', (∀ z, u'.ex (F z) = u.ex z ≫ f') → f' = f := by
  intro A A' _ _ hA hA' L L' g g' u u' h1 h2 f hf
  obtain ⟨F, hF, -⟩ := GlobalTheory.T.existsUnique_linearLift_of_holomorphic_abelianVariety A' hA' L' g' g u' h1 h2 (fun z => u.ex z ≫ f)
    (fun z w => by simp only [u.ex_add]; exact MonObj.mul_comp _ _ f) (isHolTo_ex_comp u f)
  refine ⟨F, hF, fun l hl => ?_, fun w v hv hd => ⟨isTangent_comp f hv, isDiff_comp u u' f F hF hv hd⟩,
    fun f' hf' => ?_⟩
  · rw [← u'.ker, hF, (u.ker l).mpr hl]
    exact MonObj.one_comp f
  · have hs : Smooth A.hom := hA.smooth
    have hp : IsProper A'.hom := hA'.proper
    have hr : IsReduced A.left := isReduced_of_smooth_complex _ A.hom hs
    refine ComplexPoints.over_hom_ext_of_complexPoints fun x => ?_
    obtain ⟨z, rfl⟩ := u.ex_onto x
    rw [← hf', hF]
end GlobalTheory.HomLinear
