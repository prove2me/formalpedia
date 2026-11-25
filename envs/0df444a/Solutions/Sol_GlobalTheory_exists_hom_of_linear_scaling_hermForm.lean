-- Prove2me | solution 1 for GlobalTheory.exists_hom_of_linear_scaling_hermForm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:54:57.428911+00:00
-- url     : https://prove2.me/submissions/e1a00189-af2b-4089-955b-d08b2b717dc1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SemicharacterSqEqOneOfSymmetric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SurjectiveOfComplexPointsLiftOfUniversallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniquePointOfRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsReducedSchemeOfSmoothOfIsIntegrallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_DenseClosedPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsHomOfLinearScalingHermForm
import Theorems.Thm_GlobalTheory_AnalyticHom_isMonHom_of_additive
import Theorems.Thm_GlobalTheory_AnalyticHom_exists_hom
import Theorems.Thm_GlobalTheory_ComplexPoints_hom_ext_of_points
import Theorems.Thm_GlobalTheory_SchemeHomsFromPoints_exists_hom
import Theorems.Thm_GlobalTheory_SchemeHomsFromPoints_hom_ext_of_points
import Theorems.Thm_GlobalTheory_isReduced_of_smooth_complex
import Theorems.Thm_GlobalTheory_semicharacter_sq_eq_one_of_symmetric


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
open AnalyticHom
namespace GlobalTheory
theorem _root_.solution :
    ∀ (P P' : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (u' : HolUnif P'.A P'.L P'.g)
      (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (Hm' : Matrix (Fin P'.g) (Fin P'.g) ℂ)
      (χ' : u'.Λ → ℂ),
    u.IsAH Hm χ → u'.IsAH Hm' χ' →
    (∀ (k : ℕ) θ, u.IsThetaFn Hm χ k θ → ∃! s, u.IsFnPow k s θ) →
    (∀ (k : ℕ) s, ∃! θ, u'.IsThetaFn Hm' χ' k θ ∧ u'.IsFnPow k s θ) →
    ∀ (F : (Fin P.g → ℂ) →ₗ[ℂ] (Fin P'.g → ℂ)) (n : ℕ), (∀ l ∈ u.Λ, F l ∈ u'.Λ) →
    (∀ z w, hermForm Hm' (F z) (F w) = (n : ℂ) * hermForm Hm z w) →
    ∃ f : P.A ⟶ P'.A, IsMonHom f ∧ ∀ z, u'.ex (F z) = u.ex z ≫ f := by
  intro P P' u u' Hm χ Hm' χ' h h' hs hθ F n hΛ hH
  haveI := P.isAb.smooth
  haveI := P'.isAb.smooth
  haveI := P'.isAb.proper
  obtain ⟨f, hf⟩ := exists_hom u u' P.isLB P'.isLB P'.ample
    (semicharacter_sq_eq_one_of_symmetric P u Hm χ h)
    (semicharacter_sq_eq_one_of_symmetric P' u' Hm' χ' h') hs hθ F n hΛ hH
  haveI := isReduced_of_smooth_complex _ P.A.hom inferInstance
  have hw : f ≫ P'.A.hom = P.A.hom := by
    refine ComplexPoints.hom_ext_of_points P.A.hom (terminal.from (Sp ℂ)) (terminal.hom_ext _ _)
      fun x hx => ?_
    obtain ⟨z, hz⟩ := u.ex_onto (Over.homMk x hx)
    obtain rfl : (u.ex z).left = x := by rw [hz]; rfl
    rw [← Category.assoc, hf, Over.w, Over.w]
  have key : ∀ z, u'.ex (F z) = u.ex z ≫ Over.homMk f hw := fun z =>
    Over.OverMorphism.ext (hf z).symm
  exact ⟨Over.homMk f hw, isMonHom_of_additive u u' F _ key, key⟩
end GlobalTheory
