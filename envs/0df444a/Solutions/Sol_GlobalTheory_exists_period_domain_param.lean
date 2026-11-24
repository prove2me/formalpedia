-- Prove2me | solution 1 for GlobalTheory.exists_period_domain_param
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:30:32.89703+00:00
-- url     : https://prove2.me/submissions/a7331ab3-a7fa-463b-ba2a-7f8c7cdbf210

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsContraction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DatumExistsPeriod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsPeriodDomainParam
import Theorems.Thm_GlobalTheory_PeriodChart_period_chart
import Theorems.Thm_GlobalTheory_PeriodNonempty_exists_isPeriod


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
open GlobalTheory
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open scoped CategoryTheory.Obj TensorProduct
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)), _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsTypeFn H D.p D.q ty → ∃ (B : Set (Fin D.dim → ℂ)) (P : (Fin D.dim → ℂ) → (D.La →+ (Fin g → ℂ))), IsOpen B ∧ Convex ℝ B ∧ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsHolPeriods D ty B P ∧ ∀ P', _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsPeriod D ty P' → ∃! b, b ∈ B ∧ ∃ h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ a, P' a = h (P b a) := by
  intro E _ _ _ H D g ty hty
  obtain ⟨P₀, hP₀⟩ := _root_.GlobalTheory.PeriodNonempty.exists_isPeriod E H D g ty hty
  obtain ⟨m, B, P, hm, hB, hBc, -, -, hP, huniq⟩ :=
    _root_.GlobalTheory.PeriodChart.period_chart E H D g ty hty P₀ hP₀
  have hdim : m = D.dim := by
    have h2 : Module.finrank ℚ E = 2 * InfinitePlace.nrComplexPlaces E :=
      IsTotallyComplex.finrank E
    unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum.dim
    rw [h2] at hm ⊢
    rw [Nat.mul_div_cancel_left _ two_pos]
    linarith
  subst hdim
  exact ⟨B, P, hB, hBc, hP, huniq⟩
end _root_.GlobalTheory
end GlobalTheory
