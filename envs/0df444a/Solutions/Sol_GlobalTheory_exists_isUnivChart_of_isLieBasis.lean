-- Prove2me | solution 1 for GlobalTheory.exists_isUnivChart_of_isLieBasis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:13:30.445586+00:00
-- url     : https://prove2.me/submissions/5fac62d3-2902-4ae5-ae7a-76889f731286

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_IsUnivChart
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsJetPointsOfIsLieBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_JetChartCoordinatesUniqueCommGroupStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsJetChartCoordinatesNilpotentStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsIsUnivChartOfIsLieBasis
import Theorems.Thm_GlobalTheory_T_exists_jetChart_coordinates_nilpotent
import Theorems.Thm_GlobalTheory_T_jetChart_coordinates_unique_commGroup
import Theorems.Thm_GlobalTheory_exists_jetPoints_of_isLieBasis


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (R : Type) [CommRing R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G],
      Smooth G.hom → ∀ (d : ℕ) (v : Fin d → (epsR R ⟶ G)), IsLieBasis v →
      ∃ (x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin d) m) ⟶ G), IsUnivChart G d x ∧
        (∀ j, spMap (dualLift (Pi.single j (1 : R))) ≫ x 1 = v j) := by
  intro R _ G _ _ hG d v hv
  obtain ⟨x, h₁, h₂, h₃⟩ := GlobalTheory.exists_jetPoints_of_isLieBasis R G hG d v hv
  refine ⟨x, ⟨h₁, h₂, ?_⟩, h₃⟩
  intro A _ _ aug m hm y hy
  obtain ⟨ψ, hψ, hyψ⟩ := GlobalTheory.T.exists_jetChart_coordinates_nilpotent R G hG d v hv x h₁ h₂ h₃ A aug m hm y hy
  refine ⟨ψ, ⟨hψ, hyψ⟩, ?_⟩
  rintro ψ' ⟨hψ', hyψ'⟩
  exact GlobalTheory.T.jetChart_coordinates_unique_commGroup R G hG d v hv x h₁ h₂ h₃ A aug m hm ψ' ψ hψ' hψ (hyψ'.symm.trans hyψ)
end GlobalTheory
