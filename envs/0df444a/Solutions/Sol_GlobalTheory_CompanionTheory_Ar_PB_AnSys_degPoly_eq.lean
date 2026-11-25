-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.PB.AnSys.degPoly_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:33:05.781465+00:00
-- url     : https://prove2.me/submissions/aabdae61-d2ca-4d72-9fd7-c39fc6c4c8a1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRes
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterNamed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_TargetSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_KleimanSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsUniqueStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_GenericComplexPoint
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_DivisibilityTowers_Birational
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_IsTwiceDifferentiableAt
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_MetricsProjectionFormulaNef
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_AnSys_nComp_pos
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_formPoly_const_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Filter Topology
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GlobalTheory.CompanionTheory.Ar.PB
namespace AnSys
theorem _root_.solution {e : ℕ} {σ : Type} [Fintype σ] (S : AnSys e σ) [Nonempty S.X] :
    S.degPoly = (S.nComp : ℝ) • S.degPolyDe := by
  have h : (S.nComp : ℝ) ≠ 0 := Nat.cast_ne_zero.2 S.nComp_pos.ne'
  rw [AnSys.degPolyDe, ← formPoly_const_mul, AnSys.degPoly]
  congr 1
  funext w
  rw [AnSys.degNumDe, mul_div_cancel₀ _ h]
end AnSys
end GlobalTheory.CompanionTheory.Ar.PB
