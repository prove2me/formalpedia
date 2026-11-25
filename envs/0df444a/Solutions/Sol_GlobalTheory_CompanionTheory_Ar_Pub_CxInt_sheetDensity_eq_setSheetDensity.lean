-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Pub.CxInt.sheetDensity_eq_setSheetDensity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:34:31.963184+00:00
-- url     : https://prove2.me/submissions/3785b409-15b5-4811-975e-4a39b8e36484

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IsOpenAlt
import Definitions.Def_P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Metrics__SheetDensityEqSetSheetDensity_cb85824e9bfdd8ba

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Pub
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo
open GlobalTheory.CompanionTheory.Ar.Pub.CxInt
set_option linter.unusedSectionVars false
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {e : ℕ}
namespace GlobalTheory.CompanionTheory.Ar.Pub.CxInt
theorem _root_.solution (P : Ideal (MRing ι))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) :
    sheetDensity P Ψ = setSheetDensity (mcPts P) Ψ := rfl
end GlobalTheory.CompanionTheory.Ar.Pub.CxInt
