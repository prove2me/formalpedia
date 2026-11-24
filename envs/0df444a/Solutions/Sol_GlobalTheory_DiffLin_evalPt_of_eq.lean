-- Prove2me | solution 1 for GlobalTheory.DiffLin.evalPt_of_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:22:06.470106+00:00
-- url     : https://prove2.me/submissions/f5388961-e757-466a-89f8-4230121e2e7f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_ChartLawPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_IsDiffSumSmulOfIsLieComb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_ker_jetAug_pow


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory
open GlobalTheory.DiffLin
open ReciprocityTheory.ChartRestriction.G.Chart (JetR zR jetAug dualLift dualLift_zR fstD_comp_dualLift ker_jetAug_pow)
variable {R : Type} [CommRing R] {n : ℕ}
open GlobalTheory.TangentOrigin
namespace GlobalTheory.DiffLin
theorem _root_.solution {X : Scheme.{0}} (x : Sp (JetR R (Fin n) 1) ⟶ X) (U : X.Opens)
    (hx : ⊤ ≤ x ⁻¹ᵁ U) (t : Fin n → R) (v : Sp (DualNumber R) ⟶ X)
    (e : v = spMap (dualLift t : JetR R (Fin n) 1 →+* DualNumber R) ≫ x) (f : Γ(X, U)) :
    ∃ h : ⊤ ≤ v ⁻¹ᵁ U, evalPt v U h f = dualLift t (evalPt x U hx f) := by
  subst e
  exact ⟨fun p _ => hx (Set.mem_univ _), evalPt_spMap_comp _ x U hx _ f⟩
end GlobalTheory.DiffLin
