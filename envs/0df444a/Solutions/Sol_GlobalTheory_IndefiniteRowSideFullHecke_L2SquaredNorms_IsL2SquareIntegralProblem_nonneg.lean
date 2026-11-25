-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.L2SquaredNorms.IsL2SquareIntegralProblem.nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:53:29.868647+00:00
-- url     : https://prove2.me/submissions/a426b62f-b12d-4df2-afed-38e8e96462ce

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SectionOfLineBundleOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_HeightDefect_L2SquaredNorms

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.L2SquaredNorms
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
variable {K₁ : Type} [Field K₁]
namespace GlobalTheory.IndefiniteRowSideFullHecke.L2SquaredNorms
namespace IsL2SquareIntegralProblem
theorem _root_.solution {P : ReciprocityTheory.ChartRestriction.G.Out.PolAV (Sp K₁)} {rig : LB.Gen (P.L.pull (eSec P.A))}
    {σ : K₁ →+* ℂ} {s : P.L.Sec} {v : ℝ} (h : IsL2SquareIntegralProblem P rig σ s v) : 0 ≤ v := by
  obtain ⟨_, A', _, φ, u, Hm, χ, θ, Fd, _, _, _, _, _, _, _, _, hv⟩ := h
  rw [hv]
  exact div_nonneg (MeasureTheory.integral_nonneg (fun z => by positivity)) ENNReal.toReal_nonneg
end IsL2SquareIntegralProblem
end GlobalTheory.IndefiniteRowSideFullHecke.L2SquaredNorms
