-- Prove2me | solution 1 for GlobalTheory.FlatChecks.coord_differentiableAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:42:54.114861+00:00
-- url     : https://prove2.me/submissions/8ae65f5e-396f-40b3-a4fa-984fdf89249a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_BasePsiLeviLowerBound
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_UpperHalfSurvey_CoordDifferentiableAt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.FlatChecks
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory.FlatChecks
theorem _root_.solution (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) (j : Fin Fl.δ) :
    DifferentiableAt ℂ (fun z : V (nd X) => (WithLp.toLp 2 fun k =>
      Fl.s k (cpt X (Fl.xs j) z) / Fl.w0 (cpt X (Fl.xs j) z) : V (nd X))) 0 := by
  by_contra hn
  have h := Fl.coord j
  rw [fderiv_zero_of_not_differentiableAt hn] at h
  apply h
  have h2 := Xa.n_ge
  haveI : Nonempty (Fin (nd X)) := ⟨⟨0, by omega⟩⟩
  have b := (EuclideanSpace.basisFun (Fin (nd X)) ℂ).toBasis
  simp only [ContinuousLinearMap.det, ContinuousLinearMap.coe_zero]
  exact LinearMap.det_zero' b
end GlobalTheory.FlatChecks
