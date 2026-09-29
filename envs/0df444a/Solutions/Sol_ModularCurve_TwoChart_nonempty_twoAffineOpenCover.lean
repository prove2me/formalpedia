-- Prove2me | solution 1 for ModularCurve.TwoChart.nonempty_twoAffineOpenCover
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/986c984f-3821-5bc1-8029-0c185caac43a

import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_JacJ1Iface
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_TwoChart_nonempty_twoAffineOpenCover

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian"

namespace E9Cover

open ModularCurve.TwoChart

variable (A : Type) [CommRing A] (K : Type) [Field K] [Algebra A K] (j : K) [Fact (j ≠ 0)]

private theorem ιFin_eq_ιInf_iff (x₀ : XFin A K j) (xi : XInf A K j) :
    (ιFin A K j).base x₀ = (ιInf A K j).base xi ↔
      ∃ w : XMid A K j, (fFin A K j).base w = x₀ ∧ (fInf A K j).base w = xi := by
  constructor
  · intro h
    obtain ⟨k, fi, fj, w, h₁, h₂⟩ :=
      (Scheme.IsLocallyDirected.ι_eq_ι_iff (F := span (fFin A K j) (fInf A K j))
        (i := WalkingSpan.left) (j := WalkingSpan.right) (xi := x₀) (xj := xi)).mp h
    rcases k with (_ | _ | _)
    · rcases fi with _ | _
      rcases fj with _ | _
      exact ⟨w, h₁, h₂⟩
    · rcases fj with _ | _
    · rcases fi with _ | _
  · rintro ⟨w, rfl, rfl⟩
    change (fFin A K j ≫ ιFin A K j).base w = (fInf A K j ≫ ιInf A K j).base w
    rw [glue_condition]

private theorem chartFinOpen_inf_chartInfOpen :
    chartFinOpen A K j ⊓ chartInfOpen A K j = (fFin A K j ≫ ιFin A K j).opensRange := by
  apply TopologicalSpace.Opens.ext
  rw [TopologicalSpace.Opens.coe_inf, chartFinOpen, chartInfOpen, Scheme.Hom.coe_opensRange,
    Scheme.Hom.coe_opensRange, Scheme.Hom.coe_opensRange]
  ext x
  constructor
  · rintro ⟨⟨x₀, rfl⟩, ⟨xi, hxi⟩⟩
    obtain ⟨w, hw, -⟩ := (ιFin_eq_ιInf_iff A K j x₀ xi).mp hxi.symm
    refine ⟨w, ?_⟩
    rw [Scheme.Hom.comp_apply]
    change (ιFin A K j).base ((fFin A K j).base w) = (ιFin A K j).base x₀
    rw [hw]
  · rintro ⟨w, rfl⟩
    refine ⟨⟨(fFin A K j).base w, ?_⟩, ⟨(fInf A K j).base w, ?_⟩⟩
    · rw [Scheme.Hom.comp_apply]
    · change (ιInf A K j) ((fInf A K j) w) = (fFin A K j ≫ ιFin A K j) w
      rw [glue_condition, Scheme.Hom.comp_apply]

end E9Cover

theorem solution
    (A : Type) [CommRing A] (K : Type) [Field K] [Algebra A K] (j : K) [Fact (j ≠ 0)] :
    Nonempty ((ModularCurve.TwoChartModel A K j).TwoAffineOpenCover) :=
  ⟨{ U0 := ModularCurve.TwoChart.chartFinOpen A K j
     U1 := ModularCurve.TwoChart.chartInfOpen A K j
     isAffineOpen_U0 := ModularCurve.TwoChart.isAffineOpen_chartFinOpen A K j
     isAffineOpen_U1 := ModularCurve.TwoChart.isAffineOpen_chartInfOpen A K j
     sup_eq_top := ModularCurve.TwoChart.twoChartCover A K j
     isAffineOpen_inf := by
       rw [E9Cover.chartFinOpen_inf_chartInfOpen]
       exact isAffineOpen_opensRange _ }⟩

end S_ModularCurve_TwoChart_nonempty_twoAffineOpenCover
end P2MW
export P2MW.S_ModularCurve_TwoChart_nonempty_twoAffineOpenCover (solution)
