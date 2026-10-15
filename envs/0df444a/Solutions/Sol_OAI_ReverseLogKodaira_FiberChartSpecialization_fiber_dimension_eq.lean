-- Prove2me | solution 1 for OAI.ReverseLogKodaira.FiberChartSpecialization.fiber_dimension_eq
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T03:14:51.208233+00:00
-- url     : https://prove2.me/submissions/ade642eb-40ca-41e7-8f56-1fa2c93f185b

-- Generated from openai/math@1581d4c lean/OAI/AlgebraicGeometry/LogKodaira/GlobalSpecialization.lean:L93-L110
-- (upload_full_project.md Phase 4): solution for node OAI.ReverseLogKodaira.FiberChartSpecialization.fiber_dimension_eq. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_LogKodairaFiberNegative
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_Basic
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_Adjunction
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_BaseChange
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_RelativeCanonical
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_Specialization
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_LocalCanonical
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_FiberCharts
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_LatticeBaseChange
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_GlobalSpecialization
import Theorems.Thm_OAI_ReverseLogKodaira_SmoothDimension_smooth_dimension_unique
import Theorems.Thm_OAI_ReverseLogKodaira_SmoothDimension_smooth_fiber_dimension

-- ---- from OAI.AlgebraicGeometry.LogKodaira.GlobalSpecialization ----
namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace ReverseLogKodaira.DifferentialBaseChange

 
end ReverseLogKodaira.DifferentialBaseChange

namespace ReverseLogKodaira.FiberChartSpecialization
open SmoothProjectiveVariety DifferentialBaseChange LogarithmicSpecialization

 

namespace NumeratorChart
variable {X Y : SmoothProjectiveVariety} {E : X.ReducedSNCBoundary} {D : Y.ReducedSNCBoundary}
  {f : BoundaryFibration X Y E D} {y : Y.ComplexPoint} {F : FiberModel f y}
  {U : Y.scheme.affineOpens} {hdim : X.dimension = Y.dimension + F.variety.dimension}
  {m : ℕ} {s : X.RationalPluriform m}

end NumeratorChart
end ReverseLogKodaira.FiberChartSpecialization

namespace ReverseLogKodaira.FiberChartSpecialization
open SmoothProjectiveVariety DifferentialBaseChange LogarithmicSpecialization

lemma fiber_dimension_eq
    {X Y : SmoothProjectiveVariety} {E : X.ReducedSNCBoundary} {D : Y.ReducedSNCBoundary}
    (f : StratumSmoothFibration X Y E D) (y : Y.ComplexPoint)
    (hy : y.point ∈ D.complement) (F : FiberModel f.toBoundaryFibration y) :
    X.dimension = Y.dimension + F.variety.dimension := by
  have hrange : Set.range y.hom ⊆ D.complement := by
    rintro _ ⟨z, rfl⟩
    have hz : z = complexBasePoint := Subsingleton.elim _ _
    subst z
    exact hy
  obtain ⟨hle, hr⟩ := SmoothDimension.smooth_fiber_dimension X.structural Y.structural
    X.dimension Y.dimension f.hom f.over_base y.hom F.inclusion F.variety.structural
    F.square D.complement hrange
    (by simpa only [Scheme.Hom.resLE_eq_morphismRestrict] using f.smooth)
  let := hr
  have he : X.dimension - Y.dimension = F.variety.dimension :=
    SmoothDimension.smooth_dimension_unique F.variety.scheme F.variety.structural _ _
  omega

namespace NumeratorChart

end NumeratorChart
end ReverseLogKodaira.FiberChartSpecialization

namespace ReverseLogKodaira.FiberChartSpecialization.NumeratorChart
open SmoothProjectiveVariety DifferentialBaseChange

variable {X Y : SmoothProjectiveVariety} {E : X.ReducedSNCBoundary} {D : Y.ReducedSNCBoundary}
  {f : BoundaryFibration X Y E D} {y : Y.ComplexPoint} {F : FiberModel f y}
  {U : Y.scheme.affineOpens} {hdim : X.dimension = Y.dimension + F.variety.dimension}
  {m : ℕ} {s : X.RationalPluriform m}

end ReverseLogKodaira.FiberChartSpecialization.NumeratorChart

namespace ReverseLogKodaira.FiberChartSpecialization
open SmoothProjectiveVariety DifferentialBaseChange

end ReverseLogKodaira.FiberChartSpecialization

namespace ReverseLogKodaira.FiberChartSpecialization
open SmoothProjectiveVariety DifferentialBaseChange

 

end ReverseLogKodaira.FiberChartSpecialization

end

end OAI

-- ---- platform node ----
open OAI OAI.ReverseLogKodaira OAI.ReverseLogKodaira.FiberChartSpecialization
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
open SmoothProjectiveVariety DifferentialBaseChange LogarithmicSpecialization

theorem solution
    {X Y : SmoothProjectiveVariety} {E : X.ReducedSNCBoundary} {D : Y.ReducedSNCBoundary}
    (f : StratumSmoothFibration X Y E D) (y : Y.ComplexPoint)
    (hy : y.point ∈ D.complement) (F : FiberModel f.toBoundaryFibration y) :
    X.dimension = Y.dimension + F.variety.dimension := by
  first
    | exact OAI.ReverseLogKodaira.FiberChartSpecialization.fiber_dimension_eq f y hy F
    | exact OAI.ReverseLogKodaira.FiberChartSpecialization.fiber_dimension_eq
    | (apply OAI.ReverseLogKodaira.FiberChartSpecialization.fiber_dimension_eq <;> assumption)
    | (intros; apply OAI.ReverseLogKodaira.FiberChartSpecialization.fiber_dimension_eq <;> assumption)
