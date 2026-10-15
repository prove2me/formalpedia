-- Prove2me | solution 1 for OAI.ReverseLogKodaira.FiberChartSpecialization.NumeratorChart.exists_near_fiber_point
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T03:19:26.466065+00:00
-- url     : https://prove2.me/submissions/41cc77bf-b82c-4ba6-b437-7a5fa7f2c1b9

-- Generated from openai/math@1581d4c lean/OAI/AlgebraicGeometry/LogKodaira/GlobalSpecialization.lean:L135-L168
-- (upload_full_project.md Phase 4): solution for node OAI.ReverseLogKodaira.FiberChartSpecialization.NumeratorChart.exists_near_fiber_point. The node keeps its source
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
import Theorems.Thm_OAI_ReverseLogKodaira_FiberChartSpecialization_local_logarithmic_numerator
import Theorems.Thm_OAI_ReverseLogKodaira_SmoothProjectiveVariety_exists_relative_log_chart

-- ---- from OAI.AlgebraicGeometry.LogKodaira.GlobalSpecialization ----
namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace ReverseLogKodaira.DifferentialBaseChange

 
lemma logarithmicPullback_degreeTransport
    (R B K : Type*) [CommRing R] [CommRing B] [Field K]
    [Algebra R B] [Algebra B K] [Algebra R K] [IsScalarTower R B K]
    {n n' : ℕ} (h : n = n') (m : ℕ) (t : B) (q : Pluricanonical R B n m) :
    LogarithmicSpecialization.logarithmicPullback R B K n' m t
      (degreeTransport R B h m q) = degreeTransport R K h m
        (LogarithmicSpecialization.logarithmicPullback R B K n m t q) := by
  subst n'
  rfl

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

lemma fiber_point_image
    {X Y : SmoothProjectiveVariety} {E : X.ReducedSNCBoundary} {D : Y.ReducedSNCBoundary}
    (f : BoundaryFibration X Y E D) (y : Y.ComplexPoint) (F : FiberModel f y)
    (z : F.variety.scheme) : f.hom (F.inclusion z) = y.point := by
  rw [← Scheme.Hom.comp_apply, F.square.w, Scheme.Hom.comp_apply]
  exact congrArg y.hom (Subsingleton.elim _ complexBasePoint)

namespace NumeratorChart

lemma exists_near_fiber_point
    {X Y : SmoothProjectiveVariety} {E : X.ReducedSNCBoundary} {D : Y.ReducedSNCBoundary}
    (f : StratumSmoothFibration X Y E D)
    (U : Y.scheme.affineOpens) (hU : U.1 ≤ D.complement)
    (y : Y.ComplexPoint) (hy : y.point ∈ U.1) (F : FiberModel f.toBoundaryFibration y)
    (hdim : X.dimension = Y.dimension + F.variety.dimension)
    (m : ℕ) (s : X.RationalPluriform m) (hs : s ∈ E.sections m)
    (O : X.scheme.Opens) (z : F.variety.scheme) (hz : F.inclusion z ∈ O) :
    ∃ P : NumeratorChart f.toBoundaryFibration y F U hdim m s,
      F.inclusion z ∈ P.V.1 ∧ P.V.1 ≤ O := by
  classical
  obtain ⟨V, hzV, hVO, e, hsm, t, ht, hI⟩ :=
    exists_relative_log_chart f U hU O (F.inclusion z) hz
      (by simpa only [fiber_point_image f.toBoundaryFibration y F z] using hy)
  let : Nonempty V.1 := ⟨⟨F.inclusion z, hzV⟩⟩
  let : Nonempty (F.inclusion ⁻¹ᵁ V.1) := ⟨⟨z, hzV⟩⟩
  let A := Γ(Y.scheme, U.1)
  let B := Γ(X.scheme, V.1)
  let : Algebra A B := (f.hom.appLE U.1 V.1 e).hom.toAlgebra
  have hsub : X.dimension - Y.dimension = F.variety.dimension := by omega
  let : Algebra.IsStandardSmoothOfRelativeDimension F.variety.dimension A B := by
    rw [← hsub]
    exact hsm.toAlgebra
  let : Algebra.IsStandardSmooth A B :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth F.variety.dimension
  have hr : Module.finrank B (KaehlerDifferential A B) = F.variety.dimension := by
    simp only [Module.finrank,
      Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential F.variety.dimension,
      Cardinal.toNat_natCast]
  let c := Module.finBasisOfFinrankEq B (KaehlerDifferential A B) hr
  obtain ⟨q, hq⟩ := local_logarithmic_numerator E m s hs V t ht hI
  refine ⟨⟨V, e, inferInstance, inferInstance, inferInstance, c, t, ht, hI,
    degreeTransport ℂ B hdim m q, ?_⟩, hzV, hVO⟩
  rw [logarithmicPullback_degreeTransport, hq]

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
open OAI OAI.ReverseLogKodaira OAI.ReverseLogKodaira.FiberChartSpecialization OAI.ReverseLogKodaira.FiberChartSpecialization.NumeratorChart
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
open SmoothProjectiveVariety DifferentialBaseChange LogarithmicSpecialization

theorem solution
    {X Y : SmoothProjectiveVariety} {E : X.ReducedSNCBoundary} {D : Y.ReducedSNCBoundary}
    (f : StratumSmoothFibration X Y E D)
    (U : Y.scheme.affineOpens) (hU : U.1 ≤ D.complement)
    (y : Y.ComplexPoint) (hy : y.point ∈ U.1) (F : FiberModel f.toBoundaryFibration y)
    (hdim : X.dimension = Y.dimension + F.variety.dimension)
    (m : ℕ) (s : X.RationalPluriform m) (hs : s ∈ E.sections m)
    (O : X.scheme.Opens) (z : F.variety.scheme) (hz : F.inclusion z ∈ O) :
    ∃ P : NumeratorChart f.toBoundaryFibration y F U hdim m s,
      F.inclusion z ∈ P.V.1 ∧ P.V.1 ≤ O := by
  first
    | exact OAI.ReverseLogKodaira.FiberChartSpecialization.NumeratorChart.exists_near_fiber_point f U hU y hy F hdim m s hs O z hz
    | exact OAI.ReverseLogKodaira.FiberChartSpecialization.NumeratorChart.exists_near_fiber_point
    | (apply OAI.ReverseLogKodaira.FiberChartSpecialization.NumeratorChart.exists_near_fiber_point <;> assumption)
    | (intros; apply OAI.ReverseLogKodaira.FiberChartSpecialization.NumeratorChart.exists_near_fiber_point <;> assumption)
