-- Prove2me | solution 1 for OAI.ReverseLogKodaira.FiberChartSpecialization.local_logarithmic_numerator
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T03:17:58.565975+00:00
-- url     : https://prove2.me/submissions/e91de6a2-c2f0-4cfe-8f5c-b9b5813c4b7e

-- Generated from openai/math@1581d4c lean/OAI/AlgebraicGeometry/LogKodaira/GlobalSpecialization.lean:L112-L131
-- (upload_full_project.md Phase 4): solution for node OAI.ReverseLogKodaira.FiberChartSpecialization.local_logarithmic_numerator. The node keeps its source
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
import Theorems.Thm_OAI_ReverseLogKodaira_LocalCanonical_range_pluricanonicalPullback

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

lemma local_logarithmic_numerator
    {X : SmoothProjectiveVariety} (E : X.ReducedSNCBoundary)
    (m : ℕ) (s : X.RationalPluriform m) (hs : s ∈ E.sections m)
    (V : X.scheme.affineOpens) [Nonempty V.1]
    (t : Γ(X.scheme, V.1)) (ht : t ≠ 0) (hI : E.ideal.ideal V = Ideal.span {t}) :
    ∃ q : Pluricanonical ℂ Γ(X.scheme, V.1) X.dimension m,
      logarithmicPullback ℂ Γ(X.scheme, V.1) X.scheme.functionField X.dimension m t q = s := by
  have hmem := hs V inferInstance t ht hI
  change _ ∈ Submodule.span Γ(X.scheme, V.1) _ at hmem
  rw [← LocalCanonical.range_pluricanonicalPullback ℂ Γ(X.scheme, V.1)
    X.scheme.functionField X.dimension m] at hmem
  obtain ⟨q, hq⟩ := hmem
  refine ⟨q, ?_⟩
  change ((algebraMap Γ(X.scheme, V.1) X.scheme.functionField t)^m)⁻¹ •
    LocalCanonical.pluricanonicalPullback ℂ Γ(X.scheme, V.1)
      X.scheme.functionField X.dimension m q = s
  rw [hq, smul_smul, inv_mul_cancel₀, one_smul]
  apply pow_ne_zero m
  change X.scheme.germToFunctionField V.1 t ≠ 0
  simpa only [map_zero] using (X.scheme.germToFunctionField_injective V.1).ne ht

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
    {X : SmoothProjectiveVariety} (E : X.ReducedSNCBoundary)
    (m : ℕ) (s : X.RationalPluriform m) (hs : s ∈ E.sections m)
    (V : X.scheme.affineOpens) [Nonempty V.1]
    (t : Γ(X.scheme, V.1)) (ht : t ≠ 0) (hI : E.ideal.ideal V = Ideal.span {t}) :
    ∃ q : Pluricanonical ℂ Γ(X.scheme, V.1) X.dimension m,
      logarithmicPullback ℂ Γ(X.scheme, V.1) X.scheme.functionField X.dimension m t q = s := by
  first
    | exact OAI.ReverseLogKodaira.FiberChartSpecialization.local_logarithmic_numerator E m s hs V t ht hI
    | exact OAI.ReverseLogKodaira.FiberChartSpecialization.local_logarithmic_numerator
    | (apply OAI.ReverseLogKodaira.FiberChartSpecialization.local_logarithmic_numerator <;> assumption)
    | (intros; apply OAI.ReverseLogKodaira.FiberChartSpecialization.local_logarithmic_numerator <;> assumption)
