-- Prove2me | solution 1 for OAI.PositiveEinsteinFour.classification
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T20:45:30.196673+00:00
-- url     : https://prove2.me/submissions/261fe6f2-94d4-4d42-8d35-e00e63ced40f

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_EinsteinFour
import Definitions.Def_OAIQ091C022
import Theorems.Thm_OAI_PositiveEinsteinFour_classificationOn

section
-- module Solutions.OAIQ091_EF.EinsteinFour_Classification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PositiveEinsteinFour

open EinsteinFour
open scoped Manifold ContDiff

/-- Every closed connected Einstein four-manifold with strictly positive sectional
curvature is isometric, after positive scaling, to the round sphere, complex
projective plane, or real projective four-space. -/
theorem classification_oai (M : Type*) [TopologicalSpace M] [ChartedSpace FourSpace M]
    [IsManifold I4 ∞ M] [T2Space M] [SecondCountableTopology M]
    [CompactSpace M] [ConnectedSpace M] (g : SmoothMetric M)
    (hEinstein : IsEinstein g) (hpositive : HasPositiveSectionalCurvature g) :
    ∃ a : ℝ, 0 < a ∧
      (ScaledIsometricTo g a roundDistance ∨
        ScaledIsometricTo g a fubiniStudyDistance ∨
        ScaledIsometricTo g a realProjectiveDistance) :=
  classificationOn M g hEinstein hpositive

end PositiveEinsteinFour

end OAI
end

theorem solution.{u_1} : type_of% @OAI.PositiveEinsteinFour.classification_oai.{u_1} := @OAI.PositiveEinsteinFour.classification_oai.{u_1}
