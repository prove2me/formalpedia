-- Prove2me | solution 1 for GlobalTheory.JR.WeilQuad.GaussStable.NL_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:19:28.013535+00:00
-- url     : https://prove2.me/submissions/4a36478d-353c-4004-af72-b9b92b279437

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsStableGauss
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NonemptyMeasAndReps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticWeilUnipotentTorusPreserveTest
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsStableQuadraticGaussIntegral
import Theorems.Thm_GlobalTheory_JR_Et_quadratic_structure


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.WeilQuad GlobalTheory.JR.WeilQuad.GaussStable
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
namespace GlobalTheory.JR.WeilQuad.GaussStable
theorem _root_.solution [Unram F E] (A : Et F E) (y m : A.L) :
    A.NL (y + m) = A.NL y + Algebra.trace A.K A.L (star m * y) + A.NL m := by
  obtain ⟨-, hinj, hN, htr, -⟩ := GlobalTheory.JR.Et.quadratic_structure F E A
  apply hinj
  rw [map_add, map_add, hN, hN, hN, htr, star_add, star_mul, star_star]
  ring
end GlobalTheory.JR.WeilQuad.GaussStable
