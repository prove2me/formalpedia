-- Prove2me | solution 1 for GlobalTheory.JR.WeilQuad.Fnf.NL_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:14:19.773951+00:00
-- url     : https://prove2.me/submissions/110b4f3e-887f-48f5-adb6-ab66d11ad0ee

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsStableGauss
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NonemptyMeasAndReps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticStarStructure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualMeasureExistsUniqueFourierInversion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticWeilFOpNOpFOpGauss
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
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.WeilQuad GlobalTheory.JR.WeilQuad.Fnf
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
namespace GlobalTheory.JR.WeilQuad.Fnf
theorem _root_.solution [Unram F E] (A : Et F E) (c : A.K) (a : A.L) : A.NL (c • a) = c ^ 2 * A.NL a := by
  obtain ⟨-, hinj, hN, -, -⟩ := Et.quadratic_structure F E A
  apply hinj
  rw [map_mul, map_pow, hN, hN, EtMeas.star_smul_K, Algebra.smul_def, Algebra.smul_def]
  ring
end GlobalTheory.JR.WeilQuad.Fnf
