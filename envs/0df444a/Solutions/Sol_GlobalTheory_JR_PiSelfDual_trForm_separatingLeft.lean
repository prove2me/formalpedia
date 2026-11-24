-- Prove2me | solution 1 for GlobalTheory.JR.PiSelfDual.trForm_separatingLeft
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:12:32.817905+00:00
-- url     : https://prove2.me/submissions/5fe4b292-834c-49b6-8fa2-8bca87573fda

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualIffLatticeVolumeAndPlancherelStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedQuadraticIntegralTraceFormPerfectStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedStandardAddCharConductorPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsSelfDualPiHaarTraceStarDotProductUnramified
import Theorems.Thm_GlobalTheory_JR_PiSelfDual_trForm_apply
import Theorems.Thm_GlobalTheory_T_unramifiedQuadratic_integral_traceForm_perfect


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.PiSelfDual
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  [Unram F E]
namespace GlobalTheory.JR.PiSelfDual
theorem _root_.solution (r : ℕ) (c : Fin r → E) (hc : ∀ b, trForm (F := F) r c b = 0) : c = 0 := by
  classical
  funext i
  obtain ⟨e, -, he⟩ := (GlobalTheory.T.unramifiedQuadratic_integral_traceForm_perfect F E).2.1
  have h0 := hc (Pi.single i (c i * e))
  rw [trForm_apply, dotProduct_single, Pi.star_apply] at h0
  have h1 : algebraMap F E (Algebra.trace F E (star (c i) * (c i * e))) = star (c i) * c i * (e + star e) := by
    rw [(GlobalTheory.T.unramifiedQuadratic_integral_traceForm_perfect F E).1]
    simp only [star_mul, star_star]
    ring
  rw [h0, map_zero, he, mul_one] at h1
  rcases mul_eq_zero.1 h1.symm with h | h
  · simpa using h
  · simpa using h
end GlobalTheory.JR.PiSelfDual
