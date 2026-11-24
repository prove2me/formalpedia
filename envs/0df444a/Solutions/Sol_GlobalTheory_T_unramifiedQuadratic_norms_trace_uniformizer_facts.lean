-- Prove2me | solution 1 for GlobalTheory.T.unramifiedQuadratic_norms_trace_uniformizer_facts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:26:14.699931+00:00
-- url     : https://prove2.me/submissions/9650290e-f1e7-4c7a-8d2b-5c97cce16c93

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedQuadraticNormsTraceUniformizerFacts
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedQuadraticNormsTraceUniformizerFactsStatement
import Theorems.Thm_GlobalTheory_UnitLemma_UnramNorm_unram_quadratic_facts


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : UQ), (∀ u : K.Oˣ, K.c (algebraMap K.O K.E u) = algebraMap K.O K.E u → ∃ z : K.Oˣ, algebraMap K.O K.E u = algebraMap K.O K.E z * K.c (algebraMap K.O K.E z)) ∧ (∃ z : K.O, algebraMap K.O K.E z + K.c (algebraMap K.O K.E z) = 1) ∧ (∃ ϖ : K.O, Irreducible ϖ ∧ K.c (algebraMap K.O K.E ϖ) = algebraMap K.O K.E ϖ) ∧ ∀ x : K.E, val K.O (K.c x) = val K.O x := by
  first | exact @GlobalTheory.UnitLemma.UnramNorm.unram_quadratic_facts | exact GlobalTheory.UnitLemma.UnramNorm.unram_quadratic_facts | (intros; apply GlobalTheory.UnitLemma.UnramNorm.unram_quadratic_facts <;> assumption)
end _root_.GlobalTheory.T
