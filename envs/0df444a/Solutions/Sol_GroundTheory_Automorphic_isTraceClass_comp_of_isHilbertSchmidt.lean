-- Prove2me | solution 1 for GroundTheory.Automorphic.isTraceClass_comp_of_isHilbertSchmidt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:33:37.714175+00:00
-- url     : https://prove2.me/submissions/99d566a5-2e45-4cc7-a3e2-856767bb6f38

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DiscreteSpectrumAbstract
import Definitions.Def_GroundTheory_AutomorphicForms_TraceClass
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations
import Definitions.Def_GroundTheory_AutomorphicForms_TraceFormulaSpectral
import Theorems.Thm_GroundTheory_Automorphic_two_mul_traceNorm_comp_le_of_hilbertSchmidt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ContinuousLinearMap
open scoped ENNReal InnerProductSpace InnerProduct
open GroundTheory GroundTheory.Automorphic
noncomputable section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
namespace GroundTheory.Automorphic
theorem _root_.solution {A : K →L[ℂ] H} {B : H →L[ℂ] K}
    (hA : IsHilbertSchmidt A) (hB : IsHilbertSchmidt B) : IsTraceClass (A.comp B) := by
  have h := (two_mul_traceNorm_comp_le_of_hilbertSchmidt A B).trans_lt
    (ENNReal.add_lt_top.2 ⟨hA, hB⟩)
  rw [IsTraceClass]
  by_contra hc
  rw [not_lt, top_le_iff] at hc
  rw [hc, ENNReal.mul_top two_ne_zero] at h
  exact lt_irrefl _ h
end GroundTheory.Automorphic
