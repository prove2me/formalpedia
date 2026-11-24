-- Prove2me | solution 1 for GlobalTheory.NTr.small_of_trace_small
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:28:25.184857+00:00
-- url     : https://prove2.me/submissions/f1d73b81-4392-4036-b639-acde17f7489c

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedQuadraticIntegralTraceFormPerfect
import Theorems.Thm_GlobalTheory_NTr_trace_eq
import Theorems.Thm_GlobalTheory_NTr_exists_half

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.NTr
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [hU : Unram F E]
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [hU : Unram F E]
namespace GlobalTheory.NTr
theorem _root_.solution (y : E) (h : ∀ e : E, ‖e‖ ≤ 1 → ‖Algebra.trace F E (e * y)‖ < 1) : ‖y‖ < 1 := by
  haveI := hU.charZero
  by_contra hy
  push_neg at hy
  have hy0 : y ≠ 0 := by intro h0; rw [h0, norm_zero] at hy; linarith
  obtain ⟨x, hx⟩ := hU.unram y
  obtain ⟨e0, he0, hs⟩ := exists_half F (E := E)
  have htr : Algebra.trace F E e0 = 1 := by
    apply (algebraMap F E).injective
    rw [trace_eq, hs, map_one]
  have hxpos : 0 < ‖x‖ := by rw [← hx]; exact norm_pos_iff.mpr hy0
  have hX0 : algebraMap F E x ≠ 0 := by simpa using norm_pos_iff.mp hxpos
  have key := h (e0 * algebraMap F E x / y) (by
    rw [norm_div, norm_mul, norm_algebraMap', ← hx, mul_div_assoc, div_self (norm_pos_iff.mpr hy0).ne', mul_one]
    exact he0)
  rw [div_mul_cancel₀ _ hy0, mul_comm, ← Algebra.smul_def, LinearMap.map_smul, htr, smul_eq_mul, mul_one, ← hx] at key
  linarith
end GlobalTheory.NTr
