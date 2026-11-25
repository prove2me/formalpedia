-- Prove2me | solution 1 for GlobalTheory.prod_succMin_le_rpow_mul_spanCovol
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:45:37.761803+00:00
-- url     : https://prove2.me/submissions/d1964305-7bef-448a-9771-cf520dbfddf2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsLinearIndependentSqrtEqSuccMinQuad
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LinearIndependentRealOfIntOfDiscrete
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DiscreteTopologySpanOfLinearIndependent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsNeZeroNormSqLeMulCovolumeRpow
import Theorems.Thm_GlobalTheory_prod_succMin_le_rpow_mul_covolume
import Theorems.Thm_GlobalTheory_finrank_span_eq_finrank_int
import Theorems.Thm_GlobalTheory_spanCovol_bot
import Theorems.Thm_GlobalTheory_spanCovol_eq_covolume_comap_span
import Theorems.Thm_GlobalTheory_succMin_inSpan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.spanCovol_bot



set_option autoImplicit false
noncomputable section
open Module Submodule MeasureTheory
open GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  (L : Submodule ℤ E) [DiscreteTopology L]
namespace GlobalTheory
theorem _root_.solution :
    ∏ i : Fin (finrank ℤ L), succMin L (i + 1) ≤
      (finrank ℤ L : ℝ) ^ ((finrank ℤ L : ℝ) / 2) * spanCovol L := by
  borelize E
  have h := prod_succMin_le_rpow_mul_covolume (inSpan L)
  simp only [succMin_inSpan] at h
  rw [spanCovol_eq_covolume_comap_span, ← finrank_span_eq_finrank_int]
  exact h
end GlobalTheory
