-- Prove2me | solution 1 for GlobalTheory.SW.norm_det_le_add_posSemidef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:40:12.375363+00:00
-- url     : https://prove2.me/submissions/e10f0a5b-03ba-44a7-8d5b-0e4de160bd4f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_NormDetDenomLeRankOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_PosSemidefSubMulConjTranspose
import Theorems.Thm_GlobalTheory_SW_imH_add_I_smul
import Theorems.Thm_GlobalTheory_SW_norm_det_denom_mono


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW
variable {N : ℕ}
namespace GlobalTheory.SW
theorem _root_.solution (A P : Matrix (Fin N) (Fin N) ℂ) (hA : A.PosDef)
    (hP : P.PosSemidef) : ‖A.det‖ ≤ ‖(A + P).det‖ := by
  have h1 : imH (I • A) = A := by
    have := imH_add_I_smul 0 A hA.1
    simpa [imH] using this
  have h := (norm_det_denom_mono N 1 0 (I • A) P (by simp) (by simpa using Matrix.PosDef.one)
    (by rwa [h1]) hP).2
  simpa [← smul_add, det_smul] using h
end GlobalTheory.SW
