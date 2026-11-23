-- Prove2me | solution 1 for GlobalTheory.EtaChar.eta_eq_neg_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:02:28.933907+00:00
-- url     : https://prove2.me/submissions/3d5ac9a0-164f-4dd9-a004-3b35864bbc08

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsMulStarEqOfNormOneUnramifiedQuadraticStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedValuationParitySignCharacterKernelNorm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.EtaChar
namespace GlobalTheory.EtaChar
theorem _root_.solution {F : Type} [NormedField F] (x : F) : eta x = -1 ↔ ¬ ∃ y : F, ‖x‖ = ‖y‖ ^ 2 := by
  unfold eta
  split_ifs with h
  · simp only [h, not_true_eq_false, iff_false]
    norm_num
  · simp [h]
end GlobalTheory.EtaChar
