-- Prove2me | solution 1 for GlobalTheory.JR.GLift.embHom_apply_lc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:58:43.3138+00:00
-- url     : https://prove2.me/submissions/e5a4d4de-8c00-45f1-b990-24cac3d23584

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormMulApplyLeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PreimageDiagOneGeneralLinearEmbeddingIntegralGLS

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
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.GLift
namespace GlobalTheory.JR.GLift
theorem _root_.solution {F : Type} [CommRing F] {r : ℕ} (a : Matrix (Fin r) (Fin r) F) (j : Fin r) :
    GlobalTheory.JR.Step.embHom r F a (Fin.last r) (Fin.castSucc j) = 0 := by
  simp [GlobalTheory.JR.Step.embHom, finSumFinEquiv_symm_apply_castSucc, finSumFinEquiv_symm_last]
end GlobalTheory.JR.GLift
