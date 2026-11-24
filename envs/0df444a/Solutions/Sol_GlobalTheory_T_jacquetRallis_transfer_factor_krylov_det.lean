-- Prove2me | solution 1 for GlobalTheory.T.jacquetRallis_transfer_factor_krylov_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:41:34.131467+00:00
-- url     : https://prove2.me/submissions/99fc7f1d-24f7-480f-8a53-4e2f584a3284

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisTransferFactorKrylovDet
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisTransferFactorKrylovDetStatement
import Theorems.Thm_GlobalTheory_JR_transfer_factor_lemma


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k : Type) [CommRing k] (r : ℕ), (∀ Y : Gl r k, lastDet Y = (-1) ^ r * (Cm Y).det) ∧ ∀ (g : GL (Fin r) k) (Y : Gl r k), Cm (act g Y) = Cm Y * ((g⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) := by
  first | exact @GlobalTheory.JR.transfer_factor_lemma | exact GlobalTheory.JR.transfer_factor_lemma | (intros; apply GlobalTheory.JR.transfer_factor_lemma <;> assumption)
end _root_.GlobalTheory.T
