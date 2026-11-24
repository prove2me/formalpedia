-- Prove2me | solution 1 for GlobalTheory.Tw.CentralizerAdjoin.adj_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:04:55.835635+00:00
-- url     : https://prove2.me/submissions/570c00fe-4638-4df3-a1fe-a815bc770fa5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TwConj
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MemCentIffTwConj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TwistedCentralizerIsNormOneTorus
import Theorems.Thm_GlobalTheory_Tw_CentralizerAdjoin_adj_semi
import Theorems.Thm_P2M_GlobalTheory_Tw_CentralizerAdjoin_adj_one__bd9885609913

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.Tw Matrix Polynomial
noncomputable section
open GlobalTheory GlobalTheory.Tw GlobalTheory.Tw.CentralizerAdjoin
variable {n : ℕ} {R : Type} [CommRing R] [StarRing R]
open GlobalTheory.Tw.Model
namespace GlobalTheory.Tw.CentralizerAdjoin
theorem _root_.solution {δ : Matrix (Fin n) (Fin n) R} (hδ : IsUnit δ) (r : R) :
    adj δ (algebraMap R _ r) = algebraMap R _ (star r) := by
  have h := adj_semi δ r 1 0
  rw [add_zero, adj_one' hδ] at h
  have h0 : adj δ 0 = 0 := by simp [adj]
  rw [h0, add_zero] at h
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, h]
end GlobalTheory.Tw.CentralizerAdjoin
