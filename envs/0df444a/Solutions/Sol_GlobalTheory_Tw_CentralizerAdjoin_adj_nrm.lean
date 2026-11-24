-- Prove2me | solution 1 for GlobalTheory.Tw.CentralizerAdjoin.adj_nrm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:50:49.112311+00:00
-- url     : https://prove2.me/submissions/94d9e601-d8e2-458a-ab08-c476cda481b0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TwConj
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MemCentIffTwConj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TwistedCentralizerIsNormOneTorus
import Theorems.Thm_GlobalTheory_Tw_CentralizerAdjoin_isUnit_nrm
import Theorems.Thm_GlobalTheory_Tw_Model_adj_eq
import Theorems.Thm_GlobalTheory_Tw_Model_theta_mul
import Theorems.Thm_GlobalTheory_Tw_Model_theta_theta


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
theorem _root_.solution {δ : Matrix (Fin n) (Fin n) R} (hδ : IsUnit δ) : adj δ (nrm δ) = (nrm δ)⁻¹ := by
  have hd := (Matrix.isUnit_iff_isUnit_det δ).mp hδ
  rw [adj_eq hδ (isUnit_nrm hδ)]
  congr 1
  rw [nrm, theta_mul, theta_theta hδ]
  simp only [Matrix.mul_assoc]
  rw [Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]
end GlobalTheory.Tw.CentralizerAdjoin
