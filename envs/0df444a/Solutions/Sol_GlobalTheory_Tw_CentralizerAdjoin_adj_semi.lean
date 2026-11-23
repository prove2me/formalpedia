-- Prove2me | solution 1 for GlobalTheory.Tw.CentralizerAdjoin.adj_semi
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:14:37.47103+00:00
-- url     : https://prove2.me/submissions/b840297f-f347-46b3-ad73-8594e59cb9e7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TwConj
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MemCentIffTwConj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TwistedCentralizerIsNormOneTorus

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
theorem _root_.solution (δ : Matrix (Fin n) (Fin n) R) (c : R) (g h : Matrix (Fin n) (Fin n) R) :
    adj δ (c • g + h) = star c • adj δ g + adj δ h := by
  simp only [adj, conjTranspose_add, conjTranspose_smul, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_smul, Matrix.smul_mul]
end GlobalTheory.Tw.CentralizerAdjoin
