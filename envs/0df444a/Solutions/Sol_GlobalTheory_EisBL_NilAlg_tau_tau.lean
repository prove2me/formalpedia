-- Prove2me | solution 1 for GlobalTheory.EisBL.NilAlg.tau_tau
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:27:45.777829+00:00
-- url     : https://prove2.me/submissions/cc51490f-c19e-4a64-8a0f-4f9d1a46484b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_EisensteinSeriesG2_G2HaarMeasure_PhiEqZeroIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open GlobalTheory GlobalTheory.EisBL GlobalTheory.EisBL.NilAlg
variable {B : Type} [CommRing B] {n : Type} [Fintype n] [DecidableEq n]
namespace GlobalTheory.EisBL.NilAlg
theorem _root_.solution (c : B →+* B) (hc : ∀ x, c (c x) = x) {J K : Matrix n n B} (ε : B) (hε : ε * ε = 1)
    (hJc : (J.map c)ᵀ = ε • J) (hKc : (K.map c)ᵀ = ε • K) (hJK : J * K = 1) (X : Matrix n n B) :
    tau c J K (tau c J K X) = X := by
  have hcc : (X.map c).map c = X := by ext i j; simp [hc]
  have h1 : (tau c J K X).map c = -(K * Xᵀ * J) := by
    unfold tau
    rw [Matrix.map_neg _ (map_neg c), transpose_map, Matrix.map_mul, Matrix.map_mul, hcc, transpose_mul, transpose_mul,
      hKc, hJc]
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, hε, one_smul, Matrix.mul_assoc]
  show -(J * (tau c J K X).map c * K)ᵀ = X
  rw [h1]
  rw [show J * -(K * Xᵀ * J) * K = -((J * K) * Xᵀ * (J * K)) by noncomm_ring, transpose_neg, neg_neg, hJK,
    Matrix.one_mul, Matrix.mul_one, transpose_transpose]
end GlobalTheory.EisBL.NilAlg
