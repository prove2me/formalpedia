-- Prove2me | solution 1 for GlobalTheory.EisBL.NilAlg.phi_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:17:39.344821+00:00
-- url     : https://prove2.me/submissions/b5436126-3212-416e-8f8b-5f63d3d7d50b

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
theorem _root_.solution (c : B →+* B) {J K : Matrix n n B} (hJK : J * K = 1) (hKJ : K * J = 1)
    (X : Matrix n n B) : phi c J X = 0 ↔ tau c J K X = X := by
  unfold phi tau
  constructor
  · intro h
    have h1 : J * X.map c * K = -Xᵀ := by
      calc J * X.map c * K = (Xᵀ * J + J * X.map c) * K - Xᵀ * (J * K) := by noncomm_ring
        _ = -Xᵀ := by rw [h, hJK]; noncomm_ring
    rw [h1, transpose_neg, transpose_transpose, neg_neg]
  · intro h
    have h1 : Xᵀ = -(J * X.map c * K) := by
      conv_lhs => rw [← h]
      rw [transpose_neg, transpose_transpose]
    rw [h1]
    calc -(J * X.map c * K) * J + J * X.map c = -(J * X.map c * (K * J)) + J * X.map c := by noncomm_ring
      _ = 0 := by rw [hKJ]; noncomm_ring
end GlobalTheory.EisBL.NilAlg
