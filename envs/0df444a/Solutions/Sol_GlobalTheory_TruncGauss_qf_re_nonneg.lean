-- Prove2me | solution 1 for GlobalTheory.TruncGauss.qf_re_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:39:04.084299+00:00
-- url     : https://prove2.me/submissions/29eb9cd3-25d2-4714-a530-7934c09cde44

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_IsLocalHomeomorph
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralExpNegHermitianFormPosDefStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TruncatedGaussianIntegralUniformPosSemidef

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology MeasureTheory Metric ReciprocityTheory.L2DbarEstimates
open scoped ComplexOrder
open GlobalTheory GlobalTheory.TruncGauss
namespace GlobalTheory.TruncGauss
theorem _root_.solution {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosSemidef) (w : V n) :
    0 ≤ (qf H w).re := by
  have h := hH.dotProduct_mulVec_nonneg (fun j => (starRingEnd ℂ) (w j))
  have e : star (fun j => (starRingEnd ℂ) (w j)) ⬝ᵥ (H.mulVec (fun j => (starRingEnd ℂ) (w j))) = qf H w := by
    simp only [qf, dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    rw [Complex.star_def, Complex.conj_conj]; ring
  rw [e] at h
  exact (Complex.le_def.mp h).1
end GlobalTheory.TruncGauss
