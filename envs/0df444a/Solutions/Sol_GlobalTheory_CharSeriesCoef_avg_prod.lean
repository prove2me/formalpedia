-- Prove2me | solution 1 for GlobalTheory.CharSeriesCoef.avg_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:10:45.930871+00:00
-- url     : https://prove2.me/submissions/5e7eb152-1c09-4ff2-a854-250007eb101c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousAtCharSeriesCoefZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory GlobalTheory.CharSeriesCoef
namespace GlobalTheory.CharSeriesCoef
theorem _root_.solution {Y ι : Type} [AddCommGroup Y] [Fintype ι] (w : ι → Y) (y : Y) (K : ℕ)
    (χ : AddChar Y ℂ) :
    avg (fun ik : ι × Fin K => w ik.1 + (ik.2 : ℕ) • y) χ
      = avg w χ * ((K : ℂ)⁻¹ * ∑ k : Fin K, χ y ^ (k : ℕ)) := by
  unfold avg
  rw [Fintype.sum_prod_type]
  simp only [AddChar.map_add_eq_mul, AddChar.map_nsmul_eq_pow]
  rw [← Finset.sum_mul_sum, Fintype.card_prod, Fintype.card_fin]
  push_cast
  rw [mul_inv]
  ring
end GlobalTheory.CharSeriesCoef
