-- Prove2me | solution 1 for GlobalTheory.gram_det_eq_zero_of_lt_card
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:59:04.697806+00:00
-- url     : https://prove2.me/submissions/d247c331-933e-47a7-9cba-d91100ff9225

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsScalarSubPosSemidef

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {r : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (N : Matrix (Fin r) ι ℂ) (h : r < Fintype.card ι) : (Nᴴ * N).det = 0 := by
  by_contra hd
  have hu : IsUnit (Nᴴ * N) := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hd)
  have h1 := Matrix.rank_of_isUnit _ hu
  have h2 := (Matrix.rank_mul_le_right Nᴴ N).trans (Matrix.rank_le_card_height N)
  rw [h1, Fintype.card_fin] at h2
  omega
end GlobalTheory
