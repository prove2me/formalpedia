-- Prove2me | solution 1 for GlobalTheory.SocleDet.mem_span_X_of_mul_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:53:32.163155+00:00
-- url     : https://prove2.me/submissions/0667f3ff-ebbe-446b-a163-989aeb7a85e6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_CoeffEqZeroOfMemSpanPow
import Theorems.Thm_GlobalTheory_SocleDet_coeff_eq_zero_of_mem_span_pow
import Theorems.Thm_GlobalTheory_SocleDet_mem_span_X_of_coeff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SocleDet
open Matrix
open MvPowerSeries
variable {k : Type*} [CommRing k] {σ : Type*}
namespace GlobalTheory.SocleDet
theorem _root_.solution (S : Finset σ) (i : σ) (hi : i ∉ S) (p : MvPowerSeries σ k)
    (hp : p * X i ∈ Ideal.span ((fun i => (X i : MvPowerSeries σ k)) '' S)) :
    p ∈ Ideal.span ((fun i => (X i : MvPowerSeries σ k)) '' S) := by
  classical
  refine mem_span_X_of_coeff S p fun m hm => ?_
  have := coeff_eq_zero_of_mem_span_pow 1 S (p * X i) (by simpa using hp)
    (m + Finsupp.single i 1) (fun j hj => by
      have hne : j ≠ i := fun h => hi (h ▸ hj)
      simp [hm j hj, Finsupp.single_eq_of_ne hne])
  rwa [X_def, coeff_add_mul_monomial, mul_one] at this
end GlobalTheory.SocleDet
