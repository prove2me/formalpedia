-- Prove2me | solution 1 for GroundTheory.PAdicHodge.WittVector.eq_teichmullerSeries_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:28:31.70853+00:00
-- url     : https://prove2.me/submissions/7653034b-a870-4826-a04f-9331316c4f81

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_KerTheta
import Definitions.Def_GroundTheory_PAdicHodge_TiltValuation
import Definitions.Def_GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow
import Theorems.Thm_GroundTheory_PAdicHodge_WittVector_teichmullerSeries_coeff
import Theorems.Thm_GroundTheory_PAdicHodge_WittVector_coeff_sum_teichmuller_mul_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open WittVector
variable {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R]
variable [CharP R p]
variable [PerfectRing R p]
namespace GroundTheory.PAdicHodge
namespace WittVector
theorem _root_.solution (a : ℕ → R) (x : WittVector p R) :
    x = WittVector.teichmullerSeries a ↔
      ∀ n, (p : WittVector p R) ^ (n + 1) ∣
        x - ∑ i ∈ Finset.Iic n, teichmuller p (a i) * (p : WittVector p R) ^ i := by
  have key : ∀ (n : ℕ) (d : WittVector p R), (p : WittVector p R) ^ (n + 1) ∣ d ↔
      ∀ j < n + 1, d.coeff j = 0 := fun n d => by
    rw [← Ideal.mem_span_singleton, mem_span_p_pow_iff_le_coeff_eq_zero]
  simp_rw [key, ← le_coeff_eq_iff_le_sub_coeff_eq_zero]
  constructor
  · rintro rfl n j hj
    rw [WittVector.coeff_sum_teichmuller_mul_pow, if_pos (Nat.lt_succ_iff.1 hj),
      WittVector.teichmullerSeries_coeff]
  · intro h
    ext j
    rw [h j j (Nat.lt_succ_self j), WittVector.coeff_sum_teichmuller_mul_pow, if_pos le_rfl,
      WittVector.teichmullerSeries_coeff]
end WittVector
end GroundTheory.PAdicHodge
