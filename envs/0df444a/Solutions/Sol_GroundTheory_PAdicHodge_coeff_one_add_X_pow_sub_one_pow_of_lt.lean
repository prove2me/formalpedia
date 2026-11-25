-- Prove2me | solution 1 for GroundTheory.PAdicHodge.coeff_one_add_X_pow_sub_one_pow_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:29:31.078529+00:00
-- url     : https://prove2.me/submissions/95a958fc-e5e5-4122-9d16-1274514a7a14

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_LogPowSeries
import Theorems.Thm_GroundTheory_PAdicHodge_X_dvd_one_add_X_pow_sub_one

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
open PowerSeries
namespace GroundTheory.PAdicHodge
theorem _root_.solution {R : Type*} [CommRing R] (q : ℕ) {m n : ℕ}
    (h : m < n) : (((1 + Polynomial.X : Polynomial R) ^ q - 1) ^ n).coeff m = 0 := by
  obtain ⟨g, hg⟩ := pow_dvd_pow_of_dvd (X_dvd_one_add_X_pow_sub_one (R := R) q) n
  rw [hg, Polynomial.coeff_X_pow_mul', if_neg (not_le.2 h)]
end GroundTheory.PAdicHodge
