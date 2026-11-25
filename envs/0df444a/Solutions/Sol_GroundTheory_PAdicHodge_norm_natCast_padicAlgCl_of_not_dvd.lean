-- Prove2me | solution 1 for GroundTheory.PAdicHodge.norm_natCast_padicAlgCl_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:18:57.761808+00:00
-- url     : https://prove2.me/submissions/0abcd52e-1d7a-418f-b5b2-292ba3cef130

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PAdicHodge_AxLemma
import Theorems.Thm_GroundTheory_PAdicHodge_norm_natCast_padicAlgCl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open Polynomial
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime]
namespace GroundTheory.PAdicHodge
theorem _root_.solution {n : ℕ} (h : ¬ p ∣ n) :
    ‖(n : PadicAlgCl p)‖ = 1 := by
  have hn : n ≠ 0 := by rintro rfl; exact h (dvd_zero p)
  rw [norm_natCast_padicAlgCl hn, padicValNat.eq_zero_of_not_dvd h]
  simp
end GroundTheory.PAdicHodge
