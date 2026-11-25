-- Prove2me | solution 1 for GroundTheory.PAdicHodge.inv_le_norm_natCast_padicAlgCl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:18:20.281225+00:00
-- url     : https://prove2.me/submissions/6bf39dbe-05db-40c1-badb-50180676e673

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
theorem _root_.solution {n : ℕ} (hn : n ≠ 0) (h : ¬ p ^ 2 ∣ n) :
    (p : ℝ)⁻¹ ≤ ‖(n : PadicAlgCl p)‖ := by
  have hv : padicValNat p n ≤ 1 := by
    by_contra hv
    exact h ((pow_dvd_pow p (by omega)).trans pow_padicValNat_dvd)
  rw [norm_natCast_padicAlgCl hn, ← zpow_neg_one]
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.out.one_lt.le
  exact zpow_le_zpow_right₀ hp1 (by omega)
end GroundTheory.PAdicHodge
