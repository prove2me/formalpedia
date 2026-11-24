-- Prove2me | solution 1 for GroundTheory.PAdicHodge.norm_natCast_padicAlgCl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:29:42.554253+00:00
-- url     : https://prove2.me/submissions/6dafc451-8fc8-418a-b764-5927c68b3242

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PAdicHodge_AxLemma

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
theorem _root_.solution {n : ℕ} (hn : n ≠ 0) :
    ‖(n : PadicAlgCl p)‖ = (p : ℝ) ^ (-(padicValNat p n : ℤ)) := by
  have h1 : (n : PadicAlgCl p) = algebraMap ℚ_[p] (PadicAlgCl p) ((n : ℚ) : ℚ_[p]) := by
    rw [Rat.cast_natCast, map_natCast]
  rw [h1]
  refine (PadicAlgCl.norm_extends p _).trans ?_
  rw [Padic.eq_padicNorm, padicNorm.eq_zpow_of_nonzero (by exact_mod_cast hn),
    padicValRat.of_nat]
  push_cast
  rfl
end GroundTheory.PAdicHodge
