-- Prove2me | solution 1 for GroundTheory.PAdicHodge.ax_lemma
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:58:34.006971+00:00
-- url     : https://prove2.me/submissions/b68c7d1e-aa1d-401f-87c0-26d08fee3ab7

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PAdicHodge_AxLemma
import Theorems.Thm_GroundTheory_PAdicHodge_one_lt_prime_cast
import Theorems.Thm_GroundTheory_PAdicHodge_axExponent_le
import Theorems.Thm_GroundTheory_PAdicHodge_ax_lemma_of_natDegree

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
theorem _root_.solution {K : IntermediateField ℚ_[p] (PadicAlgCl p)} (x : PadicAlgCl p) {r : ℝ}
    (h : ∀ σ : Gal(PadicAlgCl p/K), ‖σ x - x‖ ≤ r) :
    ∃ y ∈ K, ‖x - y‖ ≤ axConstant p * r := by
  obtain ⟨y, hy, hle⟩ := ax_lemma_of_natDegree _ x rfl r h
  have hr : 0 ≤ r := by simpa using h 1
  exact ⟨y, hy, hle.trans (mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_le one_lt_prime_cast.le (axExponent_le _)) hr)⟩
end GroundTheory.PAdicHodge
