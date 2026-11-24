-- Prove2me | solution 1 for GlobalTheory.CompactRep.integral_rankOne_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:16:06.656474+00:00
-- url     : https://prove2.me/submissions/e67ce2fe-c296-45de-8dd0-488e68c92d43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_CompactUnitaryFiniteInvariantSubspace
import Theorems.Thm_GlobalTheory_CompactRep_inner_integral_rankOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory InnerProductSpace
open scoped InnerProductSpace
open GlobalTheory GlobalTheory.CompactRep
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H] {X : Type} [MeasurableSpace X] {μ : Measure X}
namespace GlobalTheory.CompactRep
theorem _root_.solution {w : X → H}
    (hFi : Integrable (fun k => rankOne ℂ (w k) (w k)) μ) (v : H)
    (hpos : 0 < ∫ k, ‖⟪v, w k⟫_ℂ‖ ^ 2 ∂μ) :
    (∫ k, rankOne ℂ (w k) (w k) ∂μ : H →L[ℂ] H) ≠ 0 := by
  intro h0
  have h := inner_integral_rankOne hFi v v
  rw [h0, zero_apply, inner_zero_right] at h
  have h3 : ∫ k, ⟪w k, v⟫_ℂ * ⟪v, w k⟫_ℂ ∂μ = ((∫ k, ‖⟪v, w k⟫_ℂ‖ ^ 2 ∂μ : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    congr 1
    funext k
    rw [← inner_conj_symm (w k) v, Complex.conj_mul']
    push_cast
    rfl
  rw [h3] at h
  exact hpos.ne' (by exact_mod_cast h.symm)
end GlobalTheory.CompactRep
