-- Prove2me | solution 1 for GroundTheory.PAdicHodge.Laurent.cmul_weight_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:27:29.680868+00:00
-- url     : https://prove2.me/submissions/e6693e03-2358-409c-be94-2ce05e864579

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_RobbaSeries
import Theorems.Thm_GroundTheory_PAdicHodge_Laurent_ConvergesAt_tendsto_term
import Theorems.Thm_GroundTheory_PAdicHodge_Laurent_norm_tsum_eq_of_dominant

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
open Filter Topology
open GroundTheory.PAdicHodge.Laurent
set_option linter.unusedSectionVars false
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {a b c : ℤ → K} {ρ : ℝ}
variable [CompleteSpace K]
namespace GroundTheory.PAdicHodge.Laurent
theorem _root_.solution (hρ : 0 < ρ) (ha : ConvergesAt a ρ) (hb : ConvergesAt b ρ) {n i₀ : ℤ}
    {M : ℝ} (hM : 0 < M) (heq : (‖a i₀‖ * ρ ^ i₀) * (‖b (n - i₀)‖ * ρ ^ (n - i₀)) = M)
    (hlt : ∀ i, i ≠ i₀ → (‖a i‖ * ρ ^ i) * (‖b (n - i)‖ * ρ ^ (n - i)) < M) :
    ‖cmul a b n‖ * ρ ^ n = M := by
  have hρn : 0 < ρ ^ n := zpow_pos hρ n
  rw [← eq_div_iff hρn.ne']
  have h0 : a i₀ * b (n - i₀) ≠ 0 := by
    intro h0
    have := norm_mul_term (a := a) (b := b) hρ.ne' n i₀
    rw [h0, norm_zero, heq] at this
    exact (div_pos hM hρn).ne' this.symm
  unfold cmul
  rw [norm_tsum_eq_of_dominant (ha.tendsto_term hρ hb n) i₀ h0 fun i hi => ?_,
    norm_mul_term hρ.ne' n i₀, heq]
  rw [norm_mul_term hρ.ne' n i, norm_mul_term hρ.ne' n i₀, heq]
  exact div_lt_div_of_pos_right (hlt i hi) hρn
end GroundTheory.PAdicHodge.Laurent
