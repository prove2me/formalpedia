-- Prove2me | solution 1 for GroundTheory.PAdicHodge.Laurent.cmul_weight_lt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:40:50.359873+00:00
-- url     : https://prove2.me/submissions/d1459402-1f36-47c9-a526-ad78de8c5a39

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_RobbaSeries
import Theorems.Thm_GroundTheory_PAdicHodge_Laurent_ConvergesAt_tendsto_term
import Theorems.Thm_GroundTheory_PAdicHodge_Laurent_norm_tsum_lt

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
theorem _root_.solution (hρ : 0 < ρ) (ha : ConvergesAt a ρ) (hb : ConvergesAt b ρ) {n : ℤ}
    {M : ℝ} (hM : 0 < M) (hlt : ∀ i, (‖a i‖ * ρ ^ i) * (‖b (n - i)‖ * ρ ^ (n - i)) < M) :
    ‖cmul a b n‖ * ρ ^ n < M := by
  have hρn : 0 < ρ ^ n := zpow_pos hρ n
  rw [← lt_div_iff₀ hρn]
  refine norm_tsum_lt (ha.tendsto_term hρ hb n) (div_pos hM hρn) fun i => ?_
  rw [norm_mul_term hρ.ne' n i]
  exact div_lt_div_of_pos_right (hlt i) hρn
end GroundTheory.PAdicHodge.Laurent
