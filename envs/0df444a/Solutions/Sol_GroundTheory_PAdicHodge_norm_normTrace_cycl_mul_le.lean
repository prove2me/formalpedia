-- Prove2me | solution 1 for GroundTheory.PAdicHodge.norm_normTrace_cycl_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:30:02.934678+00:00
-- url     : https://prove2.me/submissions/78acf85b-aaba-4fe6-b8c4-9e7ba8d15d8a

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicField
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_NormNatCastPrime
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicTower
import Theorems.Thm_GroundTheory_PAdicHodge_cyclRadius_pos
import Theorems.Thm_GroundTheory_PAdicHodge_cyclRadius_succ_pow_pred
import Theorems.Thm_GroundTheory_PAdicHodge_norm_normTrace_cycl_succ_mul_le
import Theorems.Thm_GroundTheory_PAdicHodge_cycl_mono
import Theorems.Thm_GroundTheory_PAdicHodge_normTrace_mem
import Theorems.Thm_GroundTheory_PAdicHodge_normTrace_normTrace_of_le
import Theorems.Thm_GroundTheory_PAdicHodge_normTrace_of_mem


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
open IntermediateField Polynomial Module
noncomputable section
variable {p : ℕ} [Fact p.Prime]
namespace GroundTheory.PAdicHodge
theorem _root_.solution {n m : ℕ} (hn : 1 ≤ n) (hnm : n ≤ m) {x : PadicAlgCl p}
    (hx : x ∈ cycl p m) :
    ‖normTrace (cycl p n) x‖ * cyclRadius p n ≤ ‖x‖ * cyclRadius p m := by
  induction m, hnm using Nat.le_induction generalizing x with
  | base => rw [normTrace_of_mem _ hx]
  | succ m hnm ih =>
    have hm : 1 ≤ m := le_trans hn hnm
    rw [← normTrace_normTrace_of_le (cycl_mono hnm) x]
    have h1 := ih (normTrace_mem (cycl p m) x)
    have h2 := norm_normTrace_cycl_succ_mul_le hm hx
    rw [cyclRadius_succ_pow_pred hm, mul_div_assoc', div_le_iff₀ (cyclRadius_pos (p := p) m)] at h2
    exact h1.trans h2
end GroundTheory.PAdicHodge
