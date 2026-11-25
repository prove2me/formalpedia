-- Prove2me | solution 1 for GroundTheory.PAdicHodge.norm_normTrace_cycl_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:39:35.484811+00:00
-- url     : https://prove2.me/submissions/abf4db1a-52b3-4acb-b139-8057997be15e

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicField
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_NormNatCastPrime
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicTower
import Theorems.Thm_GroundTheory_PAdicHodge_cyclRadius_le_one
import Theorems.Thm_GroundTheory_PAdicHodge_inv_p_le_cyclRadius
import Theorems.Thm_GroundTheory_PAdicHodge_cyclRadius_pos
import Theorems.Thm_GroundTheory_PAdicHodge_norm_normTrace_cycl_mul_le

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
    (hx : x ∈ cycl p m) : ‖normTrace (cycl p n) x‖ ≤ p * ‖x‖ := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  have h := norm_normTrace_cycl_mul_le hn hnm hx
  have hr := cyclRadius_pos (p := p) j
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have h1 : ‖normTrace (cycl p (j + 1)) x‖ * cyclRadius p (j + 1) ≤ ‖x‖ :=
    h.trans (mul_le_of_le_one_right (norm_nonneg _) (cyclRadius_le_one _))
  have h2 : (p : ℝ)⁻¹ ≤ cyclRadius p (j + 1) := inv_p_le_cyclRadius j
  calc ‖normTrace (cycl p (j + 1)) x‖ = p * (‖normTrace (cycl p (j + 1)) x‖ * (p : ℝ)⁻¹) := by
        field_simp
    _ ≤ p * (‖normTrace (cycl p (j + 1)) x‖ * cyclRadius p (j + 1)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 (norm_nonneg _)) hp0.le
    _ ≤ p * ‖x‖ := mul_le_mul_of_nonneg_left h1 hp0.le
end GroundTheory.PAdicHodge
