-- Prove2me | solution 1 for GroundTheory.PAdicHodge.norm_normTrace_cycl_succ_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:58:37.371041+00:00
-- url     : https://prove2.me/submissions/e8017502-09c2-4cdf-ab3b-5a2f4a9537b2

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicField
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_NormNatCastPrime
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicTower
import Theorems.Thm_GroundTheory_PAdicHodge_norm_sub_one_eq_cyclRadius
import Theorems.Thm_GroundTheory_PAdicHodge_cyclRadius_le_one
import Theorems.Thm_GroundTheory_PAdicHodge_cyclRadius_pos
import Theorems.Thm_GroundTheory_PAdicHodge_adjoin_sub_one_eq_cycl
import Theorems.Thm_GroundTheory_PAdicHodge_exists_eq_sum_pow_of_adjoin_eq
import Theorems.Thm_GroundTheory_PAdicHodge_norm_mul_pow_le_norm_sum
import Theorems.Thm_GroundTheory_PAdicHodge_normTrace_cycl_sub_one_pow
import Theorems.Thm_GroundTheory_PAdicHodge_exists_isPrimitiveRoot
import Theorems.Thm_GroundTheory_PAdicHodge_normTrace_mul_of_mem
import Theorems.Thm_GroundTheory_PAdicHodge_normTrace_sum


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
theorem _root_.solution {k : ℕ} (hk : 1 ≤ k) {x : PadicAlgCl p}
    (hx : x ∈ cycl p (k + 1)) :
    ‖normTrace (cycl p k) x‖ * cyclRadius p (k + 1) ^ (p - 1) ≤ ‖x‖ := by
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot (p := p) (k + 1)
  obtain ⟨b, hb, rfl⟩ := exists_eq_sum_pow_of_adjoin_eq hk (adjoin_sub_one_eq_cycl hζ) hx
  have horth := norm_mul_pow_le_norm_sum hk hζ hb
  set x := ∑ i ∈ Finset.range p, b i * (ζ - 1) ^ i
  have hr := cyclRadius_pos (p := p) k
  have hrpow : 0 < cyclRadius p (k + 1) ^ (p - 1) := pow_pos hr _
  have hrad : ‖ζ - 1‖ = cyclRadius p (k + 1) := norm_sub_one_eq_cyclRadius hζ
  have htr : normTrace (cycl p k) x = ∑ i ∈ Finset.range p, b i * (-1) ^ i := by
    rw [normTrace_sum]
    exact Finset.sum_congr rfl fun i hi => by
      rw [normTrace_mul_of_mem _ (hb i), normTrace_cycl_sub_one_pow hk hζ (Finset.mem_range.1 hi)]
  rw [htr, ← le_div_iff₀ hrpow]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
    (div_nonneg (norm_nonneg _) hrpow.le) fun i hi => ?_
  rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, mul_one, le_div_iff₀ hrpow]
  calc ‖b i‖ * cyclRadius p (k + 1) ^ (p - 1) ≤ ‖b i‖ * ‖ζ - 1‖ ^ i := by
        rw [hrad]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hr.le (cyclRadius_le_one _)
          (by have := Finset.mem_range.1 hi; omega)) (norm_nonneg _)
    _ ≤ ‖x‖ := horth i hi
end GroundTheory.PAdicHodge
