-- Prove2me | solution 1 for GlobalTheory.sum_norm_add_sq_le_of_bounds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:11:51.988124+00:00
-- url     : https://prove2.me/submissions/17149ba3-455c-483b-9eb7-eacc5f19d93f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SumNormAddSqLeOfBounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open scoped InnerProductSpace
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (V ι : Type) [NormedAddCommGroup V] [Fintype ι] (u v : ι → V) (c s N : ℝ), 0 ≤ c → 0 ≤ s → 0 ≤ N → ∑ i, ‖u i‖ ^ 2 ≤ c ^ 2 * N → ∑ i, ‖v i‖ ^ 2 ≤ s ^ 2 * N → ∑ i, ‖u i + v i‖ ^ 2 ≤ (c + s) ^ 2 * N := by
  intro V ι _ _ u v c s N hc hs hN hu hv
  have hcs : (∑ i, ‖u i‖ * ‖v i‖) ^ 2 ≤ (∑ i, ‖u i‖ ^ 2) * ∑ i, ‖v i‖ ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have hv0 : 0 ≤ ∑ i, ‖v i‖ ^ 2 := Finset.sum_nonneg fun i _ => by positivity
  have h1 : (∑ i, ‖u i‖ * ‖v i‖) ^ 2 ≤ (c * s * N) ^ 2 := by
    calc _ ≤ _ := hcs
      _ ≤ (c ^ 2 * N) * (s ^ 2 * N) := mul_le_mul hu hv hv0 (by positivity)
      _ = _ := by ring
  have h2 : ∑ i, ‖u i‖ * ‖v i‖ ≤ c * s * N :=
    (pow_le_pow_iff_left₀ (Finset.sum_nonneg fun i _ => by positivity) (by positivity)
      two_ne_zero).1 h1
  have h3 : ∑ i, ‖u i + v i‖ ^ 2 ≤ ∑ i, (‖u i‖ ^ 2 + 2 * (‖u i‖ * ‖v i‖) + ‖v i‖ ^ 2) := by
    refine Finset.sum_le_sum fun i _ => ?_
    calc ‖u i + v i‖ ^ 2 ≤ (‖u i‖ + ‖v i‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 2
      _ = _ := by ring
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] at h3
  nlinarith
end GlobalTheory
