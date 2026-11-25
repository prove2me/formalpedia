-- Prove2me | solution 1 for GroundTheory.PAdicHodge.TeichLift.exists_pow_sub_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:18:11.605864+00:00
-- url     : https://prove2.me/submissions/c4b34c13-da4c-4b0b-9913-ccada222d13b

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ExtRobbaTeich
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_TeichLift_red___ee117558e102

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
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
open GroundTheory GroundTheory.PAdicHodge
open Ideal
open GroundTheory.PAdicHodge.TeichLift
variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L] [CharP L p]
  [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ)
namespace GroundTheory.PAdicHodge.TeichLift
theorem _root_.solution {X Y v : Γ} (hX : X ∈ T.int) (hY : Y ∈ T.int) (hv : v ∈ T.int)
    {j : ℕ} (hj : 1 ≤ j) (h : X - Y = T.π ^ j * v) :
    ∃ w ∈ T.int, X ^ p - Y ^ p = T.π ^ (j + 1) * w := by
  have hXY : T.red X = T.red Y := by
    have := congrArg T.red h
    rw [map_sub, map_mul, map_pow, red_π, zero_pow (by omega), zero_mul, sub_eq_zero] at this
    exact this
  have hG : (∑ i ∈ Finset.range p, X ^ i * Y ^ (p - 1 - i)) ∈ T.int :=
    Subring.sum_mem _ fun i _ => mul_mem (pow_mem hX _) (pow_mem hY _)
  have hGred : T.red (∑ i ∈ Finset.range p, X ^ i * Y ^ (p - 1 - i)) = 0 := by
    have : ∀ i ∈ Finset.range p, T.red (X ^ i * Y ^ (p - 1 - i)) = T.red Y ^ (p - 1) := by
      intro i hi
      rw [map_mul, map_pow, map_pow, hXY, ← pow_add]
      congr 1; have := Finset.mem_range.1 hi; omega
    rw [map_sum, Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      CharP.cast_eq_zero, zero_mul]
  obtain ⟨g, hg, hGg⟩ := T.exists_eq_π_mul _ hG hGred
  refine ⟨g * v, mul_mem hg hv, ?_⟩
  rw [← geom_sum₂_mul, hGg, h]; ring
end GroundTheory.PAdicHodge.TeichLift
