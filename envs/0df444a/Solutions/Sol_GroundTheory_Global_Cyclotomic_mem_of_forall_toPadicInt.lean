-- Prove2me | solution 1 for GroundTheory.Global.Cyclotomic.mem_of_forall_toPadicInt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:12:33.164145+00:00
-- url     : https://prove2.me/submissions/ba86929d-6115-4cd3-b903-3dc39f5ccca4

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_ProfinitePadic
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_ClosedSubgroups
import Theorems.Thm_GroundTheory_Global_Cyclotomic_toPadicInt_primeIdempotent
import Theorems.Thm_GroundTheory_Global_Cyclotomic_continuous_ofPadics
import Theorems.Thm_GroundTheory_Global_Cyclotomic_padicEquiv_apply
import Theorems.Thm_GroundTheory_Global_Cyclotomic_padicEquiv_symm_apply
import Theorems.Thm_GroundTheory_Global_Cyclotomic_val_unitsPadicEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.Cyclotomic.padicEquiv_apply
attribute [local simp] GroundTheory.Global.Cyclotomic.padicEquiv_symm_apply
attribute [local simp] GroundTheory.Global.Cyclotomic.val_unitsPadicEquiv_apply



set_option autoImplicit false
open Filter Topology
open scoped GroundTheory.LocalField.Abstract
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Cyclotomic
open GroundTheory.LocalField.Abstract
namespace GroundTheory.Global.Cyclotomic
theorem _root_.solution (H : AddSubgroup ℤ̂) (hH : IsClosed (H : Set ℤ̂)) {y : ℤ̂}
    (hy : ∀ q : Nat.Primes, ∃ h ∈ H, toPadicInt q h = toPadicInt q y) : y ∈ H := by
  choose h hh hhy using hy
  let s : Finset Nat.Primes → ℤ̂ := fun F => ∑ q ∈ F, primeIdempotent q * h q
  have hs : ∀ F, s F ∈ H := fun F =>
    H.sum_mem fun q _ => mul_mem_of_isClosed' H hH (hh q) _
  have hcomp : ∀ (F : Finset Nat.Primes) (q' : Nat.Primes), toPadicInt q' (s F) = if q' ∈ F then toPadicInt q' y else 0 := by
    intro F q'
    simp only [s, map_sum, map_mul, toPadicInt_primeIdempotent]
    split_ifs with hq'
    · rw [Finset.sum_eq_single q', Pi.single_eq_same, one_mul, hhy]
      · intro b _ hb
        rw [Pi.single_eq_of_ne hb.symm, zero_mul]
      · intro h'; exact absurd hq' h'
    · refine Finset.sum_eq_zero fun b hb => ?_
      rw [Pi.single_eq_of_ne (by rintro rfl; exact hq' hb), zero_mul]
  have ht : Tendsto (fun F => toPadics (s F)) atTop (𝓝 (toPadics y)) := by
    rw [tendsto_pi_nhds]
    intro q'
    refine tendsto_nhds_of_eventually_eq ?_
    filter_upwards [eventually_ge_atTop {q'}] with F hF
    rw [toPadics_apply, hcomp, if_pos (Finset.singleton_subset_iff.1 hF), toPadics_apply]
  have ht' := (continuous_ofPadics.tendsto _).comp ht
  simp only [Function.comp_def, ofPadics_toPadics] at ht'
  exact hH.mem_of_tendsto ht' (Eventually.of_forall hs)
end GroundTheory.Global.Cyclotomic
