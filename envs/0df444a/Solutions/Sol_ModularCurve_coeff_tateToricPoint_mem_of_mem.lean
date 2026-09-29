-- Prove2me | solution 1 for ModularCurve.coeff_tateToricPoint_mem_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/a239299e-d7c1-5104-9fde-bffb76758fcf

import Mathlib
import Definitions.Def_ModularCurve_KatzLevelPCusps
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_coeff_tateToricPoint_mem_of_mem

set_option autoImplicit false

namespace TatePGaussAux

open ModularCurve

private theorem _root_.TatePGaussAux.sum_mem {R : Type*} [CommRing R] (B : Subring R) {ι : Type*} (s : Finset ι) (f : ι → R)
    (h : ∀ i ∈ s, f i ∈ B) : (∑ i ∈ s, f i) ∈ B :=
  Subring.sum_mem B h

p2m_export "TatePGaussAux" "sum_mem"
end TatePGaussAux

open TatePGaussAux

theorem solution
    (R : Type*) [CommRing R] (p : ℕ) (B : Subring R) (c : Rˣ) (hc : (c : R) ∈ B) (hc' : ((c⁻¹ : Rˣ) : R) ∈ B) :
    (∀ m : ℕ, 0 < m → ((ModularCurve.tateToricPoint R p c).1.coeff (m : ℤ) ∈ B ∧
      (ModularCurve.tateToricPoint R p c).2.coeff (m : ℤ) ∈ B)) ∧
    (ModularCurve.tateToricPoint R p c).1.coeff 0 = (c : R) * Ring.inverse (1 - (c : R)) ^ 2 ∧
    (ModularCurve.tateToricPoint R p c).2.coeff 0 = (c : R) ^ 2 * Ring.inverse (1 - (c : R)) ^ 3 ∧
    (∀ k : ℤ, k < 0 → (ModularCurve.tateToricPoint R p c).1.coeff k = 0 ∧ (ModularCurve.tateToricPoint R p c).2.coeff k = 0) := by
  refine ⟨fun m hm => ⟨?_, ?_⟩, ?_, ?_, fun k hk => ⟨?_, ?_⟩⟩
  · rw [ModularCurve.tateToricPoint_fst, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_mk, if_neg hm.ne']
    refine B.sub_mem (B.sum_mem fun d _ => ?_) (B.mul_mem (by exact_mod_cast natCast_mem B 2) ?_)
    · split_ifs
      · exact B.mul_mem (natCast_mem B _) (B.add_mem (B.pow_mem hc _) (B.pow_mem hc' _))
      · exact B.zero_mem
    · split_ifs
      · exact B.sum_mem fun e _ => natCast_mem B _
      · exact B.zero_mem
  · rw [ModularCurve.tateToricPoint_snd, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_mk, if_neg hm.ne']
    refine B.add_mem (B.sum_mem fun d _ => ?_) ?_
    · split_ifs
      · exact B.sub_mem (B.mul_mem (natCast_mem B _) (B.pow_mem hc _)) (B.mul_mem (natCast_mem B _) (B.pow_mem hc' _))
      · exact B.zero_mem
    · split_ifs
      · exact B.sum_mem fun e _ => natCast_mem B _
      · exact B.zero_mem
  · rw [ModularCurve.tateToricPoint_fst, show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff,
      PowerSeries.coeff_mk, if_pos rfl]
  · rw [ModularCurve.tateToricPoint_snd, show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff,
      PowerSeries.coeff_mk, if_pos rfl]
  · rw [ModularCurve.tateToricPoint_fst]; exact ModularCurve.ofPowerSeries_coeff_of_neg _ hk
  · rw [ModularCurve.tateToricPoint_snd]; exact ModularCurve.ofPowerSeries_coeff_of_neg _ hk

end S_ModularCurve_coeff_tateToricPoint_mem_of_mem
end P2MW
export P2MW.S_ModularCurve_coeff_tateToricPoint_mem_of_mem (solution)
