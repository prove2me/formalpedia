-- Prove2me | solution 1 for GlobalTheory.BK.mem_span_l_pow_S_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:03:25.241796+00:00
-- url     : https://prove2.me/submissions/5a75cc45-c3ec-4b48-b948-7cfb18f52e5b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_SndDualLiftAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MemSpanLPowSIff
import Theorems.Thm_GlobalTheory_BK_mem_S


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.BK PowerSeries Filter Topology
open GlobalTheory GlobalTheory.BK
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] (l e : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K]
namespace GlobalTheory.BK
theorem _root_.solution (n : ℕ) (f : S O K e) :
    f ∈ Ideal.span {(l : S O K e)} ^ n ↔
      ∀ m, ‖coeff m (f : K⟦X⟧)‖ * wS K e m ≤ ‖(l : K)‖ ^ n := by
  have h2 : (((l : S O K e) : K⟦X⟧)) = C (l : K) := by simp
  have hl : 0 < ‖(l : K)‖ ^ n := pow_pos (norm_pos_iff.2 (l_ne_zero l)) n
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨g, rfl⟩ m
    rw [Subalgebra.coe_mul, Subalgebra.coe_pow, h2, ← map_pow, coeff_C_mul, norm_mul, norm_pow,
      mul_assoc]
    exact mul_le_of_le_one_right hl.le ((mem_S.1 g.2).1 m)
  · intro h
    have hc : ∀ m, ‖coeff m (C (((l : K) ^ n)⁻¹) * (f : K⟦X⟧))‖ * wS K e m =
        (‖(l : K)‖ ^ n)⁻¹ * (‖coeff m (f : K⟦X⟧)‖ * wS K e m) := fun m => by
      rw [coeff_C_mul, norm_mul, norm_inv, norm_pow, mul_assoc]
    refine ⟨⟨C (((l : K) ^ n)⁻¹) * (f : K⟦X⟧), mem_S.2 ⟨fun m => ?_, ?_⟩⟩, Subtype.ext ?_⟩
    · rw [hc, inv_mul_le_iff₀ hl, mul_one]
      exact h m
    · simp only [hc]
      simpa using (mem_S.1 f.2).2.const_mul (‖(l : K)‖ ^ n)⁻¹
    · rw [Subalgebra.coe_mul, Subalgebra.coe_pow, h2, ← map_pow, ← mul_assoc, ← map_mul,
        mul_inv_cancel₀ (pow_ne_zero _ (l_ne_zero l)), map_one, one_mul]
end GlobalTheory.BK
