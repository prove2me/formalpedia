-- Prove2me | solution 1 for GlobalTheory.BK.derivative_mem_S
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:07:38.81731+00:00
-- url     : https://prove2.me/submissions/a08bc349-e5de-4abf-b0cc-937a9b80e349

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_NormPowLeNormFactorial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.BK
open PowerSeries Filter Topology
variable (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K]
variable {O K}
namespace GlobalTheory.BK
theorem _root_.solution {e : ℕ} {f : K⟦X⟧} (hf : f ∈ S O K e) :
    PowerSeries.derivative K f ∈ S O K e := by
  have key : ∀ n, ‖coeff n (PowerSeries.derivative K f)‖ * wS K e n ≤
      ‖coeff (n + 1) f‖ * wS K e (n + 1) := fun n => by
    rw [coeff_derivative, norm_mul, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    unfold wS
    rw [← norm_mul, ← Nat.cast_succ, ← Nat.cast_mul]
    refine norm_natCast_le_of_dvd ?_
    rw [Nat.succ_div]
    split_ifs with h
    · rw [Nat.factorial_succ]
      refine Nat.mul_dvd_mul_right ?_ _
      have := Nat.succ_div (a := n) (b := e)
      rw [if_pos h] at this
      rw [← this]
      exact Nat.div_dvd_of_dvd h
    · exact Dvd.intro_left _ rfl
  exact ⟨fun n => (key n).trans (hf.1 _),
    squeeze_zero (fun n => mul_nonneg (norm_nonneg _) (wS_nonneg e n)) key
      (hf.2.comp (tendsto_add_atTop_nat 1))⟩
end GlobalTheory.BK
