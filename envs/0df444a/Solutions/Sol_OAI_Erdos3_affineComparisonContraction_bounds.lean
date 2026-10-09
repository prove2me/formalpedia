-- Prove2me | solution 1 for OAI.Erdos3.affineComparisonContraction_bounds
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T17:43:52.68978+00:00
-- url     : https://prove2.me/submissions/6689e0b7-34bd-4ff0-9162-081b2dd5531b

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B090

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.GeometricSpectralBudgets
namespace OAI

section

namespace Erdos3

theorem geometric_tail_after_cutoff {ε P κ B : ℝ} {r : ℕ}
    (hε : 0 < ε) (hκ0 : 0 ≤ κ) (hκhalf : κ ≤ 1 / 2)
    (hB0 : 0 ≤ B) (hB : B ≤ Real.exp P)
    (hr : CyclicCrootSisask.spectralIterations ε P ≤ r) :
    κ ^ r * B ≤ ε / 16 := by
  have hp : κ ^ r ≤ (1 / 2 : ℝ) ^ CyclicCrootSisask.spectralIterations ε P :=
    (pow_le_pow_left₀ hκ0 hκhalf r).trans
      (pow_le_pow_of_le_one (by norm_num) (by norm_num) hr)
  exact (mul_le_mul hp hB hB0 (by positivity)).trans
    (CyclicCrootSisask.half_pow_spectralIterations_mul_exp_le hε)

theorem inverse_power_low_level_bound {t κ A B L : ℝ} {d e : ℕ}
    (ht : 2 ≤ t) (hL : 0 ≤ L)
    (hAB : A ^ 2 * B ^ 2 ≤ L * t ^ d) (hκ : κ ≤ (t ^ (d + e))⁻¹) :
    κ * A ^ 2 * B ^ 2 ≤ (1 / 2 : ℝ) ^ e * L := by
  have ht0 : 0 < t := by linarith
  have hi : t⁻¹ ≤ (1 / 2 : ℝ) := by
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) ht
  calc
    κ * A ^ 2 * B ^ 2 = κ * (A ^ 2 * B ^ 2) := by ring
    _ ≤ (t ^ (d + e))⁻¹ * (L * t ^ d) :=
      mul_le_mul hκ hAB (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (by positivity)
    _ = L * ((t ^ d)⁻¹ * t ^ d) * (t ^ e)⁻¹ := by rw [pow_add, mul_inv_rev]; ring
    _ = L * (t⁻¹) ^ e := by rw [inv_mul_cancel₀ (pow_ne_zero _ ht0.ne'), mul_one, inv_pow]
    _ ≤ L * (1 / 2 : ℝ) ^ e :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (inv_nonneg.mpr ht0.le) hi e) hL
    _ = (1 / 2 : ℝ) ^ e * L := mul_comm _ _

theorem low_level_after_power_cutoff {ε P t κ A B L : ℝ} {d e : ℕ}
    (hε : 0 < ε) (ht : 2 ≤ t) (hL0 : 0 ≤ L) (hL : L ≤ Real.exp P)
    (hAB : A ^ 2 * B ^ 2 ≤ L * t ^ d) (hκ : κ ≤ (t ^ (d + e))⁻¹)
    (he : CyclicCrootSisask.spectralIterations ε P ≤ e) :
    κ * A ^ 2 * B ^ 2 ≤ ε / 16 := by
  exact (inverse_power_low_level_bound ht hL0 hAB hκ).trans
    (geometric_tail_after_cutoff hε (by norm_num) (by norm_num) hL0 hL he)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.PrimeCoordinateCells
namespace OAI

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

theorem affineComparisonContraction_bounds {ξ P : ℝ} (hξ : 0 < ξ) (hP : 0 ≤ P) :
    0 < affineComparisonContraction ξ P ∧ affineComparisonContraction ξ P ≤ 1 / 2 ∧
    affineComparisonContraction ξ P * (8 * (1 + 2) * (P + 2)) ^ 2 * (16 * (P + 2)) ^ 2 ≤ ξ / 16 := by
  have ht : 2 ≤ P + 2 := by linarith
  have hthreshold : 2 ≤ affineComparisonPrimeThreshold ξ P := by
    unfold affineComparisonPrimeThreshold
    calc
      2 ≤ P + 2 := ht
      _ = (P + 2) ^ 1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ (by linarith) (by omega)
  have hp : 0 < affineComparisonPrimeThreshold ξ P := by linarith
  refine ⟨inv_pos.mpr hp, ?_, ?_⟩
  · simpa only [affineComparisonContraction, one_div] using
      one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hthreshold
  · have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have hc : (147456 : ℝ) ≤ Real.exp 18 := by
      calc
        147456 ≤ (2 : ℝ) ^ 18 := by norm_num
        _ ≤ (Real.exp 1) ^ 18 := pow_le_pow_left₀ (by norm_num) htwo 18
        _ = _ := by rw [← Real.exp_nat_mul]; norm_num
    exact low_level_after_power_cutoff (d := 4) hξ ht (by norm_num) hc
      (by ring_nf; exact le_rfl) le_rfl le_rfl

end Erdos3

end

section

namespace Erdos3

open scoped Classical

end Erdos3

end

section

namespace Erdos3

open scoped Classical

end Erdos3

end

section

namespace Erdos3

open scoped Classical

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

end OAI

end

theorem solution : type_of% @OAI.Erdos3.affineComparisonContraction_bounds := @OAI.Erdos3.affineComparisonContraction_bounds
