-- Prove2me | solution 1 for GlobalTheory.MinorInt.weight_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:58:06.522909+00:00
-- url     : https://prove2.me/submissions/3b10c83e-80e2-4540-a0a4-b1fa50fb6004

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_LintegralMulRight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex MeasureTheory
open scoped ComplexConjugate ComplexOrder MatrixOrder
open GlobalTheory GlobalTheory.MinorInt
namespace GlobalTheory.MinorInt
theorem _root_.solution {s u M : ℝ} (hs : 0 < s) (h : 1 / 2 ≤ s ^ 2 * u) (hM : u ≤ M) (p q k : ℕ) :
    s ^ (2 * q) * (s ^ (2 * (p + q) + k))⁻¹ ≤ (2 * u) ^ p * (1 + 2 * M) ^ k := by
  have h1 : s⁻¹ ^ 2 ≤ 2 * u := by
    rw [inv_pow, inv_le_iff_one_le_mul₀ (by positivity)]; linarith
  have h2 : s⁻¹ ≤ 1 + 2 * M := by nlinarith [sq_nonneg (s⁻¹ - 1), inv_pos.2 hs]
  have h3 : s ^ (2 * q) * (s ^ (2 * (p + q) + k))⁻¹ = (s⁻¹ ^ 2) ^ p * s⁻¹ ^ k := by
    simp only [inv_pow]; field_simp; ring
  rw [h3]
  have : 0 ≤ 2 * u := le_trans (by positivity) h1
  gcongr
end GlobalTheory.MinorInt
