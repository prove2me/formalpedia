-- Prove2me | solution 1 for OAI.FourierBridge.derivative_scale_absorption
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:29:59.624776+00:00
-- url     : https://prove2.me/submissions/bd68a2c8-92bb-482b-a2ca-4137e21a8fb2

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_ExponentialSmoothing
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles

set_option autoImplicit false
open OAI
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open scoped ContDiff Manifold
open OAI.FourierBridge
namespace OAI.FourierBridge
theorem _root_.solution
    (R u m H CF : ℝ) (A n j : ℕ)
    (hR : 0 ≤ R) (hm : 0 < m)
    (_hH : 0 ≤ H) (hCF : 0 ≤ CF)
    (hu : 0 ≤ u) (hlower : m * (1 + R) ≤ 1 + u)
    (hj : j ≤ n) :
    m ^ (A + n) * (1 + R) ^ A *
      ((j.factorial : ℝ) * (CF / (1 + u) ^ (A + n)) *
        (H ^ 2 * (1 + R)) ^ j) ≤
      (j.factorial : ℝ) * CF * (H ^ 2) ^ j := by
  have hRp : 1 ≤ 1 + R := by linarith
  have hden : 0 < (1 + u) ^ (A + n) := by positivity
  have hpowR : (1 + R) ^ (A + j) ≤ (1 + R) ^ (A + n) :=
    pow_le_pow_right₀ hRp (Nat.add_le_add_left hj A)
  have hscale : m ^ (A + n) * (1 + R) ^ A * (1 + R) ^ j ≤
      (1 + u) ^ (A + n) := by
    calc
      m ^ (A + n) * (1 + R) ^ A * (1 + R) ^ j =
          m ^ (A + n) * (1 + R) ^ (A + j) := by rw [pow_add]; ring
      _ ≤ m ^ (A + n) * (1 + R) ^ (A + n) :=
        mul_le_mul_of_nonneg_left hpowR (by positivity)
      _ = (m * (1 + R)) ^ (A + n) := by rw [mul_pow]
      _ ≤ (1 + u) ^ (A + n) := by gcongr
  let Q : ℝ := (j.factorial : ℝ) * CF * (H ^ 2) ^ j
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hQscale : Q * (m ^ (A + n) * (1 + R) ^ A * (1 + R) ^ j) ≤
      Q * (1 + u) ^ (A + n) := mul_le_mul_of_nonneg_left hscale hQ
  calc
    m ^ (A + n) * (1 + R) ^ A *
        ((j.factorial : ℝ) * (CF / (1 + u) ^ (A + n)) *
          (H ^ 2 * (1 + R)) ^ j) =
      Q * (m ^ (A + n) * (1 + R) ^ A * (1 + R) ^ j) /
        (1 + u) ^ (A + n) := by dsimp [Q]; rw [mul_pow]; ring
    _ ≤ Q := (div_le_iff₀ hden).mpr (by simpa [mul_comm, mul_left_comm, mul_assoc] using hQscale)
    _ = (j.factorial : ℝ) * CF * (H ^ 2) ^ j := rfl
end OAI.FourierBridge
