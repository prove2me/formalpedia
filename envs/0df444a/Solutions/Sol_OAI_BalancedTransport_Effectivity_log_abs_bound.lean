-- Prove2me | solution 1 for OAI.BalancedTransport.Effectivity.log_abs_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T05:25:31.856629+00:00
-- url     : https://prove2.me/submissions/12d2c0c1-8b1a-48c5-9872-0e7b65d493f2

import Mathlib
import Definitions.Def_BalancedThreeStack
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FlatBounds
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveArithmetic
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RationalAlgorithms
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveExp
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RecorderRules
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_PrefixCoding
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_BoxCoding
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Work
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_TimeRegularity
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FieldBounds
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_CompactFamilies
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_ResidualRegularity
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RhoAlgorithms
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveLog

open OAI OAI.BalancedTransport OAI.BalancedTransport.Effectivity
open Filter
open scoped Topology
theorem h44_le_num {r : ℚ} (hr : 0 < r) : (r : ℝ) ≤ (r.num.natAbs : ℝ) := by
  have h1 : r ≤ (r.num : ℚ) := by
    have hn : (0 : ℚ) ≤ r.num := by exact_mod_cast (Rat.num_pos.mpr hr).le
    have hd : (1 : ℚ) ≤ r.den := by exact_mod_cast r.den_pos
    calc r = (r.num : ℚ) / r.den := (Rat.num_div_den r).symm
      _ ≤ r.num := div_le_self hn hd
  have h2 : ((r.num : ℤ) : ℝ) = (r.num.natAbs : ℝ) := by
    rw [Nat.cast_natAbs, abs_of_nonneg (Rat.num_pos.mpr hr).le]
  rw [← h2]; exact_mod_cast h1

theorem solution {q : ℚ} (hq : 0 < q) :
    |Real.log (q : ℝ)| ≤ (q.num.natAbs + q⁻¹.num.natAbs : ℕ) := by
  have hq' : (0 : ℝ) < q := Rat.cast_pos.mpr hq
  have hA := h44_le_num hq
  have hB := h44_le_num (inv_pos.mpr hq)
  push_cast
  rw [Rat.cast_inv] at hB
  rcases le_total 1 (q : ℝ) with h | h
  · rw [abs_of_nonneg (Real.log_nonneg h)]
    have := Real.log_le_sub_one_of_pos hq'
    have : (0:ℝ) ≤ (q⁻¹.num.natAbs : ℝ) := by positivity
    linarith
  · rw [abs_of_nonpos (Real.log_nonpos hq'.le h), ← Real.log_inv]
    have := Real.log_le_sub_one_of_pos (inv_pos.mpr hq')
    have : (0:ℝ) ≤ (q.num.natAbs : ℝ) := by positivity
    linarith

