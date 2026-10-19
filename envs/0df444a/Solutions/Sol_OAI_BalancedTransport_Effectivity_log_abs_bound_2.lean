-- Prove2me | solution 2 for OAI.BalancedTransport.Effectivity.log_abs_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T05:34:41.502665+00:00
-- url     : https://prove2.me/submissions/669ab0df-3cb7-48c8-b4f9-d3f2841f6129

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/EffectiveLog.lean:L135-L149
-- (upload_full_project.md Phase 4): solution for node OAI.BalancedTransport.Effectivity.log_abs_bound. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
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

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.RhoAlgorithms ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity
open Polynomial
open scoped NNReal

lemma rat_abs_le_num (q : ℚ) : |(q : ℝ)| ≤ q.num.natAbs := by
  have hden : (1 : ℝ) ≤ q.den := by exact_mod_cast q.pos
  have he : (q : ℝ) = (q.num : ℝ) / (q.den : ℝ) := by
    exact_mod_cast (Rat.num_div_den q).symm
  rw [he, abs_div, abs_of_pos (by positivity : (0 : ℝ) < q.den)]
  have ha : ((q.num.natAbs : ℕ) : ℝ) = |(q.num : ℝ)| := by
    simpa only [Int.cast_natCast, Int.cast_abs] using
      congrArg (fun a : ℤ => (a : ℝ)) (Int.natCast_natAbs q.num)
  rw [← ha]
  exact (div_le_iff₀ (by positivity : (0 : ℝ) < q.den)).mpr
    (le_mul_of_one_le_right (by positivity) hden)

end BalancedTransport.Effectivity
end

end OAI

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.EffectiveLog ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity
open Filter
open scoped Topology

lemma log_abs_bound {q : ℚ} (hq : 0 < q) :
    |Real.log (q : ℝ)| ≤ (q.num.natAbs + q⁻¹.num.natAbs : ℕ) := by
  have hq' : (0 : ℝ) < q := Rat.cast_pos.mpr hq
  have h₀ := Real.log_le_sub_one_of_pos hq'
  have h₁ := Real.log_le_sub_one_of_pos (inv_pos.mpr hq')
  rw [Real.log_inv] at h₁
  have ha := rat_abs_le_num q
  have hb := rat_abs_le_num q⁻¹
  rw [Rat.cast_inv] at hb
  rw [abs_of_pos hq'] at ha
  rw [abs_of_pos (inv_pos.mpr hq')] at hb
  apply abs_le.mpr
  push_cast
  constructor <;> linarith [Nat.cast_nonneg q.num.natAbs (α := ℝ),
    Nat.cast_nonneg q⁻¹.num.natAbs (α := ℝ)]

end BalancedTransport.Effectivity
end

end OAI

-- ---- platform node ----
open OAI OAI.BalancedTransport OAI.BalancedTransport.Effectivity
open Filter
open scoped Topology


theorem solution : type_of% @_root_.OAI.BalancedTransport.Effectivity.log_abs_bound := @_root_.OAI.BalancedTransport.Effectivity.log_abs_bound
