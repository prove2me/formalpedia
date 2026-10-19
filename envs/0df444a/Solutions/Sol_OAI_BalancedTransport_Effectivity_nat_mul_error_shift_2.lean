-- Prove2me | solution 2 for OAI.BalancedTransport.Effectivity.nat_mul_error_shift
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T05:28:46.356597+00:00
-- url     : https://prove2.me/submissions/6f88b851-1184-403c-a723-5c7dc68e4904

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/RelativeForce.lean:L84-L97
-- (upload_full_project.md Phase 4): solution for node OAI.BalancedTransport.Effectivity.nat_mul_error_shift. The node keeps its source
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

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.RelativeForce ----
namespace OAI

noncomputable section
namespace BalancedTransport.Geometry

end BalancedTransport.Geometry
end

noncomputable section
namespace BalancedTransport.Effectivity

lemma error_nonneg (n : ℕ) : 0 ≤ error n := by unfold error; positivity

lemma error_add (n k : ℕ) : error (n + k) = error n * error k := pow_add _ _ _

lemma nat_mul_error_shift (n k : ℕ) : (k : ℝ) * error (n + k) ≤ error n := by
  have hk : (k : ℝ) ≤ (2 : ℝ) ^ k := by
    induction k with
    | zero => norm_num
    | succ k ih =>
      rw [Nat.cast_succ, pow_succ]
      have hp : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
      linarith
  have he : (k : ℝ) * error k ≤ 1 := by
    unfold error
    rw [inv_pow, ← div_eq_mul_inv]
    exact (div_le_one (by positivity)).mpr hk
  rw [error_add]
  nlinarith [mul_le_mul_of_nonneg_left he (error_nonneg n)]

end BalancedTransport.Effectivity
end

end OAI

-- ---- platform node ----
open OAI OAI.BalancedTransport OAI.BalancedTransport.Effectivity


theorem solution : type_of% @_root_.OAI.BalancedTransport.Effectivity.nat_mul_error_shift := @_root_.OAI.BalancedTransport.Effectivity.nat_mul_error_shift
