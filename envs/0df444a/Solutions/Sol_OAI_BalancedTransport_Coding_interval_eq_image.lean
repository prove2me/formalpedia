-- Prove2me | solution 1 for OAI.BalancedTransport.Coding.interval_eq_image
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T05:11:53.89799+00:00
-- url     : https://prove2.me/submissions/f626724f-7530-4244-9bb3-80f53245aea6

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/PrefixCoding.lean:L193-L208
-- (upload_full_project.md Phase 4): solution for node OAI.BalancedTransport.Coding.interval_eq_image. The node keeps its source
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

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.PrefixCoding ----
namespace OAI

noncomputable section
namespace BalancedTransport.Recorder
open Stream'
variable {Q Γ : Type*}

namespace Exec

variable {M : Machine Q Γ}

end Exec

variable (M : Machine Q Γ)
open Letter Control

end BalancedTransport.Recorder
end

noncomputable section
namespace BalancedTransport.Coding
variable {S : Type*}

theorem prefix_mem_interval {r : ℝ} (hr : 0 ≤ r) (digit : S → ℝ)
    (w : List S) {z : ℝ} (hz : z ∈ Set.Icc (0 : ℝ) 1) :
    prefixPoint r digit w z ∈ interval r digit w := by
  have hpow := pow_nonneg hr w.length
  dsimp [prefixPoint, interval]
  constructor
  · linarith [mul_nonneg hpow hz.1]
  · nlinarith [hz.2]

theorem interval_eq_image {r : ℝ} (hr : 0 < r) (digit : S → ℝ) (w : List S) :
    interval r digit w = prefixPoint r digit w '' Set.Icc (0 : ℝ) 1 := by
  ext y
  constructor
  · intro hy
    have hp : 0 < r ^ w.length := pow_pos hr _
    refine ⟨(y - word r digit w) / r ^ w.length, ?_, ?_⟩
    · constructor
      · exact div_nonneg (sub_nonneg.mpr hy.1) hp.le
      · apply (div_le_one hp).mpr
        exact sub_le_iff_le_add.mpr (by simpa [add_comm] using hy.2)
    · dsimp [prefixPoint]
      field_simp
      ring
  · rintro ⟨z, hz, rfl⟩
    exact prefix_mem_interval hr.le digit w hz

end BalancedTransport.Coding
end

noncomputable section
namespace BalancedTransport.Coding
variable {S : Type*}
open Stream'

end BalancedTransport.Coding
end

end OAI

-- ---- platform node ----
open OAI OAI.BalancedTransport OAI.BalancedTransport.Coding


theorem solution : type_of% @_root_.OAI.BalancedTransport.Coding.interval_eq_image := @_root_.OAI.BalancedTransport.Coding.interval_eq_image
