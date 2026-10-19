-- Prove2me | solution 1 for OAI.BalancedTransport.Coding.stream_mem_interior
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T05:13:34.442663+00:00
-- url     : https://prove2.me/submissions/f985e845-e3c6-4044-88b5-a3f634aa9e47

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/PrefixCoding.lean:L283-L296
-- (upload_full_project.md Phase 4): solution for node OAI.BalancedTransport.Coding.stream_mem_interior. The node keeps its source
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

theorem stream_mem_unit {B : ℕ} (digit : S → Fin B) (s : Stream' S) :
    stream digit s ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨Real.ofDigits_nonneg _, Real.ofDigits_le_one _⟩

end BalancedTransport.Coding
end

noncomputable section
namespace BalancedTransport.Coding
variable {S : Type*}
open Stream'

theorem stream_cons {B : ℕ} (digit : S → Fin B) (a : S) (s : Stream' S) :
    stream digit (a :: s) = (B : ℝ)⁻¹ * ((digit a : ℝ) + stream digit s) := by
  have hh := Real.ofDigits_eq_sum_add_ofDigits (fun n => digit ((a :: s) n)) 1
  simpa [stream, Real.ofDigitsTerm, Stream'.cons, mul_add, mul_comm] using hh

theorem stream_mem_interior {B : ℕ} (hB : 0 < B) (digit : S → Fin B)
    (hlo : ∀ a, 0 < (digit a : ℝ)) (hhi : ∀ a, (digit a : ℝ) + 1 < B)
    (s : Stream' S) : stream digit s ∈ Set.Ioo (0 : ℝ) 1 := by
  have hb : 0 < (B : ℝ) := Nat.cast_pos.mpr hB
  have hs : s = s.head :: s.tail := by
    funext n
    cases n <;> rfl
  rw [hs, stream_cons]
  have htail := stream_mem_unit digit s.tail
  constructor
  · exact mul_pos (inv_pos.mpr hb) (by linarith [hlo s.head, htail.1])
  · rw [mul_comm, ← div_eq_mul_inv]
    apply (div_lt_one hb).mpr
    linarith [hhi s.head, htail.2]

end BalancedTransport.Coding
end

end OAI

-- ---- platform node ----
open OAI OAI.BalancedTransport OAI.BalancedTransport.Coding
open Stream'


theorem solution : type_of% @_root_.OAI.BalancedTransport.Coding.stream_mem_interior := @_root_.OAI.BalancedTransport.Coding.stream_mem_interior
