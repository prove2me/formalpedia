-- Prove2me | solution 1 for OAI.BalancedTransport.Coding.prefix_gap
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T05:14:52.865126+00:00
-- url     : https://prove2.me/submissions/68336645-cc7d-43b7-b03d-4d9c797871f5

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/PrefixCoding.lean:L317-L336
-- (upload_full_project.md Phase 4): solution for node OAI.BalancedTransport.Coding.prefix_gap. The node keeps its source
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
import Theorems.Thm_OAI_BalancedTransport_Coding_interval_eq_image

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

theorem word_append (r : ℝ) (digit : S → ℝ) (u v : List S) :
    word r digit (u ++ v) = word r digit u + r ^ u.length * word r digit v := by
  induction u with
  | nil => simp
  | cons a u ih =>
      simp only [List.cons_append, word, List.length_cons, pow_succ, ih]
      ring

theorem prefix_append (r : ℝ) (digit : S → ℝ) (u v : List S) (z : ℝ) :
    prefixPoint r digit (u ++ v) z = prefixPoint r digit u (prefixPoint r digit v z) := by
  simp only [prefixPoint, word_append, List.length_append, pow_add]
  ring

end BalancedTransport.Coding
end

noncomputable section
namespace BalancedTransport.Coding
variable {S : Type*}
open Stream'

theorem prefix_mem_unit {r : ℝ} (hr : 0 ≤ r) (digit : S → ℝ)
    (hd₀ : ∀ a, 0 ≤ digit a) (hd₁ : ∀ a, r * (digit a + 1) ≤ 1)
    (w : List S) {z : ℝ} (hz : z ∈ Set.Icc (0 : ℝ) 1) :
    prefixPoint r digit w z ∈ Set.Icc (0 : ℝ) 1 := by
  induction w with
  | nil => simpa using hz
  | cons a w ih =>
      rw [prefix_cons]
      exact ⟨mul_nonneg hr (add_nonneg (hd₀ a) ih.1),
        (mul_le_mul_of_nonneg_left (show digit a + prefixPoint r digit w z ≤
          digit a + 1 by linarith [ih.2]) hr).trans (hd₁ a)⟩

theorem prefix_gap {r : ℝ} (hr : 0 < r) (digit : S → ℝ)
    (hd₀ : ∀ a, 0 ≤ digit a) (hd₁ : ∀ a, r * (digit a + 1) ≤ 1)
    (p u v : List S) (a b : S) {x y : ℝ}
    (hx : x ∈ interval r digit (p ++ a :: u))
    (hy : y ∈ interval r digit (p ++ b :: v)) :
    r ^ (p.length + 1) * (digit b - digit a - 1) ≤ y - x := by
  rw [interval_eq_image hr] at hx hy
  obtain ⟨s, hs, rfl⟩ := hx
  obtain ⟨t, ht, rfl⟩ := hy
  have hs' := prefix_mem_unit hr.le digit hd₀ hd₁ u hs
  have ht' := prefix_mem_unit hr.le digit hd₀ hd₁ v ht
  rw [prefix_append, prefix_append, prefix_cons, prefix_cons]
  dsimp [prefixPoint]
  have hn : 0 ≤ r ^ p.length * r := mul_nonneg (pow_nonneg hr.le _) hr.le
  have hh : 0 ≤ r ^ p.length * r *
      (prefixPoint r digit v t - prefixPoint r digit u s + 1) :=
    mul_nonneg hn (by linarith [hs'.2, ht'.1])
  dsimp [prefixPoint] at hh
  rw [pow_succ]
  nlinarith only [hh]

end BalancedTransport.Coding
end

end OAI

-- ---- platform node ----
open OAI OAI.BalancedTransport OAI.BalancedTransport.Coding
open Stream'


theorem solution : type_of% @_root_.OAI.BalancedTransport.Coding.prefix_gap := @_root_.OAI.BalancedTransport.Coding.prefix_gap
