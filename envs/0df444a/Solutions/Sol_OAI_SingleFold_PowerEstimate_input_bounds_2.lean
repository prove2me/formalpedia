-- Prove2me | solution 2 for OAI.SingleFold.PowerEstimate.input_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T18:40:30.688612+00:00
-- url     : https://prove2.me/submissions/3f0aa0f9-5865-4423-83b2-60f1063945bf

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/SingleFold/Power.lean:L20-L35
-- (upload_full_project.md Phase 4): solution for node OAI.SingleFold.PowerEstimate.input_bounds. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SingleFold
import Definitions.Def_OAI_NumberTheory_SingleFold_PolynomialCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_RationalCodes
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticCoordinates
import Definitions.Def_OAI_NumberTheory_SingleFold_FunctionalCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_DescentMap
import Definitions.Def_OAI_NumberTheory_SingleFold_SquareSupport
import Definitions.Def_OAI_NumberTheory_SingleFold_LocalDescent
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticHeight
import Definitions.Def_OAI_NumberTheory_SingleFold_QuadraticHeight
import Definitions.Def_OAI_NumberTheory_SingleFold_FiniteGeneration
import Definitions.Def_OAI_NumberTheory_SingleFold_Rank
import Definitions.Def_OAI_NumberTheory_SingleFold_Duplication
import Definitions.Def_OAI_NumberTheory_SingleFold_Torsion
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticGrowth
import Definitions.Def_OAI_NumberTheory_SingleFold_Pell
import Definitions.Def_OAI_NumberTheory_SingleFold_Power

-- ---- from OAI.NumberTheory.SingleFold.Power ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace SingleFold.PowerEstimate
lemma input_bounds {ell u₀ b n c : ℕ} (hell : 1≤ell) (h₀ : 4≤u₀) :
    u₀ ≤ input ell u₀ b n c ∧ (c+1)*(n+1)+4 ≤ input ell u₀ b n c ∧
    b < input ell u₀ b n c ∧ n+1 < input ell u₀ b n c-1 := by
  have hp : c+1≤(c+1)^ell := Nat.le_pow hell
  have h1 : 1≤(c+1)^ell*(n+1) := by
    have : 0<(c+1)^ell*(n+1) := by positivity
    omega
  have hn : n+1≤(c+1)^ell*(n+1) := by nlinarith
  have hm := Nat.mul_le_mul_right (n+1) hp
  dsimp [input]
  constructor; omega
  constructor; nlinarith
  constructor
  · nlinarith
  · have hnn : n+1+4≤(c+1)^ell*(n+1)*(b+1)+u₀ := by nlinarith
    omega

end SingleFold.PowerEstimate

namespace SingleFold.PowerSystem
open PowerEstimate

variable {g : ℕ → ℕ} {δ : ℝ} {ell u₀ : ℕ}
variable (hδ : 0<δ) (hell : 1≤ell) (h₀ : 4≤u₀)
variable (hg : ∀ u, u₀≤u → δ*(Real.log (u:ℝ))^2<Real.log (g u:ℝ) ∧ Real.log (g u:ℝ)<(u:ℝ)*Real.log (u:ℝ))
include hδ hell h₀ hg
end SingleFold.PowerSystem

namespace SingleFold.Compiler.ScalarSF
variable {α : Type} {f g : (α → ℕ) → ℕ}
end SingleFold.Compiler.ScalarSF

namespace SingleFold.PowerCompilation
open Compiler
end SingleFold.PowerCompilation

end OAI

-- ---- platform node ----
open OAI OAI.SingleFold OAI.SingleFold.PowerEstimate


theorem solution : type_of% @_root_.OAI.SingleFold.PowerEstimate.input_bounds := @_root_.OAI.SingleFold.PowerEstimate.input_bounds
