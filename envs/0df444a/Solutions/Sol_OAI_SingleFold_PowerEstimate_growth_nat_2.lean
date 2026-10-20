-- Prove2me | solution 2 for OAI.SingleFold.PowerEstimate.growth_nat
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T18:42:05.59512+00:00
-- url     : https://prove2.me/submissions/950eb52e-58b9-4674-bddb-584042a6de9c

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/SingleFold/Power.lean:L37-L51
-- (upload_full_project.md Phase 4): solution for node OAI.SingleFold.PowerEstimate.growth_nat. The node keeps its source
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
lemma growth_nat {g : ℕ → ℕ} {δ : ℝ} {u : ℕ} (hδ : 0 < δ) (hu : 4≤u)
    (hg : δ*(Real.log (u:ℝ))^2 < Real.log (g u:ℝ) ∧ Real.log (g u:ℝ)<(u:ℝ)*Real.log (u:ℝ)) :
    0<g u ∧ g u<u^u := by
  have hu' : (1:ℝ)<u := by exact_mod_cast (show 1<u by omega)
  have hlog : 0<Real.log (u:ℝ) := Real.log_pos hu'
  have hglog : 0<Real.log (g u:ℝ) := lt_trans (mul_pos hδ (sq_pos_of_pos hlog)) hg.1
  have hgp : 0<g u := by
    by_contra h
    have he : g u=0 := by omega
    simp [he] at hglog
  refine ⟨hgp,?_⟩
  have hup : (0:ℝ)<(u:ℝ)^u := pow_pos (by linarith) _
  have hlg : Real.log (g u:ℝ)<Real.log ((u:ℝ)^u) := by simpa only [Real.log_pow] using hg.2
  have hh := (Real.log_lt_log_iff (by exact_mod_cast hgp) hup).mp hlg
  exact_mod_cast hh

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


theorem solution : type_of% @_root_.OAI.SingleFold.PowerEstimate.growth_nat := @_root_.OAI.SingleFold.PowerEstimate.growth_nat
