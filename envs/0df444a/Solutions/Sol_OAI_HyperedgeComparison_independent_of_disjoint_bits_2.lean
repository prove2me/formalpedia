-- Prove2me | solution 2 for OAI.HyperedgeComparison.independent_of_disjoint_bits
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T20:45:51.173837+00:00
-- url     : https://prove2.me/submissions/b62d1eaa-14d0-41e7-b476-c8ae1c30a339

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/HyperedgeComparison.lean:L341-L367
-- (upload_full_project.md Phase 4): solution for node OAI.HyperedgeComparison.independent_of_disjoint_bits. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CriticalZ3
import Definitions.Def_OAI_Probability_CriticalZ3_Basic
import Definitions.Def_OAI_Probability_CriticalZ3_ProductCylinder
import Definitions.Def_OAI_Probability_CriticalZ3_Symmetry
import Definitions.Def_OAI_Probability_CriticalZ3_QuarterFaces
import Definitions.Def_OAI_Probability_CriticalZ3_Resampling
import Definitions.Def_OAI_Probability_CriticalZ3_HyperedgeComparison

-- ---- from OAI.Probability.CriticalZ3.HyperedgeComparison ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uE uI uV

-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical Filter
open _root_.MeasureTheory ProbabilityTheory Classical Filter

open scoped ENNReal BigOperators Matrix

namespace HyperedgeComparison

variable {V : Type uV} {E : Type uE}

section FiniteLaw
variable [Fintype E]

/-- Functions of complementary finite sets of independent bits are independent.
The dependence conditions are extensional, avoiding auxiliary sigma-algebras. -/
theorem independent_of_disjoint_bits (p : E → Set.Icc (0 : ℝ) 1)
    (J : Finset E) (f g : (E → Bool) → ℝ)
    (hf : ∀ ω ω', (∀ e ∈ J, ω' e = ω e) → f ω' = f ω)
    (hg : ∀ ω ω', (∀ e ∉ J, ω' e = ω e) → g ω' = g ω) :
    IndepFun f g (law p) := by
  classical
  let f' : (J → Bool) → ℝ := fun a => f (fun e => if h : e ∈ J then a ⟨e,h⟩ else false)
  let g' : (↑(Jᶜ) → Bool) → ℝ := fun a =>
    g (fun e => if h : e ∈ Jᶜ then a ⟨e,h⟩ else false)
  have hi : iIndepFun (fun e (ω : E → Bool) => ω e) (law p) :=
    iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)
  have h := (hi.indepFun_finset J Jᶜ disjoint_compl_right
    (fun e => measurable_pi_apply e)).comp
    (measurable_of_countable f') (measurable_of_countable g')
  have heqf : (f' ∘ (fun (ω : E → Bool) (e : J) => ω e)) = f := by
    funext ω
    apply hf
    intro e he
    simp [he]
  have heqg : (g' ∘ (fun (ω : E → Bool) (e : ↑(Jᶜ)) => ω e)) = g := by
    funext ω
    apply hg
    intro e he
    simp [he]
  rwa [heqf, heqg] at h

end FiniteLaw
namespace Site
variable (G : SimpleGraph V)

end Site

end HyperedgeComparison

end OAI

-- ---- platform node ----
open OAI OAI.HyperedgeComparison
open MeasureTheory ProbabilityTheory Classical Filter
open scoped ENNReal BigOperators Matrix


theorem solution.{uE} : type_of% @_root_.OAI.HyperedgeComparison.independent_of_disjoint_bits.{uE} := @_root_.OAI.HyperedgeComparison.independent_of_disjoint_bits.{uE}
