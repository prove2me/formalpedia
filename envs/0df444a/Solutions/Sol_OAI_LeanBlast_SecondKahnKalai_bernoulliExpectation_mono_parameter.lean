-- Prove2me | solution 1 for OAI.LeanBlast.SecondKahnKalai.bernoulliExpectation_mono_parameter
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:43:11.76424+00:00
-- url     : https://prove2.me/submissions/80cc0fd0-1cef-44f2-97d8-8e4ea02b8be4

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GraphThreshold/BernoulliMonotonicity.lean:L20-L50
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.SecondKahnKalai.bernoulliExpectation_mono_parameter. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Action.Pointwise.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.List.Pairwise
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.Monotone
import Definitions.Def_SecondKahnKalai
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphEncoding
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphProbability
import Definitions.Def_OAI_Combinatorics_GraphThreshold_EmbeddingExtension
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphSupport
import Definitions.Def_OAI_Combinatorics_GraphThreshold_Basic
import Definitions.Def_OAI_Combinatorics_GraphThreshold_FiniteProbability
import Definitions.Def_OAI_Combinatorics_GraphThreshold_CopyOrbits
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphExpectedCopies
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphCopies
import Definitions.Def_OAI_Combinatorics_GraphThreshold_ProbabilityTree
import Definitions.Def_OAI_Combinatorics_GraphThreshold_LocalFailureNumerics
import Definitions.Def_OAI_Combinatorics_GraphThreshold_Predecessor
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphHierarchy
import Definitions.Def_OAI_Combinatorics_GraphThreshold_BernoulliCoupling
import Definitions.Def_OAI_Combinatorics_GraphThreshold_AdaptiveTrials
import Theorems.Thm_OAI_LeanBlast_SecondKahnKalai_bernoulliExpectation_union

-- ---- from OAI.Combinatorics.GraphThreshold.FiniteProbability ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace LeanBlast.SecondKahnKalai

namespace FiniteLaw

variable {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]

theorem expectation_mono (μ : FiniteLaw Ω) {f g : Ω → ℝ} (hfg : ∀ ω, f ω ≤ g ω) :
    μ.expectation f ≤ μ.expectation g :=
  Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (hfg ω) (μ.nonneg ω)

end FiniteLaw

variable {X : Type*} [Fintype X] [DecidableEq X]

end LeanBlast.SecondKahnKalai

end

end OAI

-- ---- from OAI.Combinatorics.GraphThreshold.BernoulliCoupling ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace LeanBlast.SecondKahnKalai

variable {X : Type*} [Fintype X] [DecidableEq X]

theorem bernoulliExpectation_mono {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {f g : Finset X → ℝ} (hfg : ∀ W, f W ≤ g W) :
    bernoulliExpectation p f ≤ bernoulliExpectation p g :=
  (bernoulliLaw p hp0 hp1).expectation_mono hfg

end LeanBlast.SecondKahnKalai

end

end OAI

-- ---- from OAI.Combinatorics.GraphThreshold.BernoulliMonotonicity ----
namespace OAI

/-!
# Monotonicity of finite Bernoulli probabilities

For `p ≤ q`, adjoin an independent Bernoulli set to a Bernoulli-`p` set.
The resulting union has parameter `q` and contains the first set. This gives
expectation and event monotonicity, including both endpoints of `[0, 1]`.
-/

noncomputable section
attribute [local instance] Classical.propDecidable

namespace LeanBlast.SecondKahnKalai

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- A Bernoulli set with a larger parameter has larger expectation for every
function monotone under inclusion. The function need not be nonnegative. -/
theorem bernoulliExpectation_mono_parameter {p q : ℝ}
    (hp0 : 0 ≤ p) (hpq : p ≤ q) (hq1 : q ≤ 1) (F : Finset X → ℝ)
    (hF : ∀ U V, U ⊆ V → F U ≤ F V) :
    bernoulliExpectation p F ≤ bernoulliExpectation q F := by
  have hp1 : p ≤ 1 := hpq.trans hq1
  by_cases hp : p = 1
  · have hq : q = 1 := by linarith
    simp [hp, hq]
  have hp_lt : p < 1 := by
    rcases lt_or_eq_of_le hp1 with hlt | heq
    · exact hlt
    · exact (hp heq).elim
  have hd : 0 < 1 - p := sub_pos.mpr hp_lt
  let r := (q - p) / (1 - p)
  have hr0 : 0 ≤ r := div_nonneg (sub_nonneg.mpr hpq) hd.le
  have hr1 : r ≤ 1 := (div_le_one hd).2 (by linarith)
  have hparam : p + r - p * r = q := by
    dsimp [r]
    field_simp [hd.ne']
    ring
  calc
    bernoulliExpectation p F =
        bernoulliExpectation p (fun U => bernoulliExpectation r (fun _ => F U)) := by
      simp
    _ ≤ bernoulliExpectation p (fun U => bernoulliExpectation r (fun V => F (U ∪ V))) :=
      bernoulliExpectation_mono hp0 hp1 fun U =>
        bernoulliExpectation_mono hr0 hr1 fun V => hF U (U ∪ V) Finset.subset_union_left
    _ = bernoulliExpectation q F := by
      rw [bernoulliExpectation_union, hparam]

end LeanBlast.SecondKahnKalai

end

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.SecondKahnKalai
attribute [local instance] Classical.propDecidable


theorem solution : type_of% @_root_.OAI.LeanBlast.SecondKahnKalai.bernoulliExpectation_mono_parameter := @_root_.OAI.LeanBlast.SecondKahnKalai.bernoulliExpectation_mono_parameter
