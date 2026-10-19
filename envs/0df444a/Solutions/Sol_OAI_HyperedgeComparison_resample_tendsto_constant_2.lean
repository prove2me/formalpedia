-- Prove2me | solution 2 for OAI.HyperedgeComparison.resample_tendsto_constant
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T21:02:47.606117+00:00
-- url     : https://prove2.me/submissions/618fcb7f-e03f-448c-baeb-7e8d6208b138

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/HyperedgeComparison.lean:L988-L1018
-- (upload_full_project.md Phase 4): solution for node OAI.HyperedgeComparison.resample_tendsto_constant. The node keeps its source
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
import Theorems.Thm_OAI_FiniteResampling_Transition_iterates_tendsto_constant
import Theorems.Thm_OAI_HyperedgeComparison_resamplingTransition_atom

-- ---- from OAI.Probability.CriticalZ3.Resampling ----
namespace OAI

universe uI

-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical

-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical
open scoped ENNReal

open scoped BigOperators Matrix
open Filter

namespace FiniteResampling
variable {I : Type uI} [Fintype I] [Nonempty I]

theorem le_lower {f : I → ℝ} {a : ℝ} (h : ∀ i, a ≤ f i) : a ≤ lower f :=
  Finset.le_inf' Finset.univ_nonempty f (fun i _ => h i)
namespace Transition
variable (K : Transition I)
end Transition
end FiniteResampling

end OAI

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

theorem resamplingTransition_act [Fintype V] (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (s : V) (S : Set V) (F : Set V → ℝ)
    (U : ClusterDomain s S) :
    (resamplingTransition H p s S).act (fun T => F T.1) U =
      resample H p s S F U.1 := by
  classical
  unfold FiniteResampling.Transition.act resamplingTransition resample meanAfterDelete
  simp_rw [← integral_mul_const]
  rw [← integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro ω
  dsimp only
  rw [← integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro ω'
  change (∑ T : ClusterDomain s S,
    (if nextState H s S U ω ω' = T then (1:ℝ) else 0) * F T.1) =
      F (nextState H s S U ω ω').1
  simp [ite_mul]

/-- Probability mass of the all-closed finite configuration. -/
theorem all_closed_mass (p : E → Set.Icc (0 : ℝ) 1) :
    (law p).real {fun _ => false} = ∏ e, (1 - (p e : ℝ)) := by
  classical
  rw [Measure.real_def, law, Measure.pi_singleton, ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro e _
  change (bernoulliMeasure true false (p e)).real {false} = _
  rw [bernoulliMeasure_real_apply (p e) (measurableSet_singleton false)]
  simp [unitInterval.coe_symm_eq]

theorem all_closed_mass_pos (p : E → Set.Icc (0 : ℝ) 1)
    (hp : ∀ e, (p e : ℝ) < 1) : 0 < (law p).real {fun _ => false} := by
  rw [all_closed_mass]
  exact Finset.prod_pos (fun e _ => sub_pos.mpr (hp e))

/-- The actual conditional cluster-resampling iterates tend to a nonnegative
constant. This version does not need stationarity or positive mass at every state. -/
theorem resample_tendsto_constant [Fintype V] (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (hp : ∀ e, (p e : ℝ) < 1)
    (s : V) (S : Set V) (hs : s ∉ S) (F : Set V → ℝ)
    (hF : ∀ U ∈ ClusterDomain s S, 0 ≤ F U) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ U ∈ ClusterDomain s S,
      Tendsto (fun n : ℕ => ((resample H p s S)^[n] F) U) atTop (nhds c) := by
  classical
  let z : ClusterDomain s S := ⟨{s}, ⟨by simp, by simpa using hs⟩⟩
  let : Nonempty (ClusterDomain s S) := ⟨z⟩
  let K := resamplingTransition H p s S
  let a := (law p).real {fun _ => false}
  have ha0 : 0 < a := all_closed_mass_pos p hp
  have ha1 : a ≤ 1 := measureReal_le_one
  have hatom : ∀ U, a ≤ K.weight U z := fun U => resamplingTransition_atom H p s S hs U
  obtain ⟨c, hcl, _, hlim⟩ := K.iterates_tendsto_constant z a ha0 ha1 hatom (fun U => F U.1)
  have hc : 0 ≤ c := (FiniteResampling.le_lower (fun U : ClusterDomain s S => hF U.1 U.2)).trans hcl
  have heq (n : ℕ) : (fun U : ClusterDomain s S => ((resample H p s S)^[n] F) U.1) =
      (K.act)^[n] (fun U => F U.1) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      funext U
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      rw [← resamplingTransition_act H p s S ((resample H p s S)^[n] F) U]
      exact congrFun (congrArg K.act ih) U
  refine ⟨c, hc, ?_⟩
  intro U hU
  have h := hlim ⟨U, hU⟩
  simpa only [← heq] using h

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


theorem solution.{uE,uV} : type_of% @_root_.OAI.HyperedgeComparison.resample_tendsto_constant.{uE,uV} := @_root_.OAI.HyperedgeComparison.resample_tendsto_constant.{uE,uV}
