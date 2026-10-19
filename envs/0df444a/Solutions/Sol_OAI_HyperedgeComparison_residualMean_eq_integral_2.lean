-- Prove2me | solution 2 for OAI.HyperedgeComparison.residualMean_eq_integral
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T20:49:45.06923+00:00
-- url     : https://prove2.me/submissions/0105c5e4-b38a-413c-a30e-0a6e647a46b2

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/HyperedgeComparison.lean:L439-L487
-- (upload_full_project.md Phase 4): solution for node OAI.HyperedgeComparison.residualMean_eq_integral. The node keeps its source
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
import Theorems.Thm_OAI_HyperedgeComparison_exact_cluster_independent

-- ---- from OAI.Probability.CriticalZ3.HyperedgeComparison ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uE uI uV

-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical Filter
open _root_.MeasureTheory ProbabilityTheory Classical Filter

open scoped ENNReal BigOperators Matrix

namespace HyperedgeComparison

variable {V : Type uV} {E : Type uE}

/-- Bits on deleted hyperedges are irrelevant to the surviving clusters. -/
theorem cluster_eq_of_agree_disjoint {H : Hypergraph V E} {ω ω' : E → Bool}
    {D : Set V} (hagree : ∀ e, Disjoint (H e) D → ω' e = ω e) (s : V) :
    cluster H ω' D s = cluster H ω D s := by
  have hrel : Adj H ω' D = Adj H ω D := by
    funext x y
    apply propext
    constructor <;> rintro ⟨e, he, hd, hx, hy⟩
    · exact ⟨e, (hagree e hd) ▸ he, hd, hx, hy⟩
    · exact ⟨e, (hagree e hd).trans he, hd, hx, hy⟩
  unfold cluster Connected
  rw [hrel]

section FiniteLaw
variable [Fintype E]

/-- Integrated exact-cluster independence, with no positivity restriction on
an exact cluster event (zero probability events also satisfy the identity). -/
theorem exact_cluster_integral (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (D S W : Set V) (g : (E → Bool) → ℝ)
    (hg : ∀ ω ω', (∀ e, Disjoint (H e) W → ω' e = ω e) → g ω' = g ω) :
    (∫ ω, (if clusters H ω D S = W then (1 : ℝ) else 0) * g ω ∂law p) =
      (∫ ω, if clusters H ω D S = W then (1 : ℝ) else 0 ∂law p) *
        ∫ ω, g ω ∂law p := by
  classical
  exact (exact_cluster_independent H p D S W g hg).integral_fun_mul_eq_mul_integral
    (measurable_of_countable _).aestronglyMeasurable
    (measurable_of_countable _).aestronglyMeasurable

/-- Partition a finite expectation by exact values, without conditional-probability
notation and without requiring positive individual atom masses. -/
theorem integral_eq_sum_fibers {I : Type uI} [Fintype I] [DecidableEq I]
    (p : E → Set.Icc (0 : ℝ) 1) (X : (E → Bool) → I) (f : (E → Bool) → ℝ) :
    (∫ ω, f ω ∂law p) = ∑ i, ∫ ω, if X ω = i then f ω else 0 ∂law p := by
  classical
  rw [← integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  congr 1
  funext ω
  simp

theorem residualMean_eq_integral [Fintype V] (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (s : V) (S U : Set V) (F : Set V → ℝ) :
    residualMean H p s S U F = ∫ ω, residualSample H ω s S U F ∂law p := by
  classical
  unfold residualMean
  rw [integral_eq_sum_fibers p (fun ω => clusters H ω U S),
    integral_eq_sum_fibers p (fun ω => clusters H ω U S)]
  apply Finset.sum_congr rfl
  intro W _
  by_cases hs : s ∈ W
  · have hleft : (fun ω => if clusters H ω U S = W then
        (if s ∈ clusters H ω U S then 0 else
          meanAfterDelete H p s (clusters H ω U S) F -
          meanAfterDelete H p s (clusters H ω U S ∪ U) F) else 0) =
        (fun _ => (0 : ℝ)) := by
      funext ω
      split_ifs with h <;> simp_all
    have hright : (fun ω => if clusters H ω U S = W then
        residualSample H ω s S U F else 0) = (fun _ => (0 : ℝ)) := by
      funext ω
      unfold residualSample
      split_ifs with h <;> simp_all
    rw [hleft, hright]
  · let g : (E → Bool) → ℝ := fun ω =>
        F (cluster H ω W s) - F (cluster H ω (W ∪ U) s)
    have hind := exact_cluster_integral H p U S W g (by
      intro ω ω' hagree
      dsimp [g]
      rw [cluster_eq_of_agree_disjoint hagree s,
        cluster_eq_of_agree_disjoint (fun e he => hagree e (he.mono_right Set.subset_union_left)) s])
    have hleft : (fun ω => if clusters H ω U S = W then
        (if s ∈ clusters H ω U S then 0 else
          meanAfterDelete H p s (clusters H ω U S) F -
          meanAfterDelete H p s (clusters H ω U S ∪ U) F) else 0) =
        (fun ω => (if clusters H ω U S = W then (1 : ℝ) else 0) *
          (∫ ω', g ω' ∂law p)) := by
      funext ω
      by_cases h : clusters H ω U S = W
      · simp [h, hs, g, meanAfterDelete,
          integral_sub (Integrable.of_finite) (Integrable.of_finite)]
      · simp [h]
    have hright : (fun ω => if clusters H ω U S = W then
        residualSample H ω s S U F else 0) =
        (fun ω => (if clusters H ω U S = W then (1 : ℝ) else 0) * g ω) := by
      funext ω
      by_cases h : clusters H ω U S = W
      · simp [h, hs, g, residualSample]
      · simp [h]
    rw [hleft, hright, integral_mul_const, hind]

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


theorem solution.{uE,uV} : type_of% @_root_.OAI.HyperedgeComparison.residualMean_eq_integral.{uE,uV} := @_root_.OAI.HyperedgeComparison.residualMean_eq_integral.{uE,uV}
