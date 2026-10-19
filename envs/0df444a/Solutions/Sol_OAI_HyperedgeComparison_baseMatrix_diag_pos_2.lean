-- Prove2me | solution 2 for OAI.HyperedgeComparison.baseMatrix_diag_pos
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T21:04:35.200593+00:00
-- url     : https://prove2.me/submissions/5661165c-0f86-4c21-b765-d3e9f0d999fd

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/HyperedgeComparison.lean:L1063-L1085
-- (upload_full_project.md Phase 4): solution for node OAI.HyperedgeComparison.baseMatrix_diag_pos. The node keeps its source
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

omit [Fintype E] in
/-- Closing every hyperedge isolates every node, in every deletion graph. -/
theorem cluster_all_closed (H : Hypergraph V E) (D : Set V) (s : V) :
    cluster H (fun _ => false) D s = {s} := by
  ext y
  constructor
  · intro hy
    change y = s
    induction hy with
    | refl => rfl
    | tail _ h _ => obtain ⟨e, he, _⟩ := h; simp at he
  · rintro rfl
    exact .refl

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

omit [Fintype E] in
theorem root_notin_earlier {n : ℕ} {x : Fin n → V} (hx : Function.Injective x) (k : Fin n) :
    x k ∉ earlier x k := by
  rintro ⟨j, hj, heq⟩
  exact (ne_of_lt hj) (hx heq)

/-- The diagonal mass is positive because fully closing the graph ensures E_k. -/
theorem baseMatrix_diag_pos {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (hp : ∀ e, (p e : ℝ) < 1)
    (x : Fin n → V) (hx : Function.Injective x) (k : Fin n) :
    0 < baseMatrix H p x k k := by
  have hi : (∫ ω : E → Bool, if ω = (fun _ => false) then (1:ℝ) else 0 ∂law p) =
      (law p).real {fun _ => false} := by
    simpa [Set.indicator] using
      (integral_indicator_one (μ := law p) (s := {fun _ => false}) (measurableSet_singleton _))
  apply (all_closed_mass_pos p hp).trans_le
  rw [← hi]
  unfold baseMatrix column
  apply integral_mono (Integrable.of_finite) (Integrable.of_finite)
  intro ω
  by_cases hc : ω = (fun _ => false)
  · subst ω
    have hf : firstRoot H x (fun _ => false) ∅ k k := by
      refine ⟨?_, .refl⟩
      rw [cluster_all_closed]
      simpa using root_notin_earlier hx k
    simp [hf]
  · simp only [hc, ite_false]
    split_ifs <;> norm_num

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


theorem solution.{uE,uV} : type_of% @_root_.OAI.HyperedgeComparison.baseMatrix_diag_pos.{uE,uV} := @_root_.OAI.HyperedgeComparison.baseMatrix_diag_pos.{uE,uV}
