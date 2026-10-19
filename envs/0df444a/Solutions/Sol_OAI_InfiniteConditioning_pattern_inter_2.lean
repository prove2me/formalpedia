-- Prove2me | solution 2 for OAI.InfiniteConditioning.pattern_inter
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T21:32:53.02322+00:00
-- url     : https://prove2.me/submissions/2a2e7934-e7ad-4361-9f14-1b229e279d48

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/Conditioning.lean:L103-L124
-- (upload_full_project.md Phase 4): solution for node OAI.InfiniteConditioning.pattern_inter. The node keeps its source
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
import Definitions.Def_OAI_Probability_CriticalZ3_LatticeGraph
import Definitions.Def_OAI_Probability_CriticalZ3_BoxGeometry
import Definitions.Def_OAI_Probability_CriticalZ3_LatticePaths
import Definitions.Def_OAI_Probability_CriticalZ3_EntryLayers
import Definitions.Def_OAI_Probability_CriticalZ3_SeedTrials
import Definitions.Def_OAI_Probability_CriticalZ3_Conditioning
import Theorems.Thm_OAI_InfiniteConditioning_map_replace

-- ---- from OAI.Probability.CriticalZ3.Conditioning ----
-- Lean 4.33 compatibility: Measurable.of_eval is the renamed measurable_pi_lambda
-- (Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean at d13f23b records the alias).
section Lean433MeasurableOfEval
private theorem Measurable.of_eval {α δ : Type*} {X : δ → Type*}
    [MeasurableSpace α] [∀ a, MeasurableSpace (X a)] {f : α → ∀ a, X a}
    (hf : ∀ a, Measurable fun c => f c a) : Measurable f :=
  measurable_pi_lambda f hf
end Lean433MeasurableOfEval

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e
namespace OAI

universe uF

-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical Filter
open _root_.MeasureTheory ProbabilityTheory Classical Filter

open scoped ENNReal BigOperators Matrix

/-! The exact revealed-history law used by the adaptive queue.  In particular,
classifications depending only on revealed values do not change fresh bits. -/
namespace InfiniteConditioning
-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical
variable {E : Type} [Countable E]

omit [Countable E] in
theorem measurable_replace (J : Finset E) (ξ : E → Bool) : Measurable (replace J ξ) := by
  apply Measurable.of_eval
  intro e
  by_cases he : e ∈ J
  · simp only [replace, ite_eq_left he]; exact measurable_const
  · simp only [replace, ite_eq_right he]; exact measurable_pi_apply e

omit [Countable E] in
theorem replace_eq_of_pattern {J : Finset E} {ξ ω : E → Bool} (h : ω ∈ pattern J ξ) :
    replace J ξ ω = ω := by
  funext e
  by_cases he : e ∈ J
  · exact (ite_eq_left he).trans (h e he).symm
  · exact ite_eq_right he

omit [Countable E] in
private theorem measurable_replace_compl (J : Finset E) (ξ : E → Bool) :
    @Measurable (E → Bool) (E → Bool) (⨆ e ∈ (J : Set E)ᶜ, bitSigma e)
      inferInstance (replace J ξ) := by
  apply @Measurable.of_eval (E → Bool) E (fun _ => Bool) (⨆ e ∈ (J : Set E)ᶜ, bitSigma e) _ (replace J ξ)
  intro e
  by_cases he : e ∈ J
  · simp only [replace,ite_eq_left he]; exact measurable_const
  · simp only [replace,ite_eq_right he]
    exact Measurable.of_comap_le (le_iSup_of_le e (le_iSup_of_le he le_rfl))

private theorem measurable_pattern_sigma (J : Finset E) (ξ : E → Bool) :
    MeasurableSet[⨆ e ∈ (J : Set E), bitSigma e] (pattern J ξ) := by
  simp only [pattern,Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro e
  apply MeasurableSet.iInter
  intro he
  apply measurableSet_eq_fun _ measurable_const
  exact Measurable.of_comap_le (le_iSup_of_le e (le_iSup_of_le he le_rfl))

/-- Literal finite-history factorization, including impossible histories. -/
theorem pattern_inter (p : E → Set.Icc (0 : ℝ) 1) (J : Finset E) (ξ : E → Bool)
    (A : Set (E → Bool)) (hA : MeasurableSet A) :
    ProductCylinder.law p (pattern J ξ ∩ A) =
      ProductCylinder.law p (pattern J ξ) * ProductCylinder.law (fixedParameter p J ξ) A := by
  have hi : iIndepFun (fun e (ω : E → Bool) => ω e) (ProductCylinder.law p) :=
    iIndepFun_infinitePi (X := fun _ => id) (fun _ => measurable_id)
  have hmi : iIndep (bitSigma (E := E)) (ProductCylinder.law p) :=
    (iIndepFun_iff_iIndep _ _ _).mp hi
  have h := indep_iSup_of_disjoint
    (fun e => (measurable_pi_apply e).comap_le) hmi
    (disjoint_compl_right (α := Set E) (a := (J : Set E)))
  have hh := (h.indepSet_of_measurableSet (measurable_pattern_sigma J ξ)
    ((measurable_replace_compl J ξ) hA)).measure_inter_eq_mul
  have heq : pattern J ξ ∩ replace J ξ ⁻¹' A = pattern J ξ ∩ A := by
    ext ω
    constructor <;> rintro ⟨hp,ha⟩
    · exact ⟨hp,by simpa only [Set.mem_preimage,replace_eq_of_pattern hp] using ha⟩
    · exact ⟨hp,by simpa only [Set.mem_preimage,replace_eq_of_pattern hp] using ha⟩
  rw [heq] at hh
  rw [←map_replace p J ξ,Measure.map_apply (measurable_replace J ξ) hA]
  exact hh

end InfiniteConditioning

namespace InfiniteConditioning
-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical
variable {E I : Type}

end InfiniteConditioning

namespace InfiniteConditioning
-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical
variable {E : Type}

variable [Countable E]

end InfiniteConditioning

namespace InfiniteConditioning
-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical
variable {E : Type} [Countable E]

end InfiniteConditioning

end OAI

-- ---- platform node ----
open OAI OAI.InfiniteConditioning
open MeasureTheory ProbabilityTheory Classical Filter
open scoped ENNReal BigOperators Matrix
open MeasureTheory ProbabilityTheory Classical


theorem solution : type_of% @_root_.OAI.InfiniteConditioning.pattern_inter := @_root_.OAI.InfiniteConditioning.pattern_inter
