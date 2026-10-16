-- Prove2me | solution 1 for OAI.PartialPermutation.norm_sum_weighted_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T20:50:43.336433+00:00
-- url     : https://prove2.me/submissions/b14695e9-2947-4679-91ed-9952d046c5eb

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/PartialPermutation/CosetCaps.lean:L52-L66
-- (upload_full_project.md Phase 4): solution for node OAI.PartialPermutation.norm_sum_weighted_sq_le. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_PartialPermutation
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_SchurAverage
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_ModuleTransport
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Components
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_CentralKernels
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_CompleteKernels
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_RegularRepresentation
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Plancherel
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_TrivialRepresentation

-- ---- from OAI.RepresentationTheory.PartialPermutation.CosetCaps ----
namespace OAI

section
open scoped Classical
open scoped BigOperators ComplexConjugate MonoidAlgebra
open scoped BigOperators ComplexConjugate
open scoped MonoidAlgebra BigOperators
open scoped BigOperators MonoidAlgebra Classical

namespace PartialPermutation

section CosetCap
variable {G : Type*} [Group G] [Fintype G]

lemma norm_sum_weighted_sq_le {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (c : ι → ℂ) :
    ‖∑ i, (p i : ℂ) * c i‖ ^ 2 ≤ (∑ i, p i) * ∑ i, p i * ‖c i‖ ^ 2 := by
  have hn : ‖∑ i, (p i : ℂ) * c i‖ ≤ ∑ i, p i * ‖c i‖ := by
    calc
      _ ≤ ∑ i, ‖(p i : ℂ) * c i‖ := norm_sum_le _ _
      _ = _ := by simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hp _)]
  have hnonneg : 0 ≤ ∑ i, p i * ‖c i‖ := Finset.sum_nonneg fun i _ => mul_nonneg (hp i) (norm_nonneg _)
  have hsq : (∑ i, p i * ‖c i‖) ^ 2 ≤ (∑ i, p i) * ∑ i, p i * ‖c i‖ ^ 2 := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    · exact fun i _ => hp i
    · exact fun i _ => mul_nonneg (hp i) (sq_nonneg _)
    · intro i hi
      nlinarith
  exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans hsq

end CosetCap
end PartialPermutation

end

end OAI

-- ---- platform node ----
open OAI OAI.PartialPermutation
open scoped Classical
open scoped BigOperators ComplexConjugate MonoidAlgebra
open scoped BigOperators ComplexConjugate
open scoped MonoidAlgebra BigOperators
open scoped BigOperators MonoidAlgebra Classical


theorem solution : type_of% @_root_.OAI.PartialPermutation.norm_sum_weighted_sq_le := @_root_.OAI.PartialPermutation.norm_sum_weighted_sq_le
