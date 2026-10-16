-- Prove2me | solution 1 for OAI.PartialPermutation.exists_degree_le_rpow
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T21:11:21.11177+00:00
-- url     : https://prove2.me/submissions/4d557a6b-24ed-4d4c-9cf0-ee3cfce67ef4

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/PartialPermutation/DegreeEstimates.lean:L21-L39
-- (upload_full_project.md Phase 4): solution for node OAI.PartialPermutation.exists_degree_le_rpow. The node keeps its source
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
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_ConvolutionKernels
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_ComponentGeometry
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_SmallKernels
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_ProjectionCovers
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Restriction
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_IsotypicMatrices
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_IsotypicKernels

-- ---- from OAI.RepresentationTheory.PartialPermutation.DegreeEstimates ----
-- Lean 4.34 name of Finset.prod_lt_prod (ordered-semiring version) in Mathlib 0df444a.
private abbrev Finset.prod_lt_prod₀ := @Finset.prod_lt_prod

namespace OAI

section
open scoped Classical
open scoped BigOperators ComplexConjugate MonoidAlgebra
open scoped BigOperators ComplexConjugate
open scoped MonoidAlgebra BigOperators
open scoped BigOperators MonoidAlgebra Classical

attribute [local instance] Classical.propDecidable
open scoped MonoidAlgebra BigOperators
open scoped BigOperators

namespace PartialPermutation

lemma exists_degree_le_rpow {b D : ℕ} (hb : 0 < b) (hD : 0 < D)
    (d : Fin b → ℕ) (hprod : ∏ i, d i ≤ D) :
    ∃ i, (d i : ℝ) ≤ (D : ℝ) ^ (1 / (b : ℝ)) := by
  classical
  by_contra h
  push Not at h
  have hb' : (b : ℝ) ≠ 0 := by positivity
  have hD' : (0 : ℝ) < D := by positivity
  have hp : ∏ _ : Fin b, (D : ℝ) ^ (1 / (b : ℝ)) < ∏ i, (d i : ℝ) := by
    apply Finset.prod_lt_prod₀
    · intro i hi; positivity
    · intro i hi; exact (h i).le
    · exact ⟨⟨0, hb⟩, Finset.mem_univ _, h _⟩
  have he : ∏ _ : Fin b, (D : ℝ) ^ (1 / (b : ℝ)) = D := by
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hD'.le]
    simp [hb']
  rw [he, ← Nat.cast_prod] at hp
  exact (not_lt_of_ge (Nat.cast_le.mpr hprod)) hp

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
attribute [local instance] Classical.propDecidable
open scoped MonoidAlgebra BigOperators
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.PartialPermutation.exists_degree_le_rpow := @_root_.OAI.PartialPermutation.exists_degree_le_rpow
