-- Prove2me | solution 1 for OAI.PartialPermutation.complexFourier_smallTypeKernel
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T20:56:17.510785+00:00
-- url     : https://prove2.me/submissions/ed8e2027-db38-4afa-b6a4-be6944ee4206

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/PartialPermutation/SmallKernels.lean:L32-L62
-- (upload_full_project.md Phase 4): solution for node OAI.PartialPermutation.complexFourier_smallTypeKernel. The node keeps its source
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

-- ---- from OAI.RepresentationTheory.PartialPermutation.SmallKernels ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

section
open scoped Classical
open scoped BigOperators ComplexConjugate MonoidAlgebra
open scoped BigOperators ComplexConjugate
open scoped MonoidAlgebra BigOperators
open scoped BigOperators MonoidAlgebra Classical

attribute [local instance] Classical.propDecidable
namespace PartialPermutation
noncomputable section
variable {G : Type*} [Group G] [Fintype G]

lemma complexFourier_smallTypeKernel {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) [Representation.IsIrreducible ρ]
    (R : ℝ) : complexFourier ρ (smallTypeKernel G R) =
      if (Module.finrank ℂ V : ℝ) ≤ R then 1 else 0 := by
  classical
  obtain ⟨c, ⟨e⟩, hc⟩ := irreducibleRep_complete ρ
  have hdeg : irreducibleDegree c = Module.finrank ℂ V := e.toLinearEquiv.finrank_eq
  have he (d : IrreducibleIndex G) :
      Nonempty (Representation.Equiv (irreducibleRep d) ρ) ↔ d = c := by
    exact ⟨hc d, fun h => h ▸ ⟨e⟩⟩
  unfold smallTypeKernel
  rw [complexFourier_sum]
  calc
    _ = ∑ d : IrreducibleIndex G, if d = c then
        (if (Module.finrank ℂ V : ℝ) ≤ R then (1 : Module.End ℂ V) else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro d _
      by_cases hd : (irreducibleDegree d : ℝ) ≤ R
      · simp only [hd, ite_true, centralCharacterKernel_fourier]
        by_cases hdc : d = c
        · subst d
          rw [hdeg] at hd
          simp [he, hd]
        · simp [he, hdc]
      · simp only [hd, ite_false, complexFourier]
        by_cases hdc : d = c
        · subst d
          simp [hdeg] at hd
          simp [hd]
        · simp [hdc]
    _ = _ := by simp

end
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


theorem solution : type_of% @_root_.OAI.PartialPermutation.complexFourier_smallTypeKernel := @_root_.OAI.PartialPermutation.complexFourier_smallTypeKernel
