-- Prove2me | solution 1 for OAI.PartialPermutation.linearMap_eq_on_simples
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T20:54:54.45099+00:00
-- url     : https://prove2.me/submissions/a086a9b6-83f0-4377-b0dd-0805728ddc12

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/PartialPermutation/IsotypicProjections.lean:L26-L51
-- (upload_full_project.md Phase 4): solution for node OAI.PartialPermutation.linearMap_eq_on_simples. The node keeps its source
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

-- ---- from OAI.RepresentationTheory.PartialPermutation.IsotypicProjections ----
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
section FullProjection
variable {G V : Type*} [Group G] [Fintype G]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V)

omit [FiniteDimensional ℂ V] in
lemma linearMap_eq_on_simples (A B : Module.End ℂ V)
    (h : ∀ (σ : Subrepresentation ρ) [Representation.IsIrreducible σ.toRepresentation],
      ∀ x : σ, A x = B x) : A = B := by
  let E (S : {S : Submodule ℂ[G] ρ.asModule // IsSimpleModule ℂ[G] S}) : Submodule ℂ V :=
    S.val.restrictScalars ℂ
  have htop : (⨆ S, E S) = ⊤ := by
    change (⨆ S : {S : Submodule ℂ[G] ρ.asModule // IsSimpleModule ℂ[G] S},
      S.val.restrictScalars ℂ) = ⊤
    rw [← Submodule.restrictScalars_iSup]
    have ht : (⨆ S : {S : Submodule ℂ[G] ρ.asModule // IsSimpleModule ℂ[G] S}, S.val) = ⊤ :=
      (sSup_eq_iSup' {S : Submodule ℂ[G] ρ.asModule | IsSimpleModule ℂ[G] S}).symm.trans
        (IsSemisimpleModule.sSup_simples_eq_top ℂ[G] ρ.asModule)
    rw [ht, Submodule.restrictScalars_top]
  have hker : (⊤ : Submodule ℂ V) ≤ LinearMap.ker (A - B) := by
    rw [← htop]
    refine iSup_le fun S => ?_
    intro x hx
    let σ := Subrepresentation.ofSubmodule' S.val
    have : Representation.IsIrreducible σ.toRepresentation :=
      (subrep_irreducible_iff ρ σ).mpr S.property
    exact sub_eq_zero.mpr (h σ ⟨x, hx⟩)
  apply LinearMap.ext
  intro x
  have hx := hker (Submodule.mem_top : x ∈ (⊤ : Submodule ℂ V))
  simpa only [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] using hx

end FullProjection
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


theorem solution : type_of% @_root_.OAI.PartialPermutation.linearMap_eq_on_simples := @_root_.OAI.PartialPermutation.linearMap_eq_on_simples
