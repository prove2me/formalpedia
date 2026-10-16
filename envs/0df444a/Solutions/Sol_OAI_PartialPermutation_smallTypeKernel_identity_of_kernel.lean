-- Prove2me | solution 1 for OAI.PartialPermutation.smallTypeKernel_identity_of_kernel
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T20:57:37.860713+00:00
-- url     : https://prove2.me/submissions/d5fc8081-5b20-41b2-998a-0bd17b12aca5

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/PartialPermutation/SmallKernels.lean:L80-L97
-- (upload_full_project.md Phase 4): solution for node OAI.PartialPermutation.smallTypeKernel_identity_of_kernel. The node keeps its source
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
import Theorems.Thm_OAI_PartialPermutation_complexFourier_smallTypeKernel
import Theorems.Thm_OAI_PartialPermutation_fourier_bessel
import Theorems.Thm_OAI_PartialPermutation_linearMap_eq_on_simples

-- ---- from OAI.RepresentationTheory.PartialPermutation.SmallKernels ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e

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

lemma degree_le_of_kernel_identity {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) [Representation.IsIrreducible ρ] (hρ : IsUnitary ρ)
    (k : G → ℂ) (d : ℕ) (hk : ∑ g, ‖k g‖^2 = (d : ℝ)^2 / Fintype.card G)
    (hact : complexFourier ρ k = 1) : Module.finrank ℂ V ≤ d := by
  have h := fourier_bessel ρ hρ k
  have hN : (Fintype.card G : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [hact, hsNormSq_one, hk] at h
  have hd : (Module.finrank ℂ V : ℝ)^2 ≤ (d : ℝ)^2 := by
    convert h using 1 <;> field_simp
  exact_mod_cast (sq_le_sq₀ (by positivity) (by positivity)).mp hd

lemma smallTypeKernel_identity_of_kernel {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (hρ : IsUnitary ρ)
    (k : G → ℂ) (d : ℕ) (R : ℝ) (hd : (d : ℝ) ≤ R)
    (hk : ∑ g, ‖k g‖^2 = (d : ℝ)^2 / Fintype.card G)
    (hact : complexFourier ρ k = 1) : complexFourier ρ (smallTypeKernel G R) = 1 := by
  apply linearMap_eq_on_simples ρ
  intro σ hσ x
  have := hσ
  have hu : IsUnitary σ.toRepresentation := fun g x y => hρ g x y
  have hs : complexFourier σ.toRepresentation k = 1 := by
    ext y
    rw [complexFourier_subrep, hact]
    rfl
  have hdeg := degree_le_of_kernel_identity σ.toRepresentation hu k d hk hs
  have hdegR : (Module.finrank ℂ σ.toSubmodule : ℝ) ≤ R := (Nat.cast_le.mpr hdeg).trans hd
  rw [← complexFourier_subrep, complexFourier_smallTypeKernel, ite_eq_left hdegR]
  rfl

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


theorem solution : type_of% @_root_.OAI.PartialPermutation.smallTypeKernel_identity_of_kernel := @_root_.OAI.PartialPermutation.smallTypeKernel_identity_of_kernel
