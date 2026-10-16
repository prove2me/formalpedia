-- Prove2me | solution 1 for OAI.PartialPermutation.subgroup_algebra_commute
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T21:07:40.817295+00:00
-- url     : https://prove2.me/submissions/6000a477-6cff-4978-8f55-98a607d98502

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/PartialPermutation/Restriction.lean:L124-L141
-- (upload_full_project.md Phase 4): solution for node OAI.PartialPermutation.subgroup_algebra_commute. The node keeps its source
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

-- ---- from OAI.RepresentationTheory.PartialPermutation.Restriction ----
namespace OAI

section
open scoped Classical
open scoped BigOperators ComplexConjugate MonoidAlgebra
open scoped BigOperators ComplexConjugate
open scoped MonoidAlgebra BigOperators
open scoped BigOperators MonoidAlgebra Classical

attribute [local instance] Classical.propDecidable
open scoped BigOperators
open scoped MonoidAlgebra BigOperators

namespace PartialPermutation

section GroupRestriction
variable {G M : Type*} [Group G] [AddCommGroup M] [Module ℂ[G] M]

lemma subgroup_algebra_commute (H K : Subgroup G)
    (h : ∀ g ∈ H, ∀ k ∈ K, Commute g k) (a : ℂ[H]) (b : ℂ[K]) :
    Commute (MonoidAlgebra.mapDomainAlgHom ℂ ℂ H.subtype a)
      (MonoidAlgebra.mapDomainAlgHom ℂ ℂ K.subtype b) := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a₁ a₂ ha₁ ha₂ =>
    simp only [map_add]
    exact ha₁.add_left ha₂
  | single g c =>
    induction b using MonoidAlgebra.induction_linear with
    | zero => simp
    | add b₁ b₂ hb₁ hb₂ =>
      simp only [map_add]
      exact hb₁.add_right hb₂
    | single k d =>
      simpa [MonoidAlgebra.mapDomainAlgHom] using
        (MonoidAlgebra.single_commute_single (h g g.property k k.property) (Commute.all c d))

end GroupRestriction
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
open scoped BigOperators
open scoped MonoidAlgebra BigOperators


theorem solution : type_of% @_root_.OAI.PartialPermutation.subgroup_algebra_commute := @_root_.OAI.PartialPermutation.subgroup_algebra_commute
