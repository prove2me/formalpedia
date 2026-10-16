-- Prove2me | solution 1 for OAI.PartialPermutation.group_isotypic_restrict
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T21:05:32.719161+00:00
-- url     : https://prove2.me/submissions/8baee386-e8fe-4bf4-a652-d17e95a37543

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/PartialPermutation/Restriction.lean:L56-L112
-- (upload_full_project.md Phase 4): solution for node OAI.PartialPermutation.group_isotypic_restrict. The node keeps its source
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

lemma isotypic_restrict_of_fullyInvariant {R S M : Type*}
    [Ring R] [Ring S] [AddCommGroup M] [Module R M] [Module S M]
    [IsSemisimpleModule R M] [IsSemisimpleModule S M]
    (φ : S →+* R) (hsmul : ∀ s : S, ∀ x : M, φ s • x = s • x)
    (h : IsIsotypic R M)
    (hinv : ∀ N : Submodule S M, N.IsFullyInvariant →
      ∀ r : R, ∀ x ∈ N, r • x ∈ N) : IsIsotypic S M := by
  apply isIsotypic_iff_isFullyInvariant_imp_bot_or_top.mpr
  intro N hN
  let NR : Submodule R M := { N with smul_mem' := hinv N hN }
  have hNR : NR.IsFullyInvariant := by
    intro f x hx
    let fS : Module.End S M :=
      { f.toAddMonoidHom with
        map_smul' := fun s x => by
          change f (s • x) = s • f x
          rw [← hsmul, f.map_smul, hsmul] }
    exact hN fS hx
  rcases (isIsotypic_iff_isFullyInvariant_imp_bot_or_top.mp h) NR hNR with h0 | h1
  · left
    ext x
    change x ∈ NR ↔ x = 0
    rw [h0, Submodule.mem_bot]
  · right
    ext x
    change x ∈ NR ↔ x ∈ (⊤ : Submodule S M)
    simp [h1]

section GroupRestriction
variable {G M : Type*} [Group G] [AddCommGroup M] [Module ℂ[G] M]

lemma group_isotypic_restrict [Finite G] {ι : Type*} (H : ι → Subgroup G)
    (hgen : ⨆ i, H i = ⊤)
    (hcomm : ∀ i j, i ≠ j → ∀ g ∈ H i, ∀ k ∈ H j, Commute g k)
    (h : IsIsotypic ℂ[G] M) (i : ι) :
    letI := restrictGroupModule (M := M) (H i)
    IsIsotypic ℂ[H i] M := by
  let := restrictGroupModule (M := M) (H i)
  let φ : ℂ[H i] →+* ℂ[G] :=
    (MonoidAlgebra.mapDomainAlgHom ℂ ℂ (H i).subtype).toRingHom
  apply isotypic_restrict_of_fullyInvariant φ (fun s x => rfl) h
  intro N hN
  have hsingle (g : G) : ∀ x ∈ N, (MonoidAlgebra.single g (1 : ℂ)) • x ∈ N := by
    have hg : g ∈ ⨆ j, H j := by rw [hgen]; exact Subgroup.mem_top g
    refine Subgroup.iSup_induction H
      (C := fun g => ∀ x ∈ N, (MonoidAlgebra.single g (1 : ℂ)) • x ∈ N) hg ?_ ?_ ?_
    · intro j g hg
      by_cases hji : j = i
      · subst j
        intro x hx
        have hs := N.smul_mem (MonoidAlgebra.single (⟨g, hg⟩ : H i) (1 : ℂ)) hx
        change φ (MonoidAlgebra.single (⟨g, hg⟩ : H i) (1 : ℂ)) • x ∈ N at hs
        simpa [φ, MonoidAlgebra.mapDomainAlgHom] using hs
      · have hφ (a : ℂ[H i]) : Commute (MonoidAlgebra.single g (1 : ℂ)) (φ a) := by
          induction a using MonoidAlgebra.induction_linear with
          | zero => simp
          | add a b ha hb => simpa using ha.add_right hb
          | single k a =>
            simpa [φ, MonoidAlgebra.mapDomainAlgHom] using
              (MonoidAlgebra.single_commute_single (hcomm j i hji g hg k k.property)
                (Commute.all (1 : ℂ) a))
        let T : Module.End ℂ[H i] M :=
          { toFun := fun x => (MonoidAlgebra.single g (1 : ℂ)) • x
            map_add' := smul_add _
            map_smul' := fun a x => by
              change (MonoidAlgebra.single g (1 : ℂ)) • (φ a • x) =
                φ a • ((MonoidAlgebra.single g (1 : ℂ)) • x)
              simp only [smul_smul, (hφ a).eq] }
        exact fun x hx => hN T hx
    · intro x hx
      simpa [← MonoidAlgebra.one_def] using hx
    · intro g k hg hk x hx
      have he : (MonoidAlgebra.single (g * k) (1 : ℂ) : ℂ[G]) =
          MonoidAlgebra.single g 1 * MonoidAlgebra.single k 1 := by
        simp [MonoidAlgebra.single_mul_single]
      rw [he, mul_smul]
      exact hg _ (hk _ hx)
  intro r x hx
  induction r using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simpa [add_smul] using N.add_mem ha hb
  | single g a =>
    have hg := hsingle g x hx
    have hs := N.smul_mem (MonoidAlgebra.single (1 : H i) a) hg
    change φ (MonoidAlgebra.single (1 : H i) a) •
      ((MonoidAlgebra.single g (1 : ℂ)) • x) ∈ N at hs
    simpa [φ, MonoidAlgebra.mapDomainAlgHom, smul_smul,
      MonoidAlgebra.single_mul_single] using hs

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


theorem solution : type_of% @_root_.OAI.PartialPermutation.group_isotypic_restrict := @_root_.OAI.PartialPermutation.group_isotypic_restrict
