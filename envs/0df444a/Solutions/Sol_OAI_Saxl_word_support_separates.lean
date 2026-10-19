-- Prove2me | solution 1 for OAI.Saxl.word_support_separates
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T01:32:29.064829+00:00
-- url     : https://prove2.me/submissions/ff2ad2e9-096e-46ea-a235-a5a58cf373e3

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/Saxl/SupportSeparation.lean:L130-L156
-- (upload_full_project.md Phase 4): solution for node OAI.Saxl.word_support_separates. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_Saxl
import Definitions.Def_OAI_RepresentationTheory_Saxl_Basic
import Definitions.Def_OAI_RepresentationTheory_Saxl_Polytabloid
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtSubmodule
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtDuality
import Definitions.Def_OAI_RepresentationTheory_Saxl_TableauTransport
import Definitions.Def_OAI_RepresentationTheory_Saxl_StaircaseTensor
import Definitions.Def_OAI_RepresentationTheory_Saxl_HighProjection
import Definitions.Def_OAI_RepresentationTheory_Saxl_CoordinateSector
import Definitions.Def_OAI_RepresentationTheory_Saxl_PositionSplit
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandFactorization
import Definitions.Def_OAI_RepresentationTheory_Saxl_PathAlternation
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandMatrices
import Definitions.Def_OAI_RepresentationTheory_Saxl_PathContraction
import Definitions.Def_OAI_RepresentationTheory_Saxl_ColumnContraction
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandPairing
import Definitions.Def_OAI_RepresentationTheory_Saxl_CyclicSector
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandSupport
import Definitions.Def_OAI_RepresentationTheory_Saxl_ShapeRigidity
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtClassification
import Definitions.Def_OAI_RepresentationTheory_Saxl_SupportSeparation
import Theorems.Thm_OAI_Saxl_irreducible_equiv_specht
import Theorems.Thm_OAI_Saxl_polytabloid_rowWord
import Theorems.Thm_OAI_Saxl_specht_rows_of_hom

-- ---- from OAI.RepresentationTheory.Saxl.SpechtSubmodule ----
namespace OAI

noncomputable section

open scoped TensorProduct

universe uG uV

namespace Saxl

/- The actual row-tabloid permutation module, embedded in the word space. -/
/- The Ferrers shape forces the column antisymmetrizer to have rank one
on the row-tabloid module. -/
/- On words, precomposition by a position permutation is a bijection. -/
lemma polytabloid_ne_zero {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) :
    polytabloid t ≠ 0 := by
  intro h
  have hh := congrFun h (rowWord t)
  rw [polytabloid_rowWord] at hh
  exact one_ne_zero hh

/- Every nonzero vector in the genuine complex Specht cyclic subspace
again generates that whole subspace. -/
/- Inclusion of a subrepresentation of a subrepresentation into the ambient space. -/
/- The complex polytabloid module is irreducible. -/
end Saxl

end

end OAI

-- ---- from OAI.RepresentationTheory.Saxl.SupportSeparation ----
namespace OAI

noncomputable section

open scoped TensorProduct

universe uR uX uY uG uV

namespace Saxl
open scoped MonoidAlgebra

/- In a semisimple module, support containment is equivalent to separation
by homomorphisms (multiplicities are immaterial for the band step). -/
theorem hom_separates_of_simple_support {R : Type uR} {X : Type uX} {Y : Type uY} [Ring R]
    [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    [IsSemisimpleModule R X]
    (h : ∀ S : Submodule R X, IsSimpleModule R S →
      ∃ f : S →ₗ[R] Y, f ≠ 0) (x : X) (hx : x ≠ 0) :
    ∃ f : X →ₗ[R] Y, f x ≠ 0 := by
  classical
  let K : Submodule R X := ⨅ f : X →ₗ[R] Y, LinearMap.ker f
  have hK : K = ⊥ := by
    rcases IsSemisimpleModule.eq_bot_or_exists_simple_le K with hk | ⟨S, hS, hs⟩
    · exact hk
    obtain ⟨f, hf⟩ := h S hs
    obtain ⟨F, hF⟩ := IsSemisimpleModule.extension_property S.subtype S.subtype_injective f
    exfalso
    apply hf
    ext s
    have hm : s.val ∈ K := hS s.property
    have he : F s.val = 0 := ((Submodule.mem_iInf _).mp hm F)
    change f s = 0
    exact (LinearMap.congr_fun hF s).symm.trans he
  by_contra hf
  push Not at hf
  apply hx
  have hm : x ∈ K := (Submodule.mem_iInf _).mpr (fun f => hf f)
  simpa only [hK, Submodule.mem_bot] using hm

end Saxl

namespace Saxl
open scoped MonoidAlgebra

/- The invariant-subspace and group-algebra subtype constructions agree. -/
lemma subrep_irreducible_of_simple {G : Type uG} {V : Type uV} [Group G] [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ G V} (S : Submodule ℂ[G] ρ.asModule)
    [IsSimpleModule ℂ[G] S] :
    Representation.IsIrreducible (Subrepresentation.ofSubmodule' S).toRepresentation := by
  apply (Representation.irreducible_iff_isSimpleModule_asModule _).mpr
  let e : (Subrepresentation.ofSubmodule' S).toRepresentation.asModule ≃ₗ[ℂ[G]] S :=
    subrepModuleEquiv (Subrepresentation.ofSubmodule' S)
  exact IsSimpleModule.congr e

end Saxl

namespace Saxl
open scoped MonoidAlgebra

theorem intertwining_separates_of_simple_support {G : Type uG} {X : Type uX} {Y : Type uY}
    [Group G] [Finite G] [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y]
    (ρ : Representation ℂ G X) (σ : Representation ℂ G Y)
    (h : ∀ S : Subrepresentation ρ, Representation.IsIrreducible S.toRepresentation →
      ∃ f : Representation.IntertwiningMap S.toRepresentation σ, f ≠ 0)
    (x : X) (hx : x ≠ 0) :
    ∃ f : Representation.IntertwiningMap ρ σ, f x ≠ 0 := by
  classical
  have hs (S : Submodule ℂ[G] ρ.asModule) (hS : IsSimpleModule ℂ[G] S) :
      ∃ f : S →ₗ[ℂ[G]] σ.asModule, f ≠ 0 := by
    let P := Subrepresentation.ofSubmodule' S
    let := hS
    obtain ⟨f, hf⟩ := h P (subrep_irreducible_of_simple S)
    let F := Representation.IntertwiningMap.equivLinearMapAsModule _ _ f
    let E : P.toRepresentation.asModule ≃ₗ[ℂ[G]] S := subrepModuleEquiv P
    refine ⟨F.comp E.symm.toLinearMap, ?_⟩
    intro hz
    apply hf
    apply (Representation.IntertwiningMap.equivLinearMapAsModule _ _).injective
    ext v
    have he := LinearMap.congr_fun hz (E v)
    change F v = 0
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      E.symm_apply_apply, LinearMap.zero_apply] using he
  obtain ⟨f, hf⟩ := hom_separates_of_simple_support hs (ρ.asModuleEquiv.symm x)
    (fun he => hx (ρ.asModuleEquiv.symm.injective (he.trans (map_zero _).symm)))
  exact ⟨(Representation.IntertwiningMap.equivLinearMapAsModule _ _).symm f, hf⟩

end Saxl

namespace Saxl
open scoped MonoidAlgebra

end Saxl

namespace Saxl

/- All constituents needed from a d-letter permutation module are detected
by a module containing each Specht type of height at most d. -/
theorem word_support_separates {n d : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Equiv.Perm (Fin n)) V)
    (h : ∀ (μ : YoungDiagram) (t : Tableau n μ), μ.colLen 0 ≤ d →
      ∃ f : Representation.IntertwiningMap (spechtRep t) σ, f ≠ 0)
    (x : WordSpace n d) (hx : x ≠ 0) :
    ∃ f : Representation.IntertwiningMap (wordRep n d) σ, f x ≠ 0 := by
  apply intertwining_separates_of_simple_support (wordRep n d) σ ?_ x hx
  intro S hS
  let := hS
  obtain ⟨p, ⟨e⟩⟩ := irreducible_equiv_specht S.toRepresentation
  let t := partitionTableau p
  let i : Representation.IntertwiningMap (spechtRep t) (wordRep n d) :=
    (subrepInclusion S).comp e.symm.toIntertwiningMap
  have hi : i ≠ 0 := by
    intro he
    have hz := congrArg (fun F : Representation.IntertwiningMap (spechtRep t) (wordRep n d) =>
      F ⟨polytabloid t, mem_cyclic _ _⟩) he
    have h0 : e.symm ⟨polytabloid t, mem_cyclic _ _⟩ = 0 := Subtype.ext hz
    have h1 := e.symm.injective (h0.trans (map_zero _).symm)
    exact polytabloid_ne_zero t (congrArg Subtype.val h1)
  obtain ⟨f, hf⟩ := h _ t (specht_rows_of_hom t i hi)
  refine ⟨f.comp e.toIntertwiningMap, ?_⟩
  intro he
  apply hf
  ext y
  obtain ⟨z, rfl⟩ := e.surjective y
  exact congrArg (fun F : Representation.IntertwiningMap S.toRepresentation σ => F z) he

end Saxl

end

end OAI

-- ---- platform node ----
open OAI OAI.Saxl
open scoped TensorProduct


theorem solution.{uV} : type_of% @_root_.OAI.Saxl.word_support_separates.{uV} := @_root_.OAI.Saxl.word_support_separates.{uV}
