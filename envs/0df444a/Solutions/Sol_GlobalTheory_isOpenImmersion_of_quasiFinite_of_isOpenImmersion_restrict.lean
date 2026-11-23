-- Prove2me | solution 1 for GlobalTheory.isOpenImmersion_of_quasiFinite_of_isOpenImmersion_restrict
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:28:41.179978+00:00
-- url     : https://prove2.me/submissions/be00aff9-f119-47a4-a69e-5609d8184cb6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_BijectiveAlgebraMapIntegralClosureOfBirational
import Theorems.Thm_GlobalTheory_isOpenImmersion_of_quasiFinite_of_isIso_stalkMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Topology
namespace GlobalTheory
universe u
section Normal
variable {X Y : Scheme.{u}}
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Topology in
variable {X Y : Scheme.{u}} in
private lemma isIso_stalkMap_of_comp_isOpenImmersion {W : Scheme.{u}} (f : X ⟶ Y) (c : W ⟶ X)
    [IsOpenImmersion c] (g : W ⟶ Y) [hg : IsOpenImmersion g] (h : c ≫ f = g) (w : W) :
    IsIso (f.stalkMap (c w)) := by
  subst h
  have h' := Scheme.Hom.stalkMap_comp c f w
  haveI : IsIso ((c ≫ f).stalkMap w) := inferInstance
  haveI : IsIso (f.stalkMap (c w) ≫ c.stalkMap w) := h' ▸ this
  exact IsIso.of_isIso_comp_right _ (c.stalkMap w)
end Normal
section Constructible
end Constructible
section Etale
variable {X Y : Scheme.{u}} {K : Type u} [Field K] [IsAlgClosed K]
end Etale
end GlobalTheory
end

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Topology
open GlobalTheory
universe u
variable {X Y : Scheme.{u}}
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Topology
variable {X Y : Scheme.{u}}
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution (f : X ⟶ Y) [IsSeparated f]
    [QuasiCompact f] [LocallyOfFiniteType f] [LocallyQuasiFinite f] [IsIntegral X] [IsIntegral Y]
    (hY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (V : X.Opens) (hV : Nonempty V) [IsOpenImmersion (V.ι ≫ f)] : IsOpenImmersion f := by
  obtain ⟨v, hv⟩ := hV
  have hg : genericPoint X ∈ V :=
    ((genericPoint_spec X).mem_open_set_iff V.isOpen).2 ⟨v, trivial, hv⟩
  haveI : IsIso (f.stalkMap (genericPoint X)) := by
    simpa using isIso_stalkMap_of_comp_isOpenImmersion f V.ι (V.ι ≫ f) rfl ⟨_, hg⟩
  haveI : IsDominant f := by
    refine ⟨((V.ι ≫ f).isOpenEmbedding.isOpen_range.dense ⟨_, ⟨v, hv⟩, rfl⟩).mono ?_⟩
    rintro _ ⟨w, rfl⟩
    exact ⟨V.ι w, (Scheme.Hom.comp_apply _ _ w).symm⟩
  exact _root_.GlobalTheory.isOpenImmersion_of_quasiFinite_of_isIso_stalkMap f hY
end _root_.GlobalTheory
end GlobalTheory
