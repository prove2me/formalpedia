-- Prove2me | solution 1 for GlobalTheory.birational_of_isIso_morphismRestrict
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:07:15.450314+00:00
-- url     : https://prove2.me/submissions/33b0e3ca-e553-4a81-a37a-0f925f0bb649

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_BijectiveAlgebraMapIntegralClosureOfBirational
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
theorem _root_.solution (f : X ⟶ Y) [IsIntegral X] [IsIntegral Y]
    (U : Y.Opens) (hU : Nonempty U) [IsIso (f ∣_ U)] :
    IsDominant f ∧ IsIso (f.stalkMap (genericPoint X)) := by
  obtain ⟨y, hy⟩ := hU
  obtain ⟨x, -⟩ := (f ∣_ U).surjective ⟨y, hy⟩
  refine ⟨⟨?_⟩, ?_⟩
  · refine (U.isOpen.dense ⟨y, hy⟩).mono ?_
    intro z hz
    obtain ⟨w, hw⟩ := (f ∣_ U).surjective ⟨z, hz⟩
    exact ⟨w.1, by simpa using congrArg Subtype.val hw⟩
  · have hg : genericPoint X ∈ f ⁻¹ᵁ U :=
      ((genericPoint_spec X).mem_open_set_iff (f ⁻¹ᵁ U).isOpen).2 ⟨x.1, trivial, x.2⟩
    simpa using isIso_stalkMap_of_comp_isOpenImmersion f (f ⁻¹ᵁ U).ι (f ∣_ U ≫ U.ι)
      (morphismRestrict_ι f U).symm ⟨_, hg⟩
end _root_.GlobalTheory
end GlobalTheory
