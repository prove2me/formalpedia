-- Prove2me | solution 1 for GlobalTheory.stalkMap_flat_formallyEtale_essFiniteType_of_etale_restrict
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:52:38.155924+00:00
-- url     : https://prove2.me/submissions/003bab88-09a1-4280-88d6-9328c9d991c5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StalkMapFlatFormallyEtaleEssFiniteTypeOfEtaleRes
import Theorems.Thm_GlobalTheory_ringHom_formallyEtale_respectsIso
import Theorems.Thm_GlobalTheory_formallyEtale_stalkMap_of_etale

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open GlobalTheory
universe u
namespace GlobalTheory
theorem _root_.solution :
    ∀ (M W : Scheme.{0}) (f : M ⟶ W) (U : M.Opens), Etale (U.ι ≫ f) → ∀ y ∈ U,
      (f.stalkMap y).hom.Flat ∧ (f.stalkMap y).hom.FormallyEtale ∧
        (f.stalkMap y).hom.EssFiniteType := by
  intro M W f U hg y hy
  have key : ∀ (x : M) (z : U), U.ι z = x →
      (f.stalkMap x).hom.Flat ∧ (f.stalkMap x).hom.FormallyEtale ∧
        (f.stalkMap x).hom.EssFiniteType := by
    intro x z hz
    subst hz
    have h1 := Flat.stalkMap (U.ι ≫ f) z
    have h2 := formallyEtale_stalkMap_of_etale (U.ι ≫ f) z
    have h3 := LocallyOfFiniteType.stalkMap (U.ι ≫ f) z
    have e := Scheme.Hom.stalkMap_comp U.ι f z
    rw [e] at h1 h2 h3
    have : IsIso (U.ι.stalkMap z) := (IsOpenImmersion.iff_isIso_stalkMap.1 inferInstance).2 _
    refine ⟨?_, ?_, ?_⟩
    · exact (RingHom.Flat.respectsIso.cancel_right_isIso _ _).1 h1
    · exact (ringHom_formallyEtale_respectsIso.cancel_right_isIso _ _).1 h2
    · exact (RingHom.EssFiniteType.respectsIso.cancel_right_isIso _ _).1 h3
  exact key y ⟨y, hy⟩ (by simp)
end GlobalTheory
