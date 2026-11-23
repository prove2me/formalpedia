-- Prove2me | solution 1 for GlobalTheory.exists_specMap_fromSpec_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:32:44.18486+00:00
-- url     : https://prove2.me/submissions/8ec5a858-b034-4b9b-9915-cd07c060f830

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
universe u
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {X : Scheme.{u}} {R : CommRingCat.{u}} (g : Spec R ⟶ X)
    {V : X.Opens} (hV : IsAffineOpen V) (hg : Set.range g ⊆ V) :
    ∃ φ : Γ(X, V) ⟶ R, Spec.map φ ≫ hV.fromSpec = g := by
  have hg' : Set.range g ⊆ Set.range hV.fromSpec := by rwa [hV.range_fromSpec]
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (IsOpenImmersion.lift hV.fromSpec g hg')
  exact ⟨φ, by rw [hφ, IsOpenImmersion.lift_fac]⟩
end GlobalTheory
