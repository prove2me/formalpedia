-- Prove2me | solution 1 for GlobalTheory.isIso_cechComplexMap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:48:29.963502+00:00
-- url     : https://prove2.me/submissions/e5604090-457b-41d3-8e7f-5fd1d2213f14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits
universe v v' u u'
open GlobalTheory
variable {ι : Type} [LinearOrder ι] {R : Type u} [Ring R]
namespace GlobalTheory
theorem _root_.solution {A B : Cube.{v} ι R} (φ : A ⟶ B)
    (h : ∀ s : Finset ι, s.Nonempty → Function.Bijective (φ.app s).hom) :
    IsIso (cechComplexMap φ) := by
  have : ∀ p, IsIso ((cechComplexMap φ).f p) := fun p => by
    rw [ConcreteCategory.isIso_iff_bijective]
    have h' := fun s : {s : Finset ι // s.card = p + 1} =>
      h s.1 (Finset.card_pos.1 (by have := s.2; omega))
    exact Function.Bijective.piMap h'
  exact HomologicalComplex.Hom.isIso_of_components _
end GlobalTheory
