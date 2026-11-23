-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ultra.spec_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:17:53.888206+00:00
-- url     : https://prove2.me/submissions/5f681f4d-4f0d-4ac5-add1-9c4926da29b1

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_CubeTheorem_SchemeModels
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsFiniteAffineCover
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IsProperSpreadsOut

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Filter
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ultra
variable {R₀ R : Type} [CommRing R₀] [CommRing R] {X Y : Scheme.{0}}
  (f₀ : X ⟶ Spec (CommRingCat.of R₀))
namespace GlobalTheory.CompanionTheory.Ultra
theorem _root_.solution {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (p : B →+* C) (q : A →+* B) :
    Spec.map (CommRingCat.ofHom (p.comp q)) =
      Spec.map (CommRingCat.ofHom p) ≫ Spec.map (CommRingCat.ofHom q) := by
  rw [CommRingCat.ofHom_comp, Spec.map_comp]
end GlobalTheory.CompanionTheory.Ultra
