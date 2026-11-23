-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ultra.spec_inj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:26:06.071601+00:00
-- url     : https://prove2.me/submissions/3255a4c6-3ab8-4925-a340-8efe282da238

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
theorem _root_.solution {A B : Type} [CommRing A] [CommRing B] {p q : A →+* B}
    (h : Spec.map (CommRingCat.ofHom p) = Spec.map (CommRingCat.ofHom q)) : p = q :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)
end GlobalTheory.CompanionTheory.Ultra
