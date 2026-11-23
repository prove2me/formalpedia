-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ultra.fromSpec_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:26:05.445591+00:00
-- url     : https://prove2.me/submissions/02c626aa-2a5a-4404-bd5b-8552c51dd651

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
theorem _root_.solution (W : X.affineOpens) :
    W.2.fromSpec ≫ f₀ = Spec.map (CommRingCat.ofHom (baseHom f₀ W)) := by
  simp [baseHom]
end GlobalTheory.CompanionTheory.Ultra
