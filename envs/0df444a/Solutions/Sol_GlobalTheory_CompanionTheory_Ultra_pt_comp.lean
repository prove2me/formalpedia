-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ultra.pt_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:28:34.931929+00:00
-- url     : https://prove2.me/submissions/e2f61f49-8e49-41b8-a2d4-60fb6cf2963d

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_CubeTheorem_SchemeModels
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsFiniteAffineCover
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IsProperSpreadsOut
import Theorems.Thm_GlobalTheory_CompanionTheory_Ultra_fromSpec_comp
import Theorems.Thm_GlobalTheory_CompanionTheory_Ultra_spec_comp

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
theorem _root_.solution (W : X.affineOpens) {A : Type} [CommRing A] (p : Γ(X, W.1) →+* A) :
    pt W p ≫ f₀ = Spec.map (CommRingCat.ofHom (p.comp (baseHom f₀ W))) := by
  rw [pt, Category.assoc, fromSpec_comp, spec_comp]
end GlobalTheory.CompanionTheory.Ultra
