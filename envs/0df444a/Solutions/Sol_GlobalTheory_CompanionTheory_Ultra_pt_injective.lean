-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ultra.pt_injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:56:03.996104+00:00
-- url     : https://prove2.me/submissions/bd97a040-2317-4d04-bbf0-eee66f3bb7ea

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsFiniteAffineCover

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
open Filter
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ultra
variable {ι : Type} (U : Ultrafilter ι)
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
variable {X : Scheme.{0}}
namespace GlobalTheory.CompanionTheory.Ultra
theorem _root_.solution (W : X.affineOpens) {A : Type} [CommRing A] {p q : Γ(X, W.1) →+* A}
    (h : pt W p = pt W q) : p = q := by
  have h' := (cancel_mono W.2.fromSpec).1 h
  have := Spec.map_injective h'
  exact congrArg CommRingCat.Hom.hom this
end GlobalTheory.CompanionTheory.Ultra
