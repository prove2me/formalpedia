-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ultra.pt_res
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:56:04.182222+00:00
-- url     : https://prove2.me/submissions/9974e515-73e2-45f6-8133-76d486a3f3ce

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
theorem _root_.solution {W W' : X.affineOpens} (h : W.1 ≤ W'.1) {A : Type} [CommRing A]
    (p : Γ(X, W.1) →+* A) : pt W' (p.comp (res h)) = pt W p := by
  have := IsAffineOpen.map_fromSpec W'.2 W.2 (homOfLE h).op
  simp only [pt, res, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
  simp [this]
end GlobalTheory.CompanionTheory.Ultra
