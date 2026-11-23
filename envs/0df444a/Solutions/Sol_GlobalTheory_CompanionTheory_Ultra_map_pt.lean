-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ultra.map_pt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:16:34.570251+00:00
-- url     : https://prove2.me/submissions/0d0b529a-6b7c-4316-bd35-e30ae256be5a

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
theorem _root_.solution (W : X.affineOpens) {A B : Type} [CommRing A] [CommRing B] (p : Γ(X, W.1) →+* A)
    (q : A →+* B) :
    Spec.map (CommRingCat.ofHom q) ≫ pt W p = pt W (q.comp p) := by
  simp [pt, CommRingCat.ofHom_comp, Spec.map_comp]
end GlobalTheory.CompanionTheory.Ultra
