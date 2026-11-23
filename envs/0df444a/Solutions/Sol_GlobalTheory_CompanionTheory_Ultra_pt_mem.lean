-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ultra.pt_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:56:04.163647+00:00
-- url     : https://prove2.me/submissions/5fb9f290-9c3a-4c03-8ff6-b5837a2701b6

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
theorem _root_.solution (W : X.affineOpens) {A : Type} [CommRing A] (p : Γ(X, W.1) →+* A)
    (x : Spec (CommRingCat.of A)) : (pt W p) x ∈ W.1 := by
  have : (W.2.fromSpec) ((Spec.map (CommRingCat.ofHom p)) x) ∈ Set.range W.2.fromSpec :=
    ⟨_, rfl⟩
  rw [W.2.range_fromSpec] at this
  simpa [pt] using this
end GlobalTheory.CompanionTheory.Ultra
