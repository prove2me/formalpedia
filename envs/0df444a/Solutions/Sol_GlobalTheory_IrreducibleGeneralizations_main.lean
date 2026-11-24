-- Prove2me | solution 1 for GlobalTheory.IrreducibleGeneralizations.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:28:06.553455+00:00
-- url     : https://prove2.me/submissions/4101d54a-1147-41b7-b12a-fc5fa4f52212

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIrreducibleGeneralizations
import Theorems.Thm_GlobalTheory_IrreducibleGeneralizations_component_eq_closure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1
open GlobalTheory GlobalTheory.IrreducibleGeneralizations
open AlgebraicGeometry Topology
namespace GlobalTheory.IrreducibleGeneralizations
theorem _root_.solution : ∀ {X : AlgebraicGeometry.Scheme} {x : ↥X} [IsDomain (↑(TopCat.Presheaf.stalk (AlgebraicGeometry.PresheafedSpace.presheaf (AlgebraicGeometry.SheafedSpace.toPresheafedSpace (AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace (AlgebraicGeometry.Scheme.toLocallyRingedSpace X)))) x) : Type u_1)] {Z W : Set ↥X}, Z ∈ irreducibleComponents ↥X → W ∈ irreducibleComponents ↥X → x ∈ Z → x ∈ W → Z = W := by
  intro X x _ Z W hZ hW hxZ hxW
  rw [component_eq_closure hZ hxZ, component_eq_closure hW hxW]
end GlobalTheory.IrreducibleGeneralizations
