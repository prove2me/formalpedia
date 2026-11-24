-- Prove2me | solution 1 for GlobalTheory.IrreducibleGeneralizations.isIrreducible_generalizations
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:53:50.610066+00:00
-- url     : https://prove2.me/submissions/23a51b9c-2c98-4660-9ba3-e99b8758d8e6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIrreducibleGeneralizations

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
theorem _root_.solution {X : Scheme.{u_1}} (x : X) [IsDomain (X.presheaf.stalk x)] :
    IsIrreducible {y : X | y ⤳ x} := by

  have hSpec : IsIrreducible (Set.univ : Set (PrimeSpectrum (X.presheaf.stalk x))) :=
    IrreducibleSpace.isIrreducible_univ _
  rw [← Scheme.range_fromSpecStalk, ← Set.image_univ]
  exact hSpec.image _ (X.fromSpecStalk x).continuous.continuousOn
end GlobalTheory.IrreducibleGeneralizations
