-- Prove2me | solution 1 for GlobalTheory.length_restrictScalars_of_isLocalHom
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:53:49.708813+00:00
-- url     : https://prove2.me/submissions/02cb0c89-d0dc-44de-a32b-2aa5a9b26738

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthRestrictScalarsEqSumInertiaDegOfSubset

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory
variable (R S X : Type*) [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S] [Algebra R S]
  [IsLocalHom (algebraMap R S)] [AddCommGroup X] [Module R X] [Module S X] [IsScalarTower R S X]
namespace GlobalTheory
theorem _root_.solution
    [Module.Finite (ResidueField R) (ResidueField S)] :
    Module.length R X =
      Module.length S X * (Module.finrank (ResidueField R) (ResidueField S) : ℕ∞) := by
  rw [IsLocalRing.length_restrictScalars R S X, Module.length_eq_finrank]
end GlobalTheory
