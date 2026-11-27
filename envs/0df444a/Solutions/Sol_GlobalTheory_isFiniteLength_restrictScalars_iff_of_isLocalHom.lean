-- Prove2me | solution 1 for GlobalTheory.isFiniteLength_restrictScalars_iff_of_isLocalHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:38:59.458308+00:00
-- url     : https://prove2.me/submissions/66b880bd-608b-4c28-93d6-19bff63473d3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthRestrictScalarsEqSumInertiaDegOfSubset
import Theorems.Thm_GlobalTheory_length_restrictScalars_of_isLocalHom

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
    IsFiniteLength R X ↔ IsFiniteLength S X := by
  rw [← Module.length_ne_top_iff, ← Module.length_ne_top_iff,
    length_restrictScalars_of_isLocalHom R S X]
  have h : (Module.finrank (ResidueField R) (ResidueField S) : ℕ∞) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ResidueField R) (M := ResidueField S)).ne'
  constructor
  · intro h1 h2
    exact h1 (by rw [h2, ENat.top_mul h])
  · intro h1
    exact WithTop.mul_ne_top h1 (ENat.coe_ne_top _)
end GlobalTheory
