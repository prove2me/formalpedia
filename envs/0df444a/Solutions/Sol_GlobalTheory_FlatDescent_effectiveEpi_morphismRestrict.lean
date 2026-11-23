-- Prove2me | solution 1 for GlobalTheory.FlatDescent.effectiveEpi_morphismRestrict
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:37:32.871795+00:00
-- url     : https://prove2.me/submissions/df6a2288-54cd-47e7-a883-37ca0e0cffe2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAppTopEqOfEffectiveEpi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry Opposite
open GlobalTheory
open GlobalTheory.FlatDescent
universe u
variable {X Y Z : Scheme.{u}}
namespace GlobalTheory.FlatDescent
theorem _root_.solution (p : Y ⟶ X) [Flat p] [Surjective p] [QuasiCompact p]
    (U : X.Opens) : EffectiveEpi (p ∣_ U) := by
  have : Flat (p ∣_ U) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict p U).flip ‹_›
  have : Surjective (p ∣_ U) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict p U).flip ‹_›
  have : QuasiCompact (p ∣_ U) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict p U).flip ‹_›
  infer_instance
end GlobalTheory.FlatDescent
