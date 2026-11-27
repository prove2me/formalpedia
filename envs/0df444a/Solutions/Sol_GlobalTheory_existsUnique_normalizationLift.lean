-- Prove2me | solution 1 for GlobalTheory.existsUnique_normalizationLift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:38:10.235114+00:00
-- url     : https://prove2.me/submissions/fc3eed03-ce5e-41a7-87a8-d4d0dbc120a8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoNormalizationPullbackOfToIntegralClosure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open GlobalTheory
variable {X Y T Z : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
variable (a : X ⟶ T) (g : T ⟶ Z) [IsIntegralHom g] (b : Y ⟶ Z) (H : a ≫ g = f ≫ b)
include H
namespace GlobalTheory
theorem _root_.solution :
    ∃! m : f.normalization ⟶ T, f.toNormalization ≫ m = a ∧ m ≫ g = f.fromNormalization ≫ b :=
  ⟨normalizationLift f a g b H, ⟨by simp, by simp⟩,
    fun _ h ↦ eq_normalizationLift f a g b H h.1 h.2⟩
end GlobalTheory
