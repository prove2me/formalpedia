-- Prove2me | solution 1 for GlobalTheory.FlatDescent.isUnit_app_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:43:43.52527+00:00
-- url     : https://prove2.me/submissions/c585c6a9-71a8-40b4-ba45-bef613c22fcc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAppTopEqOfEffectiveEpi
import Theorems.Thm_GlobalTheory_FlatDescent_isUnit_appTop_iff
import Theorems.Thm_GlobalTheory_FlatDescent_appTop_morphismRestrict_apply
import Theorems.Thm_GlobalTheory_FlatDescent_effectiveEpi_morphismRestrict

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
theorem _root_.solution (p : Y ⟶ X) [Flat p] [Surjective p] [QuasiCompact p] (U : X.Opens)
    (a : Γ(X, U)) : IsUnit (p.app U a) ↔ IsUnit a := by
  have := effectiveEpi_morphismRestrict p U
  rw [← isUnit_map_iff (p ⁻¹ᵁ U).topIso.inv.hom, ← appTop_morphismRestrict_apply,
    isUnit_appTop_iff, isUnit_map_iff]
end GlobalTheory.FlatDescent
