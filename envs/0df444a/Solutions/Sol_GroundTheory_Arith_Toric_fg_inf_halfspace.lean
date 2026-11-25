-- Prove2me | solution 1 for GroundTheory.Arith.Toric.fg_inf_halfspace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:11:58.166971+00:00
-- url     : https://prove2.me/submissions/41ce6ae4-1898-4d71-b3c3-4fd05d886442

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_ExistsDualNegOfNotMemHullFinset
import Theorems.Thm_GroundTheory_Arith_Toric_hull_inf_halfspace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Toric
open Module PointedCone
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {V W : Type*} [AddCommGroup V] [Module 𝕜 V] [AddCommGroup W] [Module 𝕜 W]
namespace GroundTheory.Arith.Toric
theorem _root_.solution {C : PointedCone 𝕜 V} (hC : C.FG) (g : Dual 𝕜 V) :
    (C ⊓ (positive 𝕜 𝕜).comap g).FG := by
  classical
  obtain ⟨S, rfl⟩ := hC
  rw [hull_inf_halfspace]
  exact ⟨_, rfl⟩
end GroundTheory.Arith.Toric
