-- Prove2me | solution 1 for GlobalTheory.Hk.RealChar.chi_real
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:37:58.844886+00:00
-- url     : https://prove2.me/submissions/b9c7d624-c2fd-4e8a-8d2d-bebe76dd5358

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExpSumBoundsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NormRayClassFamilyFOneGeOfRealCharacter

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
noncomputable section
open GlobalTheory GlobalTheory.Hk GlobalTheory.Hk.RealChar
namespace GlobalTheory.Hk.RealChar
theorem _root_.solution {𝓕 : LFam} {χ : AddChar 𝓕.G ℂ} (h : χ * χ = 1) (g : 𝓕.G) :
    χ g = 1 ∨ χ g = -1 := by
  have : χ g * χ g = 1 := by
    have := DFunLike.congr_fun h g
    simpa using this
  exact mul_self_eq_one_iff.1 this
end GlobalTheory.Hk.RealChar
