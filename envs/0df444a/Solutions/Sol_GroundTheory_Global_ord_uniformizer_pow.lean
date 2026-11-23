-- Prove2me | solution 1 for GroundTheory.Global.ord_uniformizer_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:59:35.658981+00:00
-- url     : https://prove2.me/submissions/ae490e34-e711-471e-b6ee-a09dd40147d9

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_GroundTheory_LocalFields_FilteredSurj
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_LocalIndex
import Theorems.Thm_GroundTheory_LocalField_ord_mul
import Theorems.Thm_GroundTheory_LocalField_ord_uniformizer


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open ValuativeRel IsLocalRing GroundTheory.LocalField
open scoped WithZero
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {n : ℕ}
namespace GroundTheory.Global
theorem _root_.solution {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) (d : ℕ) : ord ((ϖ : K) ^ d) = d := by
  have h0 : (ϖ : K) ≠ 0 := by exact_mod_cast hϖ.ne_zero
  induction d with
  | zero => simp [ord]
  | succ d ih =>
    rw [pow_succ, ord_mul (pow_ne_zero _ h0) h0, ih, ord_uniformizer hϖ]
    push_cast
    ring
end GroundTheory.Global
