-- Prove2me | solution 1 for GroundTheory.Global.exists_natCast_eq_unit_mul_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:02:57.422726+00:00
-- url     : https://prove2.me/submissions/99d08385-435c-47f9-9941-0d2d0761a4d4

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_GroundTheory_LocalFields_FilteredSurj
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_LocalIndex
import Theorems.Thm_GroundTheory_Global_ord_uniformizer_pow
import Theorems.Thm_GroundTheory_LocalField_ord_mul
import Theorems.Thm_GroundTheory_LocalField_ord_unit


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
theorem _root_.solution (hn : (n : K) ≠ 0) {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) :
    ∃ (d : ℕ) (ε : 𝒪[K]ˣ), (n : 𝒪[K]) = ε * ϖ ^ d ∧ ord (n : K) = d := by
  have h0 : (n : 𝒪[K]) ≠ 0 := by
    intro h
    apply hn
    simpa using congrArg (fun x : 𝒪[K] ↦ (x : K)) h
  obtain ⟨d, ε, h⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 hϖ
  refine ⟨d, ε, h, ?_⟩
  have hK : (n : K) = ((ε : 𝒪[K]) : K) * (ϖ : K) ^ d := by
    simpa using congrArg (fun x : 𝒪[K] ↦ (x : K)) h
  have hε : ((ε : 𝒪[K]) : K) ≠ 0 := by exact_mod_cast ε.ne_zero
  have hϖd : (ϖ : K) ^ d ≠ 0 := pow_ne_zero _ (by exact_mod_cast hϖ.ne_zero)
  rw [hK, ord_mul hε hϖd, ord_unit, ord_uniformizer_pow hϖ, zero_add]
end GroundTheory.Global
