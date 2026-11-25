-- Prove2me | solution 1 for GroundTheory.Global.eq_zero_of_forall_mem_maximalIdeal_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:08:38.33275+00:00
-- url     : https://prove2.me/submissions/7d15f7c3-043e-4fa2-b75b-b20eb21a16ef

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_GroundTheory_LocalFields_FilteredSurj
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_LocalIndex

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
namespace GroundTheory.Global
theorem _root_.solution {x : 𝒪[K]} (hx : ∀ k, x ∈ 𝓂[K] ^ k) : x = 0 := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  by_contra h0
  obtain ⟨m, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 hϖ
  have h := (mem_maximalIdeal_pow_iff hϖ).mp (hx (m + 1))
  rw [pow_succ, mul_comm (u : 𝒪[K]), mul_dvd_mul_iff_left (pow_ne_zero m hϖ.ne_zero)] at h
  exact hϖ.not_isUnit (isUnit_of_dvd_unit h u.isUnit)
end GroundTheory.Global
