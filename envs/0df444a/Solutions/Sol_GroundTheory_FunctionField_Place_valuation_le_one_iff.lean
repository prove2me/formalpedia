-- Prove2me | solution 1 for GroundTheory.FunctionField.Place.valuation_le_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:55:05.020431+00:00
-- url     : https://prove2.me/submissions/5e92f453-bae8-4bd9-8cab-99546737ec0b

import Mathlib
import Definitions.Def_GroundTheory_FunctionField_PlaceDefs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.FunctionField
open IntermediateField
open scoped WithZero
open Polynomial
variable (k K : Type*) [Field k] [Field K] [Algebra k K]
open GroundTheory.FunctionField.Place
variable {k K} (v : Place k K)
variable [IsFunctionField k K]
namespace GroundTheory.FunctionField.Place
theorem _root_.solution (x : K) : v.valuation x ≤ 1 ↔ x ∈ v.ring := by
  constructor
  · intro h
    by_contra hx
    have hx0 : x ≠ 0 := fun h0 => hx (h0 ▸ v.ring.zero_mem)
    have hinv : x⁻¹ ∈ v.ring.nonunits := v.ring.inv_mem_nonunits_iff.2 (Or.inr hx)
    obtain ⟨hr, hrm⟩ := v.ring.mem_nonunits_iff_exists_mem_maximalIdeal.1 hinv
    have hlt : v.valuation x⁻¹ < 1 :=
      (v.heightOneSpectrum.valuation_lt_one_iff_mem (K := K) ⟨x⁻¹, hr⟩).2 hrm
    rw [map_inv₀, inv_lt_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hx0))] at hlt
    exact absurd h (not_le.2 hlt)
  · intro hx
    exact v.heightOneSpectrum.valuation_le_one (K := K) (⟨x, hx⟩ : v.ring)
end GroundTheory.FunctionField.Place
