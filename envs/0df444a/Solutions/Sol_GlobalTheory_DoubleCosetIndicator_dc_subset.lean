-- Prove2me | solution 1 for GlobalTheory.DoubleCosetIndicator.dc_subset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:33:03.473402+00:00
-- url     : https://prove2.me/submissions/fcd61031-46ec-4229-bcce-a3d7dbdd1679

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsEqSumIndicator

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DoubleCosetIndicator
namespace GlobalTheory.DoubleCosetIndicator
theorem _root_.solution {G : Type} [Group G] (R K : Subgroup G) {s t x : G}
    (hs : x ∈ dc R K s) (ht : x ∈ dc R K t) : dc R K s ⊆ dc R K t := by
  rintro y ⟨a, ha, b, hb, rfl⟩
  obtain ⟨r, hr, κ, hκ, hx⟩ := hs
  obtain ⟨r', hr', κ', hκ', hx'⟩ := ht
  have hrs : r * s * κ = r' * t * κ' := hx.symm.trans hx'
  have hs' : s = r⁻¹ * r' * t * κ' * κ⁻¹ := by
    calc s = r⁻¹ * (r * s * κ) * κ⁻¹ := by group
      _ = r⁻¹ * (r' * t * κ') * κ⁻¹ := by rw [hrs]
      _ = r⁻¹ * r' * t * κ' * κ⁻¹ := by group
  refine ⟨a * r⁻¹ * r', R.mul_mem (R.mul_mem ha (R.inv_mem hr)) hr', κ' * κ⁻¹ * b,
    K.mul_mem (K.mul_mem hκ' (K.inv_mem hκ)) hb, ?_⟩
  rw [hs']
  group
end GlobalTheory.DoubleCosetIndicator
