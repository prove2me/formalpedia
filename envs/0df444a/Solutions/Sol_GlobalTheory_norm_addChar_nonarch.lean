-- Prove2me | solution 1 for GlobalTheory.norm_addChar_nonarch
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:25:01.829863+00:00
-- url     : https://prove2.me/submissions/e6d4772d-3484-4140-9e4b-5bf27f6da541

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchroedingerOperatorHeisenbergInnerPreserving
import Theorems.Thm_GlobalTheory_SplitFlip_CondLE_mul
import Theorems.Thm_GlobalTheory_SplitWeil_Model_isCompact_int


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open GlobalTheory
open ValuativeRel
namespace GlobalTheory
theorem _root_.solution {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ0 : AddChar k ℂ) (hψ : Continuous ψ0) (t : k) : ‖ψ0 t‖ = 1 := by
  have hO : IsCompact (𝒪[k] : Set k) := by exact GlobalTheory.SplitWeil.Model.isCompact_int
  have hK : IsCompact ((fun u => t * u) '' (𝒪[k] : Set k)) := hO.image (continuous_const.mul continuous_id)
  obtain ⟨C, hC⟩ := (hK.image hψ).isBounded.exists_norm_le
  have hpow : ∀ n : ℤ, ‖ψ0 t‖ ^ n ≤ C := fun n => by
    have hmem : ψ0 (t * (n : k)) ∈ ψ0 '' ((fun u => t * u) '' (𝒪[k] : Set k)) :=
      ⟨t * n, ⟨n, intCast_mem _ n, rfl⟩, rfl⟩
    have := hC _ hmem
    rwa [mul_comm, ← zsmul_eq_mul, AddChar.map_zsmul_eq_zpow, norm_zpow] at this
  have hne : ψ0 t ≠ 0 := fun h => by
    have := AddChar.map_add_eq_mul ψ0 t (-t)
    rw [add_neg_cancel, AddChar.map_zero_eq_one, h, zero_mul] at this
    exact one_ne_zero this
  have hpos : 0 < ‖ψ0 t‖ := norm_pos_iff.2 hne
  refine le_antisymm ?_ ?_
  · by_contra h
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C (not_le.1 h)
    exact absurd (hpow n) (by rw [zpow_natCast]; exact not_le.2 hn)
  · by_contra h
    have h1 : 1 < ‖ψ0 t‖⁻¹ := one_lt_inv₀ hpos |>.2 (not_le.1 h)
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C h1
    have := hpow (-(n : ℤ))
    rw [_root_.zpow_neg, zpow_natCast, ← inv_pow] at this
    exact absurd this (not_le.2 hn)
end GlobalTheory
