-- Prove2me | solution 1 for GroundTheory.Global.KummerIndex.ker_ordMod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:36:00.53313+00:00
-- url     : https://prove2.me/submissions/60700c7b-9fb1-408f-bb8a-4580d885e998

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_LocalIndexAtPlace
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IndexProductFormula
import Definitions.Def_GroundTheory_ProfiniteCohomology_KummerBasic
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_KummerIndexLemma_HasEnoughRootsOfUnityOfRingHom
import Theorems.Thm_GroundTheory_Global_KummerIndex_mem_localUnits_iff
import Theorems.Thm_GroundTheory_Global_KummerIndex_exists_uniformizer_unit
import Theorems.Thm_GroundTheory_Global_coe_integerEquivAdicCompletionIntegers
import Theorems.Thm_GroundTheory_Global_residueFieldEquiv_mk
import Theorems.Thm_GroundTheory_ProfCoh_kummerPairingLeft_apply
import Theorems.Thm_GroundTheory_ProfCoh_kummerPairingRight_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.coe_integerEquivAdicCompletionIntegers
attribute [local simp] GroundTheory.Global.residueFieldEquiv_mk
attribute [local simp] GroundTheory.ProfCoh.kummerPairingLeft_apply
attribute [local simp] GroundTheory.ProfCoh.kummerPairingRight_apply



set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Global
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField GroundTheory.ProfCoh WithZero
open GroundTheory.Global.KummerIndex
variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
namespace GroundTheory.Global.KummerIndex
theorem _root_.solution (p : ℕ) [NeZero p] :
    (ordMod v p).ker = localUnits v ⊔ unitsPow (v.adicCompletion K) p := by
  apply le_antisymm
  · intro x hx
    have hx0 : Valued.v (x : v.adicCompletion K) ≠ 0 := (Valuation.ne_zero_iff _).2 x.ne_zero
    rw [MonoidHom.mem_ker] at hx
    change Multiplicative.ofAdd (((-log (Valued.v (x : v.adicCompletion K)) : ℤ) : ZMod p)) = 1
      at hx
    rw [ofAdd_eq_one, ZMod.intCast_zmod_eq_zero_iff_dvd] at hx
    obtain ⟨k, hk⟩ := hx
    obtain ⟨π, hπ⟩ := exists_uniformizer_unit v
    have hu : x * ((π ^ k) ^ p)⁻¹ ∈ localUnits v := by
      rw [mem_localUnits_iff, Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀,
        Units.val_pow_eq_pow_val, Units.val_zpow_eq_zpow_val, map_pow, map_zpow₀, hπ,
        ← exp_zsmul, ← exp_nsmul, ← exp_log hx0]
      rw [← exp_neg, ← exp_add]
      have : -(-log (Valued.v (x : v.adicCompletion K))) = (p : ℤ) * (-k) := by
        rw [hk]; ring
      rw [exp_eq_one]
      rw [neg_neg] at this
      rw [this]
      simp only [smul_eq_mul, nsmul_eq_mul]
      ring
    have hx' : x = (x * ((π ^ k) ^ p)⁻¹) * (π ^ k) ^ p := by group
    rw [hx']
    exact Subgroup.mul_mem_sup hu ⟨π ^ k, rfl⟩
  · rw [sup_le_iff]
    constructor
    · intro x hx
      rw [MonoidHom.mem_ker]
      change Multiplicative.ofAdd (((-log (Valued.v (x : v.adicCompletion K)) : ℤ) : ZMod p)) = 1
      rw [(mem_localUnits_iff).1 hx, log_one]
      simp
    · rintro _ ⟨b, rfl⟩
      have hb : Valued.v (b : v.adicCompletion K) ≠ 0 := (Valuation.ne_zero_iff _).2 b.ne_zero
      rw [MonoidHom.mem_ker]
      change Multiplicative.ofAdd (((-log (Valued.v (((b ^ p : (v.adicCompletion K)ˣ)) :
        v.adicCompletion K)) : ℤ) : ZMod p)) = 1
      rw [Units.val_pow_eq_pow_val, map_pow, log_pow]
      simp
end GroundTheory.Global.KummerIndex
