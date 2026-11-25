-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.rankTorus_inv_conj_apply_facts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:34:11.758797+00:00
-- url     : https://prove2.me/submissions/3e0a471c-0d62-47b0-b6c3-4b27e63f5f97

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolicGroups
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresParabolic
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolicLocal
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_zpow_mul_mem
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_valuation_zpow_mul_le
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_rankTorus_inv_conj_apply
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_blockRank_eq
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_blockRank_lt
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_mem_oppositeUnipotentRadical


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal ValuativeRel Topology Filter Set
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable (F) (n : ℕ) {α : Type*} [LinearOrder α] (β : Fin n → α)
variable {F n β}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution {k t m : ℕ} (hm : k + t ≤ m) {z : GL (Fin n) F}
    (hz : z ∈ oppositeUnipotentRadical F n β)
    (hb : ∀ i j, (GLnLocal.uniformizer F : F) ^ k * z i j ∈ 𝒪[F]) (i j : Fin n) :
    ((rankTorus F n β m)⁻¹ * z * rankTorus F n β m : GL (Fin n) F) i j ∈ 𝒪[F] ∧
      valuation F (((rankTorus F n β m)⁻¹ * z * rankTorus F n β m : GL (Fin n) F) i j -
        (1 : Matrix (Fin n) (Fin n) F) i j) ≤ valuation F (GLnLocal.uniformizer F : F) ^ t := by
  obtain ⟨hlow, h1⟩ := mem_oppositeUnipotentRadical.1 hz
  rw [rankTorus_inv_conj_apply]
  rcases lt_trichotomy (β i) (β j) with h | h | h
  · rw [hlow i j h, mul_zero, one_apply_ne (fun e => h.ne (by rw [e])), sub_zero, map_zero]
    exact ⟨zero_mem _, zero_le'⟩
  · rw [h1 i j h, blockRank_eq h, sub_self, zpow_zero, one_mul, sub_self, map_zero]
    refine ⟨?_, zero_le'⟩
    by_cases hij : i = j
    · rw [hij, one_apply_eq]
      exact one_mem _
    · rw [one_apply_ne hij]
      exact zero_mem _
  · have hr := blockRank_lt h
    have hexp : ((k + t : ℕ) : ℤ) ≤
        ((m * blockRank β i : ℕ) : ℤ) - ((m * blockRank β j : ℕ) : ℤ) := by
      have : m * blockRank β j + m ≤ m * blockRank β i := by nlinarith
      push_cast
      omega
    rw [one_apply_ne (fun e => h.ne' (by rw [e])), sub_zero]
    exact ⟨zpow_mul_mem (hb i j) (by omega), valuation_zpow_mul_le (hb i j) hexp⟩
end GroundTheory.Automorphic.Parabolic
