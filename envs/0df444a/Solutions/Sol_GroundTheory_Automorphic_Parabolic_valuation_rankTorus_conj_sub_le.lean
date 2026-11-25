-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.valuation_rankTorus_conj_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:44:37.608334+00:00
-- url     : https://prove2.me/submissions/4e70a086-0d5d-4013-a03f-8187738d0914

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolic
import Definitions.Def_GroundTheory_AutomorphicForms_AffineBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_IwahoriFactorization
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_valuation_zpow_mul_le_pow_mul
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_blockRank_eq
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_blockRank_lt
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_mem_unipotentRadical
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_rankTorus_conj_apply


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
  {n : ℕ} {α : Type*} [LinearOrder α] {β : Fin n → α}
local notation "ϖ" => ((GLnLocal.uniformizer F : 𝒪[F]) : F)
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution {e : ℕ} {u : GL (Fin n) F}
    (hu : u ∈ unipotentRadical F n β) (i j : Fin n) :
    valuation F ((rankTorus F n β e * u * (rankTorus F n β e)⁻¹ : GL (Fin n) F) i j -
      (1 : Matrix (Fin n) (Fin n) F) i j) ≤
        valuation F ϖ ^ e * valuation F (u i j - (1 : Matrix (Fin n) (Fin n) F) i j) := by
  obtain ⟨hP, h1⟩ := mem_unipotentRadical.1 hu
  rw [rankTorus_conj_apply]
  rcases lt_trichotomy (β i) (β j) with h | h | h
  · have hij : i ≠ j := fun hh => h.ne (by rw [hh])
    rw [one_apply_ne hij, sub_zero, sub_zero]
    refine valuation_zpow_mul_le_pow_mul ?_
    have := blockRank_lt h
    have : e * blockRank β i + e ≤ e * blockRank β j := by nlinarith
    push_cast
    omega
  · rw [h1 i j h, blockRank_eq h, sub_self, zpow_zero, one_mul, sub_self, map_zero]
    exact zero_le
  · rw [hP h, mul_zero, one_apply_ne (fun hh => h.ne' (by rw [hh])), sub_zero, map_zero]
    exact zero_le
end GroundTheory.Automorphic.Parabolic
