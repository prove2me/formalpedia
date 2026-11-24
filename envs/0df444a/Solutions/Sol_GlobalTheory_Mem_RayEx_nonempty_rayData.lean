-- Prove2me | solution 1 for GlobalTheory.Mem.RayEx.nonempty_rayData
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:23:52.949471+00:00
-- url     : https://prove2.me/submissions/ec3ef432-badc-4bb6-a4f3-124e3b353924

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayDataNonempty
import Theorems.Thm_GlobalTheory_Mem_RayEx_ne_zero_of_sub_one_mem
import Theorems.Thm_GlobalTheory_Mem_RayEx_ne_bot_of_isCoprime
import Theorems.Thm_GlobalTheory_Mem_RayEx_exists_group
import Theorems.Thm_GlobalTheory_Mem_RayEx_map_mul_mk

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.RayEx
open NumberField IsDedekindDomain
open Classical
namespace GlobalTheory.Mem.RayEx
theorem _root_.solution (K : Type) [Field K] [NumberField K] (M : ℕ) (hM : 2 ≤ M) : Nonempty (RayData K M) := by
  set m : Ideal (𝓞 K) := Ideal.span {(M : 𝓞 K)} with hmdef
  have hm0 : m ≠ ⊥ := by
    rw [hmdef, Ne, Ideal.span_singleton_eq_bot]
    exact Nat.cast_ne_zero.mpr (by omega)
  have hm : m ≠ ⊤ := by
    rw [hmdef, Ne, Ideal.span_singleton_eq_top]
    intro h
    have h' : IsUnit (algebraMap ℤ (𝓞 K) (M : ℤ)) := by simpa using h
    have := (isUnit_map_iff (algebraMap ℤ (𝓞 K)) _).mp h'
    rw [Int.isUnit_iff] at this
    omega
  haveI : Finite (𝓞 K ⧸ m) := Ideal.finiteQuotientOfFreeOfNeBot m hm0
  obtain ⟨G, _, _, φ, hs, he⟩ := exists_group hm
  refine ⟨{ G := G
            cls := fun I => if h : IsCoprime I m then φ ⟨I, h⟩ else 1
            cls_mul := ?_, cls_surj := ?_, cls_eq := ?_ }⟩
  · intro I J hI hJ _ _
    rw [dif_pos hI, dif_pos hJ, dif_pos (hI.mul_left hJ)]
    exact map_mul_mk φ hI hJ
  · intro c
    obtain ⟨⟨I, hI⟩, rfl⟩ := hs c
    exact ⟨I, hI, ne_bot_of_isCoprime hm hI, dif_pos hI⟩
  · intro I J hI hJ _ _
    rw [dif_pos hI, dif_pos hJ, he]
    constructor
    · rintro ⟨a, b, ha, hb, h⟩
      exact ⟨a, b, ne_zero_of_sub_one_mem hm ha, ne_zero_of_sub_one_mem hm hb, ha, hb, h⟩
    · rintro ⟨a, b, -, -, ha, hb, h⟩
      exact ⟨a, b, ha, hb, h⟩
end GlobalTheory.Mem.RayEx
