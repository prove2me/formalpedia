-- Prove2me | solution 1 for GordanGenProof.minkowskiQ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:59:29.901084+00:00
-- url     : https://prove2.me/submissions/bcafe7a4-6309-4f2f-afaa-12a7f0443003

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_GordanCones
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GordanIntegerMultiple_ExistsIntMultiple
import Theorems.Thm_GordanGenProof_mem_gcone_insert
import Theorems.Thm_GordanGenProof_fm_vec
import Theorems.Thm_GordanGenProof_mem_hcone_stdIneq
import Theorems.Thm_GordanGenProof_mem_gcone_empty
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
namespace GordanGenProof
open Finset
private theorem rat_dotProduct_zero_left {n : ℕ} (x : Fin n → ℚ) : (0 : Fin n → ℚ) ⬝ᵥ x = 0 := by
  show ∑ j, (0 : Fin n → ℚ) j * x j = 0
  simp
private theorem rat_dotProduct_sub_smul_right {n : ℕ} (a x w : Fin n → ℚ) (t : ℚ) :
    a ⬝ᵥ (x - t • w) = a ⬝ᵥ x - t * (a ⬝ᵥ w) := by
  show ∑ j, a j * (x - t • w) j = ∑ j, a j * x j - t * ∑ j, a j * w j
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => by
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
end GordanGenProof
end

set_option autoImplicit false
set_option autoImplicit false
open GordanGenProof
open Finset
namespace GordanGenProof
theorem _root_.solution {n : ℕ} (T : Finset (Fin n → ℚ)) :
    ∃ A : Finset (Fin n → ℚ), gcone T id = hcone A id := by
  refine Finset.induction_on T ?_ ?_
  · exact ⟨stdIneq n, Set.ext fun x => by
      rw [mem_gcone_empty, mem_hcone_stdIneq]⟩
  · intro w T hw ih
    obtain ⟨A, hA⟩ := ih
    refine ⟨fmSet (A.image (fun a => (a, -(a ⬝ᵥ w))) ∪ {((0 : Fin n → ℚ), (1 : ℚ))}),
      Set.ext fun x => ?_⟩
    rw [← fm_vec, mem_gcone_insert hw, hA]
    refine exists_congr fun t => ?_
    constructor
    · rintro ⟨ht, h⟩ p hp
      rcases Finset.mem_union.1 hp with hp | hp
      · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hp
        have h1 : 0 ≤ a ⬝ᵥ (x - t • w) := h a ha
        rw [rat_dotProduct_sub_smul_right] at h1
        show 0 ≤ a ⬝ᵥ x + -(a ⬝ᵥ w) * t
        have e : -(a ⬝ᵥ w) * t = -(t * (a ⬝ᵥ w)) := by ring
        rw [e]
        linarith
      · rw [Finset.mem_singleton.1 hp]
        show 0 ≤ (0 : Fin n → ℚ) ⬝ᵥ x + 1 * t
        rw [rat_dotProduct_zero_left, one_mul, zero_add]
        exact ht
    · intro h
      have ht : 0 ≤ t := by
        have h0 := h ((0 : Fin n → ℚ), (1 : ℚ)) (Finset.mem_union_right _ (Finset.mem_singleton_self _))
        have h0' : 0 ≤ (0 : Fin n → ℚ) ⬝ᵥ x + 1 * t := h0
        rw [rat_dotProduct_zero_left, one_mul, zero_add] at h0'
        exact h0'
      refine ⟨ht, ?_⟩
      show ∀ a ∈ A, 0 ≤ id a ⬝ᵥ (x - t • id w)
      intro a ha
      have h2 := h (a, -(a ⬝ᵥ w)) (Finset.mem_union_left _ (Finset.mem_image_of_mem _ ha))
      have h2' : 0 ≤ a ⬝ᵥ x + -(a ⬝ᵥ w) * t := h2
      show 0 ≤ a ⬝ᵥ (x - t • w)
      rw [rat_dotProduct_sub_smul_right]
      have e : -(a ⬝ᵥ w) * t = -(t * (a ⬝ᵥ w)) := by ring
      rw [e] at h2'
      linarith
end GordanGenProof
