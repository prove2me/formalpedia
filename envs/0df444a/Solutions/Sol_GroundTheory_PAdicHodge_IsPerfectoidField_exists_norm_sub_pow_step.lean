-- Prove2me | solution 1 for GroundTheory.PAdicHodge.IsPerfectoidField.exists_norm_sub_pow_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:15:34.923857+00:00
-- url     : https://prove2.me/submissions/44fefe4d-535c-4c67-a253-32e08a4612fa

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidField
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidCriterion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.PAdicHodge
namespace IsPerfectoidField
section Norm
variable {F : Type*} [NormedField F] [IsUltrametricDist F] (p : ℕ)
end Norm
section Perfectoid
private theorem norm_sub_le_max_of_ultrametric_field {E : Type*} [SeminormedAddCommGroup E] [IsUltrametricDist E]
    (a b : E) : ‖a - b‖ ≤ max ‖a‖ ‖b‖ := by
  simpa [sub_eq_add_neg] using IsUltrametricDist.norm_add_le_max a (-b)
variable {F : Type*} [NontriviallyNormedField F] [IsUltrametricDist F] (p : ℕ) [Fact p.Prime]
end Perfectoid
end IsPerfectoidField
end GroundTheory.PAdicHodge
end
end

set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open GroundTheory.PAdicHodge.IsPerfectoidField
variable {F : Type*} [NontriviallyNormedField F] [IsUltrametricDist F] (p : ℕ) [Fact p.Prime]
namespace GroundTheory.PAdicHodge.IsPerfectoidField
theorem _root_.solution {π : F} (hπ : ‖π‖ ≤ 1)
    (h : ∀ x : F, ‖x‖ ≤ 1 → ∃ y : F, ‖y‖ ≤ 1 ∧ ‖x - y ^ p‖ ≤ ‖π‖ ^ p)
    {x z : F} (hz : ‖z‖ ≤ 1) {k : ℕ} (hxz : ‖x - z ^ p‖ ≤ ‖π‖ ^ (p * k)) :
    ∃ z' : F, ‖z'‖ ≤ 1 ∧ ‖z' - z‖ ≤ ‖π‖ ^ k ∧
      ‖x - z' ^ p‖ ≤ max (‖π‖ ^ (p * (k + 1))) (‖(p : F)‖ * ‖π‖ ^ k) := by
  have hp : p.Prime := Fact.out
  by_cases h0 : π ^ (p * k) = 0
  · refine ⟨z, hz, by simp [pow_nonneg (norm_nonneg π)], ?_⟩
    have : ‖x - z ^ p‖ ≤ 0 := by rwa [← norm_pow, h0, norm_zero] at hxz
    exact this.trans (le_max_of_le_left (pow_nonneg (norm_nonneg _) _))
  set w := (x - z ^ p) / π ^ (p * k) with hw
  have hw1 : ‖w‖ ≤ 1 := by
    rw [hw, norm_div, norm_pow]
    exact div_le_one_of_le₀ hxz (pow_nonneg (norm_nonneg _) _)
  obtain ⟨u, hu1, hu⟩ := h w hw1
  have hπk : ‖π ^ k‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hπ
  have hb1 : ‖π ^ k * u‖ ≤ 1 := by
    rw [norm_mul]; exact mul_le_one₀ hπk (norm_nonneg _) hu1
  refine ⟨z + π ^ k * u, ?_, ?_, ?_⟩
  · exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hz hb1)
  · rw [add_sub_cancel_left, norm_mul, norm_pow]
    exact mul_le_of_le_one_right (pow_nonneg (norm_nonneg _) _) hu1
  · obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp (⟨z, mem_normInteger.2 hz⟩ : normInteger F)
      ⟨π ^ k * u, mem_normInteger.2 hb1⟩
    have hr' := congrArg (fun t : normInteger F => (t : F)) hr
    simp only [Subring.coe_add, SubmonoidClass.coe_pow, Subring.coe_mul,
      SubringClass.coe_natCast] at hr'
    have hr1 : ‖(r : F)‖ ≤ 1 := mem_normInteger.1 r.2
    have hxw : x - z ^ p = π ^ (p * k) * w := by
      rw [hw, mul_div_cancel₀ _ h0]
    have key : x - (z + π ^ k * u) ^ p =
        π ^ (p * k) * (w - u ^ p) - (p : F) * z * (π ^ k * u) * r := by
      rw [hr']
      have : (π ^ k * u) ^ p = π ^ (p * k) * u ^ p := by
        rw [mul_pow, ← pow_mul, mul_comm k p]
      rw [this]
      linear_combination hxw
    rw [key]
    refine (norm_sub_le_max_of_ultrametric_field _ _).trans (max_le_max ?_ ?_)
    · rw [norm_mul, norm_pow, mul_add, mul_one, pow_add]
      exact mul_le_mul_of_nonneg_left hu (pow_nonneg (norm_nonneg _) _)
    · rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_pow]
      have h1 : ‖z‖ * (‖π‖ ^ k * ‖u‖) * ‖(r : F)‖ ≤ ‖π‖ ^ k := by
        calc ‖z‖ * (‖π‖ ^ k * ‖u‖) * ‖(r : F)‖ ≤ 1 * (‖π‖ ^ k * 1) * 1 := by
              gcongr
          _ = ‖π‖ ^ k := by ring
      calc ‖(p : F)‖ * ‖z‖ * (‖π‖ ^ k * ‖u‖) * ‖(r : F)‖
          = ‖(p : F)‖ * (‖z‖ * (‖π‖ ^ k * ‖u‖) * ‖(r : F)‖) := by ring
        _ ≤ ‖(p : F)‖ * ‖π‖ ^ k := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
end GroundTheory.PAdicHodge.IsPerfectoidField
