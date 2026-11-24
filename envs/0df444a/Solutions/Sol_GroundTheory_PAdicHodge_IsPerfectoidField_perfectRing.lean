-- Prove2me | solution 1 for GroundTheory.PAdicHodge.IsPerfectoidField.perfectRing
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:49:20.414579+00:00
-- url     : https://prove2.me/submissions/251ef19e-5a9b-4af6-8754-20c571480e48

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open NNReal
open GroundTheory.PAdicHodge.IsPerfectoidField
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
namespace GroundTheory.PAdicHodge.IsPerfectoidField
theorem _root_.solution (p : ℕ) [Fact p.Prime] [CharP K p] [IsPerfectoidField K p] :
    PerfectRing K p := by
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero

  have h1 : ∀ x : K, ‖x‖ ≤ 1 → ∃ y : K, y ^ p = x := by
    intro x hx
    obtain ⟨z, hz⟩ := IsPerfectoidField.surjective_pow (K := K) (p := p)
      (Ideal.Quotient.mk _ ⟨x, mem_normInteger.2 hx⟩)
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
    refine ⟨y, ?_⟩
    have hz' : Ideal.Quotient.mk (Ideal.span {(p : normInteger K)}) (y ^ p) =
        Ideal.Quotient.mk _ ⟨x, mem_normInteger.2 hx⟩ := by
      rw [map_pow]; exact hz
    rw [Ideal.Quotient.eq] at hz'
    have hp : (p : normInteger K) = 0 := by
      ext; simp [CharP.cast_eq_zero]
    rw [hp, Ideal.span_singleton_eq_bot.2 rfl, Ideal.mem_bot, sub_eq_zero] at hz'
    have := congrArg Subtype.val hz'
    simpa using this
  refine PerfectRing.ofSurjective K p fun x => ?_
  rcases le_or_gt ‖x‖ 1 with hx | hx
  · exact h1 x hx
  · have hx0 : x ≠ 0 := by rintro rfl; norm_num at hx
    obtain ⟨y, hy⟩ := h1 x⁻¹ (by rw [norm_inv]; exact inv_le_one_of_one_le₀ hx.le)
    exact ⟨y⁻¹, by rw [frobenius_def, inv_pow, hy, inv_inv]⟩
end GroundTheory.PAdicHodge.IsPerfectoidField
