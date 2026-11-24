-- Prove2me | solution 1 for GlobalTheory.TransDecay.seminorm_mul_shift_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:38:59.937659+00:00
-- url     : https://prove2.me/submissions/13eb6dad-6114-47db-a322-0dbccf80f8ba

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TranslationIsometrySchwartzOperator

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped SchwartzMap
open GlobalTheory GlobalTheory.TransDecay
namespace GlobalTheory.TransDecay
theorem _root_.solution {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (χ h : 𝓢(V, ℂ)) (hχ : HasCompactSupport (χ : V → ℂ)) (l m M : ℕ) :
    ∃ C : ℝ, ∀ (v : V) (k' : 𝓢(V, ℂ)), (∀ x, k' x = χ x * h (x + v)) →
      SchwartzMap.seminorm ℂ l m k' ≤ C * ((1 + ‖v‖) ^ M)⁻¹ := by
  obtain ⟨r, hr⟩ := hχ.isCompact.isBounded.subset_closedBall (0 : V)
  set R := max r 0
  have hR0 : 0 ≤ R := le_max_right _ _
  have hxR : ∀ x ∈ tsupport (χ : V → ℂ), ‖x‖ ≤ R := fun x hx => by
    have := hr hx
    rw [Metric.mem_closedBall, dist_zero_right] at this
    exact this.trans (le_max_left _ _)
  set S := ((Finset.Iic (M, m)).sup fun p : ℕ × ℕ => SchwartzMap.seminorm ℂ p.1 p.2) h
  have hS0 : 0 ≤ S := apply_nonneg _ _
  set A := ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * SchwartzMap.seminorm ℂ 0 i χ
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun i _ => by positivity
  refine ⟨R ^ l * A * ((1 + R) ^ M * (2 ^ M * S)), fun v k' hk' => ?_⟩
  have hvpos : 0 < (1 + ‖v‖) ^ M := by positivity
  refine SchwartzMap.seminorm_le_bound ℂ l m k' (by positivity) fun x => ?_
  have hfun : (k' : V → ℂ) = fun y => χ y * h (y + v) := funext hk'
  rw [hfun]
  have hsh : ContDiff ℝ (⊤ : ℕ∞) (fun y => h (y + v)) :=
    (h.smooth ⊤).comp (contDiff_id.add contDiff_const)
  have hL := norm_iteratedFDeriv_mul_le (χ.smooth ⊤) hsh x (n := m) (by exact_mod_cast le_top)
  have hterm : ∀ i ∈ Finset.range (m + 1), ‖x‖ ^ l * ((m.choose i : ℝ) * ‖iteratedFDeriv ℝ i χ x‖ *
      ‖iteratedFDeriv ℝ (m - i) (fun y => h (y + v)) x‖) ≤
      R ^ l * ((m.choose i : ℝ) * SchwartzMap.seminorm ℂ 0 i χ) * ((1 + R) ^ M * (2 ^ M * S)) *
        ((1 + ‖v‖) ^ M)⁻¹ := by
    intro i _
    by_cases hx : x ∈ tsupport (χ : V → ℂ)
    · have hx1 := hxR x hx
      rw [iteratedFDeriv_comp_add_right]
      have hj : (1 + ‖x + v‖) ^ M * ‖iteratedFDeriv ℝ (m - i) h (x + v)‖ ≤ 2 ^ M * S :=
        SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (M, m)) le_rfl (Nat.sub_le _ _) h (x + v)
      have hv : 1 + ‖v‖ ≤ (1 + R) * (1 + ‖x + v‖) := by
        have : ‖v‖ ≤ ‖x + v‖ + ‖x‖ := by
          calc ‖v‖ = ‖(x + v) - x‖ := by simp
            _ ≤ _ := norm_sub_le _ _
        nlinarith [norm_nonneg (x + v)]
      have hD : ‖iteratedFDeriv ℝ (m - i) h (x + v)‖ ≤
          (1 + R) ^ M * (2 ^ M * S) * ((1 + ‖v‖) ^ M)⁻¹ := by
        rw [← div_eq_mul_inv, le_div_iff₀ hvpos]
        calc ‖iteratedFDeriv ℝ (m - i) h (x + v)‖ * (1 + ‖v‖) ^ M
            ≤ ‖iteratedFDeriv ℝ (m - i) h (x + v)‖ * ((1 + R) * (1 + ‖x + v‖)) ^ M := by gcongr
          _ = (1 + R) ^ M * ((1 + ‖x + v‖) ^ M * ‖iteratedFDeriv ℝ (m - i) h (x + v)‖) := by
            rw [mul_pow]; ring
          _ ≤ (1 + R) ^ M * (2 ^ M * S) := by gcongr
      have hχi : ‖iteratedFDeriv ℝ i χ x‖ ≤ SchwartzMap.seminorm ℂ 0 i χ :=
        SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ χ i x
      calc ‖x‖ ^ l * ((m.choose i : ℝ) * ‖iteratedFDeriv ℝ i χ x‖ *
            ‖iteratedFDeriv ℝ (m - i) h (x + v)‖)
          ≤ R ^ l * ((m.choose i : ℝ) * SchwartzMap.seminorm ℂ 0 i χ *
            ((1 + R) ^ M * (2 ^ M * S) * ((1 + ‖v‖) ^ M)⁻¹)) := by gcongr
        _ = _ := by ring
    · have h0 : iteratedFDeriv ℝ i χ x = 0 := by
        by_contra hne
        exact hx (support_iteratedFDeriv_subset i (Function.mem_support.2 hne))
      rw [h0, norm_zero, mul_zero, zero_mul, mul_zero]
      positivity
  calc ‖x‖ ^ l * ‖iteratedFDeriv ℝ m (fun y => χ y * h (y + v)) x‖
      ≤ ‖x‖ ^ l * ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i χ x‖ *
          ‖iteratedFDeriv ℝ (m - i) (fun y => h (y + v)) x‖ := by gcongr
    _ = ∑ i ∈ Finset.range (m + 1), ‖x‖ ^ l * ((m.choose i : ℝ) * ‖iteratedFDeriv ℝ i χ x‖ *
          ‖iteratedFDeriv ℝ (m - i) (fun y => h (y + v)) x‖) := Finset.mul_sum _ _ _
    _ ≤ ∑ i ∈ Finset.range (m + 1), R ^ l * ((m.choose i : ℝ) * SchwartzMap.seminorm ℂ 0 i χ) *
          ((1 + R) ^ M * (2 ^ M * S)) * ((1 + ‖v‖) ^ M)⁻¹ := Finset.sum_le_sum hterm
    _ = R ^ l * A * ((1 + R) ^ M * (2 ^ M * S)) * ((1 + ‖v‖) ^ M)⁻¹ := by
        rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.mul_sum]
end GlobalTheory.TransDecay
