-- Prove2me | solution 1 for GlobalTheory.entire_sub_conj_bounded_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:47:44.718377+00:00
-- url     : https://prove2.me/submissions/6caf6b48-f039-411d-8f92-9583439c831f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EntireAntilinearLatticePeriodsConst
import Theorems.Thm_GlobalTheory_eq_zero_of_norm_real_mul_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix
open scoped ContDiff BigOperators Real
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {φ : ℂ → ℂ} {b : ℂ} {C : ℝ} (hφ : Differentiable ℂ φ)
    (h : ∀ s, ‖φ s - (starRingEnd ℂ) s * b‖ ≤ C) : b = 0 ∧ ∀ s, φ s = φ 0 := by

  have hshift : ∀ a s, φ (s + a) - φ s = φ a - φ 0 := by
    intro a
    have hd : Differentiable ℂ (fun s => φ (s + a) - φ s) :=
      (hφ.comp (differentiable_id.add_const a)).sub hφ
    have hbd : Bornology.IsBounded (Set.range (fun s => φ (s + a) - φ s)) := by
      rw [isBounded_iff_forall_norm_le]
      refine ⟨2 * C + ‖(starRingEnd ℂ) a * b‖, ?_⟩
      rintro _ ⟨s, rfl⟩
      show ‖φ (s + a) - φ s‖ ≤ _
      have e : φ (s + a) - φ s = ((φ (s + a) - (starRingEnd ℂ) (s + a) * b)
          - (φ s - (starRingEnd ℂ) s * b)) + (starRingEnd ℂ) a * b := by
        rw [map_add]; ring
      rw [e]
      calc _ ≤ ‖(φ (s + a) - (starRingEnd ℂ) (s + a) * b) - (φ s - (starRingEnd ℂ) s * b)‖
            + ‖(starRingEnd ℂ) a * b‖ := norm_add_le _ _
        _ ≤ (‖φ (s + a) - (starRingEnd ℂ) (s + a) * b‖ + ‖φ s - (starRingEnd ℂ) s * b‖)
            + ‖(starRingEnd ℂ) a * b‖ := by gcongr; exact norm_sub_le _ _
        _ ≤ _ := by linarith [h (s + a), h s]
    intro s
    simpa [zero_add] using hd.apply_eq_apply_of_bounded hbd s 0

  have hderiv : ∀ s, deriv φ s = deriv φ 0 := by
    intro s
    have e1 : (fun x => φ (x + s)) = fun x => φ x + (φ s - φ 0) := by
      funext x
      linear_combination hshift s x
    have e2 := congrArg (fun f => deriv f 0) e1
    simp only [deriv_comp_add_const, deriv_add_const, zero_add] at e2
    exact e2

  obtain ⟨β, hlin⟩ : ∃ β : ℂ, ∀ s, φ s = φ 0 + β * s := by
    refine ⟨deriv φ 0, fun s => ?_⟩
    have hd : Differentiable ℂ (fun s => φ s - deriv φ 0 * s) :=
      hφ.sub (differentiable_id.const_mul _)
    have hz : ∀ x, deriv (fun s => φ s - deriv φ 0 * s) x = 0 := by
      intro x
      have hx : HasDerivAt (fun s => φ s - deriv φ 0 * s) (deriv φ x - deriv φ 0 * 1) x :=
        (hφ x).hasDerivAt.sub ((hasDerivAt_id' x).const_mul _)
      rw [hx.deriv, hderiv x]
      ring
    have := is_const_of_deriv_eq_zero hd hz s 0
    linear_combination this

  have hB : ∀ s, ‖β * s - (starRingEnd ℂ) s * b‖ ≤ C + ‖φ 0‖ := by
    intro s
    have e : β * s - (starRingEnd ℂ) s * b = (φ s - (starRingEnd ℂ) s * b) - φ 0 := by
      rw [hlin s]; ring
    rw [e]
    exact (norm_sub_le _ _).trans (by linarith [h s])
  have h1 : β - b = 0 := eq_zero_of_norm_real_mul_le (C := C + ‖φ 0‖) fun r => by
    have hr := hB r
    rw [Complex.conj_ofReal] at hr
    calc ‖(r : ℂ) * (β - b)‖ = ‖β * (r : ℂ) - (r : ℂ) * b‖ := by congr 1; ring
      _ ≤ _ := hr
  have h2 : Complex.I * (β + b) = 0 := eq_zero_of_norm_real_mul_le (C := C + ‖φ 0‖) fun r => by
    have hr := hB (r * Complex.I)
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I] at hr
    calc ‖(r : ℂ) * (Complex.I * (β + b))‖
        = ‖β * ((r : ℂ) * Complex.I) - (r : ℂ) * -Complex.I * b‖ := by congr 1; ring
      _ ≤ _ := hr
  have h3 : β + b = 0 := (mul_eq_zero.mp h2).resolve_left Complex.I_ne_zero
  have hβ : β = 0 := by linear_combination (h1 + h3) / 2
  refine ⟨by linear_combination (h3 - h1) / 2, fun s => ?_⟩
  rw [hlin s, hβ, zero_mul, add_zero]
end GlobalTheory
