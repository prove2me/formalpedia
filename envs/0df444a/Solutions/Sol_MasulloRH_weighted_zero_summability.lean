-- Prove2me | solution 1 for MasulloRH.weighted_zero_summability
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-20T22:11:16.027239+00:00
-- url     : https://prove2.me/submissions/34a29772-39c9-4d9f-bd57-e95736b8ade4

import Definitions.Def_MasulloRH_RegularizedTrace
import Theorems.Thm_ConnesRZ_actual_zero_reciprocal_square_summable

set_option autoImplicit false
open MasulloRH

theorem solution (α : ℝ) (_hα : 0 < α) : Summable (zeroDecayWeight α) := by
  let incl (ρ : ZetaZerosInTraceStrip α) : {z : ℂ // ConnesRZ.IsCriticalZero z} :=
    ⟨ρ.val, ρ.prop.1, ρ.prop.2.1, ρ.prop.2.2.1⟩
  have hi : Function.Injective incl := fun a b h => Subtype.ext (congrArg (fun r : {z : ℂ // ConnesRZ.IsCriticalZero z} => r.val) h)
  have h := (ConnesRZ.actual_zero_reciprocal_square_summable.comp_injective hi).mul_left 2
  apply h.of_nonneg_of_le
  · intro ρ
    dsimp [zeroDecayWeight]
    positivity
  · intro ρ
    let z := ρ.val
    have h0 : 0 ≤ z.re := ρ.prop.2.1.le
    have h1 : z.re ≤ 1 := ρ.prop.2.2.1.le
    have hn : Complex.normSq ((z - 1 / 2) / Complex.I) =
        (z.re - 1/2)^2 + z.im^2 := by
      rw [Complex.normSq_div, Complex.normSq_I, div_one, Complex.normSq_apply]
      simp [pow_two]
    change (analyticOrderNatAt riemannZeta z : ℝ) / (1 + z.im^2) ≤
      2 * ((analyticOrderNatAt riemannZeta z : ℝ) / (1 + Complex.normSq ((z - 1/2) / Complex.I)))
    rw [hn, ← mul_div_assoc]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    rw [mul_assoc, mul_left_comm 2]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    nlinarith [mul_nonneg h0 (sub_nonneg.mpr h1), sq_nonneg z.im]
