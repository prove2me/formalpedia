-- Prove2me | solution 1 for LogSobolevMC.TwoPoint.eq_A_1_solution
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T22:59:12.922983+00:00
-- url     : https://prove2.me/submissions/f183e045-64c2-491d-b260-43f1e7799bfa

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_mm_lower
import Definitions.Def_LogSobolevMC_TwoPoint_Setting
open LogSobolevMC.TwoPoint
private lemma l_deriv (θ s : ℝ) (hx : 1+(1-θ)*s ≠ 0) (hy : 1-θ*s ≠ 0)
    (hz : 1+θ*(1-θ)*s^2 ≠ 0) :
    deriv (lFun θ) s =
      θ * (2*(1+(1-θ)*s)*(1-θ)) * (Real.log ((1+(1-θ)*s)^2)+1) +
      (1-θ) * (2*(1-θ*s)*(-θ)) * (Real.log ((1-θ*s)^2)+1) -
      (2*θ*(1-θ)*s) * (Real.log (1+θ*(1-θ)*s^2)+1) := by
  have hX : HasDerivAt (fun s : ℝ => (1+(1-θ)*s)^2) (2*(1+(1-θ)*s)*(1-θ)) s := by
    convert (((hasDerivAt_id s).const_mul (1-θ)).const_add 1).pow 2 using 1 <;>
      first | rfl | (dsimp; ring; done) | (ext x; dsimp; ring)
  have hY : HasDerivAt (fun s : ℝ => (1-θ*s)^2) (2*(1-θ*s)*(-θ)) s := by
    convert ((hasDerivAt_const s 1).sub ((hasDerivAt_id s).const_mul θ)).pow 2 using 1 <;>
      first | rfl | (dsimp; ring; done) | (ext x; dsimp; ring)
  have hZ : HasDerivAt (fun s : ℝ => 1+θ*(1-θ)*s^2) (2*θ*(1-θ)*s) s := by
    convert (((hasDerivAt_id s).pow 2).const_mul (θ*(1-θ))).const_add 1 using 1 <;>
      first | rfl | (dsimp; ring; done) | (ext x; dsimp; ring)
  have H := ((hX.mul (hX.log (pow_ne_zero 2 hx))).const_mul θ).add
    ((hY.mul (hY.log (pow_ne_zero 2 hy))).const_mul (1-θ))
  have H' := H.sub (hZ.mul (hZ.log hz))
  have hf : lFun θ =
      ((fun y => θ * ((1+(1-θ)*y)^2 * Real.log ((1+(1-θ)*y)^2))) +
      (fun y => (1-θ) * ((1-θ*y)^2 * Real.log ((1-θ*y)^2)))) -
      (fun y => (1+θ*(1-θ)*y^2)*Real.log (1+θ*(1-θ)*y^2)) := by
    ext y
    dsimp [lFun]
    ring
  have hder := H'.deriv
  simp only [Pi.mul_def, Pi.add_def, Pi.sub_def] at hder
  rw [hf]
  simp only [Pi.mul_def, Pi.add_def, Pi.sub_def]
  rw [hder]
  field_simp [hx, hy, hz]
  ring

theorem solution (θ : ℝ) (h0 : 0 < θ) (h1 : θ < 1 / 2) :
    let a := Real.log ((1 - θ) / θ) / (1 - 2 * θ)
    let s := (1 - 2 * θ) / (2 * θ * (1 - θ))
    s ≠ 0 ∧ -(1 - θ)⁻¹ ≤ s ∧ s ≤ θ⁻¹ ∧
      lFun θ s - a * eFun θ s = 0 ∧
      deriv (lFun θ) s - a * deriv (eFun θ) s = 0 := by
  dsimp
  have hq : 0 < 1-θ := by linarith
  have hd : 0 < 1-2*θ := by linarith
  let s := (1-2*θ)/(2*θ*(1-θ))
  have hs : 0 < s := div_pos hd (by positivity)
  have hX : 1+(1-θ)*s = 1/(2*θ) := by dsimp [s]; field_simp; ring
  have hY : 1-θ*s = 1/(2*(1-θ)) := by dsimp [s]; field_simp; ring
  have hZ : 1+θ*(1-θ)*s^2 = (1/(2*θ))*(1/(2*(1-θ))) := by
    dsimp [s]; field_simp; ring
  have hx : 0 < 1/(2*θ) := by positivity
  have hy : 0 < 1/(2*(1-θ)) := by positivity
  have hlog : Real.log ((1-θ)/θ) = Real.log (1/(2*θ)) - Real.log (1/(2*(1-θ))) := by
    rw [← Real.log_div hx.ne' hy.ne']
    congr 1
    field_simp
  refine ⟨hs.ne', ?_, ?_, ?_, ?_⟩
  · have hi : 0 < (1-θ)⁻¹ := inv_pos.mpr hq
    linarith
  · rw [← one_div]
    apply (le_div_iff₀ h0).mpr
    change s*θ ≤ 1
    have he : s*θ = (1-2*θ)/(2*(1-θ)) := by dsimp [s]; field_simp
    rw [he]
    apply (div_le_iff₀ (show 0 < 2*(1-θ) by positivity)).mpr
    linarith
  · change lFun θ s - Real.log ((1-θ)/θ)/(1-2*θ)*eFun θ s = 0
    unfold lFun eFun
    rw [hX,hY,hZ,Real.log_pow,Real.log_pow,Real.log_mul hx.ne' hy.ne',hlog]
    dsimp [s]
    field_simp
    ring
  · change deriv (lFun θ) s - Real.log ((1-θ)/θ)/(1-2*θ)*deriv (eFun θ) s = 0
    have he : deriv (eFun θ) s = 2*θ*(1-θ)*s := by
      have H : HasDerivAt (eFun θ) (2*θ*(1-θ)*s) s := by
        convert ((hasDerivAt_id s).pow 2).const_mul (θ*(1-θ)) using 1 <;>
          first | rfl | (dsimp [eFun]; ring; done) | (ext x; dsimp [eFun]; ring)
      exact H.deriv
    rw [l_deriv θ s (by rw [hX]; exact hx.ne') (by rw [hY]; exact hy.ne')
      (by rw [hZ]; exact (mul_pos hx hy).ne'),he]
    rw [hX,hY,hZ,Real.log_pow,Real.log_pow,Real.log_mul hx.ne' hy.ne',hlog]
    generalize Real.log (1/(2*θ)) = X
    generalize Real.log (1/(2*(1-θ))) = Y
    dsimp [s]
    field_simp [h0.ne', hq.ne', hd.ne']
    ring_nf
    field_simp [show 1-θ*2 ≠ 0 by nlinarith]
    ring
#print axioms solution
