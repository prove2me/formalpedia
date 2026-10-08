-- Prove2me | solution 1 for Helfgott.circle_arc_integral_scaled
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-05T04:49:33.592076+00:00
-- url     : https://prove2.me/submissions/97cae9a7-a642-4761-a761-323d327a5e73

import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Tactic

section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency true
open MeasureTheory Set Metric

namespace Helfgott

theorem circle_arc_integral (f : AddCircle (1:ℝ) → ℂ) (c ε : ℝ)
    (hε : ε ≤ (1/2:ℝ)) :
    (∫ α in ball (c : AddCircle (1:ℝ)) ε,f α ∂AddCircle.haarAddCircle) =
      ∫ t in Ioo (c-ε) (c+ε),f (t : AddCircle (1:ℝ)) := by
  have hv : (volume : Measure (AddCircle (1:ℝ))) = AddCircle.haarAddCircle := by
    simpa only [ENNReal.ofReal_one,one_smul] using AddCircle.volume_eq_smul_haarAddCircle (T:=1)
  rw [← hv,← integral_indicator measurableSet_ball]
  rw [← AddCircle.integral_preimage (1:ℝ) (c-1/2)]
  have hcoe (t : ℝ) (ht : t ∈ Ioc (c-1/2) (c-1/2+1)) :
      ((t : AddCircle (1:ℝ)) ∈ ball (c : AddCircle (1:ℝ)) ε) ↔
        t ∈ Ioo (c-ε) (c+ε) := by
    have htlo := (mem_Ioc.mp ht).1
    have hthi := (mem_Ioc.mp ht).2
    have habs : |t-c| ≤ (1:ℝ)/2 := by apply abs_le.mpr;constructor <;>linarith
    have hn : ‖((t-c:ℝ) : AddCircle (1:ℝ))‖ = |t-c| :=
      (AddCircle.norm_coe_eq_abs_iff (1:ℝ) (by norm_num)).mpr (by simpa using habs)
    simp only [mem_ball,dist_eq_norm,← AddCircle.coe_sub,hn,mem_Ioo]
    rw [abs_lt]
    constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]
  have he : (∫ t in Ioc (c-1/2) (c-1/2+1),
      (ball (c : AddCircle (1:ℝ)) ε).indicator f (t : AddCircle (1:ℝ))) =
      ∫ t in Ioc (c-1/2) (c-1/2+1),
        (Ioo (c-ε) (c+ε)).indicator (fun t : ℝ => f (t : AddCircle (1:ℝ))) t := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    dsimp only
    by_cases hm : t ∈ Ioo (c-ε) (c+ε)
    · rw [Set.indicator_of_mem ((hcoe t ht).mpr hm),Set.indicator_of_mem hm]
    · rw [Set.indicator_of_notMem (fun hc => hm ((hcoe t ht).mp hc)),Set.indicator_of_notMem hm]
  rw [he,setIntegral_indicator measurableSet_Ioo]
  have hs : Ioo (c-ε) (c+ε) ⊆ Ioc (c-1/2) (c-1/2+1) := by
    intro t ht
    rcases mem_Ioo.mp ht with ⟨hl,hr⟩
    exact mem_Ioc.mpr ⟨by linarith,by linarith⟩
  rw [inter_eq_right.mpr hs]

theorem circle_arc_integral_scaled (f : AddCircle (1:ℝ) → ℂ) (c ε x : ℝ)
    (hε0 : 0 ≤ ε) (hε : ε ≤ (1/2:ℝ)) (hx : 0 < x) :
    (∫ α in ball (c : AddCircle (1:ℝ)) ε,f α ∂AddCircle.haarAddCircle) =
      x⁻¹ • (∫ β in Icc (-(x*ε)) (x*ε),f ((c+β/x : ℝ) : AddCircle (1:ℝ))) := by
  calc
    _ = ∫ t in Ioo (c-ε) (c+ε),f (t : AddCircle (1:ℝ)) := circle_arc_integral f c ε hε
    _ = ∫ u in (-ε)..ε,f ((c+u : ℝ) : AddCircle (1:ℝ)) := by
      rw [← integral_Ioc_eq_integral_Ioo,← intervalIntegral.integral_of_le (by linarith : c-ε ≤ c+ε)]
      simpa only [sub_eq_add_neg] using
        (intervalIntegral.integral_comp_add_left (f:=fun t : ℝ => f (t : AddCircle (1:ℝ)))
          (a:= -ε) (b:=ε) c).symm
    _ = _ := by
      rw [integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (by nlinarith : -(x*ε) ≤ x*ε)]
      have hs := intervalIntegral.integral_comp_div
        (f:=fun u : ℝ => f ((c+u : ℝ) : AddCircle (1:ℝ)))
        (a:= -(x*ε)) (b:=x*ε) hx.ne'
      simp only [neg_div,mul_div_cancel_left₀ ε hx.ne'] at hs
      rw [hs,smul_smul,inv_mul_cancel₀ hx.ne',one_smul]

end Helfgott
end

open MeasureTheory Set Metric Helfgott

theorem solution (f : AddCircle (1:ℝ) → ℂ) (c ε x : ℝ)
    (hε0 : 0 ≤ ε) (hε : ε ≤ (1/2:ℝ)) (hx : 0 < x) :
    (∫ α in ball (c : AddCircle (1:ℝ)) ε,f α ∂AddCircle.haarAddCircle) =
      x⁻¹ • (∫ β in Icc (-(x*ε)) (x*ε),f ((c+β/x : ℝ) : AddCircle (1:ℝ))) := Helfgott.circle_arc_integral_scaled f c ε x hε0 hε hx

#print axioms solution
