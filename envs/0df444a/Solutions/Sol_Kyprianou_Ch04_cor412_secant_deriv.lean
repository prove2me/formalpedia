-- Prove2me | solution 1 for Kyprianou.Ch04.cor412_secant_deriv
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:20:11.17355+00:00
-- url     : https://prove2.me/submissions/445f2391-71b1-4e3b-b3c5-7c4b7182caab

import Mathlib
open Set Filter
open scoped Topology
set_option autoImplicit false

theorem solution (f : ℝ → ℝ) (h0 : f 0 = 0)
    (hc : ConvexOn ℝ (Ici 0) f)
    (hd : 0 < derivWithin f (Ici 0) 0) :
    max 0 (sInf ((fun x : ℝ => f x / x) '' Ioi 0)) =
      derivWithin f (Ici 0) 0 := by
  let d := derivWithin f (Ici 0) 0
  have hdiff : DifferentiableWithinAt ℝ f (Ici 0) 0 :=
    by_contradiction fun h => hd.ne' (derivWithin_zero_of_not_differentiableWithinAt h)
  have hlim := hasDerivWithinAt_iff_tendsto_slope.mp hdiff.hasDerivWithinAt
  have heq : Ici (0 : ℝ) \ {0} = Ioi 0 := by ext x; simp
  rw [heq] at hlim
  have hslope : slope f 0 = (fun x : ℝ => f x / x) := by
    funext x; rw [slope_def_field, h0, sub_zero, sub_zero]
  rw [hslope] at hlim
  have hlim' : Tendsto (fun x : ℝ => f x / x) (𝓝[>] 0) (𝓝 d) := by
    exact hlim
  have hmono : MonotoneOn (fun x : ℝ => f x / x) (Ioi 0) := by
    rw [← hslope, ← heq]
    exact hc.slope_mono (by simp)
  have hlo (x : ℝ) (hx : 0 < x) : d ≤ f x / x := by
    apply le_of_tendsto hlim'
    filter_upwards [self_mem_nhdsWithin, (eventually_lt_nhds hx).filter_mono nhdsWithin_le_nhds] with y hy hyx
    exact hmono hy hx hyx.le
  let S := (fun x : ℝ => f x / x) '' Ioi 0
  have hne : S.Nonempty := ⟨f 1 / 1, 1, by norm_num, rfl⟩
  have hb : BddBelow S := ⟨d, by rintro y ⟨x, hx, rfl⟩; exact hlo x hx⟩
  have hlow : d ≤ sInf S := le_csInf hne (by rintro y ⟨x, hx, rfl⟩; exact hlo x hx)
  have hupp : sInf S ≤ d := by
    apply ge_of_tendsto hlim'
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact csInf_le hb ⟨x, hx, rfl⟩
  rw [show sInf S = d from le_antisymm hupp hlow, max_eq_right hd.le]
