-- Prove2me | solution 1 for Kyprianou.Ch04.bvSubcriticalSecantSlope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:47:21.423795+00:00
-- url     : https://prove2.me/submissions/2443775e-8579-461f-b924-a62de83ccfd7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_Kyprianou_Ch04_bvSubcriticalSecantLower
import Theorems.Thm_Kyprianou_Ch04_bvSecantLowerBoundsJumpMean
import Theorems.Thm_Kyprianou_Ch04_positiveSubcriticalTrafficArithmetic
open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

/-- Under positive subcritical traffic the secant infimum equals drift less jump mean. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F) (hBV : L.BoundedVariation) (hd : 0 < L.drift) :
    let M := ∫⁻ y : ℝ, ENNReal.ofReal (-y) ∂L.ν
    let rho := M / ENNReal.ofReal L.drift
    0 < rho → rho < 1 →
    max 0 (sInf ((fun a : ℝ => L.ψ a / a) '' Ioi 0)) = L.drift - M.toReal ∧
      0 < L.drift - M.toReal := by
  intro M rho hr0 hr1
  obtain ⟨htop,hM0,hMr⟩ := Kyprianou.Ch04.positiveSubcriticalTrafficArithmetic M L.drift hd hr0 hr1
  let S := (fun a : ℝ => L.ψ a / a) '' Ioi 0
  let m := sInf S
  have hl := Kyprianou.Ch04.bvSubcriticalSecantLower P F L hBV hd htop
  have hb : BddBelow S := ⟨L.drift-M.toReal, by rintro x ⟨a,ha,rfl⟩; exact hl a ha⟩
  have hne : S.Nonempty := ⟨L.ψ 1 / 1,1,by norm_num,rfl⟩
  have hlow : L.drift-M.toReal ≤ m := le_csInf hne (by rintro x ⟨a,ha,rfl⟩; exact hl a ha)
  have hu := Kyprianou.Ch04.bvSecantLowerBoundsJumpMean P F L hBV hd m
    (fun a ha => csInf_le hb ⟨a,ha,rfl⟩)
  have hpos : 0 < L.drift-m := ENNReal.ofReal_pos.mp
    (lt_of_lt_of_le (pos_iff_ne_zero.mpr hM0) hu)
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hu
  rw [ENNReal.toReal_ofReal hpos.le] at h
  have he : m = L.drift-M.toReal := by linarith
  change max 0 m = L.drift - M.toReal ∧ _
  rw [he,max_eq_right (by linarith : 0 ≤ L.drift-M.toReal)]
  exact ⟨rfl,by linarith⟩
