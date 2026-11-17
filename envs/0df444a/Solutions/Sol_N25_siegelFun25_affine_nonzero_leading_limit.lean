-- Prove2me | solution 1 for N25.siegelFun25_affine_nonzero_leading_limit
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:47:50.01855+00:00
-- url     : https://prove2.me/submissions/8e98c9a3-94b9-487b-8646-a455906038e3

import Mathlib
import Definitions.Def_ModularCurve_SiegelFunction
import Theorems.Thm_N25_siegelFun25_nonzero_leading_limit

set_option autoImplicit false

open Filter Topology

namespace N25

theorem _root_.solution (r s : ℤ)
    (hs : (25 : ℤ) ∣ r → ¬(25 : ℤ) ∣ s)
    (φ : UpperHalfPlane → UpperHalfPlane) (a b : ℝ) (ha : 0 < a)
    (hφ : ∀ τ : UpperHalfPlane, (φ τ : ℂ) = (a : ℂ) * (τ : ℂ) + (b : ℂ)) :
    ∃ c : ℂ, c ≠ 0 ∧ Tendsto
      (fun τ : UpperHalfPlane => ModularCurve.siegelFun 25 r s (φ τ : ℂ) /
        Complex.exp (Real.pi * Complex.I *
          ((((r % 25 : ℤ) : ℂ) / 25) ^ 2 - ((r % 25 : ℤ) : ℂ) / 25 + 1 / 6) *
            (a : ℂ) * (τ : ℂ)))
      UpperHalfPlane.atImInfty (nhds c) := by
  have him (τ : UpperHalfPlane) : (φ τ).im = a * τ.im := by
    change (φ τ : ℂ).im = a * (τ : ℂ).im
    rw [hφ]
    simp
  have ht : Tendsto φ UpperHalfPlane.atImInfty UpperHalfPlane.atImInfty := by
    rw [UpperHalfPlane.atImInfty, tendsto_comap_iff]
    apply tendsto_atTop.mpr
    intro t
    have hv : ∀ᶠ τ : UpperHalfPlane in UpperHalfPlane.atImInfty, t / a ≤ τ.im :=
      preimage_mem_comap (eventually_ge_atTop (t / a))
    filter_upwards [hv] with τ hτ
    change t ≤ (φ τ).im
    rw [him]
    nlinarith [(div_le_iff₀ ha).mp hτ]
  obtain ⟨c, hc, hl⟩ := siegelFun25_nonzero_leading_limit r s hs
  let B : ℂ := (((r % 25 : ℤ) : ℂ) / 25) ^ 2 - ((r % 25 : ℤ) : ℂ) / 25 + 1 / 6
  let w : ℂ := Complex.exp (Real.pi * Complex.I * B * (b : ℂ))
  have hw : w ≠ 0 := Complex.exp_ne_zero _
  refine ⟨w * c, mul_ne_zero hw hc, ?_⟩
  have hm := (hl.comp ht).const_mul w
  apply hm.congr'
  filter_upwards [] with τ
  have he : Complex.exp (Real.pi * Complex.I * B * (φ τ : ℂ)) =
      w * Complex.exp (Real.pi * Complex.I * B * (a : ℂ) * (τ : ℂ)) := by
    rw [hφ]
    dsimp [w]
    rw [← Complex.exp_add]
    congr 1
    ring
  change w * (ModularCurve.siegelFun 25 r s (φ τ : ℂ) /
      Complex.exp (Real.pi * Complex.I * B * (φ τ : ℂ))) =
    ModularCurve.siegelFun 25 r s (φ τ : ℂ) /
      Complex.exp (Real.pi * Complex.I * B * (a : ℂ) * (τ : ℂ))
  rw [he]
  field_simp

end N25
