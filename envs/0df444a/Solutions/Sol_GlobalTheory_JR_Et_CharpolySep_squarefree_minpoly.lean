-- Prove2me | solution 1 for GlobalTheory.JR.Et.CharpolySep.squarefree_minpoly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:57:26.905584+00:00
-- url     : https://prove2.me/submissions/1f4585cf-4784-4c15-9bb1-1b039593b642

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MulMatMemUnitaryGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyEtaleGeneratorMulMatrixSeparable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.Et GlobalTheory.JR.Et.CharpolySep
namespace GlobalTheory.JR.Et.CharpolySep
theorem _root_.solution {F K : Type} [Field F] [CommRing K] [Algebra F K] [IsReduced K] [Module.Finite F K]
    (τ : K) : Squarefree (minpoly F τ) := by
  intro x hx
  obtain ⟨h, hh⟩ := hx
  have hint : IsIntegral F τ := Algebra.IsIntegral.isIntegral τ
  have hm0 : minpoly F τ ≠ 0 := minpoly.ne_zero hint
  have hs : Polynomial.aeval τ (x * h) = 0 := by
    apply IsReduced.eq_zero
    refine ⟨2, ?_⟩
    have : (x * h) ^ 2 = minpoly F τ * h := by rw [hh]; ring
    rw [← map_pow, this, map_mul, minpoly.aeval, zero_mul]
  have hd : minpoly F τ ∣ x * h := minpoly.dvd F τ hs
  rw [hh] at hd
  have hxh : x * h ≠ 0 := by
    intro h0; apply hm0; rw [hh, mul_assoc, h0, mul_zero]
  have h2 : x * (x * h) ∣ 1 * (x * h) := by rw [one_mul, ← mul_assoc]; exact hd
  exact isUnit_of_dvd_one ((mul_dvd_mul_iff_right hxh).1 h2)
end GlobalTheory.JR.Et.CharpolySep
