-- Prove2me | solution 1 for GlobalTheory.PeriodChart.symm_contraction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:24:35.135308+00:00
-- url     : https://prove2.me/submissions/6bd6841e-989c-406b-a1dc-4a00ec894951

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsContraction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix Module
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PeriodChart
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace GlobalTheory.PeriodChart
theorem _root_.solution (F F₀ : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (N : V →ₗ⋆[ℂ] V)
    (hF : ∀ z w, F z w = starRingEnd ℂ (F w z))
    (hp : ∀ z, z ≠ 0 → 0 < (F z z).re) (hp₀ : ∀ z, z ≠ 0 → 0 < (F₀ z z).re)
    (h : ∀ z w, (F (z + N z) (w + N w)).im = (F₀ z w).im) :
    (∀ z w, F₀ (N z) w = F₀ (N w) z) ∧ ∀ z, z ≠ 0 → (F₀ (N z) (N z)).re < (F₀ z z).re := by

  have expand : ∀ (s t : ℂ) (z w : V), F (s • z + N (s • z)) (t • w + N (t • w)) =
      s * starRingEnd ℂ t * F z w + starRingEnd ℂ s * t * F (N z) (N w) +
      starRingEnd ℂ s * starRingEnd ℂ t * F (N z) w + s * t * F z (N w) := by
    intro s t z w
    simp only [map_add, map_smul, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      Complex.conj_conj]
    ring
  have expand₀ : ∀ (s t : ℂ) (z w : V), F₀ (s • z) (t • w) = s * starRingEnd ℂ t * F₀ z w := by
    intro s t z w
    simp only [map_smul, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul]
    ring
  have key : ∀ z w, F z (N w) = F w (N z) ∧ F₀ z w = F z w - F (N w) (N z) := by
    intro z w
    have E : ∀ s t : ℂ, (s * starRingEnd ℂ t * F z w + starRingEnd ℂ s * t * F (N z) (N w) +
        starRingEnd ℂ s * starRingEnd ℂ t * F (N z) w + s * t * F z (N w)).im =
        (s * starRingEnd ℂ t * F₀ z w).im := by
      intro s t
      rw [← expand, ← expand₀]
      exact h _ _
    have E11 := E 1 1
    have EII := E Complex.I Complex.I
    have E1I := E 1 Complex.I
    have EI1 := E Complex.I 1
    simp only [map_one, Complex.conj_I, one_mul, mul_one, Complex.add_im, Complex.mul_im, Complex.mul_re,
      Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im] at E11 EII E1I EI1
    have hre : (F z (N w)).re = (F (N z) w).re := by linarith
    have him : (F z (N w)).im = -(F (N z) w).im := by linarith
    have hc : F z (N w) = starRingEnd ℂ (F (N z) w) := Complex.ext (by simp [hre]) (by simp [him])
    refine ⟨?_, ?_⟩
    · rw [hc, hF (N z) w, Complex.conj_conj]
    · rw [hF (N w) (N z)]
      apply Complex.ext
      · simp only [Complex.sub_re, Complex.conj_re]; linarith
      · simp only [Complex.sub_im, Complex.conj_im]; linarith
  refine ⟨fun z w => ?_, fun z hz => ?_⟩
  · rw [(key (N z) w).2, (key (N w) z).2]
    have h1 : F (N z) w = F (N w) z := by
      rw [hF (N z) w, (key w z).1, ← hF (N w) z]
    rw [h1, (key (N w) (N z)).1]
  · have hA : F₀ z z = F z z - F (N z) (N z) := (key z z).2
    have hB : F₀ (N z) (N z) = F (N z) (N z) - F (N (N z)) (N (N z)) := (key (N z) (N z)).2
    have hC : F z (N (N z)) = F (N z) (N z) := (key z (N z)).1
    have hC' : F (N (N z)) z = F (N z) (N z) := by
      rw [hF (N (N z)) z, hC, ← hF (N z) (N z)]
    by_cases hz2 : z - N (N z) = 0
    · have hNN : N (N z) = z := (sub_eq_zero.mp hz2).symm
      have hneg : F₀ (N z) (N z) = -F₀ z z := by rw [hB, hA, hNN]; ring
      rw [hneg, Complex.neg_re]
      have := hp₀ z hz
      linarith
    · have hpos := hp _ hz2
      have hD : F (z - N (N z)) (z - N (N z)) = F₀ z z - F₀ (N z) (N z) := by
        rw [hA, hB]
        simp only [map_sub, LinearMap.sub_apply]
        rw [hC, hC']
        try ring
      rw [hD, Complex.sub_re] at hpos
      linarith
end GlobalTheory.PeriodChart
