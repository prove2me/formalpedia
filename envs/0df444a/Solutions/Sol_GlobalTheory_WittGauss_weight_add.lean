-- Prove2me | solution 1 for GlobalTheory.WittGauss.weight_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:55:24.915196+00:00
-- url     : https://prove2.me/submissions/3f7a14b4-5b63-439b-86df-c25f157d2239

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UltraSumLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WittVectorGaussNormUltrametric
import Theorems.Thm_GlobalTheory_WittGauss_teichmuller_mul_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.WittGauss
open WittVector
variable {R : Type} [CommRing R] (a : R → ℝ) (hb : ∀ x, 0 ≤ a x ∧ a x ≤ 1) (h0 : a 0 = 0)
  (h1 : a 1 = 1) (hm : ∀ x y, a (x * y) = a x * a y) (ha : ∀ x y, a (x + y) ≤ max (a x) (a y))
include hb h0 h1 hm ha
namespace GlobalTheory.WittGauss
theorem _root_.solution (p : ℕ) [Fact p.Prime] (c : ℝ) (hc : 0 ≤ c) (x y : WittVector p R)
    (hx : ∀ i, a (x.coeff i) ≤ c ^ p ^ i) (hy : ∀ i, a (y.coeff i) ≤ c ^ p ^ i) (n : ℕ) :
    a ((x + y).coeff n) ≤ c ^ p ^ n := by
  have key : ∀ z : WittVector p R, (∀ i, a (z.coeff i) ≤ c ^ p ^ i) →
      ∃ Z : WittVector p (weightRing a hb h0 h1 hm ha c hc),
        WittVector.map (weightRing a hb h0 h1 hm ha c hc).subtype Z =
          teichmuller p Polynomial.X * WittVector.map Polynomial.C z := by
    intro z hz
    refine ⟨WittVector.mk p fun i => ⟨Polynomial.X ^ p ^ i * Polynomial.C (z.coeff i), ?_⟩, ?_⟩
    · intro k
      rw [mul_comm, Polynomial.coeff_C_mul_X_pow]
      split_ifs with h
      · rw [h]; exact hz i
      · simpa [h0] using pow_nonneg hc k
    · rw [teichmuller_mul_eq]
      ext1 i
      simp [scaleCoeff, WittVector.map_coeff]
  obtain ⟨X, hX⟩ := key x hx
  obtain ⟨Y, hY⟩ := key y hy
  have h : WittVector.map (weightRing a hb h0 h1 hm ha c hc).subtype (X + Y) =
      scaleCoeff p Polynomial.X (WittVector.map Polynomial.C (x + y)) := by
    rw [← teichmuller_mul_eq, map_add, map_add, mul_add, hX, hY]
  have h2 := congrArg (fun z => WittVector.coeff z n) h
  simp only [WittVector.map_coeff, scaleCoeff, WittVector.coeff_mk] at h2
  have h3 := ((X + Y).coeff n).2 (p ^ n)
  change a (((weightRing a hb h0 h1 hm ha c hc).subtype ((X + Y).coeff n)).coeff _) ≤ _ at h3
  rwa [h2, mul_comm, Polynomial.coeff_C_mul_X_pow, if_pos rfl] at h3
end GlobalTheory.WittGauss
