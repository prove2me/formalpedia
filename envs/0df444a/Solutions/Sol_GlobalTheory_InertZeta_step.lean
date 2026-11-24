-- Prove2me | solution 1 for GlobalTheory.InertZeta.step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:45:05.314872+00:00
-- url     : https://prove2.me/submissions/8c3f0d19-1047-4cfb-a063-e68feadaaa44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnitaryLeviSummationGeometricSeries
import Theorems.Thm_GlobalTheory_InertZeta_LeviSum_core
import Theorems.Thm_GlobalTheory_InertZeta_HasLen_unique


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.InertZeta
open GlobalTheory GlobalTheory.InertZeta
open LeviSum
namespace GlobalTheory.InertZeta
theorem _root_.solution : Step := by
  intro Y C q N ℓ l φ₀ α X y Z hq hα hy hy1 hyα hyα' H hZ
  subst hy
  have hg := core Y q N l φ₀ α X Z hq hα hy1 hyα hyα' hZ
  have hfib : ∀ ab : ℤ × Y, HasSum (fun c => X ^ ℓ ab.1 ab.2 c *
      (α ^ ab.1 * (q : ℂ) ^ (-ab.1 * ((N : ℤ) + 1)) * φ₀ ab.2))
      (((q : ℂ) ^ (2 * l ab.2 + (2 * N + 2) * ab.1.toNat) * X ^ (ab.1.natAbs + l ab.2) * jFac q N X) *
        (α ^ ab.1 * (q : ℂ) ^ (-ab.1 * ((N : ℤ) + 1)) * φ₀ ab.2)) :=
    fun ab => (H X hy1 ab.1 ab.2).mul_right _

  have hXn : ‖(q : ℂ) ^ (N + 1) * ((‖X‖ : ℝ) : ℂ)‖ = ‖(q : ℂ) ^ (N + 1) * X‖ := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_norm]
  have hαn : ‖((‖α‖ : ℝ) : ℂ)‖ = ‖α‖ := by rw [Complex.norm_real, Real.norm_eq_abs, abs_norm]
  have hZn : Summable (fun b => ((q : ℂ) ^ 2 * ((‖X‖ : ℝ) : ℂ)) ^ l b * ((‖φ₀ b‖ : ℝ) : ℂ)) := by
    have := Complex.summable_ofReal.mpr (summable_norm_iff.mpr hZ.summable)
    convert this using 2 with b
    push_cast [norm_mul, norm_pow, Complex.norm_natCast]
    ring
  have hgn := core Y q N l (fun b => ((‖φ₀ b‖ : ℝ) : ℂ)) ((‖α‖ : ℝ) : ℂ) ((‖X‖ : ℝ) : ℂ) _ hq
    (by exact_mod_cast norm_ne_zero_iff.mpr hα) (hXn ▸ hy1) (by rw [hXn, hαn]; exact hyα)
    (by rw [hXn, hαn]; exact hyα') hZn.hasSum
  have hfibn : ∀ ab : ℤ × Y, HasSum (fun c => ((‖X‖ : ℝ) : ℂ) ^ ℓ ab.1 ab.2 c *
      (((‖α‖ : ℝ) : ℂ) ^ ab.1 * (q : ℂ) ^ (-ab.1 * ((N : ℤ) + 1)) * ((‖φ₀ ab.2‖ : ℝ) : ℂ)))
      (((q : ℂ) ^ (2 * l ab.2 + (2 * N + 2) * ab.1.toNat) * ((‖X‖ : ℝ) : ℂ) ^ (ab.1.natAbs + l ab.2) *
        jFac q N ((‖X‖ : ℝ) : ℂ)) *
        (((‖α‖ : ℝ) : ℂ) ^ ab.1 * (q : ℂ) ^ (-ab.1 * ((N : ℤ) + 1)) * ((‖φ₀ ab.2‖ : ℝ) : ℂ))) :=
    fun ab => (H _ (hXn ▸ hy1) ab.1 ab.2).mul_right _
  have hnorm : ∀ p : (ℤ × Y) × C,
      ((‖X ^ ℓ p.1.1 p.1.2 p.2 * (α ^ p.1.1 * (q : ℂ) ^ (-p.1.1 * ((N : ℤ) + 1)) * φ₀ p.1.2)‖ : ℝ) : ℂ) =
      ((‖X‖ : ℝ) : ℂ) ^ ℓ p.1.1 p.1.2 p.2 *
        (((‖α‖ : ℝ) : ℂ) ^ p.1.1 * (q : ℂ) ^ (-p.1.1 * ((N : ℤ) + 1)) * ((‖φ₀ p.1.2‖ : ℝ) : ℂ)) := by
    intro p
    rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_zpow, norm_zpow, Complex.norm_natCast]
    push_cast
    rfl
  have hsum : Summable (fun p : (ℤ × Y) × C =>
      X ^ ℓ p.1.1 p.1.2 p.2 * (α ^ p.1.1 * (q : ℂ) ^ (-p.1.1 * ((N : ℤ) + 1)) * φ₀ p.1.2)) := by
    rw [← summable_norm_iff, summable_prod_of_nonneg (fun _ => norm_nonneg _)]
    refine ⟨fun ab => ?_, ?_⟩
    · rw [← Complex.summable_ofReal]
      exact (funext fun c => (hnorm (ab, c)).symm) ▸ (hfibn ab).summable
    · rw [← Complex.summable_ofReal]
      refine hgn.summable.congr fun ab => ?_
      rw [Complex.ofReal_tsum]
      exact ((funext fun c => (hnorm (ab, c)).symm) ▸ (hfibn ab)).tsum_eq.symm
  rw [hg.unique (hsum.hasSum.prod_fiberwise hfib)]
  exact hsum.hasSum
end GlobalTheory.InertZeta
