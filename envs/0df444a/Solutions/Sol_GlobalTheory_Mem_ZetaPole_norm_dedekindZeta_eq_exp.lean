-- Prove2me | solution 1 for GlobalTheory.Mem.ZetaPole.norm_dedekindZeta_eq_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:50:14.791345+00:00
-- url     : https://prove2.me/submissions/f591713f-46ba-4d1b-8d3b-0c6b9ffa9e0d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TsumIdealMulAbsNormCpowEqExpTsum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_NotInjectiveTwoPrimesEqualNormCofinite
import Theorems.Thm_GlobalTheory_Mem_ZetaPole_dedekindZeta_eq_tsum_ideal
import Theorems.Thm_GlobalTheory_Mem_ZetaPole_ofReal_logFactor
import Theorems.Thm_GlobalTheory_tsum_ideal_mul_absNorm_cpow_eq_exp_tsum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Filter Topology
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.ZetaPole
namespace GlobalTheory.Mem.ZetaPole
theorem _root_.solution (K : Type) [Field K] [NumberField K] {s : ℝ} (hs : 1 < s) :
    ‖dedekindZeta K s‖ =
      Real.exp (∑' v : HeightOneSpectrum (𝓞 K), logFactor (Ideal.absNorm v.asIdeal) s) := by
  classical
  have hs' : 1 < (s : ℂ).re := by simpa using hs
  have hs0 : (s : ℂ) ≠ 0 := by rintro h; rw [h] at hs'; norm_num at hs'
  have h := GlobalTheory.tsum_ideal_mul_absNorm_cpow_eq_exp_tsum K (fun I => if I = ⊥ then 0 else 1)
    (by simp) (by simp) (fun I J => by
      by_cases hI : I = ⊥ <;> by_cases hJ : J = ⊥ <;> simp [hI, hJ, Ideal.mul_eq_bot])
    (fun I => by split_ifs <;> simp) s hs'
  have e1 : ∀ I : Ideal (𝓞 K), (if I = ⊥ then (0 : ℂ) else 1) * ((Ideal.absNorm I : ℕ) : ℂ) ^ (-(s : ℂ))
      = ((Ideal.absNorm I : ℕ) : ℂ) ^ (-(s : ℂ)) := fun I => by
    by_cases hI : I = ⊥
    · simp [hI, hs0]
    · simp [hI]
  simp only [e1] at h
  simp only [← ofReal_logFactor (NumberField.HeightOneSpectrum.one_lt_absNorm _)
    (lt_trans one_pos hs)] at h
  rw [dedekindZeta_eq_tsum_ideal K hs', h, ← Complex.ofReal_tsum, Complex.norm_exp,
    Complex.ofReal_re]
end GlobalTheory.Mem.ZetaPole
