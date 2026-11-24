-- Prove2me | solution 1 for GlobalTheory.Mem.ZetaPole.not_injective_double_primes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:08:33.669398+00:00
-- url     : https://prove2.me/submissions/61d3873e-311b-4521-8c0d-7ed01fa99828

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TsumIdealMulAbsNormCpowEqExpTsum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_NotInjectiveTwoPrimesEqualNormCofinite
import Theorems.Thm_GlobalTheory_Mem_ZetaPole_logFactor_nonneg
import Theorems.Thm_GlobalTheory_Mem_ZetaPole_logFactor_le
import Theorems.Thm_GlobalTheory_Mem_ZetaPole_summable_logFactor
import Theorems.Thm_GlobalTheory_Mem_ZetaPole_norm_dedekindZeta_eq_exp

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
theorem _root_.solution :
    ∀ (K F : Type) [Field K] [NumberField K] [Field F] [NumberField F] (S : Set (HeightOneSpectrum (𝓞 K))), S.Finite → ∀ f : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} × Bool → HeightOneSpectrum (𝓞 F), Function.Injective f → (∀ x, Ideal.absNorm (f x).asIdeal = Ideal.absNorm x.1.1.asIdeal) → False := by
  intro K F _ _ _ _ S hS f hf hN
  set c : ℝ := ∑ v ∈ hS.toFinset, logFactor (Ideal.absNorm v.asIdeal) 1 with hc
  have key : ∀ s : ℝ, 1 < s →
      Real.exp (-2 * c) * ‖dedekindZeta K s‖ ^ 2 ≤ ‖dedekindZeta F s‖ := by
    intro s hs
    rw [norm_dedekindZeta_eq_exp K hs, norm_dedekindZeta_eq_exp F hs, sq, ← Real.exp_add,
      ← Real.exp_add, Real.exp_le_exp]
    have hK := summable_logFactor K hs
    have hF := summable_logFactor F hs
    have h1 := tsum_comp_le_tsum_of_inj hF (fun v => logFactor_nonneg
      (NumberField.HeightOneSpectrum.one_lt_absNorm v) (by linarith)) hf
    have h2 := hF.comp_injective hf
    have e : ((fun v : HeightOneSpectrum (𝓞 F) => logFactor (Ideal.absNorm v.asIdeal) s) ∘ f) =
        fun x => logFactor (Ideal.absNorm x.1.1.asIdeal) s := by
      funext x
      simp only [Function.comp_apply, hN]
    rw [e] at h1 h2
    rw [h2.tsum_prod] at h1
    simp only [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_bool, nsmul_eq_mul,
      tsum_mul_left, Nat.cast_ofNat] at h1
    have h3 := hK.sum_add_tsum_compl (s := hS.toFinset)
    rw [hS.coe_toFinset] at h3
    have h4 : ∑ v ∈ hS.toFinset, logFactor (Ideal.absNorm v.asIdeal) s ≤ c :=
      Finset.sum_le_sum fun v _ =>
        logFactor_le (NumberField.HeightOneSpectrum.one_lt_absNorm v) hs.le
    have h5 : ∑' x : ↑(Sᶜ), logFactor (Ideal.absNorm x.1.asIdeal) s =
      ∑' x : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}, logFactor (Ideal.absNorm x.1.asIdeal) s := rfl
    linarith
  have tK := (tendsto_sub_one_mul_dedekindZeta_nhdsGT K).norm
  have tF := (tendsto_sub_one_mul_dedekindZeta_nhdsGT F).norm
  have t0 : Tendsto (fun s : ℝ => ‖(s : ℂ) - 1‖) (𝓝[>] 1) (𝓝 0) := by
    have : Continuous fun s : ℝ => ‖(s : ℂ) - 1‖ := by fun_prop
    simpa using (this.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 1))
  have hle := le_of_tendsto_of_tendsto ((tK.pow 2).const_mul (Real.exp (-2 * c))) (t0.mul tF) (by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have := mul_le_mul_of_nonneg_left (key s hs) (sq_nonneg ‖(s : ℂ) - 1‖)
    simp only [norm_mul]
    nlinarith)
  have hpos : 0 < ‖(dedekindZeta_residue K : ℂ)‖ :=
    norm_pos_iff.2 (by exact_mod_cast dedekindZeta_residue_ne_zero K)
  have : 0 < Real.exp (-2 * c) * ‖(dedekindZeta_residue K : ℂ)‖ ^ 2 := by positivity
  linarith
end GlobalTheory.Mem.ZetaPole
