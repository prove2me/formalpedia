-- Prove2me | solution 1 for GlobalTheory.dedekindZeta_eulerProduct_mul_sub_one_entire_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:12:49.202774+00:00
-- url     : https://prove2.me/submissions/6019378a-47f0-481f-a8d5-8af2155b2f52

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IdealCharacterLContinuationNeZeroOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_InfinitelyManyPrimesInRayClass
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_DedekindZetaEulerProductMulSubOneEntire
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TsumIdealMulAbsNormCpowEqExpTsum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_NotInjectiveTwoPrimesEqualNormCofinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DedekindZetaEulerProductMulSubOneEntireNeZero
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_GlobalTheory_Mem_PosDirichlet_congr
import Theorems.Thm_GlobalTheory_Mem_ZetaPole_dedekindZeta_eq_tsum_ideal
import Theorems.Thm_GlobalTheory_dedekindZeta_eulerProduct_mul_sub_one_entire
import Theorems.Thm_GlobalTheory_tsum_ideal_mul_absNorm_cpow_eq_exp_tsum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply


section
open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial
open scoped ContDiff Classical
namespace GlobalTheory
open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial in
open scoped ContDiff Classical in
private lemma dedekindZeta_eq_exp_tsum_neg_log (K : Type) [Field K] [NumberField K] (s : ℂ)
    (hs : 1 < s.re) :
    dedekindZeta K s = Complex.exp (∑' P : HeightOneSpectrum (𝓞 K),
      -Complex.log (1 - 1 * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-s))) := by
  have hs0 : -s ≠ 0 := by
    intro h
    rw [neg_eq_zero.mp h] at hs
    norm_num at hs
  have key := _root_.GlobalTheory.tsum_ideal_mul_absNorm_cpow_eq_exp_tsum K (fun I => if I = ⊥ then 0 else 1)
    (by simp) (by simp) (fun I J => by
      by_cases hI : I = ⊥ <;> by_cases hJ : J = ⊥ <;> simp [hI, hJ, Ideal.mul_eq_bot])
    (fun I => by split_ifs <;> simp) s hs
  rw [_root_.GlobalTheory.Mem.ZetaPole.dedekindZeta_eq_tsum_ideal K hs]
  convert key using 1
  · refine tsum_congr fun I => ?_
    by_cases hI : I = ⊥
    · simp [hI, Complex.zero_cpow hs0]
    · simp [hI]
  · congr 1
    refine tsum_congr fun P => ?_
    simp [P.ne_bot]
end GlobalTheory
end

set_option autoImplicit false
open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial
open scoped ContDiff Classical
open GlobalTheory
open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial
open scoped ContDiff Classical
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution :
    ∀ (K : Type) [Field K] [NumberField K], ∃ Z : ℂ → ℂ, Differentiable ℂ Z ∧ Z 1 ≠ 0 ∧ ∀ s : ℂ, 1 < s.re → Z s = (s - 1) * Complex.exp (∑' P : HeightOneSpectrum (𝓞 K), -Complex.log (1 - 1 * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-s))) := by
  intro K _ _
  obtain ⟨Z, hZd, hZ⟩ := _root_.GlobalTheory.dedekindZeta_eulerProduct_mul_sub_one_entire K
  refine ⟨Z, hZd, ?_, hZ⟩
  have h1 : Tendsto (fun s : ℝ => Z s) (𝓝[>] 1) (𝓝 (Z 1)) := by
    have : Continuous fun s : ℝ => Z s := hZd.continuous.comp Complex.continuous_ofReal
    simpa using (this.tendsto 1).mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (fun s : ℝ => Z s) (𝓝[>] 1) (𝓝 (dedekindZeta_residue K : ℂ)) := by
    refine (tendsto_sub_one_mul_dedekindZeta_nhdsGT K).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs' : 1 < (s : ℂ).re := by simpa using hs
    rw [hZ s hs', dedekindZeta_eq_exp_tsum_neg_log K s hs']
  rw [tendsto_nhds_unique h1 h2]
  exact_mod_cast dedekindZeta_residue_ne_zero K
end _root_.GlobalTheory
end GlobalTheory
