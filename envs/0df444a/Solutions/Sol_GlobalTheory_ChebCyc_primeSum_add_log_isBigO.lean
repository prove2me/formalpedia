-- Prove2me | solution 1 for GlobalTheory.ChebCyc.primeSum_add_log_isBigO
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:08:35.346993+00:00
-- url     : https://prove2.me/submissions/e00c8ee5-b133-4f67-9655-4732b584e88b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IdealCharacterLContinuationNeZeroOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_InfinitelyManyPrimesInRayClass
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_NotInjectiveTwoPrimesEqualNormCofinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NumberFieldPrimeZetaSumAddLogIsBigO
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_GlobalTheory_Mem_PosDirichlet_congr
import Theorems.Thm_GlobalTheory_Mem_RayPrimes_logSum_sub_bounded
import Theorems.Thm_GlobalTheory_Mem_RayPrimes_two_le_absNorm
import Theorems.Thm_GlobalTheory_Mem_ZetaPole_norm_dedekindZeta_eq_exp
import Theorems.Thm_GlobalTheory_Mem_ZetaPole_ofReal_logFactor
import Theorems.Thm_GlobalTheory_countable_ideal_and_summable_absNorm_rpow
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
namespace GlobalTheory.ChebCyc
open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial in
open scoped ContDiff Classical in
private theorem tsum_logFactor_add_log_sub_one_isBigO_one (K : Type) [Field K] [NumberField K] :
    (fun s : ℝ => (∑' P : HeightOneSpectrum (𝓞 K),
      _root_.GlobalTheory.Mem.ZetaPole.logFactor (Ideal.absNorm P.asIdeal) s) + Real.log (s - 1))
      =O[𝓝[>] 1] (fun _ => (1 : ℝ)) := by
  have hT := (tendsto_sub_one_mul_dedekindZeta_nhdsGT K).norm
  have hr : ‖((dedekindZeta_residue K : ℝ) : ℂ)‖ ≠ 0 := by
    simp [dedekindZeta_residue_ne_zero]
  have hL := ((Real.continuousAt_log hr).tendsto.comp hT).isBigO_one ℝ
  refine hL.congr' ?_ EventuallyEq.rfl
  filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)
  simp only [Function.comp_apply]
  rw [norm_mul, _root_.GlobalTheory.Mem.ZetaPole.norm_dedekindZeta_eq_exp K hs]
  have hs1 : ‖(s : ℂ) - 1‖ = s - 1 := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_of_nonneg (by linarith)]
  rw [hs1, Real.log_mul (sub_ne_zero.2 hs.ne') (Real.exp_pos _).ne', Real.log_exp]
  ring
open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial in
open scoped ContDiff Classical in
private theorem tsum_logFactor_sub_tsum_absNorm_rpow_isBigO_one (K : Type) [Field K]
    [NumberField K] :
    (fun s : ℝ => (∑' P : HeightOneSpectrum (𝓞 K),
      _root_.GlobalTheory.Mem.ZetaPole.logFactor (Ideal.absNorm P.asIdeal) s) -
      ∑' P : HeightOneSpectrum (𝓞 K), ((Ideal.absNorm P.asIdeal : ℕ) : ℝ) ^ (-s))
      =O[𝓝[>] 1] (fun _ => (1 : ℝ)) := by
  have hN : ∀ P : HeightOneSpectrum (𝓞 K), 2 ≤ Ideal.absNorm P.asIdeal :=
    fun P => _root_.GlobalTheory.Mem.RayPrimes.two_le_absNorm P
  have hC := _root_.GlobalTheory.Mem.RayPrimes.logSum_sub_bounded (fun P : HeightOneSpectrum (𝓞 K) =>
    Ideal.absNorm P.asIdeal) hN (fun _ => 1) (fun _ => by simp)
    (fun s hs => ((_root_.GlobalTheory.countable_ideal_and_summable_absNorm_rpow K).2 s hs).2)
  have hC' : (fun s : ℝ => (((∑' P : HeightOneSpectrum (𝓞 K),
      _root_.GlobalTheory.Mem.ZetaPole.logFactor (Ideal.absNorm P.asIdeal) s) -
      ∑' P : HeightOneSpectrum (𝓞 K), ((Ideal.absNorm P.asIdeal : ℕ) : ℝ) ^ (-s) : ℝ) : ℂ))
      =O[𝓝[>] 1] (fun _ => (1 : ℝ)) := by
    refine hC.congr' ?_ EventuallyEq.rfl
    filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)
    rw [Complex.ofReal_sub, Complex.ofReal_tsum, Complex.ofReal_tsum]
    congr 1
    · refine tsum_congr fun P => ?_
      rw [_root_.GlobalTheory.Mem.ZetaPole.ofReal_logFactor (by linarith [hN P]) (by linarith), one_mul]
    · refine tsum_congr fun P => ?_
      rw [Complex.ofReal_cpow (Nat.cast_nonneg _), one_mul, Complex.ofReal_natCast,
        Complex.ofReal_neg]
  rw [← isBigO_norm_left]
  exact hC'.norm_left.congr_left fun s => Complex.norm_real _
end GlobalTheory.ChebCyc
end

set_option autoImplicit false
open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial
open scoped ContDiff Classical
open GlobalTheory GlobalTheory.ChebCyc
open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial
open scoped ContDiff Classical
namespace GlobalTheory.ChebCyc
namespace _root_.GlobalTheory.ChebCyc
theorem _root_.solution : ∀ (K : Type) [Field K] [NumberField K], (fun s : ℝ => (∑' P : HeightOneSpectrum (𝓞 K), ((Ideal.absNorm P.asIdeal : ℕ) : ℝ) ^ (-s)) + Real.log (s - 1)) =O[𝓝[>] 1] (fun _ => (1 : ℝ)) := by
  intro K _ _
  refine ((tsum_logFactor_add_log_sub_one_isBigO_one K).sub
    (tsum_logFactor_sub_tsum_absNorm_rpow_isBigO_one K)).congr_left fun s => ?_
  ring
end _root_.GlobalTheory.ChebCyc
end GlobalTheory.ChebCyc
