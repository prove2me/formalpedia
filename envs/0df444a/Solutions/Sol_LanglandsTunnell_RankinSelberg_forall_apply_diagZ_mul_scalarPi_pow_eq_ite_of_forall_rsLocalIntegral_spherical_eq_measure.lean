-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.forall_apply_diagZ_mul_scalarPi_pow_eq_ite_of_forall_rsLocalIntegral_spherical_eq_measure
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/c9435636-c441-5c9a-9ce0-59e27c948e29

import Mathlib
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_HaarQuotient
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Theorems.Thm_LanglandsTunnell_CubicInduction_eq_zero_of_forall_sum_mul_pow_mul_heckeRecursionSeq_eq_zero
import Theorems.Thm_HaarQuotient_lintegral_eq_lintegral_lintegral_mul_out
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_eq_one_of_mem_integers
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Theorems.Thm_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_unipotent_localLevelOne_scalarPi_diagZ_torusFactor_of_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_LanglandsTunnell_RankinSelberg_forall_apply_diagZ_mul_scalarPi_pow_eq_ite_of_forall_rsLocalIntegral_spherical_eq_measure
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse

section FormalInverseOfSeries

open scoped Topology

theorem hasSum_coeff_mk_mul_coe_mul_pow (c : ℕ → ℂ) (Q : Polynomial ℂ) (z : ℂ)
    (hs : Summable fun n : ℕ => c n * z ^ n) :
    HasSum (fun n : ℕ => PowerSeries.coeff n (PowerSeries.mk c * (Q : PowerSeries ℂ)) * z ^ n)
      ((∑' n : ℕ, c n * z ^ n) * Q.eval z) := by
  set G : ℕ → ℂ := fun n => PowerSeries.coeff n (PowerSeries.mk c * (Q : PowerSeries ℂ)) with hG
  show HasSum (fun n : ℕ => G n * z ^ n) _
  set D := Q.natDegree with hD

  set u : ℕ → ℕ → ℂ := fun j n => if j ≤ n then c (n - j) * Q.coeff j * z ^ n else 0 with hu
  have hu_sum : ∀ j : ℕ, HasSum (u j) (Q.coeff j * z ^ j * ∑' n : ℕ, c n * z ^ n) := by
    intro j
    have hshift : HasSum (fun n : ℕ => u j (n + j)) (Q.coeff j * z ^ j * ∑' n : ℕ, c n * z ^ n) := by
      have h0 := hs.hasSum.mul_left (Q.coeff j * z ^ j)
      refine h0.congr_fun ?_
      intro n
      simp only [hu, Nat.le_add_left, if_true, Nat.add_sub_cancel, pow_add]
      ring
    have hzero : ∑ i ∈ Finset.range j, u j i = 0 := by
      refine Finset.sum_eq_zero fun i hi => ?_
      rw [Finset.mem_range] at hi
      simp [hu, not_le.mpr hi]
    have hshift' : HasSum (fun n : ℕ => u j (n + j))
        ((Q.coeff j * z ^ j * ∑' n : ℕ, c n * z ^ n) - ∑ i ∈ Finset.range j, u j i) := by
      rwa [hzero, sub_zero]
    exact (hasSum_nat_add_iff' j).mp hshift'

  have hG_eq : ∀ n : ℕ, G n * z ^ n = ∑ j ∈ Finset.range (D + 1), u j n := by
    intro n
    simp only [hG, PowerSeries.coeff_mul, PowerSeries.coeff_mk, Polynomial.coeff_coe, Finset.sum_mul]
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => c i * Q.coeff j * z ^ n)]
    simp only [Nat.succ_eq_add_one]
    rw [← Finset.sum_range_reflect]
    have hre : ∀ k ∈ Finset.range (n + 1),
        c (n + 1 - 1 - k) * Q.coeff (n - (n + 1 - 1 - k)) * z ^ n = c (n - k) * Q.coeff k * z ^ n := by
      intro k hk
      rw [Finset.mem_range] at hk
      rw [show n + 1 - 1 - k = n - k by omega, show n - (n - k) = k by omega]
    rw [Finset.sum_congr rfl hre]

    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
    symm
    refine Finset.sum_subset (f := fun k => c (n - k) * Q.coeff k * z ^ n) ?_ ?_
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_range] at hk
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le hk.2)
    · intro k hk hk'
      simp only [Finset.mem_filter, Finset.mem_range, not_and] at hk hk'
      have hkD : D < k := by
        by_contra hle
        exact hk' (Nat.lt_succ_of_le (not_lt.mp hle)) (Nat.lt_succ_iff.mp hk)
      show c (n - k) * Q.coeff k * z ^ n = 0
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (hD ▸ hkD)]
      ring

  have hfin := hasSum_sum (s := Finset.range (D + 1)) (f := fun j n => u j n)
    (a := fun j => Q.coeff j * z ^ j * ∑' n : ℕ, c n * z ^ n) (fun j _ => hu_sum j)
  have heval : Q.eval z = ∑ j ∈ Finset.range (D + 1), Q.coeff j * z ^ j := Polynomial.eval_eq_sum_range z
  have hval : (∑' n : ℕ, c n * z ^ n) * Q.eval z =
      ∑ j ∈ Finset.range (D + 1), Q.coeff j * z ^ j * ∑' n : ℕ, c n * z ^ n := by
    rw [heval, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [hval, show (fun n : ℕ => G n * z ^ n) = fun n => ∑ j ∈ Finset.range (D + 1), u j n from funext hG_eq]
  exact hfin

theorem tsum_mul_eval_eq_one_of_mk_mul_coe_eq_one (c : ℕ → ℂ) (Q : Polynomial ℂ) (z : ℂ)
    (hs : Summable fun n : ℕ => c n * z ^ n) (h : PowerSeries.mk c * (Q : PowerSeries ℂ) = 1) :
    (∑' n : ℕ, c n * z ^ n) * Q.eval z = 1 := by
  have h1 := hasSum_coeff_mk_mul_coe_mul_pow c Q z hs
  rw [h] at h1
  have h2 : HasSum (fun n : ℕ => PowerSeries.coeff n (1 : PowerSeries ℂ) * z ^ n) 1 := by
    have hfun : (fun n : ℕ => PowerSeries.coeff n (1 : PowerSeries ℂ) * z ^ n) =
        fun n : ℕ => if n = 0 then (1 : ℂ) else 0 := by
      funext n
      by_cases hn : n = 0
      · subst hn; simp
      · simp [PowerSeries.coeff_one, hn]
    rw [hfun]
    simpa using hasSum_ite_eq (0 : ℕ) (1 : ℂ)
  exact h1.unique h2

theorem mk_mul_coe_eq_one_of_forall_tsum_mul_eval_eq_one (F : ℕ → ℂ) (P : Polynomial ℂ) {r : ℝ}
    (hr : 0 < r) (hsum : ∀ z : ℂ, ‖z‖ < r → Summable fun n : ℕ => F n * z ^ n)
    (h : ∀ z : ℂ, ‖z‖ < r → (∑' n : ℕ, F n * z ^ n) * P.eval z = 1) :
    PowerSeries.mk F * (P : PowerSeries ℂ) = 1 := by

  set G : ℕ → ℂ := fun n => PowerSeries.coeff n (PowerSeries.mk F * (P : PowerSeries ℂ)) with hG
  have hA : ∀ z : ℂ, ‖z‖ < r → HasSum (fun n : ℕ => G n * z ^ n) ((∑' n : ℕ, F n * z ^ n) * P.eval z) :=
    fun z hz => hasSum_coeff_mk_mul_coe_mul_pow F P z (hsum z hz)
  have hB : ∀ z : ℂ, ‖z‖ < r → HasSum (fun n : ℕ => G n * z ^ n) 1 := fun z hz => h z hz ▸ hA z hz
  have hC : ∀ n : ℕ, G n = if n = 0 then 1 else 0 := by
    set Gc : ℕ → ℂ := fun n => if n = 0 then (1 : ℂ) else 0 with hGc

    have hr2 : (0 : ℝ) < r / 2 := by positivity
    have hsumG : HasSum (fun n : ℕ => G n * ((r / 2 : ℝ) : ℂ) ^ n) 1 := by
      refine hB _ ?_
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr2]
      linarith
    have hradG : (0 : ENNReal) < (FormalMultilinearSeries.ofScalars ℂ G).radius := by
      refine lt_of_lt_of_le ?_
        ((FormalMultilinearSeries.ofScalars ℂ G).le_radius_of_tendsto (r := ⟨r / 2, hr2.le⟩) (l := 0) ?_)
      · exact ENNReal.coe_pos.mpr (by exact_mod_cast hr2)
      · have ht := hsumG.summable.tendsto_atTop_zero
        have ht' := ht.norm
        simp only [norm_zero, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr2] at ht'
        have h__ := ht'
        try simp [FormalMultilinearSeries.ofScalars_norm] at h__
        try simp [FormalMultilinearSeries.ofScalars_norm]
        exact h__
    have hradGc : (0 : ENNReal) < (FormalMultilinearSeries.ofScalars ℂ Gc).radius := by
      refine lt_of_lt_of_le ?_
        ((FormalMultilinearSeries.ofScalars ℂ Gc).le_radius_of_bound (C := 1) (r := 1) ?_)
      · exact zero_lt_one
      · intro n
        rw [FormalMultilinearSeries.ofScalars_norm]
        cases n <;> simp [hGc]

    have h1 : HasFPowerSeriesAt (FormalMultilinearSeries.ofScalars ℂ G).sum
        (FormalMultilinearSeries.ofScalars ℂ G) 0 :=
      ((FormalMultilinearSeries.ofScalars ℂ G).hasFPowerSeriesOnBall hradG).hasFPowerSeriesAt
    have h2 : HasFPowerSeriesAt (FormalMultilinearSeries.ofScalars ℂ Gc).sum
        (FormalMultilinearSeries.ofScalars ℂ Gc) 0 :=
      ((FormalMultilinearSeries.ofScalars ℂ Gc).hasFPowerSeriesOnBall hradGc).hasFPowerSeriesAt
    have heq : ∀ᶠ z in 𝓝 (0 : ℂ), (FormalMultilinearSeries.ofScalars ℂ G).sum z =
        (FormalMultilinearSeries.ofScalars ℂ Gc).sum z := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hr] with z hz
      rw [Metric.mem_ball, dist_zero_right] at hz
      have hGz : (FormalMultilinearSeries.ofScalars ℂ G).sum z = 1 := by
        change FormalMultilinearSeries.ofScalarsSum G z = 1
        rw [FormalMultilinearSeries.ofScalars_sum_eq]
        simpa only [smul_eq_mul] using (hB z hz).tsum_eq
      have hGcz : (FormalMultilinearSeries.ofScalars ℂ Gc).sum z = 1 := by
        change FormalMultilinearSeries.ofScalarsSum Gc z = 1
        rw [FormalMultilinearSeries.ofScalars_sum_eq]
        simp [hGc]
      rw [hGz, hGcz]
    have hser := h1.eq_formalMultilinearSeries_of_eventually h2 heq
    have hfun : G = Gc := FormalMultilinearSeries.ofScalars_series_injective ℂ ℂ hser
    intro n
    exact congrFun hfun n
  ext n
  simpa [hG] using hC n

theorem exists_re_lt_and_cpow_neg_eq {N : ℝ} (hN : 1 < N) (σ : ℝ) {X : ℂ} (hX : X ≠ 0)
    (hXr : ‖X‖ < N ^ (-σ)) : ∃ s : ℂ, σ < s.re ∧ ((N : ℂ) ^ (-s)) = X := by
  have hN0 : (0 : ℝ) < N := by linarith
  have hlogN : 0 < Real.log N := Real.log_pos hN
  refine ⟨-(Complex.log X / (Real.log N : ℂ)), ?_, ?_⟩
  · have hre : (-(Complex.log X / (Real.log N : ℂ))).re = -(Real.log ‖X‖ / Real.log N) := by
      rw [Complex.neg_re, Complex.div_ofReal_re, Complex.log_re]
    rw [hre]
    have hlt : Real.log ‖X‖ < -σ * Real.log N := by
      have := Real.log_lt_log (norm_pos_iff.mpr hX) hXr
      rwa [Real.log_rpow hN0] at this
    have hdiv : Real.log ‖X‖ / Real.log N < -σ := (div_lt_iff₀ hlogN).mpr hlt
    linarith
  · have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN0.ne'
    rw [Complex.cpow_def_of_ne_zero hNc, neg_neg, ← Complex.ofReal_log hN0.le]
    rw [mul_div_cancel₀ _ (by exact_mod_cast hlogN.ne')]
    exact Complex.exp_log hX

theorem hasSum_cone_coeff_mul_pow (c : ℤ × ℤ → ℂ) (hc : ∀ p : ℤ × ℤ, ¬ (0 ≤ p.2 ∧ p.2 ≤ p.1) → c p = 0)
    (X S : ℂ) (h : HasSum (fun p : ℤ × ℤ => c p * X ^ (p.1 + p.2).toNat) S) :
    HasSum (fun n : ℕ => (∑ k ∈ Finset.range (n / 2 + 1), c ((n : ℤ) - k, (k : ℤ))) * X ^ n) S := by

  let e : (Σ n : ℕ, Fin (n / 2 + 1)) → ℤ × ℤ := fun q => ((q.1 : ℤ) - (q.2 : ℕ), ((q.2 : ℕ) : ℤ))
  have he : Function.Injective e := by
    rintro ⟨n, k⟩ ⟨n', k'⟩ hq
    simp only [e, Prod.mk.injEq] at hq
    have h1 : (k : ℕ) = k' := by exact_mod_cast hq.2
    have h2 : n = n' := by omega
    subst h2
    simp only [Sigma.mk.injEq, heq_eq_eq, true_and]
    exact Fin.ext h1
  have hrange : ∀ p : ℤ × ℤ, p ∉ Set.range e → c p * X ^ (p.1 + p.2).toNat = 0 := by
    intro p hp
    rw [hc p, zero_mul]
    rintro ⟨h0, h12⟩
    apply hp
    refine ⟨⟨(p.1 + p.2).toNat, ⟨p.2.toNat, ?_⟩⟩, ?_⟩
    · omega
    · ext <;> simp only [e] <;> omega
  have hsig : HasSum (fun q => c (e q) * X ^ ((e q).1 + (e q).2).toNat) S :=
    (he.hasSum_iff hrange).mpr h
  have hdeg : ∀ q : (Σ n : ℕ, Fin (n / 2 + 1)), ((e q).1 + (e q).2).toNat = q.1 := by
    rintro ⟨n, k⟩
    simp only [e]
    omega
  simp_rw [hdeg] at hsig
  refine hsig.sigma fun n => ?_
  rw [Finset.sum_mul, ← Fin.sum_univ_eq_sum_range (fun k => c ((n : ℤ) - k, (k : ℤ)) * X ^ n)]
  exact hasSum_fintype _

end FormalInverseOfSeries

section ConstantTermOffPuncturedDisc

open scoped Topology

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "CubicInduction.embedMat2 CubicInduction.iotaGL CubicInduction.coe_iotaGL TateLocal.modulus CubicInduction.eq_zero_of_forall_sum_mul_pow_mul_heckeRecursionSeq_eq_zero TateLocal.psiLocal_eq_one_of_mem_integers TateLocal.modulus_adicCompletion_eq_nnnorm RankinSelberg.hasSum_cell_terms_rsLocalIntegral CubicInduction.exists_unipotent_localLevelOne_scalarPi_diagZ_torusFactor_of_ne_zero"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "embedMat2 iotaGL coe_iotaGL varpi eq_zero_of_forall_sum_mul_pow_mul_heckeRecursionSeq_eq_zero exists_unipotent_localLevelOne_scalarPi_diagZ_torusFactor_of_ne_zero"
namespace PuncturedDisc
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

theorem tsum_mul_zero_pow (F : ℕ → ℂ) : (∑' n : ℕ, F n * (0 : ℂ) ^ n) = F 0 := by
  rw [tsum_eq_single 0 fun n hn => by simp [zero_pow hn]]
  simp

theorem coeff_zero_mul_eval_zero_eq_eval_zero_of_forall_ne_zero (F : ℕ → ℂ) (P R : Polynomial ℂ) {r : ℝ}
    (hr : 0 < r) (hsum : ∀ z : ℂ, z ≠ 0 → ‖z‖ < r → Summable fun n : ℕ => F n * z ^ n)
    (h : ∀ z : ℂ, z ≠ 0 → ‖z‖ < r → (∑' n : ℕ, F n * z ^ n) * P.eval z = R.eval z) :
    F 0 * P.eval 0 = R.eval 0 := by

  have hr2 : (0 : ℝ) < r / 2 := by positivity
  have hsum2 : Summable fun n : ℕ => F n * ((r / 2 : ℝ) : ℂ) ^ n := by
    refine hsum _ (by exact_mod_cast hr2.ne') ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr2]
    linarith
  have hrad : (0 : ENNReal) < (FormalMultilinearSeries.ofScalars ℂ F).radius := by
    refine lt_of_lt_of_le ?_
      ((FormalMultilinearSeries.ofScalars ℂ F).le_radius_of_tendsto (r := ⟨r / 2, hr2.le⟩) (l := 0) ?_)
    · exact ENNReal.coe_pos.mpr (by exact_mod_cast hr2)
    · have ht := hsum2.tendsto_atTop_zero
      have ht' := ht.norm
      simp only [norm_zero, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr2] at ht'
      have h__ := ht'
      try simp [FormalMultilinearSeries.ofScalars_norm] at h__
      try simp [FormalMultilinearSeries.ofScalars_norm]
      exact h__

  have hfp : HasFPowerSeriesAt (FormalMultilinearSeries.ofScalars ℂ F).sum
      (FormalMultilinearSeries.ofScalars ℂ F) 0 :=
    ((FormalMultilinearSeries.ofScalars ℂ F).hasFPowerSeriesOnBall hrad).hasFPowerSeriesAt
  have hval : ∀ z : ℂ, (FormalMultilinearSeries.ofScalars ℂ F).sum z = ∑' n : ℕ, F n * z ^ n := by
    intro z
    change FormalMultilinearSeries.ofScalarsSum F z = _
    rw [FormalMultilinearSeries.ofScalars_sum_eq]
    simp only [smul_eq_mul]
  set g : ℂ → ℂ := fun z => (FormalMultilinearSeries.ofScalars ℂ F).sum z * P.eval z with hg
  have hcont : ContinuousAt g 0 := hfp.continuousAt.mul P.continuous.continuousAt

  have hpunct : ∀ᶠ z in 𝓝[≠] (0 : ℂ), R.eval z = g z := by
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds (0 : ℂ) hr)]
      with z hz hzr
    rw [Metric.mem_ball, dist_zero_right] at hzr
    simp only [hg, hval]
    exact (h z hz hzr).symm
  have h1 : Filter.Tendsto g (𝓝[≠] (0 : ℂ)) (𝓝 (g 0)) := hcont.tendsto.mono_left nhdsWithin_le_nhds
  have h2 : Filter.Tendsto g (𝓝[≠] (0 : ℂ)) (𝓝 (R.eval 0)) :=
    (R.continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' hpunct
  have h0 : g 0 = R.eval 0 := tendsto_nhds_unique h1 h2
  simpa only [hg, hval, tsum_mul_zero_pow] using h0

theorem coeff_zero_mul_eval_zero_eq_of_forall_ne_zero (F : ℕ → ℂ) (P : Polynomial ℂ) (C : ℂ) {r : ℝ}
    (hr : 0 < r) (hsum : ∀ z : ℂ, z ≠ 0 → ‖z‖ < r → Summable fun n : ℕ => F n * z ^ n)
    (h : ∀ z : ℂ, z ≠ 0 → ‖z‖ < r → (∑' n : ℕ, F n * z ^ n) * P.eval z = C) :
    F 0 * P.eval 0 = C := by
  have := coeff_zero_mul_eval_zero_eq_eval_zero_of_forall_ne_zero F P (Polynomial.C C) hr hsum
    fun z hz hzr => by rw [Polynomial.eval_C]; exact h z hz hzr
  rwa [Polynomial.eval_C] at this

theorem eval_mul_natCast_cpow_neg_add_half_add_half (N : ℕ) (hN : 1 < N) (E : Polynomial ℂ) (a w : ℂ) :
    E.eval (a * (N : ℂ) ^ (-(w + 1 / 2 + 1 / 2))) =
      (E.comp (Polynomial.C (a * (N : ℂ) ^ (-(1 : ℂ))) * Polynomial.X)).eval ((N : ℂ) ^ (-w)) := by
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  rw [Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    show -(w + 1 / 2 + 1 / 2) = -(1 : ℂ) + -w by ring, Complex.cpow_add _ _ hN0, mul_assoc]

end LanglandsTunnell.CubicInduction.PuncturedDisc

end ConstantTermOffPuncturedDisc

section ComplexPowerIdentities

namespace SphericalValuesLemmas

theorem ofReal_zpow_neg_cpow {N : ℝ} (hN : 0 < N) (k : ℕ) (w : ℂ) :
    (((N ^ (-(k : ℤ)) : ℝ) : ℂ)) ^ w = ((N : ℂ) ^ (-w)) ^ k := by
  have h1 : (N ^ (-(k : ℤ)) : ℝ) = N ^ (-(k : ℝ)) := by
    rw [show (-(k : ℝ)) = ((-(k : ℤ) : ℤ) : ℝ) by push_cast; ring, Real.rpow_intCast]
  rw [h1, ← Complex.cpow_mul_ofReal_nonneg hN.le, ← Complex.cpow_nat_mul]
  congr 1
  push_cast
  ring

end SphericalValuesLemmas

end ComplexPowerIdentities

section TwoRowProductSeries

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "CubicInduction.embedMat2 CubicInduction.iotaGL CubicInduction.coe_iotaGL TateLocal.modulus CubicInduction.eq_zero_of_forall_sum_mul_pow_mul_heckeRecursionSeq_eq_zero TateLocal.psiLocal_eq_one_of_mem_integers TateLocal.modulus_adicCompletion_eq_nnnorm RankinSelberg.hasSum_cell_terms_rsLocalIntegral CubicInduction.exists_unipotent_localLevelOne_scalarPi_diagZ_torusFactor_of_ne_zero"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "embedMat2 iotaGL coe_iotaGL varpi eq_zero_of_forall_sum_mul_pow_mul_heckeRecursionSeq_eq_zero exists_unipotent_localLevelOne_scalarPi_diagZ_torusFactor_of_ne_zero"
namespace TwoRowProduct
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

noncomputable def pairComplete (x₁ x₂ : ℂ) (j : ℕ) : ℂ :=
  ∑ i ∈ Finset.range (j + 1), x₁ ^ i * x₂ ^ (j - i)

def seqMinor (b : ℕ → ℂ) (k₁ : ℕ) : ℕ → ℂ
  | 0 => b k₁ * b 0
  | k + 1 => b k₁ * b (k + 1) - b (k₁ + 1) * b k

theorem sum_seqMinor_telescope (b : ℕ → ℂ) (n : ℕ) :
    ∀ c : ℕ, c ≤ n → ∑ k ∈ Finset.range (c + 1), seqMinor b (n - k) k = b (n - c) * b c := by
  intro c
  induction c with
  | zero => intro _; simp [seqMinor]
  | succ c ih =>
    intro hc
    rw [Finset.sum_range_succ, ih (Nat.le_of_succ_le hc)]
    have h : n - (c + 1) + 1 = n - c := by omega
    simp only [seqMinor, h]
    ring

theorem pow_mul_pairComplete_eq (x₁ x₂ : ℂ) (n k : ℕ) (hk : k ∈ Finset.range (n / 2 + 1)) :
    (x₁ * x₂) ^ k * pairComplete x₁ x₂ (n - 2 * k) =
      ∑ a ∈ Finset.range (n + 1), if k ≤ a ∧ a ≤ n - k then x₁ ^ a * x₂ ^ (n - a) else 0 := by
  have hk' : 2 * k ≤ n := by
    have := Finset.mem_range.mp hk
    omega
  unfold pairComplete
  rw [Finset.mul_sum, Finset.sum_ite, Finset.sum_const_zero, add_zero]

  have himage : (Finset.range (n + 1)).filter (fun a => k ≤ a ∧ a ≤ n - k) =
      (Finset.range (n - 2 * k + 1)).map (addLeftEmbedding k) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_map, addLeftEmbedding_apply]
    constructor
    · rintro ⟨_, hka, han⟩
      exact ⟨a - k, by omega, by omega⟩
    · rintro ⟨i, hi, rfl⟩
      omega
  simp only [himage, Finset.sum_map]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ n - 2 * k := by
    have := Finset.mem_range.mp hi
    omega
  simp only [addLeftEmbedding_apply]
  have e₁ : n - (k + i) = n - 2 * k - i + k := by omega
  rw [e₁, pow_add, pow_add, mul_pow]
  ring

theorem sum_mul_pow_eq_sum_pairComplete_mul_seqMinor (b : ℕ → ℂ) (x₁ x₂ : ℂ) (n : ℕ) :
    ∑ m ∈ Finset.range (n + 1), b m * b (n - m) * (x₁ ^ m * x₂ ^ (n - m)) =
      ∑ k ∈ Finset.range (n / 2 + 1),
        (x₁ * x₂) ^ k * pairComplete x₁ x₂ (n - 2 * k) * seqMinor b (n - k) k := by

  have hrhs : ∀ k ∈ Finset.range (n / 2 + 1),
      (x₁ * x₂) ^ k * pairComplete x₁ x₂ (n - 2 * k) * seqMinor b (n - k) k =
        ∑ a ∈ Finset.range (n + 1),
          if k ≤ a ∧ a ≤ n - k then x₁ ^ a * x₂ ^ (n - a) * seqMinor b (n - k) k else 0 := by
    intro k hk
    rw [pow_mul_pairComplete_eq x₁ x₂ n k hk, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    split_ifs <;> simp
  rw [Finset.sum_congr rfl hrhs, Finset.sum_comm]
  refine Finset.sum_congr rfl fun a ha => ?_
  have ha' : a ≤ n := by
    have := Finset.mem_range.mp ha
    omega

  set c := min a (n - a) with hc
  have hfilter : (Finset.range (n / 2 + 1)).filter (fun k => k ≤ a ∧ a ≤ n - k) = Finset.range (c + 1) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, hc]
    omega
  rw [← Finset.sum_filter]
  simp only [hfilter]
  have hsum : ∑ k ∈ Finset.range (c + 1), x₁ ^ a * x₂ ^ (n - a) * seqMinor b (n - k) k =
      x₁ ^ a * x₂ ^ (n - a) * ∑ k ∈ Finset.range (c + 1), seqMinor b (n - k) k := by
    rw [Finset.mul_sum]
  rw [hsum, sum_seqMinor_telescope b n c (by omega)]

  rcases le_total a (n - a) with h | h
  · have e : c = a := min_eq_left h
    rw [e]
    ring
  · have e : c = n - a := min_eq_right h
    have e' : n - (n - a) = a := by omega
    rw [e, e']
    ring

theorem sum_range_add_two (f : ℕ → ℂ) (m : ℕ) :
    ∑ k ∈ Finset.range (m + 2), f k = f 0 + f 1 + ∑ k ∈ Finset.range m, f (k + 2) := by
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  ring

theorem sum_cut_eq_kappa_mul (b h : ℕ → ℂ) (κ : ℂ) (hh0 : h 0 = 1)
    (hA : ∀ k : ℕ, b (k + 2) * b 2 - b (k + 3) * b 1 = κ * h k)
    (hB : ∀ k₁ k₂ : ℕ, b (k₁ + 2) * b (k₂ + 3) - b (k₁ + 3) * b (k₂ + 2) =
      κ * (h k₁ * h (k₂ + 1) - h (k₁ + 1) * h k₂))
    (x₁ x₂ : ℂ) (n : ℕ) :
    ∑ k ∈ Finset.range (n / 2 + 1),
        (x₁ * x₂) ^ (k + 2) * pairComplete x₁ x₂ (n - 2 * k) * seqMinor b (n - k + 2) (k + 2) =
      κ * ((x₁ * x₂) ^ 2 * ∑ k ∈ Finset.range (n / 2 + 1),
        (x₁ * x₂) ^ k * pairComplete x₁ x₂ (n - 2 * k) * seqMinor h (n - k) k) := by
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := by
    have := Finset.mem_range.mp hk
    omega
  cases k with
  | zero =>
    have e := hA n
    simp only [seqMinor, hh0, Nat.sub_zero]
    linear_combination (x₁ * x₂) ^ (0 + 2) * pairComplete x₁ x₂ (n - 2 * 0) * e
  | succ k =>
    obtain ⟨k₁, rfl⟩ : ∃ k₁, n = k₁ + (k + 1) := ⟨n - (k + 1), by omega⟩
    have e₁ : k₁ + (k + 1) - (k + 1) + 2 = k₁ + 2 := by omega
    have e₂ : k₁ + (k + 1) - (k + 1) = k₁ := by omega
    have e := hB k₁ k
    rw [e₁, e₂]
    show (x₁ * x₂) ^ (k + 1 + 2) * pairComplete x₁ x₂ (k₁ + (k + 1) - 2 * (k + 1)) *
          (b (k₁ + 2) * b (k + 3) - b (k₁ + 3) * b (k + 2)) =
        κ * ((x₁ * x₂) ^ 2 * ((x₁ * x₂) ^ (k + 1) * pairComplete x₁ x₂ (k₁ + (k + 1) - 2 * (k + 1)) *
          (h k₁ * h (k + 1) - h (k₁ + 1) * h k)))
    linear_combination ((x₁ * x₂) ^ (k + 1 + 2) * pairComplete x₁ x₂ (k₁ + (k + 1) - 2 * (k + 1))) * e

end LanglandsTunnell.CubicInduction.TwoRowProduct

end TwoRowProductSeries

section DualCoefficientReadOff

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "CubicInduction.embedMat2 CubicInduction.iotaGL CubicInduction.coe_iotaGL TateLocal.modulus CubicInduction.eq_zero_of_forall_sum_mul_pow_mul_heckeRecursionSeq_eq_zero TateLocal.psiLocal_eq_one_of_mem_integers TateLocal.modulus_adicCompletion_eq_nnnorm RankinSelberg.hasSum_cell_terms_rsLocalIntegral CubicInduction.exists_unipotent_localLevelOne_scalarPi_diagZ_torusFactor_of_ne_zero"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "embedMat2 iotaGL coe_iotaGL varpi eq_zero_of_forall_sum_mul_pow_mul_heckeRecursionSeq_eq_zero exists_unipotent_localLevelOne_scalarPi_diagZ_torusFactor_of_ne_zero"
namespace TwoRowProduct
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

open scoped Topology

theorem pairValues_heckeRecursionSeq_one_eq_sum (a₁ a₂ : ℂ) (r : ℕ) :
    UnramifiedWhittaker.heckeRecursionSeq 1 (a₁ + a₂) (a₁ * a₂) r =
      ∑ i ∈ Finset.range (r + 1), a₁ ^ i * a₂ ^ (r - i) := by
  have hstep : ∀ r : ℕ,
      (∑ i ∈ Finset.range (r + 1 + 1), a₁ ^ i * a₂ ^ (r + 1 - i)) =
        a₁ * (∑ i ∈ Finset.range (r + 1), a₁ ^ i * a₂ ^ (r - i)) + a₂ ^ (r + 1) := by
    intro r
    rw [Finset.sum_range_succ', Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [Nat.add_sub_add_right, pow_succ]
      ring
    · simp
  induction r using Nat.twoStepInduction with
  | zero => simp [UnramifiedWhittaker.heckeRecursionSeq]
  | one =>
    simp only [UnramifiedWhittaker.heckeRecursionSeq, div_one, Finset.sum_range_succ, Finset.sum_range_zero,
      pow_zero, pow_one, Nat.sub_zero, Nat.sub_self, one_mul, mul_one]
    ring
  | more n ih1 ih2 =>
    rw [UnramifiedWhittaker.heckeRecursionSeq, div_one, ih2, ih1]
    show _ = ∑ i ∈ Finset.range (n + 1 + 1 + 1), a₁ ^ i * a₂ ^ (n + 1 + 1 - i)
    rw [hstep (n + 1), hstep n]
    ring

theorem pairComplete_eq_heckeRecursionSeq (x₁ x₂ : ℂ) (j : ℕ) :
    pairComplete x₁ x₂ j = UnramifiedWhittaker.heckeRecursionSeq 1 (x₁ + x₂) (x₁ * x₂) j := by
  unfold pairComplete
  exact (pairValues_heckeRecursionSeq_one_eq_sum x₁ x₂ j).symm

theorem eq_on_cone_of_forall_sum_pairComplete_mul_eq (V M : ℕ → ℕ → ℂ)
    (h : ∀ x₁ x₂ : ℂ, x₁ * x₂ ≠ 0 → ∀ n : ℕ,
      ∑ k ∈ Finset.range (n / 2 + 1), (x₁ * x₂) ^ k * pairComplete x₁ x₂ (n - 2 * k) * V (n - k) k =
        ∑ k ∈ Finset.range (n / 2 + 1), (x₁ * x₂) ^ k * pairComplete x₁ x₂ (n - 2 * k) * M (n - k) k) :
    ∀ n k : ℕ, k ≤ n / 2 → V (n - k) k = M (n - k) k := by
  intro n k hk
  have hz := LanglandsTunnell.CubicInduction.eq_zero_of_forall_sum_mul_pow_mul_heckeRecursionSeq_eq_zero n
    (fun j => V (n - j) j - M (n - j) j) ?_ k hk
  · exact sub_eq_zero.1 hz
  intro x₁ x₂ hx
  have h' := h x₁ x₂ hx n
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib] at h'
  refine Eq.trans ?_ h'
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← pairComplete_eq_heckeRecursionSeq]
  ring

theorem radius_pos_of_forall_hasSum (a : ℕ → ℂ) (S : ℂ → ℂ) {r : ℝ} (hr : 0 < r)
    (ha : ∀ z : ℂ, ‖z‖ < r → HasSum (fun n : ℕ => a n * z ^ n) (S z)) :
    (0 : ENNReal) < (FormalMultilinearSeries.ofScalars ℂ a).radius := by
  have hr2 : (0 : ℝ) < r / 2 := by positivity
  have hsum : HasSum (fun n : ℕ => a n * ((r / 2 : ℝ) : ℂ) ^ n) (S ((r / 2 : ℝ) : ℂ)) := by
    refine ha _ ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr2]
    linarith
  refine lt_of_lt_of_le ?_
    ((FormalMultilinearSeries.ofScalars ℂ a).le_radius_of_tendsto (r := ⟨r / 2, hr2.le⟩) (l := 0) ?_)
  · exact ENNReal.coe_pos.mpr (by exact_mod_cast hr2)
  · have ht := hsum.summable.tendsto_atTop_zero
    have ht' := ht.norm
    simp only [norm_zero, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr2] at ht'
    have h__ := ht'
    try simp [FormalMultilinearSeries.ofScalars_norm] at h__
    try simp [FormalMultilinearSeries.ofScalars_norm]
    exact h__

theorem eq_of_forall_hasSum_eq (a c : ℕ → ℂ) (S : ℂ → ℂ) {r : ℝ} (hr : 0 < r)
    (ha : ∀ z : ℂ, ‖z‖ < r → HasSum (fun n : ℕ => a n * z ^ n) (S z))
    (hc : ∀ z : ℂ, ‖z‖ < r → HasSum (fun n : ℕ => c n * z ^ n) (S z)) : a = c := by
  have h1 : HasFPowerSeriesAt (FormalMultilinearSeries.ofScalars ℂ a).sum
      (FormalMultilinearSeries.ofScalars ℂ a) 0 :=
    ((FormalMultilinearSeries.ofScalars ℂ a).hasFPowerSeriesOnBall
      (radius_pos_of_forall_hasSum a S hr ha)).hasFPowerSeriesAt
  have h2 : HasFPowerSeriesAt (FormalMultilinearSeries.ofScalars ℂ c).sum
      (FormalMultilinearSeries.ofScalars ℂ c) 0 :=
    ((FormalMultilinearSeries.ofScalars ℂ c).hasFPowerSeriesOnBall
      (radius_pos_of_forall_hasSum c S hr hc)).hasFPowerSeriesAt
  have heq : ∀ᶠ z in 𝓝 (0 : ℂ), (FormalMultilinearSeries.ofScalars ℂ a).sum z =
      (FormalMultilinearSeries.ofScalars ℂ c).sum z := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hr] with z hz
    rw [Metric.mem_ball, dist_zero_right] at hz
    have haz : (FormalMultilinearSeries.ofScalars ℂ a).sum z = S z := by
      change FormalMultilinearSeries.ofScalarsSum a z = S z
      rw [FormalMultilinearSeries.ofScalars_sum_eq]
      simpa only [smul_eq_mul] using (ha z hz).tsum_eq
    have hcz : (FormalMultilinearSeries.ofScalars ℂ c).sum z = S z := by
      change FormalMultilinearSeries.ofScalarsSum c z = S z
      rw [FormalMultilinearSeries.ofScalars_sum_eq]
      simpa only [smul_eq_mul] using (hc z hz).tsum_eq
    rw [haz, hcz]
  exact FormalMultilinearSeries.ofScalars_series_injective ℂ ℂ (h1.eq_formalMultilinearSeries_of_eventually h2 heq)

theorem eq_seqMinor_on_cone_of_forall_hasSum (b : ℕ → ℂ) (V : ℕ → ℕ → ℂ) (S : ℂ → ℂ → ℂ → ℂ) {r : ℝ}
    (hr : 0 < r)
    (hV : ∀ x₁ x₂ : ℂ, x₁ * x₂ ≠ 0 → ∀ z : ℂ, ‖z‖ < r →
      HasSum (fun n : ℕ =>
        (∑ k ∈ Finset.range (n / 2 + 1), (x₁ * x₂) ^ k * pairComplete x₁ x₂ (n - 2 * k) * V (n - k) k) * z ^ n)
        (S x₁ x₂ z))
    (hb : ∀ x₁ x₂ : ℂ, x₁ * x₂ ≠ 0 → ∀ z : ℂ, ‖z‖ < r →
      HasSum (fun n : ℕ =>
        (∑ m ∈ Finset.range (n + 1), b m * b (n - m) * (x₁ ^ m * x₂ ^ (n - m))) * z ^ n)
        (S x₁ x₂ z)) :
    ∀ n k : ℕ, k ≤ n / 2 → V (n - k) k = seqMinor b (n - k) k := by
  refine eq_on_cone_of_forall_sum_pairComplete_mul_eq V (seqMinor b) ?_
  intro x₁ x₂ hx n
  have hcoeff : (∑ k ∈ Finset.range (n / 2 + 1), (x₁ * x₂) ^ k * pairComplete x₁ x₂ (n - 2 * k) * V (n - k) k) =
      ∑ m ∈ Finset.range (n + 1), b m * b (n - m) * (x₁ ^ m * x₂ ^ (n - m)) :=
    congrFun (eq_of_forall_hasSum_eq
      (fun n : ℕ => ∑ k ∈ Finset.range (n / 2 + 1), (x₁ * x₂) ^ k * pairComplete x₁ x₂ (n - 2 * k) * V (n - k) k)
      (fun n : ℕ => ∑ m ∈ Finset.range (n + 1), b m * b (n - m) * (x₁ ^ m * x₂ ^ (n - m)))
      (S x₁ x₂) hr (hV x₁ x₂ hx) (hb x₁ x₂ hx)) n
  rw [hcoeff]
  exact sum_mul_pow_eq_sum_pairComplete_mul_seqMinor b x₁ x₂ n

end LanglandsTunnell.CubicInduction.TwoRowProduct

end DualCoefficientReadOff

section FormalCoefficientReadOff

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "CubicInduction.embedMat2 CubicInduction.iotaGL CubicInduction.coe_iotaGL TateLocal.modulus CubicInduction.eq_zero_of_forall_sum_mul_pow_mul_heckeRecursionSeq_eq_zero TateLocal.psiLocal_eq_one_of_mem_integers TateLocal.modulus_adicCompletion_eq_nnnorm RankinSelberg.hasSum_cell_terms_rsLocalIntegral CubicInduction.exists_unipotent_localLevelOne_scalarPi_diagZ_torusFactor_of_ne_zero"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "embedMat2 iotaGL coe_iotaGL varpi eq_zero_of_forall_sum_mul_pow_mul_heckeRecursionSeq_eq_zero exists_unipotent_localLevelOne_scalarPi_diagZ_torusFactor_of_ne_zero"
namespace FormalReadOff
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

theorem rescale_mul_rescale_coe_eq_one (H : PowerSeries ℂ) (Q : Polynomial ℂ)
    (hH : H * (Q : PowerSeries ℂ) = 1) (x : ℂ) :
    PowerSeries.rescale x H * PowerSeries.rescale x (Q : PowerSeries ℂ) = 1 := by
  rw [← map_mul, hH, map_one]

theorem coe_comp_C_mul_X (p : Polynomial ℂ) (x : ℂ) :
    ((p.comp (Polynomial.C x * Polynomial.X) : Polynomial ℂ) : PowerSeries ℂ) =
      PowerSeries.rescale x (p : PowerSeries ℂ) := by
  ext n
  rw [Polynomial.coeff_coe, Polynomial.comp_C_mul_X_coeff, PowerSeries.coeff_rescale, Polynomial.coeff_coe,
    mul_comm]

theorem coeff_eq_sum_range_of_mul_coe_comp_eq (S H : PowerSeries ℂ) (Q U : Polynomial ℂ) (x₁ x₂ : ℂ)
    (hH : H * (Q : PowerSeries ℂ) = 1)
    (hS : S * ((Q.comp (Polynomial.C x₁ * Polynomial.X) * Q.comp (Polynomial.C x₂ * Polynomial.X) :
        Polynomial ℂ) : PowerSeries ℂ) =
      ((U.comp (Polynomial.C x₁ * Polynomial.X) * U.comp (Polynomial.C x₂ * Polynomial.X) :
        Polynomial ℂ) : PowerSeries ℂ))
    (n : ℕ) :
    PowerSeries.coeff n S =
      ∑ m ∈ Finset.range (n + 1),
        PowerSeries.coeff m ((U : PowerSeries ℂ) * H) * PowerSeries.coeff (n - m) ((U : PowerSeries ℂ) * H) *
          (x₁ ^ m * x₂ ^ (n - m)) := by
  have h₁ := rescale_mul_rescale_coe_eq_one H Q hH x₁
  have h₂ := rescale_mul_rescale_coe_eq_one H Q hH x₂
  rw [Polynomial.coe_mul, Polynomial.coe_mul, coe_comp_C_mul_X, coe_comp_C_mul_X, coe_comp_C_mul_X,
    coe_comp_C_mul_X] at hS

  have hprod : S =
      PowerSeries.rescale x₁ ((U : PowerSeries ℂ) * H) * PowerSeries.rescale x₂ ((U : PowerSeries ℂ) * H) := by
    rw [map_mul, map_mul]
    linear_combination (PowerSeries.rescale x₁ H * PowerSeries.rescale x₂ H) * hS -
      (S * (PowerSeries.rescale x₂ H * PowerSeries.rescale x₂ (Q : PowerSeries ℂ))) * h₁ - S * h₂
  rw [hprod, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [PowerSeries.coeff_rescale]
  ring

end LanglandsTunnell.CubicInduction.FormalReadOff

end FormalCoefficientReadOff

section ClosedFormCore

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "CubicInduction.embedMat2 CubicInduction.iotaGL CubicInduction.coe_iotaGL TateLocal.modulus CubicInduction.eq_zero_of_forall_sum_mul_pow_mul_heckeRecursionSeq_eq_zero TateLocal.psiLocal_eq_one_of_mem_integers TateLocal.modulus_adicCompletion_eq_nnnorm RankinSelberg.hasSum_cell_terms_rsLocalIntegral CubicInduction.exists_unipotent_localLevelOne_scalarPi_diagZ_torusFactor_of_ne_zero"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "embedMat2 iotaGL coe_iotaGL varpi eq_zero_of_forall_sum_mul_pow_mul_heckeRecursionSeq_eq_zero exists_unipotent_localLevelOne_scalarPi_diagZ_torusFactor_of_ne_zero"
namespace ClosedForm
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

theorem hasSum_coeff_mul_pow_eval (R : Polynomial ℂ) (z : ℂ) :
    HasSum (fun n : ℕ => R.coeff n * z ^ n) (R.eval z) := by
  rw [Polynomial.eval_eq_sum_range]
  refine hasSum_sum_of_ne_finset_zero fun n hn => ?_
  have hdeg : R.natDegree < n := by
    simp only [Finset.mem_range, not_lt] at hn
    omega
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt hdeg, zero_mul]

theorem mk_mul_coe_eq_coe_of_forall_hasSum (N : ℕ) (hN : 1 < N) (c : ℤ × ℤ → ℂ)
    (hc : ∀ p : ℤ × ℤ, ¬ (0 ≤ p.2 ∧ p.2 ≤ p.1) → c p = 0) (Φ : ℂ → ℂ) (σ : ℝ) (Q R : Polynomial ℂ)
    (hsum : ∀ t : ℂ, σ < t.re → HasSum (fun p : ℤ × ℤ => c p * ((N : ℂ) ^ (-t)) ^ (p.1 + p.2).toNat) (Φ t))
    (hQR : ∀ t : ℂ, σ < t.re → Φ t * Q.eval ((N : ℂ) ^ (-t)) = R.eval ((N : ℂ) ^ (-t))) :
    PowerSeries.mk (fun n : ℕ => ∑ k ∈ Finset.range (n / 2 + 1), c ((n : ℤ) - k, (k : ℤ))) * (Q : PowerSeries ℂ) =
      (R : PowerSeries ℂ) := by
  set F : ℕ → ℂ := fun n : ℕ => ∑ k ∈ Finset.range (n / 2 + 1), c ((n : ℤ) - k, (k : ℤ)) with hF
  have hN' : (1 : ℝ) < N := by exact_mod_cast hN
  have hr : (0 : ℝ) < (N : ℝ) ^ (-σ) := Real.rpow_pos_of_pos (by linarith) _

  have hdisc : ∀ z : ℂ, z ≠ 0 → ‖z‖ < (N : ℝ) ^ (-σ) →
      ∃ S : ℂ, HasSum (fun n : ℕ => F n * z ^ n) S ∧ S * Q.eval z = R.eval z := by
    intro z hz hzr
    obtain ⟨t, ht, htz⟩ := exists_re_lt_and_cpow_neg_eq hN' σ hz hzr
    rw [Complex.ofReal_natCast] at htz
    refine ⟨Φ t, ?_, ?_⟩
    · have h6 := hasSum_cone_coeff_mul_pow c hc _ _ (hsum t ht)
      rw [htz] at h6
      exact h6
    · have h := hQR t ht
      rw [htz] at h
      exact h

  have hF0 : F 0 * Q.eval 0 = R.eval 0 := by
    refine PuncturedDisc.coeff_zero_mul_eval_zero_eq_eval_zero_of_forall_ne_zero F Q R hr ?_ ?_
    · intro z hz hzr
      obtain ⟨S, hS, -⟩ := hdisc z hz hzr
      exact hS.summable
    · intro z hz hzr
      obtain ⟨S, hS, hSQ⟩ := hdisc z hz hzr
      rw [hS.tsum_eq]
      exact hSQ

  have key : (fun n : ℕ => PowerSeries.coeff n (PowerSeries.mk F * (Q : PowerSeries ℂ))) = fun n : ℕ => R.coeff n := by
    refine TwoRowProduct.eq_of_forall_hasSum_eq _ _ (fun z => R.eval z) hr ?_ fun z _ => hasSum_coeff_mul_pow_eval R z
    intro z hz
    by_cases h0 : z = 0
    · subst h0
      have h1 : HasSum (fun n : ℕ => PowerSeries.coeff n (PowerSeries.mk F * (Q : PowerSeries ℂ)) * (0 : ℂ) ^ n)
          (PowerSeries.coeff 0 (PowerSeries.mk F * (Q : PowerSeries ℂ)) * (0 : ℂ) ^ 0) :=
        hasSum_single 0 fun n hn => by rw [zero_pow hn, mul_zero]
      convert h1 using 1
      all_goals try rfl
      rw [pow_zero, mul_one, PowerSeries.coeff_mul, Finset.Nat.antidiagonal_zero, Finset.sum_singleton,
        PowerSeries.coeff_mk, Polynomial.coeff_coe, Polynomial.coeff_zero_eq_eval_zero]
      exact hF0.symm
    · obtain ⟨S, hS, hSQ⟩ := hdisc z h0 hz
      have h1 := hasSum_coeff_mk_mul_coe_mul_pow F Q z hS.summable
      rw [hS.tsum_eq, hSQ] at h1
      exact h1
  ext n
  rw [Polynomial.coeff_coe]
  exact congrFun key n

end LanglandsTunnell.CubicInduction.ClosedForm

end ClosedFormCore

section TorusValueIdentities

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "CubicInduction.embedMat2 CubicInduction.iotaGL CubicInduction.coe_iotaGL TateLocal.modulus CubicInduction.eq_zero_of_forall_sum_mul_pow_mul_heckeRecursionSeq_eq_zero TateLocal.psiLocal_eq_one_of_mem_integers TateLocal.modulus_adicCompletion_eq_nnnorm RankinSelberg.hasSum_cell_terms_rsLocalIntegral CubicInduction.exists_unipotent_localLevelOne_scalarPi_diagZ_torusFactor_of_ne_zero"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "embedMat2 iotaGL coe_iotaGL varpi eq_zero_of_forall_sum_mul_pow_mul_heckeRecursionSeq_eq_zero exists_unipotent_localLevelOne_scalarPi_diagZ_torusFactor_of_ne_zero"
namespace TorusValueKit
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

theorem hasSum_sub_shift (f : ℤ × ℤ → ℂ) (S : ℂ) (h : HasSum f S) (M : ℤ × ℤ) :
    HasSum (fun p : ℤ × ℤ => f (p - M)) S :=
  (Equiv.subRight M).hasSum_iff.2 h

theorem apply_mul_zpow_eq_zpow_mul {G : Type*} [Group G] (f : G → ℂ) (S : G) (om : ℂ) (hom : om ≠ 0)
    (hf : ∀ g : G, f (g * S) = om * f g) (g : G) (k : ℤ) : f (g * S ^ k) = om ^ k * f g := by
  induction k using Int.induction_on with
  | zero => simp only [zpow_zero, mul_one, one_mul]
  | succ k ih =>
    rw [zpow_add_one, ← mul_assoc, hf, ih, zpow_add_one₀ hom]
    ring
  | pred k ih =>
    have h₀ : g * S ^ (-(k : ℤ) - 1) * S = g * S ^ (-(k : ℤ)) := by
      rw [mul_assoc, zpow_sub_one, inv_mul_cancel_right]
    have h₁ := hf (g * S ^ (-(k : ℤ) - 1))
    rw [h₀, ih] at h₁
    have h₂ : f (g * S ^ (-(k : ℤ) - 1)) = om⁻¹ * (om ^ (-(k : ℤ)) * f g) := by
      rw [h₁, inv_mul_cancel_left₀ hom]
    rw [h₂, zpow_sub_one₀ hom]
    ring

theorem sum_mul_pow_mul_mul_pow_eq (c x₁ x₂ : ℂ) (m : ℕ) :
    ∑ i ∈ Finset.range (m + 1), (c * x₁) ^ i * (c * x₂) ^ (m - i) =
      c ^ m * ∑ i ∈ Finset.range (m + 1), x₁ ^ i * x₂ ^ (m - i) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have him : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hc : c ^ i * c ^ (m - i) = c ^ m := by rw [← pow_add, Nat.add_sub_of_le him]
  rw [← hc, mul_pow, mul_pow]
  ring

private theorem _root_.LanglandsTunnell.CubicInduction.TorusValueKit.natCast_cpow_half_mul_self (N : ℕ) (hN : 1 < N) :
    (N : ℂ) ^ (1 / 2 : ℂ) * (N : ℂ) ^ (1 / 2 : ℂ) = N := by
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  rw [← Complex.cpow_add _ _ hN0, show (1 / 2 : ℂ) + 1 / 2 = 1 by norm_num, Complex.cpow_one]

p2m_export "LanglandsTunnell.CubicInduction.TorusValueKit" "natCast_cpow_half_mul_self"

theorem coeff_quadratic_mul_mk (u₀ u₁ u₂ : ℂ) (h : ℕ → ℂ) :
    PowerSeries.coeff 0 ((PowerSeries.C u₀ + PowerSeries.C u₁ * PowerSeries.X +
        PowerSeries.C u₂ * PowerSeries.X ^ 2) * PowerSeries.mk h) = u₀ * h 0 ∧
      PowerSeries.coeff 1 ((PowerSeries.C u₀ + PowerSeries.C u₁ * PowerSeries.X +
        PowerSeries.C u₂ * PowerSeries.X ^ 2) * PowerSeries.mk h) = u₀ * h 1 + u₁ * h 0 ∧
      ∀ n : ℕ, PowerSeries.coeff (n + 2) ((PowerSeries.C u₀ + PowerSeries.C u₁ * PowerSeries.X +
        PowerSeries.C u₂ * PowerSeries.X ^ 2) * PowerSeries.mk h) =
          u₀ * h (n + 2) + u₁ * h (n + 1) + u₂ * h n := by
  have key : ∀ n : ℕ, PowerSeries.coeff n ((PowerSeries.C u₀ + PowerSeries.C u₁ * PowerSeries.X +
      PowerSeries.C u₂ * PowerSeries.X ^ 2) * PowerSeries.mk h) =
        u₀ * h n + u₁ * (if 1 ≤ n then h (n - 1) else 0) + u₂ * (if 2 ≤ n then h (n - 2) else 0) := by
    intro n
    rw [show (PowerSeries.C u₀ + PowerSeries.C u₁ * PowerSeries.X + PowerSeries.C u₂ * PowerSeries.X ^ 2) *
        PowerSeries.mk h = PowerSeries.C u₀ * PowerSeries.mk h +
          PowerSeries.C u₁ * (PowerSeries.X ^ 1 * PowerSeries.mk h) +
            PowerSeries.C u₂ * (PowerSeries.X ^ 2 * PowerSeries.mk h) by ring]
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_mk]
  refine ⟨?_, ?_, fun n => ?_⟩
  · rw [key]
    simp
  · rw [key]
    simp
  · rw [key]
    simp [show n + 2 - 1 = n + 1 by omega]

theorem coeff_X_pow_mul_add_and_eq_zero (B : PowerSeries ℂ) (p : ℕ) :
    (∀ i : ℕ, PowerSeries.coeff (i + p) (PowerSeries.X ^ p * B) = PowerSeries.coeff i B) ∧
      ∀ i : ℕ, i < p → PowerSeries.coeff i (PowerSeries.X ^ p * B) = 0 := by
  refine ⟨fun i => PowerSeries.coeff_X_pow_mul B p i, fun i hi => ?_⟩
  rw [PowerSeries.coeff_X_pow_mul', if_neg (by omega)]

end LanglandsTunnell.CubicInduction.TorusValueKit

end TorusValueIdentities

section MassOfTheIdentityCell

section CosetCell

variable {G : Type*} [Group G]

open scoped Pointwise in

theorem cosetCell_eq_mul (H K : Subgroup G) :
    {g : G | ∃ n ∈ H, ∃ k ∈ K, g = n * k} = (H : Set G) * (K : Set G) := by
  ext g
  simp only [Set.mem_setOf_eq, Set.mem_mul, SetLike.mem_coe]
  constructor
  · rintro ⟨n, hn, k, hk, rfl⟩; exact ⟨n, hn, k, hk, rfl⟩
  · rintro ⟨n, hn, k, hk, rfl⟩; exact ⟨n, hn, k, hk, rfl⟩

open scoped Pointwise in
theorem cosetCell_isOpen [TopologicalSpace G] [ContinuousMul G] (H K : Subgroup G)
    (hK : IsOpen (K : Set G)) :
    IsOpen {g : G | ∃ n ∈ H, ∃ k ∈ K, g = n * k} := by
  rw [cosetCell_eq_mul]; exact hK.mul_left

theorem mem_cosetCell_mul_iff (H K : Subgroup G) {h : G} (hh : h ∈ H) (g : G) :
    h * g ∈ {g : G | ∃ n ∈ H, ∃ k ∈ K, g = n * k} ↔ g ∈ {g : G | ∃ n ∈ H, ∃ k ∈ K, g = n * k} := by
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨n, hn, k, hk, e⟩
    exact ⟨h⁻¹ * n, H.mul_mem (H.inv_mem hh) hn, k, hk, by rw [mul_assoc, ← e, inv_mul_cancel_left]⟩
  · rintro ⟨n, hn, k, hk, rfl⟩
    exact ⟨h * n, H.mul_mem hh hn, k, hk, (mul_assoc _ _ _).symm⟩

theorem preimage_out_mem_cosetCell (H K : Subgroup G) :
    (Quotient.mk'' : G → MulAction.orbitRel.Quotient H G) ⁻¹'
        {q : MulAction.orbitRel.Quotient H G | q.out ∈ {g : G | ∃ n ∈ H, ∃ k ∈ K, g = n * k}} =
      {g : G | ∃ n ∈ H, ∃ k ∈ K, g = n * k} := by
  ext g
  simp only [Set.mem_preimage, Set.mem_setOf_eq]

  have horb : (Quotient.mk'' g : MulAction.orbitRel.Quotient H G).out ∈ MulAction.orbit H g :=
    MulAction.orbitRel_apply.1 (Quotient.mk_out' g)
  obtain ⟨h, hhg⟩ := MulAction.mem_orbit_iff.1 horb
  have e : (Quotient.mk'' g : MulAction.orbitRel.Quotient H G).out = (h : G) * g := by
    rw [← hhg]; rfl
  rw [e]
  exact mem_cosetCell_mul_iff H K h.2 g

end CosetCell

section Mass

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

theorem measure_eq_mul_withDensity_cosetCell (μ : MeasureTheory.Measure G) [μ.IsMulLeftInvariant]
    [MeasureTheory.SFinite μ] (H : Subgroup G) (hH : IsClosed (H : Set G)) (μH : MeasureTheory.Measure H)
    [μH.IsHaarMeasure] [μH.IsMulRightInvariant] (K : Subgroup G) (hKo : IsOpen (K : Set G)) :
    μ (K : Set G) =
      μH (Subtype.val ⁻¹' (K : Set G)) *
        (μ.withDensity (HaarQuotient.density H μH)) {g : G | ∃ n ∈ H, ∃ k ∈ K, g = n * k} := by
  set cell : Set G := {g : G | ∃ n ∈ H, ∃ k ∈ K, g = n * k} with hcell
  set Sq : Set (MulAction.orbitRel.Quotient H G) := {q | q.out ∈ cell} with hSq
  have hcell_open : IsOpen cell := cosetCell_isOpen H K hKo
  have hpre : (Quotient.mk'' : G → MulAction.orbitRel.Quotient H G) ⁻¹' Sq = cell :=
    preimage_out_mem_cosetCell H K
  have hSq_meas : MeasurableSet Sq := by
    rw [measurableSet_quotient, hpre]; exact hcell_open.measurableSet
  have hKH_meas : MeasurableSet (Subtype.val ⁻¹' (K : Set G) : Set H) :=
    (hKo.preimage continuous_subtype_val).measurableSet

  have hf : Measurable ((K : Set G).indicator fun _ => (1 : ENNReal)) :=
    measurable_const.indicator hKo.measurableSet
  have hformula := HaarQuotient.lintegral_eq_lintegral_lintegral_mul_out μ H hH μH
    ((K : Set G).indicator fun _ => (1 : ENNReal)) hf
  rw [MeasureTheory.lintegral_indicator_const hKo.measurableSet, one_mul] at hformula

  have hinner : ∀ q : MulAction.orbitRel.Quotient H G,
      ∫⁻ x : H, (K : Set G).indicator (fun _ => (1 : ENNReal)) ((x : G) * q.out) ∂μH =
        Sq.indicator (fun _ => μH (Subtype.val ⁻¹' (K : Set G))) q := by
    intro q
    by_cases hq : q ∈ Sq
    · rw [Set.indicator_of_mem hq]
      obtain ⟨n, hn, k, hk, hout⟩ := hq
      have hpt : ∀ x : H, (K : Set G).indicator (fun _ => (1 : ENNReal)) ((x : G) * q.out) =
          (Subtype.val ⁻¹' (K : Set G) : Set H).indicator (fun _ => (1 : ENNReal)) (x * ⟨n, hn⟩) := by
        intro x
        have h1 : (x : G) * q.out ∈ (K : Set G) ↔ (x * ⟨n, hn⟩ : H) ∈ (Subtype.val ⁻¹' (K : Set G) : Set H) := by
          rw [Set.mem_preimage, hout, ← mul_assoc, Subgroup.coe_mul]
          exact K.mul_mem_cancel_right hk
        by_cases hm : (x : G) * q.out ∈ (K : Set G)
        · rw [Set.indicator_of_mem hm, Set.indicator_of_mem (h1.1 hm)]
        · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem (fun h => hm (h1.2 h))]
      simp_rw [hpt]
      rw [MeasureTheory.lintegral_mul_right_eq_self
        (fun y : H => (Subtype.val ⁻¹' (K : Set G) : Set H).indicator (fun _ => (1 : ENNReal)) y) (⟨n, hn⟩ : H),
        MeasureTheory.lintegral_indicator_const hKH_meas, one_mul]
    · rw [Set.indicator_of_notMem hq]
      have hzero : ∀ x : H, (K : Set G).indicator (fun _ => (1 : ENNReal)) ((x : G) * q.out) = 0 := by
        intro x
        apply Set.indicator_of_notMem
        intro hmem
        apply hq

        show q.out ∈ cell
        have : (x : G) * q.out ∈ cell := ⟨1, H.one_mem, (x : G) * q.out, hmem, (one_mul _).symm⟩
        exact (mem_cosetCell_mul_iff H K x.2 q.out).1 this
      simp_rw [hzero]
      exact MeasureTheory.lintegral_zero
  simp_rw [hinner] at hformula
  rw [MeasureTheory.lintegral_indicator_const hSq_meas, HaarQuotient.measure,
    MeasureTheory.Measure.map_apply measurable_quotient_mk'' hSq_meas, hpre] at hformula
  exact hformula

theorem withDensity_density_cosetCell_ne_zero_and_ne_top (μ : MeasureTheory.Measure G) [μ.IsHaarMeasure]
    (H : Subgroup G) (hH : IsClosed (H : Set G)) (μH : MeasureTheory.Measure H) [μH.IsHaarMeasure]
    [μH.IsMulRightInvariant] (K : Subgroup G) (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G)) :
    (μ.withDensity (HaarQuotient.density H μH)) {g : G | ∃ n ∈ H, ∃ k ∈ K, g = n * k} ≠ 0 ∧
      (μ.withDensity (HaarQuotient.density H μH)) {g : G | ∃ n ∈ H, ∃ k ∈ K, g = n * k} ≠ ⊤ := by
  have hμK := measure_eq_mul_withDensity_cosetCell μ H hH μH K hKo

  have hK0 : μ (K : Set G) ≠ 0 := (hKo.measure_pos μ ⟨1, K.one_mem⟩).ne'
  have hKtop : μ (K : Set G) ≠ ⊤ := hKc.measure_lt_top.ne

  have hc0 : μH (Subtype.val ⁻¹' (K : Set G)) ≠ 0 :=
    ((hKo.preimage continuous_subtype_val).measure_pos μH ⟨1, K.one_mem⟩).ne'
  constructor
  · intro h0
    rw [h0, mul_zero] at hμK
    exact hK0 hμK
  · intro htop
    rw [htop, ENNReal.mul_top hc0] at hμK
    exact hKtop hμK

theorem toReal_withDensity_density_cosetCell_ne_zero (μ : MeasureTheory.Measure G) [μ.IsHaarMeasure]
    (H : Subgroup G) (hH : IsClosed (H : Set G)) (μH : MeasureTheory.Measure H) [μH.IsHaarMeasure]
    [μH.IsMulRightInvariant] (K : Subgroup G) (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G)) :
    ((((μ.withDensity (HaarQuotient.density H μH)) {g : G | ∃ n ∈ H, ∃ k ∈ K, g = n * k}).toReal : ℝ) : ℂ) ≠ 0 := by
  obtain ⟨h0, htop⟩ := withDensity_density_cosetCell_ne_zero_and_ne_top μ H hH μH K hKo hKc
  exact_mod_cast ENNReal.toReal_ne_zero.2 ⟨h0, htop⟩

end Mass

end MassOfTheIdentityCell

section SphericalCellIdentities

namespace SphericalCellLemmas

section TorusPoints

variable {F : Type*} [Field F]

theorem scalarPi_zpow_coe (π : F) (hπ : π ≠ 0) (n : ℤ) :
    ((UnramifiedWhittaker.scalarPi π hπ ^ n : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![π ^ n, 0; 0, π ^ n] := by
  have hs : ((UnramifiedWhittaker.scalarPi π hπ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![π, 0; 0, π] := rfl
  have hsi : (((UnramifiedWhittaker.scalarPi π hπ)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![π⁻¹, 0; 0, π⁻¹] := by
    rw [Matrix.coe_units_inv, hs]
    refine Matrix.inv_eq_left_inv ?_
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hπ]
  induction n using Int.induction_on with
  | zero => simp [Matrix.one_fin_two]
  | succ k ih =>
    rw [zpow_add_one, Units.val_mul, ih, hs]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, zpow_add_one₀ hπ]
  | pred k ih =>
    rw [zpow_sub_one, Units.val_mul, ih, hsi]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, zpow_sub_one₀ hπ]

theorem diagZ_mul_scalarPi_zpow_coe (π : F) (hπ : π ≠ 0) (m n : ℤ) :
    ((UnramifiedWhittaker.diagZ π hπ m * UnramifiedWhittaker.scalarPi π hπ ^ n : GL (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) = !![π ^ m * π ^ n, 0; 0, π ^ n] := by
  have hd : ((UnramifiedWhittaker.diagZ π hπ m : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![π ^ m, 0; 0, 1] :=
    rfl
  rw [Units.val_mul, hd, scalarPi_zpow_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem iotaGL_diagZ_mul_scalarPi_zpow_coe (π : F) (hπ : π ≠ 0) (m n : ℤ) :
    ((LanglandsTunnell.CubicInduction.iotaGL
        (UnramifiedWhittaker.diagZ π hπ m * UnramifiedWhittaker.scalarPi π hπ ^ n) : GL (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) = Matrix.diagonal ![π ^ (m + n), π ^ n, 1] := by
  rw [LanglandsTunnell.CubicInduction.coe_iotaGL, diagZ_mul_scalarPi_zpow_coe, zpow_add₀ hπ]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [LanglandsTunnell.CubicInduction.embedMat2, Matrix.diagonal]

end TorusPoints

section Local

variable (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))

theorem psiLocal_eq_one_of_valued_le_one (x : v.adicCompletion ℚ) (hx : Valued.v x ≤ 1) :
    NumberField.StandardAddChar.psiLocal ℚ v x = 1 :=
  LanglandsTunnell.TateLocal.psiLocal_eq_one_of_mem_integers ℚ v x
    ((IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers (NumberField.RingOfIntegers ℚ) ℚ v).2 hx)

theorem valued_zpow_eq_exp_neg {π : v.adicCompletion ℚ} (hϖ : Valued.v π = WithZero.exp (-1 : ℤ)) (k : ℤ) :
    Valued.v (π ^ k) = WithZero.exp (-k) := by
  rw [map_zpow₀, hϖ, ← WithZero.exp_zsmul, smul_eq_mul, show k * (-1 : ℤ) = -k by ring]

theorem valued_lt_of_neg_or_neg {π : v.adicCompletion ℚ} (hϖ : Valued.v π = WithZero.exp (-1 : ℤ))
    {m n : ℤ} (h : m < 0 ∨ n < 0) :
    Valued.v ((![π ^ (m + n), π ^ n, 1] : Fin 3 → v.adicCompletion ℚ) 1) <
        Valued.v ((![π ^ (m + n), π ^ n, 1] : Fin 3 → v.adicCompletion ℚ) 0) ∨
      Valued.v ((![π ^ (m + n), π ^ n, 1] : Fin 3 → v.adicCompletion ℚ) 2) <
        Valued.v ((![π ^ (m + n), π ^ n, 1] : Fin 3 → v.adicCompletion ℚ) 1) := by
  show Valued.v (π ^ n) < Valued.v (π ^ (m + n)) ∨ Valued.v (1 : v.adicCompletion ℚ) < Valued.v (π ^ n)
  have h1 : Valued.v (1 : v.adicCompletion ℚ) = WithZero.exp (0 : ℤ) := by rw [map_one, WithZero.exp_zero]
  rw [valued_zpow_eq_exp_neg v hϖ, valued_zpow_eq_exp_neg v hϖ, h1]
  rcases h with hm | hn
  · exact Or.inl (WithZero.exp_lt_exp.2 (by omega))
  · exact Or.inr (WithZero.exp_lt_exp.2 (by omega))

theorem modulus_det_diagZ_mul_scalarPi_zpow {π : v.adicCompletion ℚ} (hπ : π ≠ 0)
    (hnorm : ‖π‖ = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹) (m n : ℤ) :
    (LanglandsTunnell.TateLocal.modulus
        ((Matrix.GeneralLinearGroup.det (UnramifiedWhittaker.diagZ π hπ m * UnramifiedWhittaker.scalarPi π hπ ^ n) :
          (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ) =
      ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(m + 2 * n)) := by
  have hN : ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ≠ 0 := by
    intro h0
    have hπ' : ‖π‖ ≠ 0 := norm_ne_zero_iff.2 hπ
    rw [hnorm, h0, inv_zero] at hπ'
    exact hπ' rfl
  have hdet : ((Matrix.GeneralLinearGroup.det
      (UnramifiedWhittaker.diagZ π hπ m * UnramifiedWhittaker.scalarPi π hπ ^ n) : (v.adicCompletion ℚ)ˣ) :
        v.adicCompletion ℚ) =
      Matrix.det ((UnramifiedWhittaker.diagZ π hπ m * UnramifiedWhittaker.scalarPi π hπ ^ n :
        GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) := rfl
  rw [hdet, diagZ_mul_scalarPi_zpow_coe, Matrix.det_fin_two_of, mul_zero, sub_zero,
    LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm ℚ v, coe_nnnorm]
  simp only [norm_mul, norm_zpow, hnorm, inv_zpow']
  rw [← zpow_add₀ hN, ← zpow_add₀ hN]
  congr 1
  ring

end Local

end SphericalCellLemmas

end SphericalCellIdentities

section CellInstanceLemmas

open IsDedekindDomain NumberField MeasureTheory

namespace CellInstances

section Generic

theorem secondCountableTopology_GL2_of_ring (A : Type*) [Ring A] [TopologicalSpace A]
    [SecondCountableTopology A] : SecondCountableTopology (GL (Fin 2) A) := by
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) A) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → A))
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) A)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact (Units.isEmbedding_embedProduct (M := Matrix (Fin 2) (Fin 2) A)).isInducing.secondCountableTopology

theorem isMulRightInvariant_of_comm {H : Type*} [Group H] [MeasurableSpace H] (μ : Measure H)
    [μ.IsMulLeftInvariant] (hcomm : ∀ a b : H, a * b = b * a) : μ.IsMulRightInvariant := by
  refine ⟨fun g => ?_⟩
  have : (fun h : H => h * g) = fun h : H => g * h := funext fun h => hcomm h g
  simp only [this]
  exact map_mul_left_eq_self μ g

end Generic

section Unipotent

variable {R : Type*} [CommRing R]

theorem coe_range_unipotentGL2Hom :
    ((AutomorphicForm.unipotentGL2Hom (R := R)).range : Set (GL (Fin 2) R)) =
      {g : GL (Fin 2) R | (g : Matrix (Fin 2) (Fin 2) R) 0 0 = 1 ∧
        (g : Matrix (Fin 2) (Fin 2) R) 1 0 = 0 ∧ (g : Matrix (Fin 2) (Fin 2) R) 1 1 = 1} := by
  ext g
  simp only [SetLike.mem_coe, MonoidHom.mem_range, Set.mem_setOf_eq]
  constructor
  · rintro ⟨x, rfl⟩
    simp [AutomorphicForm.unipotentGL2Hom]
  · rintro ⟨h00, h10, h11⟩
    refine ⟨Multiplicative.ofAdd ((g : Matrix (Fin 2) (Fin 2) R) 0 1), ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [AutomorphicForm.unipotentGL2Hom, h00, h10, h11]

theorem isClosed_range_unipotentGL2Hom [TopologicalSpace R] [T2Space R] :
    IsClosed ((AutomorphicForm.unipotentGL2Hom (R := R)).range : Set (GL (Fin 2) R)) := by
  rw [coe_range_unipotentGL2Hom]
  have hc : ∀ i j : Fin 2, Continuous fun g : GL (Fin 2) R => (g : Matrix (Fin 2) (Fin 2) R) i j :=
    fun i j => Units.continuous_val.matrix_elem i j
  exact (isClosed_eq (hc 0 0) continuous_const).inter
    ((isClosed_eq (hc 1 0) continuous_const).inter (isClosed_eq (hc 1 1) continuous_const))

theorem mul_comm_range_unipotentGL2Hom (a b : (AutomorphicForm.unipotentGL2Hom (R := R)).range) :
    a * b = b * a := by
  obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 a.2
  obtain ⟨y, hy⟩ := MonoidHom.mem_range.1 b.2
  apply Subtype.ext
  simp only [Subgroup.coe_mul]
  rw [← hx, ← hy, ← map_mul, ← map_mul, mul_comm]

end Unipotent

section Local

variable (v : HeightOneSpectrum (𝓞 ℚ))

theorem coe_localLevelOne_top :
    (AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ : Set (GL (Fin 2) (v.adicCompletion ℚ))) =
      AutomorphicForm.localIntegralSet ℚ v := by
  ext g
  rw [SetLike.mem_coe, AdelicDock.mem_localLevelOne_iff, AutomorphicForm.mem_localIntegralSet]
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨h₁.integral, h₂.integral⟩
  · rintro ⟨h₁, h₂⟩
    refine ⟨⟨h₁, ?_, ?_⟩, ⟨h₂, ?_, ?_⟩⟩ <;> rw [AdelicLevel.idealBound_top]
    · exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).1 (h₁ 1 0)
    · exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).1 (sub_mem (h₁ 1 1) (one_mem _))
    · exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).1 (h₂ 1 0)
    · exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).1 (sub_mem (h₂ 1 1) (one_mem _))

theorem isOpen_localLevelOne_top :
    IsOpen (AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ : Set (GL (Fin 2) (v.adicCompletion ℚ))) := by
  rw [coe_localLevelOne_top]
  exact AutomorphicForm.isOpen_localIntegralSet ℚ v

theorem isCompact_localLevelOne_top :
    IsCompact (AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ : Set (GL (Fin 2) (v.adicCompletion ℚ))) := by
  rw [coe_localLevelOne_top]
  exact AutomorphicForm.isCompact_localIntegralSet ℚ v

theorem secondCountableTopology_adicCompletion : SecondCountableTopology (v.adicCompletion ℚ) := by
  haveI : Countable (WithVal (v.valuation ℚ)) := (WithVal.equiv (v := v.valuation ℚ)).injective.countable
  infer_instance

theorem secondCountableTopology_GL2 : SecondCountableTopology (GL (Fin 2) (v.adicCompletion ℚ)) := by
  haveI := secondCountableTopology_adicCompletion v
  exact secondCountableTopology_GL2_of_ring _

end Local

end CellInstances

end CellInstanceLemmas

section CellModulusLemmas

open IsDedekindDomain NumberField

namespace CellModulus

variable (v : HeightOneSpectrum (𝓞 ℚ))

theorem coe_localLevelOne_top :
    (AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ : Set (GL (Fin 2) (v.adicCompletion ℚ))) =
      AutomorphicForm.localIntegralSet ℚ v := by
  ext g
  rw [SetLike.mem_coe, AdelicDock.mem_localLevelOne_iff, AutomorphicForm.mem_localIntegralSet]
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨h₁.integral, h₂.integral⟩
  · rintro ⟨h₁, h₂⟩
    refine ⟨⟨h₁, ?_, ?_⟩, ⟨h₂, ?_, ?_⟩⟩ <;> rw [AdelicLevel.idealBound_top]
    · exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).1 (h₁ 1 0)
    · exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).1 (sub_mem (h₁ 1 1) (one_mem _))
    · exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).1 (h₂ 1 0)
    · exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).1 (sub_mem (h₂ 1 1) (one_mem _))

theorem valued_det_eq_one_of_mem (k : GL (Fin 2) (v.adicCompletion ℚ))
    (hk : k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤) :
    Valued.v ((Matrix.GeneralLinearGroup.det k : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) = 1 := by
  have hk' : k ∈ AutomorphicForm.localIntegralSet ℚ v := by
    rw [← coe_localLevelOne_top v]
    exact hk
  obtain ⟨h₁, h₂⟩ := (AutomorphicForm.mem_localIntegralSet ℚ v).1 hk'
  have hdet : ∀ g : GL (Fin 2) (v.adicCompletion ℚ),
      (∀ i j, (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j ∈ v.adicCompletionIntegers ℚ) →
      Valued.v ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) ≤ 1 := by
    intro g hg
    change Valued.v (Matrix.det (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))) ≤ 1
    rw [Matrix.det_fin_two]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).1
      (sub_mem (mul_mem (hg 0 0) (hg 1 1)) (mul_mem (hg 0 1) (hg 1 0)))
  have hle : Valued.v ((Matrix.GeneralLinearGroup.det k : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) ≤ 1 :=
    hdet k h₁
  have hinv : Valued.v ((Matrix.GeneralLinearGroup.det k⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) ≤ 1 :=
    hdet k⁻¹ h₂
  rw [map_inv, Units.val_inv_eq_inv_val, map_inv₀] at hinv
  have hne : Valued.v ((Matrix.GeneralLinearGroup.det k : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) ≠ 0 :=
    (Valuation.ne_zero_iff _).2 (Units.ne_zero _)
  exact le_antisymm hle ((inv_le_one₀ (pos_iff_ne_zero.2 hne)).1 hinv)

theorem nnnorm_det_eq_one_of_mem (k : GL (Fin 2) (v.adicCompletion ℚ))
    (hk : k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤) :
    ‖((Matrix.GeneralLinearGroup.det k : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)‖₊ = 1 := by
  ext
  rw [coe_nnnorm, FinitePlace.norm_def, valued_det_eq_one_of_mem v k hk, map_one, NNReal.coe_one]

theorem modulus_det_mul_of_mem (k : GL (Fin 2) (v.adicCompletion ℚ))
    (hk : k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤) (g : GL (Fin 2) (v.adicCompletion ℚ)) :
    ((LanglandsTunnell.TateLocal.modulus
        ((Matrix.GeneralLinearGroup.det (g * k) : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)) : ℝ) =
      ((LanglandsTunnell.TateLocal.modulus
        ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)) : ℝ) := by
  rw [map_mul, Units.val_mul, LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm,
    LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm, nnnorm_mul, nnnorm_det_eq_one_of_mem v k hk,
    mul_one]

theorem modulus_det_unipotent_mul (n : GL (Fin 2) (v.adicCompletion ℚ))
    (hn : n ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range)
    (g : GL (Fin 2) (v.adicCompletion ℚ)) :
    ((LanglandsTunnell.TateLocal.modulus
        ((Matrix.GeneralLinearGroup.det (n * g) : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)) : ℝ) =
      ((LanglandsTunnell.TateLocal.modulus
        ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)) : ℝ) := by
  obtain ⟨x, rfl⟩ := hn
  have hdet : Matrix.GeneralLinearGroup.det (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ) x) = 1 := by
    ext
    show Matrix.det ((AutomorphicForm.unipotentGL2 x.toAdd : GL (Fin 2) (v.adicCompletion ℚ)) :
      Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) = 1
    rw [AutomorphicForm.unipotentGL2_coe, Matrix.det_fin_two_of]
    ring
  rw [map_mul, hdet, one_mul]

theorem unipotentGL2Hom_eq_unipotent (x : Multiplicative (v.adicCompletion ℚ)) :
    AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ) x = UnramifiedWhittaker.unipotent x.toAdd :=
  Units.ext rfl

end CellModulus

end CellModulusLemmas

section GenericExtraction

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "CubicInduction.embedMat2 CubicInduction.iotaGL CubicInduction.coe_iotaGL TateLocal.modulus CubicInduction.eq_zero_of_forall_sum_mul_pow_mul_heckeRecursionSeq_eq_zero TateLocal.psiLocal_eq_one_of_mem_integers TateLocal.modulus_adicCompletion_eq_nnnorm RankinSelberg.hasSum_cell_terms_rsLocalIntegral CubicInduction.exists_unipotent_localLevelOne_scalarPi_diagZ_torusFactor_of_ne_zero"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "embedMat2 iotaGL coe_iotaGL varpi eq_zero_of_forall_sum_mul_pow_mul_heckeRecursionSeq_eq_zero exists_unipotent_localLevelOne_scalarPi_diagZ_torusFactor_of_ne_zero"
namespace Extraction
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

open LanglandsTunnell.CubicInduction.TwoRowProduct LanglandsTunnell.CubicInduction.TorusValueKit LanglandsTunnell.CubicInduction.FormalReadOff

theorem heckeRecursionSeq_div_eq (N lam om : ℂ) (hN : N ≠ 0) (m : ℕ) :
    UnramifiedWhittaker.heckeRecursionSeq N lam (om / N) m =
      (N ^ m)⁻¹ * UnramifiedWhittaker.heckeRecursionSeq 1 lam om m := by
  induction m using Nat.twoStepInduction with
  | zero => simp [UnramifiedWhittaker.heckeRecursionSeq]
  | one => simp [UnramifiedWhittaker.heckeRecursionSeq, div_eq_inv_mul]
  | more m ih0 ih1 =>
    simp only [UnramifiedWhittaker.heckeRecursionSeq, ih0, ih1, pow_succ]
    field_simp

theorem torusFactor_eq (N : ℕ) (hN : 1 < N) (r x₁ x₂ : ℂ) (hr : r * r = N) (m : ℕ) :
    UnramifiedWhittaker.torusFactor (N : ℂ) (r * x₁ + r * x₂) (x₁ * x₂) (m : ℤ) =
      ((N : ℂ) ^ m)⁻¹ * (r ^ m * pairComplete x₁ x₂ m) := by
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hr0 : r ≠ 0 := fun h => hN0 (by rw [← hr, h, mul_zero])
  rw [UnramifiedWhittaker.torusFactor, if_pos (Int.natCast_nonneg m), Int.toNat_natCast,
    show x₁ * x₂ = (r * x₁) * (r * x₂) / (N : ℂ) by
      rw [← hr, show (r * x₁) * (r * x₂) = (x₁ * x₂) * (r * r) by ring, mul_div_assoc,
        div_self (mul_ne_zero hr0 hr0), mul_one],
    heckeRecursionSeq_div_eq _ _ _ hN0, ← pairComplete_eq_heckeRecursionSeq]
  congr 1
  unfold pairComplete
  exact sum_mul_pow_mul_mul_pow_eq r x₁ x₂ m

theorem cell_identity (N : ℕ) (hN : 1 < N) (r x₁ x₂ z D : ℂ) (hr : r * r = N) (hx : x₁ * x₂ ≠ 0)
    (hz : z ≠ 0) (m k : ℤ) (hm : 0 ≤ m) (M : ℕ) (hkM : 0 ≤ k + M) :
    (N : ℂ) ^ m * (D * ((x₁ * x₂) ^ k * UnramifiedWhittaker.torusFactor (N : ℂ) (r * x₁ + r * x₂) (x₁ * x₂) m)) *
        (r ^ (m + 2 * k) * z ^ (m + 2 * k)) * ((x₁ * x₂) ^ (M : ℤ) * z ^ (2 * M : ℤ)) =
      (x₁ * x₂) ^ (k + M).toNat * pairComplete x₁ x₂ m.toNat * (D * (N : ℂ) ^ (m + k)) *
        z ^ (m + 2 * k + 2 * M).toNat := by
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hr0 : r ≠ 0 := fun h => hN0 (by rw [← hr, h, mul_zero])
  have hx₁ : x₁ ≠ 0 := left_ne_zero_of_mul hx
  have hx₂ : x₂ ≠ 0 := right_ne_zero_of_mul hx
  obtain ⟨m', rfl⟩ : ∃ m' : ℕ, m = m' := ⟨m.toNat, (Int.toNat_of_nonneg hm).symm⟩
  obtain ⟨j, hj⟩ : ∃ j : ℕ, k + M = j := ⟨(k + M).toNat, (Int.toNat_of_nonneg hkM).symm⟩
  obtain rfl : k = (j : ℤ) - M := by omega
  rw [torusFactor_eq N hN r x₁ x₂ hr m', Int.toNat_natCast, show ((j : ℤ) - M + M).toNat = j by omega,
    show (m' : ℤ) + 2 * ((j : ℤ) - M) + 2 * M = ((m' + 2 * j : ℕ) : ℤ) by omega, Int.toNat_natCast]

  have e₁ : (x₁ * x₂) ^ ((j : ℤ) - M) = (x₁ * x₂) ^ j * ((x₁ * x₂) ^ M)⁻¹ := by
    rw [zpow_sub₀ hx, zpow_natCast, zpow_natCast, div_eq_mul_inv]
  have e₂ : r ^ ((m' : ℤ) + 2 * ((j : ℤ) - M)) = r ^ (m' + 2 * j) * (r ^ (2 * M))⁻¹ := by
    rw [show (m' : ℤ) + 2 * ((j : ℤ) - M) = ((m' + 2 * j : ℕ) : ℤ) - ((2 * M : ℕ) : ℤ) by omega,
      zpow_sub₀ hr0, zpow_natCast, zpow_natCast, div_eq_mul_inv]
  have e₃ : z ^ ((m' : ℤ) + 2 * ((j : ℤ) - M)) = z ^ (m' + 2 * j) * (z ^ (2 * M))⁻¹ := by
    rw [show (m' : ℤ) + 2 * ((j : ℤ) - M) = ((m' + 2 * j : ℕ) : ℤ) - ((2 * M : ℕ) : ℤ) by omega,
      zpow_sub₀ hz, zpow_natCast, zpow_natCast, div_eq_mul_inv]
  have e₄ : z ^ (2 * M : ℤ) = z ^ (2 * M) := by
    rw [show (2 * M : ℤ) = ((2 * M : ℕ) : ℤ) by omega, zpow_natCast]
  have e₅ : (N : ℂ) ^ ((m' : ℤ) + ((j : ℤ) - M)) = (N : ℂ) ^ (m' + j) * ((N : ℂ) ^ M)⁻¹ := by
    rw [show (m' : ℤ) + ((j : ℤ) - M) = ((m' + j : ℕ) : ℤ) - (M : ℤ) by omega, zpow_sub₀ hN0,
      zpow_natCast, zpow_natCast, div_eq_mul_inv]
  rw [e₁, e₂, e₃, e₄, e₅, zpow_natCast, zpow_natCast]

  rw [← hr]
  field_simp
  ring

noncomputable def cellArray (vol : ℂ) (N M : ℕ) (D : ℤ → ℤ → ℂ) (P : ℤ × ℤ) : ℂ :=
  vol * (N : ℂ) ^ (P.1 - M) * D (P.1 - P.2) (P.2 - M)

noncomputable def coneFamily (x₁ x₂ : ℂ) (V : ℤ × ℤ → ℂ) (P : ℤ × ℤ) : ℂ :=
  if 0 ≤ P.2 ∧ P.2 ≤ P.1 then (x₁ * x₂) ^ P.2.toNat * pairComplete x₁ x₂ (P.1 - P.2).toNat * V P else 0

theorem coneFamily_eq_zero (x₁ x₂ : ℂ) (V : ℤ × ℤ → ℂ) (P : ℤ × ℤ) (hP : ¬ (0 ≤ P.2 ∧ P.2 ≤ P.1)) :
    coneFamily x₁ x₂ V P = 0 := by
  rw [coneFamily, if_neg hP]

theorem coneFamily_apply (x₁ x₂ : ℂ) (V : ℤ × ℤ → ℂ) (n k : ℕ) (hk : k ≤ n / 2) :
    coneFamily x₁ x₂ V ((n : ℤ) - k, (k : ℤ)) =
      (x₁ * x₂) ^ k * pairComplete x₁ x₂ (n - 2 * k) * V ((n : ℤ) - k, (k : ℤ)) := by
  rw [coneFamily, if_pos ⟨Int.natCast_nonneg k, by omega⟩]
  simp only [Int.toNat_natCast]
  rw [show ((n : ℤ) - k - k).toNat = n - 2 * k by omega]

theorem hasSum_coneFamily {N : ℕ} (hN : 1 < N) {r z x₁ x₂ : ℂ} (hr : r * r = N) (hz : z ≠ 0)
    (hx : x₁ * x₂ ≠ 0) (M : ℕ) (vol : ℂ) (D W δ : ℤ → ℤ → ℂ)
    (hD : ∀ m k : ℤ, k + M < 0 → D m k = 0)
    (hW : ∀ m k : ℤ, W m k = (x₁ * x₂) ^ k * UnramifiedWhittaker.torusFactor (N : ℂ) (r * x₁ + r * x₂) (x₁ * x₂) m)
    (hδ : ∀ m k : ℤ, δ m k = r ^ (m + 2 * k) * z ^ (m + 2 * k)) {Ψ : ℂ}
    (hsum : HasSum (fun p : ℤ × ℤ =>
      vol * (N : ℂ) ^ (p.1 - p.2) * (D (p.1 - p.2) p.2 * W (p.1 - p.2) p.2) * δ (p.1 - p.2) p.2) Ψ) :
    HasSum (fun P : ℤ × ℤ => coneFamily x₁ x₂ (cellArray vol N M D) P * z ^ (P.1 + P.2).toNat)
      ((x₁ * x₂) ^ (M : ℤ) * z ^ (2 * M : ℤ) * Ψ) := by
  have h₁ := (hasSum_sub_shift _ _ hsum ((M : ℤ), (M : ℤ))).mul_left ((x₁ * x₂) ^ (M : ℤ) * z ^ (2 * M : ℤ))
  refine h₁.congr_fun fun P => ?_
  simp only [Prod.fst_sub, Prod.snd_sub]
  rw [hW, hδ, show P.1 - (M : ℤ) - (P.2 - M) = P.1 - P.2 by ring]
  by_cases hP : 0 ≤ P.2 ∧ P.2 ≤ P.1
  · have hci := cell_identity N hN r x₁ x₂ z (D (P.1 - P.2) (P.2 - M)) hr hx hz (P.1 - P.2) (P.2 - M) (by omega) M
      (by omega)
    rw [show P.2 - (M : ℤ) + M = P.2 by ring, show P.1 - P.2 + (P.2 - (M : ℤ)) = P.1 - M by ring,
      show P.1 - P.2 + 2 * (P.2 - (M : ℤ)) + 2 * M = P.1 + P.2 by ring] at hci
    rw [coneFamily, if_pos hP, cellArray]
    linear_combination (-vol) * hci
  · rw [coneFamily_eq_zero _ _ _ _ hP, zero_mul]
    rcases not_and_or.1 hP with h₂ | h₂
    · rw [hD _ _ (by omega)]
      ring
    · rw [UnramifiedWhittaker.torusFactor, if_neg (by omega)]
      ring

end LanglandsTunnell.CubicInduction.Extraction

end GenericExtraction

section ScalarIdentitiesOfTheAverage

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "CubicInduction.embedMat2 CubicInduction.iotaGL CubicInduction.coe_iotaGL TateLocal.modulus CubicInduction.eq_zero_of_forall_sum_mul_pow_mul_heckeRecursionSeq_eq_zero TateLocal.psiLocal_eq_one_of_mem_integers TateLocal.modulus_adicCompletion_eq_nnnorm RankinSelberg.hasSum_cell_terms_rsLocalIntegral CubicInduction.exists_unipotent_localLevelOne_scalarPi_diagZ_torusFactor_of_ne_zero"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "embedMat2 iotaGL coe_iotaGL varpi eq_zero_of_forall_sum_mul_pow_mul_heckeRecursionSeq_eq_zero exists_unipotent_localLevelOne_scalarPi_diagZ_torusFactor_of_ne_zero"
namespace AverageScalarLemmas
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

theorem natCast_cpow_half_mul_self (N : ℕ) (hN : 1 < N) :
    (N : ℂ) ^ (1 / 2 : ℂ) * (N : ℂ) ^ (1 / 2 : ℂ) = N := by
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  rw [← Complex.cpow_add _ _ hN0, show (1 / 2 : ℂ) + 1 / 2 = 1 by norm_num, Complex.cpow_one]

theorem cpow_half_mul_cpow_neg_add_half_mul_cpow_neg_one_sub (N : ℕ) (hN : 1 < N) (s : ℂ) :
    (N : ℂ) ^ (1 / 2 : ℂ) * (N : ℂ) ^ (-(s + 1 / 2)) * (N : ℂ) ^ (-(1 - s)) = (N : ℂ)⁻¹ := by
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  rw [← Complex.cpow_add _ _ hN0, ← Complex.cpow_add _ _ hN0,
    show (1 / 2 : ℂ) + -(s + 1 / 2) + -(1 - s) = -1 by ring, Complex.cpow_neg_one]

theorem cpow_neg_sub_half (N : ℕ) (hN : 1 < N) (t : ℂ) :
    (N : ℂ) ^ (-(t - 1 / 2)) = (N : ℂ) ^ (1 / 2 : ℂ) * (N : ℂ) ^ (-t) := by
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  rw [← Complex.cpow_add _ _ hN0]
  congr 1
  ring

theorem ofReal_natCast_zpow_neg_cpow (N : ℕ) (d : ℤ) (w : ℂ) :
    (((N : ℝ) ^ (-d) : ℝ) : ℂ) ^ w = ((N : ℂ) ^ (-w)) ^ d := by
  have hN' : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  rw [← Real.rpow_intCast, ← Complex.cpow_mul_ofReal_nonneg hN', Complex.ofReal_natCast, ← Complex.cpow_int_mul]
  congr 1
  push_cast
  ring

theorem ofReal_natCast_zpow_neg_cpow_sub_half (N : ℕ) (hN : 1 < N) (d : ℤ) (t : ℂ) :
    (((N : ℝ) ^ (-d) : ℝ) : ℂ) ^ (t - 1 / 2) = ((N : ℂ) ^ (1 / 2 : ℂ)) ^ d * ((N : ℂ) ^ (-t)) ^ d := by
  rw [ofReal_natCast_zpow_neg_cpow, cpow_neg_sub_half N hN, mul_zpow]

end LanglandsTunnell.CubicInduction.AverageScalarLemmas

end ScalarIdentitiesOfTheAverage

section NormOfUniformiser

namespace E4Norm

variable (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))

theorem norm_eq_inv_of_valued_eq_exp_neg_one {π : v.adicCompletion ℚ}
    (hϖ : Valued.v π = WithZero.exp (-1 : ℤ)) : ‖π‖ = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹ := by
  rw [NumberField.FinitePlace.norm_def, hϖ, WithZero.exp_eq_coe_ofAdd,
    WithZeroMulInt.toNNReal_neg_apply _ WithZero.coe_ne_zero, WithZero.unzero_coe, toAdd_ofAdd, zpow_neg_one]
  simp

theorem modulus_det_torus_point {π : v.adicCompletion ℚ} (hπ : π ≠ 0)
    (hϖ : Valued.v π = WithZero.exp (-1 : ℤ)) (m n : ℤ) :
    (LanglandsTunnell.TateLocal.modulus
        ((Matrix.GeneralLinearGroup.det (UnramifiedWhittaker.diagZ π hπ m * UnramifiedWhittaker.scalarPi π hπ ^ n) :
          (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ) =
      ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(m + 2 * n)) :=
  SphericalCellLemmas.modulus_det_diagZ_mul_scalarPi_zpow v hπ (norm_eq_inv_of_valued_eq_exp_neg_one v hϖ) m n

end E4Norm

end NormOfUniformiser

section Assembly

p2m_open "IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_RankinSelberg_forall_apply_diagZ_mul_scalarPi_pow_eq_ite_of_forall_rsLocalIntegral_spherical_eq_measure.LanglandsTunnell.CubicInduction LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal UnramifiedWhittaker"

open LanglandsTunnell.CubicInduction.TwoRowProduct LanglandsTunnell.CubicInduction.Extraction LanglandsTunnell.CubicInduction.TorusValueKit LanglandsTunnell.CubicInduction.AverageScalarLemmas

private theorem sum_pairComplete_mul_ite_eq (vol x₁ x₂ : ℂ) (n : ℕ) :
    ∑ k ∈ Finset.range (n / 2 + 1),
        (x₁ * x₂) ^ k * pairComplete x₁ x₂ (n - 2 * k) * (if n - k = 0 ∧ k = 0 then vol else 0) =
      if n = 0 then vol else 0 := by
  by_cases hn : n = 0
  · subst hn
    simp [pairComplete]
  · rw [if_neg hn]
    refine Finset.sum_eq_zero fun k hk => ?_
    have hk' : k ≤ n / 2 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [if_neg (by omega), mul_zero]

set_option maxHeartbeats 4000000 in
theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ))
    (ϖ : v.adicCompletionIntegers ℚ)
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    (f : GL (Fin 2) (v.adicCompletion ℚ) → ℂ)
    (hfψ : ∀ (x : v.adicCompletion ℚ) (g : GL (Fin 2) (v.adicCompletion ℚ)),
      f (unipotent x * g) = (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹ x * f g)
    (hfK : ∀ (k g : GL (Fin 2) (v.adicCompletion ℚ)),
      k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ → f (g * k) = f g)
    (hsupp : ∀ m n : ℤ, (n < 0 ∨ m < n) →
      f (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ (m - n) * scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n) = 0)
    (hid : ∀ (a₁ a₂ : ℂ) (ha : a₁ * a₂ ≠ 0)
        (W₂ : GL (Fin 2) (v.adicCompletion ℚ) → ℂ)
        (hW₂ψ : ∀ (x : v.adicCompletion ℚ) (g : GL (Fin 2) (v.adicCompletion ℚ)),
          W₂ (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ v x * W₂ g)
        (hW₂K : ∀ (k g : GL (Fin 2) (v.adicCompletion ℚ)),
          k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ → W₂ (g * k) = W₂ g)
        (hW₂1 : W₂ 1 = 1)
        (hW₂Z : ∀ g : GL (Fin 2) (v.adicCompletion ℚ),
          W₂ (g * scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) =
            a₁ * a₂ / (Ideal.absNorm v.asIdeal : ℂ) * W₂ g)
        (hW₂T : ∀ m : ℤ, W₂ (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ m) =
          torusFactor (Ideal.absNorm v.asIdeal : ℂ) (a₁ + a₂) (a₁ * a₂ / (Ideal.absNorm v.asIdeal : ℂ)) m),
        letI := localGLBorel ℚ v
        haveI := borelSpace_localGLBorel ℚ v
        ∀ (μ₂ : Measure (GL (Fin 2) (v.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
          (μN : Measure ↥(unipotentGL2Hom (R := v.adicCompletion ℚ)).range) [μN.IsHaarMeasure],
        ∃ σ₂ : ℝ,
          (∀ s : ℂ, σ₂ < s.re →
            Integrable
              (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
                (f g * W₂ g) *
                  ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) :
                      v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
              (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN))) ∧
          (∀ s : ℂ, σ₂ < s.re →
            RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN
                (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
                  (modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ))
                s f W₂ =
              (((μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN))
                  {g : GL (Fin 2) (v.adicCompletion ℚ) |
                    ∃ n ∈ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
                      ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, g = n * k}).toReal : ℂ))) :
    ∀ m n : ℤ, f (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ (m - n) * scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n) = if m = 0 ∧ n = 0 then 1 else 0 := by

  set N : ℕ := Ideal.absNorm v.asIdeal with hNdef
  have hN : 1 < N := NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  set r : ℂ := (N : ℂ) ^ (1 / 2 : ℂ) with hrdef
  have hr : r * r = N := AverageScalarLemmas.natCast_cpow_half_mul_self N hN
  have hr0 : r ≠ 0 := fun h => hN0 (by rw [← hr, h, mul_zero])

  set D : ℤ → ℤ → ℂ := fun d k => f (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ d * scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ k) with hDdef
  have hD : ∀ d k : ℤ, k + (0 : ℕ) < 0 → D d k = 0 := by
    intro d k hk
    have h := hsupp (d + k) k (Or.inl (by omega))
    rwa [show d + k - k = d by ring] at h

  letI := localGLBorel ℚ v
  haveI := borelSpace_localGLBorel ℚ v
  haveI : SecondCountableTopology (GL (Fin 2) (v.adicCompletion ℚ)) :=
    CellInstances.secondCountableTopology_GL2 v
  haveI : LocallyCompactSpace (GL (Fin 2) (v.adicCompletion ℚ)) := locallyCompactSpace_localGL ℚ v
  have hHc : IsClosed ((AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range :
      Set (GL (Fin 2) (v.adicCompletion ℚ))) :=
    CellInstances.isClosed_range_unipotentGL2Hom
  haveI : LocallyCompactSpace (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range :=
    hHc.locallyCompactSpace
  set μ₂ : Measure (GL (Fin 2) (v.adicCompletion ℚ)) := Measure.haar with hμ₂
  set μN : Measure (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range := Measure.haar with hμN
  haveI : μN.IsMulRightInvariant :=
    CellInstances.isMulRightInvariant_of_comm μN CellInstances.mul_comm_range_unipotentGL2Hom

  obtain ⟨vol, hvol_eq⟩ : ∃ vol : ℂ, vol =
      (((μ₂.withDensity
        (HaarQuotient.density (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN))
      {g : GL (Fin 2) (v.adicCompletion ℚ) |
        ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
          ∃ k ∈ AdelicDock.localLevelOne (NumberField.RingOfIntegers ℚ) ℚ v ⊤, g = n * k}).toReal : ℂ) := ⟨_, rfl⟩
  have hvol : vol ≠ 0 := by
    rw [hvol_eq]
    exact toReal_withDensity_density_cosetCell_ne_zero μ₂ _ hHc μN (AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤)
      (CellInstances.isOpen_localLevelOne_top v) (CellInstances.isCompact_localLevelOne_top v)

  set δf : GL (Fin 2) (v.adicCompletion ℚ) → ℝ := fun g =>
    (modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ) with hδf
  have hδN : ∀ n ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
      ∀ g : GL (Fin 2) (v.adicCompletion ℚ), δf (n * g) = δf g :=
    fun n hn g => CellModulus.modulus_det_unipotent_mul v n hn g
  have hδK : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤,
      ∀ g : GL (Fin 2) (v.adicCompletion ℚ), δf (g * k) = δf g :=
    fun k hk g => CellModulus.modulus_det_mul_of_mem v k hk g

  have hpairs : ∀ x₁ x₂ : ℂ, x₁ * x₂ ≠ 0 → ∀ n : ℕ,
      ∑ k ∈ Finset.range (n / 2 + 1), (x₁ * x₂) ^ k * pairComplete x₁ x₂ (n - 2 * k) *
          cellArray vol N 0 D (((n - k : ℕ) : ℤ), (k : ℤ)) =
      ∑ k ∈ Finset.range (n / 2 + 1), (x₁ * x₂) ^ k * pairComplete x₁ x₂ (n - 2 * k) *
          (if n - k = 0 ∧ k = 0 then vol else 0) := by
    intro x₁ x₂ hx n
    rw [sum_pairComplete_mul_ite_eq]

    set a₁ : ℂ := r * x₁ with ha₁
    set a₂ : ℂ := r * x₂ with ha₂
    have hx₁ : x₁ ≠ 0 := left_ne_zero_of_mul hx
    have hx₂ : x₂ ≠ 0 := right_ne_zero_of_mul hx
    have ha : a₁ * a₂ ≠ 0 := mul_ne_zero (mul_ne_zero hr0 hx₁) (mul_ne_zero hr0 hx₂)
    have hom : a₁ * a₂ / (N : ℂ) = x₁ * x₂ := by
      rw [div_eq_iff hN0, ← hr, ha₁, ha₂]; ring
    have hlam : a₁ + a₂ = r * x₁ + r * x₂ := by rw [ha₁, ha₂]
    have hz0 : a₁ * a₂ / (N : ℂ) ≠ 0 := by rw [hom]; exact hx
    obtain ⟨W₂, hW₂ψ, hW₂K, hW₂1, hW₂Z, hW₂T⟩ :=
      LanglandsTunnell.CubicInduction.exists_unipotent_localLevelOne_scalarPi_diagZ_torusFactor_of_ne_zero v
        (NumberField.StandardAddChar.psiLocal ℚ v) (SphericalCellLemmas.psiLocal_eq_one_of_valued_le_one v)
        hπ hϖ (a₁ * a₂ / (N : ℂ)) hz0 (N : ℂ) (a₁ + a₂) (a₁ * a₂ / (N : ℂ))
    obtain ⟨σ₂, hint, hval⟩ := hid a₁ a₂ ha W₂ hW₂ψ hW₂K hW₂1 hW₂Z hW₂T μ₂ μN

    have hNinv : ∀ n ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
        ∀ g : GL (Fin 2) (v.adicCompletion ℚ), f (n * g) * W₂ (n * g) = f g * W₂ g := by
      intro n hn g
      obtain ⟨y, rfl⟩ := MonoidHom.mem_range.1 hn
      rw [CellModulus.unipotentGL2Hom_eq_unipotent v, hfψ, hW₂ψ, AddChar.inv_apply]
      have h1 : NumberField.StandardAddChar.psiLocal ℚ v (-y.toAdd) * NumberField.StandardAddChar.psiLocal ℚ v y.toAdd = 1 := by
        rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
      linear_combination (f g * W₂ g) * h1
    have hKinv : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤,
        ∀ g : GL (Fin 2) (v.adicCompletion ℚ), f (g * k) * W₂ (g * k) = f g * W₂ g := by
      intro k hk g
      rw [hfK k g hk, hW₂K k g hk]

    have hc : ∀ p : ℤ × ℤ, ¬ (0 ≤ p.2 ∧ p.2 ≤ p.1) → coneFamily x₁ x₂ (cellArray vol N 0 D) p = 0 :=
      fun p hp => coneFamily_eq_zero _ _ _ p hp
    have hmk := ClosedForm.mk_mul_coe_eq_coe_of_forall_hasSum N hN (coneFamily x₁ x₂ (cellArray vol N 0 D)) hc
      (fun _ => vol) σ₂ 1 (Polynomial.C vol) ?_ ?_
    rotate_left
    ·
      intro s hs
      have hz : (N : ℂ) ^ (-s) ≠ 0 := by
        rw [Complex.cpow_def_of_ne_zero hN0]; exact Complex.exp_ne_zero _
      have h4 := LanglandsTunnell.RankinSelberg.hasSum_cell_terms_rsLocalIntegral v hπ hϖ μ₂ μN δf hδN hδK s f W₂
        hNinv hKinv (hint s hs)
      rw [hval s hs, ← hvol_eq] at h4
      have h5 := Extraction.hasSum_coneFamily hN hr hz hx 0 vol D
        (fun d k => W₂ (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ d * scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ k))
        (fun d k => ((δf (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ d * scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ k) : ℝ) : ℂ) ^ (s - 1 / 2)) hD ?_ ?_ (Ψ := vol) ?_
      · simpa using h5
      · intro d k
        show W₂ (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ d * scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ k) = _
        rw [apply_mul_zpow_eq_zpow_mul W₂ (scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) (a₁ * a₂ / (N : ℂ)) hz0 hW₂Z (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ d) k, hW₂T d,
          hom, hlam]
      · intro d k
        show ((δf (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ d * scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ k) : ℝ) : ℂ) ^ (s - 1 / 2) = _
        rw [hδf]
        show (((modulus ((Matrix.GeneralLinearGroup.det (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ d * scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ k) :
          (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ) : ℝ) : ℂ) ^ (s - 1 / 2) = _
        rw [E4Norm.modulus_det_torus_point v hπ hϖ d k, ofReal_natCast_zpow_neg_cpow_sub_half N hN (d + 2 * k) s]
      · refine h4.congr_fun fun p => ?_
        simp only [hNdef]
        ring
    · intro s hs
      simp

    have hcoef := congrArg (PowerSeries.coeff n) hmk
    simp only [Polynomial.coe_one, mul_one, Polynomial.coe_C, PowerSeries.coeff_mk, PowerSeries.coeff_C] at hcoef
    rw [← hcoef]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k ≤ n / 2 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [coneFamily_apply x₁ x₂ _ n k hk', Nat.cast_sub (by omega : k ≤ n)]

  have hcone := eq_on_cone_of_forall_sum_pairComplete_mul_eq
    (fun a b => cellArray vol N 0 D ((a : ℤ), (b : ℤ))) (fun a b => if a = 0 ∧ b = 0 then vol else 0) hpairs

  clear hpairs hid hfψ hfK
  intro m n
  by_cases hcn : n < 0 ∨ m < n
  · rw [hsupp m n hcn, if_neg (by omega)]
  · obtain ⟨b, rfl⟩ : ∃ b : ℕ, n = b := ⟨n.toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
    obtain ⟨a, rfl⟩ : ∃ a : ℕ, m = a := ⟨m.toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
    have hba : b ≤ a := by
      have h' : ((b : ℕ) : ℤ) ≤ a := by omega
      exact_mod_cast h'
    have hk := hcone (a + b) b (by omega)
    simp only [cellArray, Nat.add_sub_cancel, Nat.cast_zero, sub_zero] at hk
    have hNm : (N : ℂ) ^ (a : ℤ) ≠ 0 := zpow_ne_zero _ hN0
    change D ((a : ℤ) - b) b = _
    by_cases h00 : a = 0 ∧ b = 0
    · obtain ⟨rfl, rfl⟩ := h00
      rw [if_pos (by simp)] at hk
      rw [if_pos (by simp)]
      simp only [Nat.cast_zero, sub_zero, zpow_zero, mul_one] at hk ⊢
      have h2 : vol * D 0 0 = vol * 1 := by rw [mul_one]; exact hk
      exact mul_left_cancel₀ hvol h2
    · rw [if_neg h00] at hk
      rw [if_neg (by
        rintro ⟨ha, hb⟩
        exact h00 ⟨by exact_mod_cast ha, by exact_mod_cast hb⟩)]
      exact (mul_eq_zero.1 hk).resolve_left (mul_ne_zero hvol hNm)

end Assembly

end S_LanglandsTunnell_RankinSelberg_forall_apply_diagZ_mul_scalarPi_pow_eq_ite_of_forall_rsLocalIntegral_spherical_eq_measure
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_forall_apply_diagZ_mul_scalarPi_pow_eq_ite_of_forall_rsLocalIntegral_spherical_eq_measure (solution)
