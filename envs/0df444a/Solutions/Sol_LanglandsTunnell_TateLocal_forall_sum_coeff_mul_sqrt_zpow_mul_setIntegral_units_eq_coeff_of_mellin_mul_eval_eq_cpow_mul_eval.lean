-- Prove2me | solution 1 for LanglandsTunnell.TateLocal.forall_sum_coeff_mul_sqrt_zpow_mul_setIntegral_units_eq_coeff_of_mellin_mul_eval_eq_cpow_mul_eval
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/1bf38551-3632-5e02-9fab-e846ac31d9a4

import Mathlib
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_NumberField_AdelicLevel

import Theorems.Thm_LanglandsTunnell_TateLocal_hasSum_setIntegral_shell_comap_val_mulMeasure_and_modulus_eq_of_valued_eq
import Theorems.Thm_LanglandsTunnell_TateLocal_isHaarMeasure_comap_val_mulMeasure
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Theorems.Thm_LanglandsTunnell_TateLocal_addCharLevel_psiLocal_rat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_TateLocal_forall_sum_coeff_mul_sqrt_zpow_mul_setIntegral_units_eq_coeff_of_mellin_mul_eval_eq_cpow_mul_eval

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory LanglandsTunnell.TateLocal
open NumberField.AdelicLevel (diagOne)

open scoped ENNReal NNReal

noncomputable section

namespace DSJC

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => p.adicCompletion ℚ

theorem borelSpace_units :
    letI := localBorel ℚ p
    BorelSpace (F)ˣ := by
  letI := localBorel ℚ p
  refine ⟨?_⟩
  show MeasurableSpace.comap Units.val (borel F) = borel (F)ˣ
  rw [← borel_comap]
  congr 1
  exact (Units.isEmbedding_val₀ (G₀ := F)).eq_induced.symm

theorem secondCountableTopology_units : SecondCountableTopology (F)ˣ :=
  (Units.isEmbedding_val₀ (G₀ := F)).isInducing.secondCountableTopology

theorem locallyCompactSpace_units : LocallyCompactSpace (F)ˣ := by
  refine (⟨Units.isEmbedding_val₀, ?_⟩ : Topology.IsOpenEmbedding (Units.val : (F)ˣ → F)).locallyCompactSpace
  have : Set.range (Units.val : (F)ˣ → F) = {x | x ≠ 0} := by
    ext x
    simp only [Set.mem_range, Set.mem_setOf_eq]
    exact ⟨by rintro ⟨u, rfl⟩; exact u.ne_zero, fun hx => ⟨Units.mk0 x hx, rfl⟩⟩
  rw [this]; exact isOpen_ne

theorem isAddHaarMeasure_selfDualHaarAt :
    letI := localBorel ℚ p
    (selfDualHaarAt ℚ p).IsAddHaarMeasure := by
  letI := localBorel ℚ p
  haveI : BorelSpace F := borelSpace_localBorel ℚ p
  have : selfDualHaarAt ℚ p = Measure.addHaarMeasure (integersPositiveCompacts ℚ p) := by
    unfold selfDualHaarAt
    rw [LanglandsTunnell.TateLocal.addCharLevel_psiLocal_rat p]
    simp
  rw [this]; infer_instance

theorem isHaarMeasure_tau :
    letI := localBorel ℚ p
    (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)) : Measure (F)ˣ).IsHaarMeasure := by
  letI := localBorel ℚ p
  haveI : BorelSpace F := borelSpace_localBorel ℚ p
  haveI := isAddHaarMeasure_selfDualHaarAt p
  haveI := borelSpace_units p
  exact LanglandsTunnell.TateLocal.isHaarMeasure_comap_val_mulMeasure ℚ p (selfDualHaarAt ℚ p)

theorem cpow_ne_zero' (q : ℝ) (hq : 0 < q) (z : ℂ) : (q : ℂ) ^ z ≠ 0 := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hq.ne')]; exact Complex.exp_ne_zero _

theorem cpow_shell (q : ℝ) (hq : 0 < q) (j : ℤ) (s : ℂ) :
    (((q ^ (-j) : ℝ)) : ℂ) ^ (s - 1 / 2) = ((q : ℂ) ^ ((2 : ℂ)⁻¹)) ^ j * ((q : ℂ) ^ (-s)) ^ j := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hqj : 0 < q ^ (-j) := zpow_pos hq _
  have hqj0 : (((q ^ (-j) : ℝ)) : ℂ) ≠ 0 := by exact_mod_cast hqj.ne'
  have hlog1 : Complex.log (((q ^ (-j) : ℝ)) : ℂ) = ((((-j : ℤ) : ℝ) * Real.log q : ℝ) : ℂ) := by
    rw [← Complex.ofReal_log hqj.le, Real.log_zpow]
  have hlogq : Complex.log (q : ℂ) = ((Real.log q : ℝ) : ℂ) := (Complex.ofReal_log hq.le).symm
  rw [Complex.cpow_def_of_ne_zero hqj0, hlog1, ← Complex.cpow_int_mul, ← Complex.cpow_int_mul,
    Complex.cpow_def_of_ne_zero hq0, Complex.cpow_def_of_ne_zero hq0, hlogq, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem exists_eq_cpow_neg (q : ℝ) (hq : 1 < q) (σ₀ : ℝ) (z : ℂ) (hz : z ≠ 0) (hzR : ‖z‖ < q ^ (-σ₀)) :
    ∃ s : ℂ, σ₀ < s.re ∧ (q : ℂ) ^ (-s) = z := by
  have hq0 : 0 < q := one_pos.trans hq
  have hlogq : 0 < Real.log q := Real.log_pos hq
  refine ⟨-(Complex.log z) / (Real.log q : ℂ), ?_, ?_⟩
  · have hre : (-(Complex.log z) / (Real.log q : ℂ)).re = -Real.log ‖z‖ / Real.log q := by
      rw [Complex.div_ofReal_re, Complex.neg_re, Complex.log_re]
    rw [hre, lt_div_iff₀ hlogq]
    have h1 : Real.log ‖z‖ < -σ₀ * Real.log q := by
      have := Real.log_lt_log (norm_pos_iff.2 hz) hzR
      rwa [Real.log_rpow hq0] at this
    linarith
  · rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hq0.ne'), (Complex.ofReal_log hq0.le).symm]
    have hne : ((Real.log q : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hlogq.ne'
    rw [show ((Real.log q : ℝ) : ℂ) * -(-Complex.log z / (Real.log q : ℂ)) = Complex.log z by field_simp]
    exact Complex.exp_log hz

theorem coeff_eq_zero_of_hasSum_zero (d : ℕ → ℂ) (R : ℝ) (hR : 0 < R)
    (h : ∀ z : ℂ, z ≠ 0 → ‖z‖ < R → HasSum (fun n => d n * z ^ n) 0) : ∀ n, d n = 0 := by
  set P : FormalMultilinearSeries ℂ ℂ ℂ := FormalMultilinearSeries.ofScalars ℂ d with hP
  set f : ℂ → ℂ := fun z => if z = 0 then d 0 else 0 with hf
  have hcoeff : ∀ n, P.coeff n = d n := fun n => by rw [hP, FormalMultilinearSeries.coeff_ofScalars]
  have hfp : HasFPowerSeriesAt f P 0 := by
    rw [hasFPowerSeriesAt_iff]
    have hball : Metric.ball (0 : ℂ) R ∈ nhds (0 : ℂ) := Metric.ball_mem_nhds 0 hR
    refine Filter.mem_of_superset hball fun z hz => ?_
    rw [Metric.mem_ball, dist_zero_right] at hz
    simp only [Set.mem_setOf_eq, zero_add, hcoeff, smul_eq_mul]
    by_cases hz0 : z = 0
    · subst hz0
      have hf0' : f 0 = d 0 := by simp only [hf, if_true]
      rw [hf0']
      have : (fun n : ℕ => (0 : ℂ) ^ n * d n) = fun n => if n = 0 then d 0 else 0 := by
        funext n; cases n <;> simp
      rw [this]; exact hasSum_ite_eq 0 (d 0)
    · have hfz' : f z = 0 := by simp only [hf, hz0, if_false]
      rw [hfz']
      have := h z hz0 hz
      simpa only [mul_comm] using this

  have hcont : ContinuousAt f 0 := hfp.continuousAt
  have hf0 : f 0 = 0 := by
    have h1 : Filter.Tendsto f (nhdsWithin 0 {(0 : ℂ)}ᶜ) (nhds (f 0)) := hcont.tendsto.mono_left nhdsWithin_le_nhds
    have h2 : Filter.Tendsto f (nhdsWithin 0 {(0 : ℂ)}ᶜ) (nhds 0) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with z hz
      have hz' : z ≠ 0 := Set.mem_compl_singleton_iff.1 hz
      simp only [hf, hz', if_false]
    exact tendsto_nhds_unique h1 h2
  have hd0 : d 0 = 0 := by simpa only [hf, if_true] using hf0
  have hfz : f = 0 := by
    funext z
    simp only [hf, Pi.zero_apply]
    split_ifs
    · exact hd0
    · rfl
  have hP0 : P = 0 := by
    rw [hfz] at hfp
    exact hfp.eq_zero
  intro n
  rw [← hcoeff, hP0]
  rfl

theorem sqrt_eq_cpow_half (q : ℝ) (hq : 0 ≤ q) : ((Real.sqrt q : ℝ) : ℂ) = (q : ℂ) ^ ((2 : ℂ)⁻¹) := by
  rw [Real.sqrt_eq_rpow, one_div, Complex.ofReal_cpow hq]
  congr 1
  push_cast
  ring

theorem laurent_coeff_zero (e : ℤ → ℂ) (L : ℤ) (he0 : ∀ n : ℤ, n < L → e n = 0)
    (R : ℝ) (hR : 0 < R)
    (he : ∀ z : ℂ, z ≠ 0 → ‖z‖ < R → HasSum (fun n : ℤ => e n * z ^ n) 0) :
    ∀ n : ℤ, e n = 0 := by
  classical
  set g : ℕ → ℤ := fun k => L + (k : ℤ) with hgdef
  have hg : Function.Injective g := fun a b hab => by
    have : (L + a : ℤ) = L + b := hab
    exact_mod_cast (add_left_cancel this)
  have hsupp : ∀ (z : ℂ), ∀ n ∉ Set.range g, e n * z ^ n = 0 := by
    intro z n hn
    have : n < L := by
      by_contra hge
      push Not at hge
      exact hn ⟨(n - L).toNat, by simp only [hgdef]; omega⟩
    rw [he0 n this, zero_mul]
  have hd : ∀ z : ℂ, z ≠ 0 → ‖z‖ < R → HasSum (fun k : ℕ => e (L + (k : ℤ)) * z ^ k) 0 := by
    intro z hz hzR
    have h1 : HasSum ((fun n : ℤ => e n * z ^ n) ∘ g) 0 := (hg.hasSum_iff (hsupp z)).2 (he z hz hzR)
    have h2 := h1.mul_left (z ^ (-L))
    rw [mul_zero] at h2
    convert h2 using 1 <;> try with_reducible_and_instances rfl
    funext k
    simp only [Function.comp_apply, hgdef]
    rw [zpow_add₀ hz, zpow_neg, zpow_natCast]
    field_simp
  have hcoef := coeff_eq_zero_of_hasSum_zero (fun k => e (L + (k : ℤ))) R hR hd
  intro n
  by_cases hLn : L ≤ n
  · have h3 : e (L + (((n - L).toNat : ℕ) : ℤ)) = 0 := hcoef _
    rwa [show L + (((n - L).toNat : ℕ) : ℤ) = n by rw [Int.toNat_of_nonneg (by omega)]; ring] at h3
  · exact he0 n (not_le.1 hLn)

theorem setIntegral_shell
    {ϖ : p.adicCompletionIntegers ℚ}
    (hπ : algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    (g : (F)ˣ → ℂ) (e : ℝ → ℂ) (n : ℤ) :
    letI := localBorel ℚ p
    ∫ y in {y : (F)ˣ | Valued.v (y : F) = WithZero.exp (-(n))}, g y * e ((modulus (y : F) : ℝ))
        ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) =
      (∫ u in {u : (F)ˣ | Valued.v (u : F) = 1},
          g ((Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) F ϖ) hπ) ^ n * u)
          ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) *
        e ((((Ideal.absNorm p.asIdeal : ℕ) : ℝ)) ^ (-n)) := by
  letI iF : MeasurableSpace F := localBorel ℚ p
  haveI : BorelSpace F := borelSpace_localBorel ℚ p
  haveI := borelSpace_units p
  haveI := secondCountableTopology_units p
  haveI := locallyCompactSpace_units p
  haveI := isHaarMeasure_tau p
  obtain ⟨hSmeas, huniq, hmass, hmod, hsum⟩ :=
    LanglandsTunnell.TateLocal.hasSum_setIntegral_shell_comap_val_mulMeasure_and_modulus_eq_of_valued_eq p
  set τ : Measure (F)ˣ := Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)) with hτ
  set ϖu : (F)ˣ := Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) F ϖ) hπ with hϖu
  have hvϖ : Valued.v (ϖu : F) = WithZero.exp (-1 : ℤ) := hϖ
  have hS0 : {u : (F)ˣ | Valued.v (u : F) = WithZero.exp (-((0 : ℤ)))} = {u : (F)ˣ | Valued.v (u : F) = 1} := by
    ext u; simp
  have hmp : MeasurePreserving (fun u : (F)ˣ => ϖu ^ n * u) τ τ := measurePreserving_mul_left τ (ϖu ^ n)
  have hemb : MeasurableEmbedding (fun u : (F)ˣ => ϖu ^ n * u) := (MeasurableEquiv.mulLeft (ϖu ^ n)).measurableEmbedding
  have hpre : (fun u : (F)ˣ => ϖu ^ n * u) ⁻¹' {y : (F)ˣ | Valued.v (y : F) = WithZero.exp (-(n))} =
      {u : (F)ˣ | Valued.v (u : F) = 1} := by
    ext u
    rw [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_setOf_eq, Units.val_mul, map_mul, Units.val_zpow_eq_zpow_val,
      map_zpow₀, hvϖ, ← WithZero.exp_zsmul, smul_eq_mul, mul_neg, mul_one]
    exact mul_eq_left₀ WithZero.exp_ne_zero
  have h1 := hmp.setIntegral_preimage_emb hemb (fun y : (F)ˣ => g y * e ((modulus (y : F) : ℝ)))
    {y : (F)ˣ | Valued.v (y : F) = WithZero.exp (-(n))}
  rw [hpre] at h1
  rw [← h1]
  have hshell_mem : ∀ u : (F)ˣ, u ∈ {u : (F)ˣ | Valued.v (u : F) = 1} →
      ϖu ^ n * u ∈ {y : (F)ˣ | Valued.v (y : F) = WithZero.exp (-(n))} := by
    intro u hu
    rw [Set.mem_setOf_eq] at hu
    rw [Set.mem_setOf_eq, Units.val_mul, map_mul, Units.val_zpow_eq_zpow_val, map_zpow₀, hvϖ, ← WithZero.exp_zsmul,
      smul_eq_mul, mul_neg, mul_one, hu, mul_one]
  have hmeas1 : MeasurableSet {u : (F)ˣ | Valued.v (u : F) = 1} := by rw [← hS0]; exact hSmeas 0
  have hpt : ∀ u ∈ {u : (F)ˣ | Valued.v (u : F) = 1},
      g (ϖu ^ n * u) * e ((modulus (((ϖu ^ n * u : (F)ˣ)) : F) : ℝ)) =
        g (ϖu ^ n * u) * e ((((Ideal.absNorm p.asIdeal : ℕ) : ℝ)) ^ (-n)) := by
    intro u hu
    rw [hmod n _ (hshell_mem u hu)]
  rw [setIntegral_congr_fun hmeas1 hpt, integral_mul_const]

end DSJC

open DSJC in

theorem dsJC
    (p : HeightOneSpectrum (𝓞 ℚ))
    {ϖ : p.adicCompletionIntegers ℚ}
    (hπ : algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    (f : (p.adicCompletion ℚ)ˣ → ℂ)
    (hfsupp : ∃ C : ℝ, ∀ y : (p.adicCompletion ℚ)ˣ, C < ‖(y : (p.adicCompletion ℚ))‖ → f y = 0)
    (P Q : Polynomial ℂ) (m : ℤ) (σ₀ : ℝ)
    (hmellin : letI := localBorel ℚ p
      ∀ s : ℂ, σ₀ < s.re →
        Integrable (fun y : (p.adicCompletion ℚ)ˣ => f y * ((modulus (y : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s - 1 / 2))
          (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) ∧
        (∫ y : (p.adicCompletion ℚ)ˣ, f y * ((modulus (y : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s - 1 / 2)
            ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) * Q.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
          (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) :
    letI := localBorel ℚ p
    ∀ k : ℤ,
      (∑ j ∈ Finset.range (Q.natDegree + 1),
          Q.coeff j * ((Real.sqrt (Ideal.absNorm p.asIdeal : ℝ) : ℝ) : ℂ) ^ (k - (j : ℤ)) *
            ∫ u in {u : (p.adicCompletion ℚ)ˣ | Valued.v (u : (p.adicCompletion ℚ)) = 1},
              f ((Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ) ^ (k - (j : ℤ)) * u)
              ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) =
        (if 0 ≤ k + m then P.coeff (k + m).toNat else 0) := by
  classical
  letI iF : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
  haveI : BorelSpace (p.adicCompletion ℚ) := borelSpace_localBorel ℚ p
  haveI := borelSpace_units p
  obtain ⟨hSmeas, huniq, hmass, hmod, hsum⟩ :=
    LanglandsTunnell.TateLocal.hasSum_setIntegral_shell_comap_val_mulMeasure_and_modulus_eq_of_valued_eq p
  set τ : Measure (p.adicCompletion ℚ)ˣ := Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)) with hτ
  set ϖu : (p.adicCompletion ℚ)ˣ := Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ with hϖu
  have hvϖ : Valued.v (ϖu : p.adicCompletion ℚ) = WithZero.exp (-1 : ℤ) := hϖ

  set q : ℝ := ((Ideal.absNorm p.asIdeal : ℕ) : ℝ) with hq
  have hq1 : 1 < q := by
    have := NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal p
    rw [hq]
    have h' : (1 : ℝ) < ((Ideal.absNorm p.asIdeal : ℝ≥0) : ℝ) := by exact_mod_cast this
    simpa using h'
  have hq0 : 0 < q := one_pos.trans hq1
  have hqC : ((Ideal.absNorm p.asIdeal : ℂ)) = (q : ℂ) := by rw [hq]; push_cast; rfl

  set J : ℤ → ℂ := fun n => ∫ u in {u : (p.adicCompletion ℚ)ˣ | Valued.v (u : (p.adicCompletion ℚ)) = 1},
      f (ϖu ^ n * u) ∂τ with hJ

  obtain ⟨C, hC⟩ := hfsupp
  obtain ⟨M, hM⟩ := pow_unbounded_of_one_lt C hq1
  have hS0 : {u : (p.adicCompletion ℚ)ˣ | Valued.v (u : p.adicCompletion ℚ) = WithZero.exp (-((0 : ℤ)))} =
      {u : (p.adicCompletion ℚ)ˣ | Valued.v (u : p.adicCompletion ℚ) = 1} := by
    ext u; simp
  have hmeas1 : MeasurableSet {u : (p.adicCompletion ℚ)ˣ | Valued.v (u : p.adicCompletion ℚ) = 1} := by
    rw [← hS0]; exact hSmeas 0
  have hshell_mem : ∀ (n : ℤ) (u : (p.adicCompletion ℚ)ˣ), u ∈ {u : (p.adicCompletion ℚ)ˣ | Valued.v (u : p.adicCompletion ℚ) = 1} →
      ϖu ^ n * u ∈ {y : (p.adicCompletion ℚ)ˣ | Valued.v (y : p.adicCompletion ℚ) = WithZero.exp (-(n))} := by
    intro n u hu
    rw [Set.mem_setOf_eq] at hu
    rw [Set.mem_setOf_eq, Units.val_mul, map_mul, Units.val_zpow_eq_zpow_val, map_zpow₀, hvϖ, ← WithZero.exp_zsmul,
      smul_eq_mul, mul_neg, mul_one, hu, mul_one]
  have hJ0 : ∀ n : ℤ, n < -(M : ℤ) → J n = 0 := by
    intro n hn
    simp only [hJ]
    refine (setIntegral_congr_fun hmeas1 fun u hu => ?_).trans (integral_zero _ _)
    show f (ϖu ^ n * u) = 0
    apply hC
    have hnorm : ‖((ϖu ^ n * u : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ)‖ = q ^ (-n) := by
      have := hmod n _ (hshell_mem n u hu)
      rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm, coe_nnnorm] at this
      exact this
    rw [hnorm]
    calc C < q ^ M := hM
      _ = q ^ ((M : ℕ) : ℤ) := (zpow_natCast _ _).symm
      _ ≤ q ^ (-n) := zpow_le_zpow_right₀ hq1.le (by omega)

  set β : ℂ := ((Real.sqrt q : ℝ) : ℂ) with hβ
  have hβq : β = (q : ℂ) ^ ((2 : ℂ)⁻¹) := by rw [hβ]; exact sqrt_eq_cpow_half q hq0.le
  have hβ0 : β ≠ 0 := by rw [hβq]; exact cpow_ne_zero' q hq0 _

  set T : Finset ℤ := (Finset.range (P.natDegree + 1)).image (fun j : ℕ => (j : ℤ) - m) with hT
  set Pc : ℤ → ℂ := fun n => P.coeff (n + m).toNat with hPc
  have hRHS : ∀ X : ℂ, X ≠ 0 → X ^ (-m) * P.eval X = ∑ n ∈ T, Pc n * X ^ n := by
    intro X hX
    rw [Polynomial.eval_eq_sum_range, Finset.mul_sum, hT, Finset.sum_image (fun a _ b _ hab => by
      have : (a : ℤ) = b := by linarith
      exact_mod_cast this)]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hPc]
    rw [show (((j : ℤ) - m + m)).toNat = j by simp, zpow_sub₀ hX, zpow_natCast, zpow_neg, div_eq_mul_inv]
    ring
  have hsumT : ∀ z : ℂ, HasSum (fun n : ℤ => (if n ∈ T then Pc n else 0) * z ^ n) (∑ n ∈ T, Pc n * z ^ n) := by
    intro z
    have h1 : HasSum (fun n : ℤ => (if n ∈ T then Pc n else 0) * z ^ n) (∑ n ∈ T, (if n ∈ T then Pc n else 0) * z ^ n) :=
      hasSum_sum_of_ne_finset_zero (fun n hn => by simp [hn])
    have h2 : ∑ n ∈ T, (if n ∈ T then Pc n else 0) * z ^ n = ∑ n ∈ T, Pc n * z ^ n :=
      Finset.sum_congr rfl (fun n hn => by rw [if_pos hn])
    rwa [h2] at h1

  set A : ℤ → ℂ := fun k => ∑ j ∈ Finset.range (Q.natDegree + 1),
      Q.coeff j * β ^ (k - (j : ℤ)) * J (k - (j : ℤ)) with hA

  have hdisc : ∀ z : ℂ, z ≠ 0 → ‖z‖ < q ^ (-σ₀) →
      HasSum (fun k : ℤ => A k * z ^ k) (∑ n ∈ T, Pc n * z ^ n) := by
    intro z hz hzR
    obtain ⟨s, hs, hsz⟩ := exists_eq_cpow_neg q hq1 σ₀ z hz hzR
    obtain ⟨hint, hval⟩ := hmellin s hs
    have hHS := hsum _ hint
    rw [hqC, hsz] at hval
    have hm : (q : ℂ) ^ ((m : ℂ) * s) = z ^ (-m) := by
      rw [← hsz, ← Complex.cpow_int_mul]; congr 1; push_cast; ring
    rw [hm, hRHS z hz] at hval
    suffices key : ∀ I : ℂ,
        HasSum (fun n : ℤ =>
          ∫ y in {y : (p.adicCompletion ℚ)ˣ | Valued.v (y : p.adicCompletion ℚ) = WithZero.exp (-(n))},
            f y * ((modulus (y : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s - 1 / 2) ∂τ) I →
        I * Q.eval z = ∑ n ∈ T, Pc n * z ^ n →
        HasSum (fun k : ℤ => A k * z ^ k) (∑ n ∈ T, Pc n * z ^ n) from
      key _ hHS hval
    intro I hHS' hval'

    have hI' : HasSum (fun n : ℤ => J n * β ^ n * z ^ n) I := by
      convert hHS' using 1
      funext n
      rw [DSJC.setIntegral_shell p hπ hϖ f (fun r => ((r : ℝ) : ℂ) ^ (s - 1 / 2)) n]
      show J n * β ^ n * z ^ n = J n * ((((q ^ (-n) : ℝ)) : ℂ) ^ (s - 1 / 2))
      rw [cpow_shell q hq0 n s, hsz, ← hβq]; ring

    have hQ : ∀ j : ℕ, HasSum (fun k : ℤ => Q.coeff j * β ^ (k - (j : ℤ)) * J (k - (j : ℤ)) * z ^ k)
        (Q.coeff j * z ^ j * I) := by
      intro j
      have h1 := hI'.mul_left (Q.coeff j * z ^ j)
      refine (Equiv.addRight (j : ℤ)).hasSum_iff.1 ?_
      convert h1 using 1 <;> try with_reducible_and_instances rfl
      funext n
      simp only [Function.comp_apply, Equiv.coe_addRight, add_sub_cancel_right]
      rw [zpow_add₀ hz, zpow_natCast]; ring
    have hQsum : HasSum (fun k : ℤ => ∑ j ∈ Finset.range (Q.natDegree + 1),
        Q.coeff j * β ^ (k - (j : ℤ)) * J (k - (j : ℤ)) * z ^ k)
        (∑ j ∈ Finset.range (Q.natDegree + 1), Q.coeff j * z ^ j * I) := hasSum_sum fun j _ => hQ j
    have hIQ : ∑ j ∈ Finset.range (Q.natDegree + 1), Q.coeff j * z ^ j * I = ∑ n ∈ T, Pc n * z ^ n := by
      rw [← hval', Polynomial.eval_eq_sum_range, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [← hIQ]
    convert hQsum using 1
    funext k
    simp only [hA, Finset.sum_mul]

  obtain ⟨L₀, hL₀⟩ := Finset.bddBelow T
  set e : ℤ → ℂ := fun k => A k - (if k ∈ T then Pc k else 0) with hedef
  have he0 : ∀ k : ℤ, k < min (-(M : ℤ)) L₀ → e k = 0 := by
    intro k hk
    have hk1 : k < -(M : ℤ) := lt_of_lt_of_le hk (min_le_left _ _)
    have hkT : k ∉ T := fun hkT => absurd (hL₀ hkT) (not_le.2 (lt_of_lt_of_le hk (min_le_right _ _)))
    have hAk : A k = 0 := by
      simp only [hA]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [hJ0 (k - (j : ℤ)) (by omega), mul_zero]
    simp only [hedef, hAk, hkT, if_false, sub_self]
  have he : ∀ z : ℂ, z ≠ 0 → ‖z‖ < q ^ (-σ₀) → HasSum (fun k : ℤ => e k * z ^ k) 0 := by
    intro z hz hzR
    have h1 := (hdisc z hz hzR).sub (hsumT z)
    rw [sub_self] at h1
    convert h1 using 1 <;> try with_reducible_and_instances rfl
    funext k; simp only [hedef]; ring
  have hzero := laurent_coeff_zero e _ he0 (q ^ (-σ₀)) (Real.rpow_pos_of_pos hq0 _) he

  intro k
  have hk : A k = (if k ∈ T then Pc k else 0) := by
    have := hzero k
    simp only [hedef] at this
    exact sub_eq_zero.1 this
  have hTk : (if k ∈ T then Pc k else 0) = (if 0 ≤ k + m then P.coeff (k + m).toNat else 0) := by
    by_cases hkm : 0 ≤ k + m
    · rw [if_pos hkm]
      by_cases hkT : k ∈ T
      · rw [if_pos hkT]
      · rw [if_neg hkT]
        have hdeg : P.natDegree < (k + m).toNat := by
          by_contra hle
          push Not at hle
          exact hkT (by
            rw [hT, Finset.mem_image]
            exact ⟨(k + m).toNat, Finset.mem_range.2 (by omega), by rw [Int.toNat_of_nonneg hkm]; ring⟩)
        exact (Polynomial.coeff_eq_zero_of_natDegree_lt hdeg).symm
    · rw [if_neg hkm, if_neg]
      intro hkT
      rw [hT, Finset.mem_image] at hkT
      obtain ⟨j, hj, hjk⟩ := hkT
      omega
  calc _ = A k := by simp only [hA, hJ]
    _ = _ := hk
    _ = _ := hTk

theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))
    {ϖ : p.adicCompletionIntegers ℚ}
    (hπ : algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    (f : (p.adicCompletion ℚ)ˣ → ℂ) (hf : IsLocallyConstant f)
    (hfsupp : ∃ C : ℝ, ∀ y : (p.adicCompletion ℚ)ˣ, C < ‖(y : (p.adicCompletion ℚ))‖ → f y = 0)
    (P Q : Polynomial ℂ) (m : ℤ) (σ₀ : ℝ)
    (hmellin : letI := localBorel ℚ p
      ∀ s : ℂ, σ₀ < s.re →
        Integrable (fun y : (p.adicCompletion ℚ)ˣ => f y * ((modulus (y : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s - 1 / 2))
          (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) ∧
        (∫ y : (p.adicCompletion ℚ)ˣ, f y * ((modulus (y : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s - 1 / 2)
            ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) * Q.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
          (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) :
    letI := localBorel ℚ p
    ∀ k : ℤ,
      (∑ j ∈ Finset.range (Q.natDegree + 1),
          Q.coeff j * ((Real.sqrt (Ideal.absNorm p.asIdeal : ℝ) : ℝ) : ℂ) ^ (k - (j : ℤ)) *
            ∫ u in {u : (p.adicCompletion ℚ)ˣ | Valued.v (u : (p.adicCompletion ℚ)) = 1},
              f ((Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ) ^ (k - (j : ℤ)) * u)
              ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) =
        (if 0 ≤ k + m then P.coeff (k + m).toNat else 0) :=
  dsJC p hπ hϖ f hfsupp P Q m σ₀ hmellin

end

end S_LanglandsTunnell_TateLocal_forall_sum_coeff_mul_sqrt_zpow_mul_setIntegral_units_eq_coeff_of_mellin_mul_eval_eq_cpow_mul_eval
end P2MW
export P2MW.S_LanglandsTunnell_TateLocal_forall_sum_coeff_mul_sqrt_zpow_mul_setIntegral_units_eq_coeff_of_mellin_mul_eval_eq_cpow_mul_eval (solution)
