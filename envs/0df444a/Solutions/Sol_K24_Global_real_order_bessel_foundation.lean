-- Prove2me | solution 1 for K24.Global.real_order_bessel_foundation
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T20:02:42.921187+00:00
-- url     : https://prove2.me/submissions/fa438d8e-f66d-42e9-84e0-aeaa8cab0dcd

import Definitions.Def_K24GlobalStatement
set_option autoImplicit false
set_option maxSynthPendingDepth 16
noncomputable section
open MeasureTheory TemperedDistribution FourierTransform Filter
open scoped NNReal ENNReal SchwartzMap Topology

/- Inlined BesselComplete; source hash recorded in PROVENANCE.json. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 16
noncomputable section
open MeasureTheory TemperedDistribution Filter
open scoped NNReal ENNReal SchwartzMap Topology

namespace K24.Global

theorem besselRepresentative_add {s : ℝ} {T U : LocalDistribution}
    (hT : BesselMem s T) (hU : BesselMem s U) :
    besselRepresentative (hT.add hU) = besselRepresentative hT + besselRepresentative hU := by
  apply besselRepresentative_unique
  rw [map_add, besselRepresentative_spec hT, besselRepresentative_spec hU]
  simp only [← Lp.toTemperedDistributionCLM_apply, map_add]

theorem besselRepresentative_sub {s : ℝ} {T U : LocalDistribution}
    (hT : BesselMem s T) (hU : BesselMem s U) :
    besselRepresentative (hT.sub hU) = besselRepresentative hT - besselRepresentative hU := by
  apply besselRepresentative_unique
  rw [map_sub, besselRepresentative_spec hT, besselRepresentative_spec hU]
  simp only [← Lp.toTemperedDistributionCLM_apply, map_sub]

theorem besselMem_real_smul {s : ℝ} {T : LocalDistribution} (hT : BesselMem s T) (c : ℝ) :
    BesselMem s (c • T) := by
  exact ⟨c • besselRepresentative hT, by
    rw [ContinuousLinearMap.map_smul_of_tower, besselRepresentative_spec hT]
    simp only [← Lp.toTemperedDistributionCLM_apply, ContinuousLinearMap.map_smul_of_tower]⟩

theorem besselRepresentative_real_smul {s : ℝ} {T : LocalDistribution}
    (hT : BesselMem s T) (c : ℝ) :
    besselRepresentative (besselMem_real_smul hT c) = c • besselRepresentative hT := by
  apply besselRepresentative_unique
  rw [ContinuousLinearMap.map_smul_of_tower, besselRepresentative_spec hT]
  simp only [← Lp.toTemperedDistributionCLM_apply, ContinuousLinearMap.map_smul_of_tower]

theorem besselSobolevENN_sub_eq {s : ℝ} {T U : LocalDistribution}
    (hT : BesselMem s T) (hU : BesselMem s U) :
    besselSobolevENN s (T - U) =
      ENNReal.ofReal ‖besselRepresentative hT - besselRepresentative hU‖ := by
  rw [besselSobolevENN_of_mem (hT.sub hU), besselRepresentative_sub]

theorem besselSobolev_complete (s : ℝ) (f : ℕ → LocalDistribution)
    (hf : ∀ n, BesselMem s (f n))
    (hc : ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ i ≥ N, ∀ j ≥ N,
      besselSobolevENN s (f i - f j) < ENNReal.ofReal eps) :
    ∃ T, BesselMem s T ∧ ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ i ≥ N,
      besselSobolevENN s (f i - T) < ENNReal.ofReal eps := by
  have hC : CauchySeq (fun n => besselRepresentative (hf n)) := by
    apply Metric.cauchySeq_iff.mpr
    intro eps heps
    obtain ⟨N, hN⟩ := hc eps heps
    refine ⟨N, fun i hi j hj => ?_⟩
    apply (ENNReal.ofReal_lt_ofReal_iff heps).mp
    simpa only [dist_eq_norm, besselSobolevENN_sub_eq (hf i) (hf j)] using hN i hi j hj
  obtain ⟨v, hv⟩ := cauchySeq_tendsto_of_complete hC
  let T : LocalDistribution := besselPotential SobolevModel ℂ (-s) (v : LocalDistribution)
  have hTrep : besselPotential SobolevModel ℂ s T = (v : LocalDistribution) := by
    simp [T]
  have hT : BesselMem s T := ⟨v, hTrep⟩
  refine ⟨T, hT, fun eps heps => ?_⟩
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hv) eps heps
  refine ⟨N, fun i hi => ?_⟩
  rw [besselSobolevENN_sub_eq (hf i) hT, besselRepresentative_unique hT v hTrep]
  apply (ENNReal.ofReal_lt_ofReal_iff heps).mpr
  simpa only [dist_eq_norm] using hN i hi

theorem besselSobolev_banach_proof (s : ℝ) :
    SectionBanachSpace {T : LocalDistribution | BesselMem s T} (besselSobolevENN s) where
  zero_mem := memSobolev_fun_zero SobolevModel ℂ s 2
  add_mem T hT U hU := hT.add hU
  smul_mem c T hT := besselMem_real_smul hT c
  finite T hT := (besselSobolevENN_lt_top_iff s T).mpr hT
  zero_norm := besselSobolevENN_zero s
  definite T hT hn := by
    have hz : besselRepresentative hT = 0 := by
      apply norm_eq_zero.mp
      apply le_antisymm _ (norm_nonneg _)
      simpa only [besselSobolevENN_of_mem hT, ENNReal.ofReal_eq_zero] using hn
    have hd := besselRepresentative_spec hT
    rw [hz] at hd
    have hback := congrArg (besselPotential SobolevModel ℂ (-s)) hd
    simpa only [besselPotential_besselPotential_apply, add_neg_cancel, besselPotential_zero,
      ContinuousLinearMap.id_apply, ← Lp.toTemperedDistributionCLM_apply, map_zero] using hback
  triangle T hT U hU := by
    rw [besselSobolevENN_of_mem (hT.add hU), besselRepresentative_add hT hU,
      besselSobolevENN_of_mem hT, besselSobolevENN_of_mem hU,
      ← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (norm_add_le _ _)
  homogeneous c T hT := by
    rw [besselSobolevENN_of_mem (besselMem_real_smul hT c), besselRepresentative_real_smul,
      norm_smul, Real.norm_eq_abs, ENNReal.ofReal_mul (abs_nonneg c), besselSobolevENN_of_mem hT]
  complete := besselSobolev_complete s

end K24.Global

/- Inlined FourierBound; source hash recorded in PROVENANCE.json. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 16
noncomputable section
open MeasureTheory TemperedDistribution FourierTransform Filter
open scoped NNReal ENNReal SchwartzMap Topology

namespace K24.Global

theorem bessel_inverse_weight_memL2 {s : ℝ} (hs : 2 < s) :
    MemLp (fun x : SobolevModel => (1 + ‖x‖ ^ 2) ^ (-s / 2)) 2 volume := by
  have hdim : (Module.finrank ℝ SobolevModel : ℝ) < 2 * s := by
    have hd : Module.finrank ℝ SobolevModel = 4 := by simp [SobolevModel]
    rw [hd]
    exact_mod_cast (by linarith : (4 : ℝ) < 2 * s)
  constructor
  · have hg : (fun x : SobolevModel => (1 + ‖x‖ ^ 2) ^ (-s / 2)).HasTemperateGrowth := by
      fun_prop
    exact hg.1.continuous.aestronglyMeasurable
  · rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)]
    suffices h : ∫⁻ a : SobolevModel, ENNReal.ofReal ‖(1 + ‖a‖ ^ 2) ^ (-s)‖ < ⊤ from by
      norm_cast
      simp_rw [ofReal_norm] at h
      simp_rw [← enorm_pow]
      convert h
      rw [← Real.rpow_mul_natCast (by positivity)]
      simp
    apply ((integrable_rpow_neg_one_add_norm_sq hdim).congr _).lintegral_lt_top
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_eq_self.mpr (by positivity)]
    congr
    ring

theorem bessel_fourier_L1_bound_proof (s : ℝ) (hs : 2 < s) :
    ∃ A : ℝ≥0, ∀ T : LocalDistribution, BesselMem s T →
    ∃ v : Lp ℂ 1 (volume : Measure SobolevModel),
      𝓕 T = (v : LocalDistribution) ∧
      ENNReal.ofReal ‖v‖ ≤ (A : ℝ≥0∞) * besselSobolevENN s T := by
  let w : SobolevModel → ℂ := fun x => Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (-s / 2))
  have hw : MemLp w 2 volume := (bessel_inverse_weight_memL2 hs).ofReal
  let W : LocalL2 := hw.toLp w
  refine ⟨‖W‖₊, fun T hT => ?_⟩
  let u : LocalL2 := 𝓕 (besselRepresentative hT)
  have hu : smulLeftCLM ℂ (fun x : SobolevModel => ((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ))
      (𝓕 T) = (u : LocalDistribution) := by
    rw [← fourier_besselPotential_eq_smulLeftCLM_fourier_apply,
      besselRepresentative_spec hT, Lp.fourier_toTemperedDistribution_eq]
  let v : Lp ℂ 1 (volume : Measure SobolevModel) := W • u
  refine ⟨v, ?_, ?_⟩
  · have hv : (v : LocalDistribution) = smulLeftCLM ℂ w (u : LocalDistribution) :=
      Lp.toTemperedDistribution_smul_eq (by fun_prop) hw u
    rw [hv, ← hu, smulLeftCLM_smulLeftCLM_apply (by fun_prop) (by fun_prop)]
    convert! (smulLeftCLM_const 1 (𝓕 T)).symm using 1
    · simp
    · congr
      ext x
      rw [Pi.mul_apply]
      dsimp [w]
      norm_cast
      rw [← Real.rpow_add (by positivity)]
      ring_nf
      simp
  · have hbound : ‖v‖ ≤ ‖W‖ * ‖besselRepresentative hT‖ := by
      calc
        ‖v‖ ≤ ‖W‖ * ‖u‖ := Lp.norm_smul_le W u
        _ = _ := by simp only [u, Lp.norm_fourier_eq]
    rw [besselSobolevENN_of_mem hT]
    calc
      ENNReal.ofReal ‖v‖ ≤ ENNReal.ofReal (‖W‖ * ‖besselRepresentative hT‖) :=
        ENNReal.ofReal_le_ofReal hbound
      _ = _ := by rw [ENNReal.ofReal_mul (norm_nonneg W), ofReal_norm]; rfl

end K24.Global

/- Inlined LocalInterface; source hash recorded in PROVENANCE.json. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 16
noncomputable section
open MeasureTheory TemperedDistribution FourierTransform Filter
open scoped NNReal ENNReal SchwartzMap Topology

namespace K24.Global

theorem complexifyLocal_sub (f g : SobolevModel → ℝ) :
    complexifyLocal (f - g) = complexifyLocal f - complexifyLocal g := by
  ext x; simp [complexifyLocal]

theorem localFunctionDistribution_sub (f g : SobolevModel → ℝ)
    (hf : MemLp (complexifyLocal f) 2 volume) (hg : MemLp (complexifyLocal g) 2 volume)
    (hfg : MemLp (complexifyLocal (f - g)) 2 volume) :
    localFunctionDistribution (f - g) hfg = localFunctionDistribution f hf - localFunctionDistribution g hg := by
  have heq : complexifyLocal (f - g) = complexifyLocal f - complexifyLocal g := by
    ext x; simp [complexifyLocal]
  unfold localFunctionDistribution
  simp only [← Lp.toTemperedDistributionCLM_apply, ← map_sub]
  congr 1
  apply Lp.ext
  filter_upwards [hfg.coeFn_toLp, hf.coeFn_toLp, hg.coeFn_toLp,
    Lp.coeFn_sub (hf.toLp (complexifyLocal f)) (hg.toLp (complexifyLocal g))] with x hfgx hfx hgx hsub
  rw [hfgx, hsub, Pi.sub_apply, hfx, hgx]
  exact congrFun heq x

theorem localSobolev_Cauchy_distribution_limit (s : ℝ) (f : ℕ → SobolevModel → ℝ)
    (hf : ∀ n, LocalSobolevMem s (f n))
    (hc : ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ i ≥ N, ∀ j ≥ N,
      localSobolevENN s (f i - f j) < ENNReal.ofReal eps) :
    ∃ (hL2 : ∀ n, MemLp (complexifyLocal (f n)) 2 volume) (T : LocalDistribution),
      BesselMem s T ∧ ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ i ≥ N,
        besselSobolevENN s (localFunctionDistribution (f i) (hL2 i) - T) < ENNReal.ofReal eps := by
  classical
  choose hL2 hB using hf
  refine ⟨hL2, ?_⟩
  apply besselSobolev_complete s _ hB
  intro eps heps
  obtain ⟨N, hN⟩ := hc eps heps
  refine ⟨N, fun i hi j hj => ?_⟩
  have hsub : MemLp (complexifyLocal (f i - f j)) 2 volume := by
    rw [complexifyLocal_sub]
    exact (hL2 i).sub (hL2 j)
  rw [← localFunctionDistribution_sub _ _ (hL2 i) (hL2 j) hsub]
  simpa only [localSobolevENN, dif_pos hsub] using hN i hi j hj

theorem localSobolev_fourier_L1_bound (s : ℝ) (hs : 2 < s) :
    ∃ A : ℝ≥0, ∀ f : SobolevModel → ℝ, LocalSobolevMem s f →
    ∃ (h : MemLp (complexifyLocal f) 2 volume) (v : Lp ℂ 1 (volume : Measure SobolevModel)),
      𝓕 (localFunctionDistribution f h) = (v : LocalDistribution) ∧
      ENNReal.ofReal ‖v‖ ≤ (A : ℝ≥0∞) * localSobolevENN s f := by
  obtain ⟨A, hA⟩ := bessel_fourier_L1_bound_proof s hs
  refine ⟨A, fun f ⟨h, hs⟩ => ?_⟩
  obtain ⟨v, hv, hb⟩ := hA _ hs
  refine ⟨h, v, hv, ?_⟩
  simpa only [localSobolevENN, dif_pos h] using hb

end K24.Global

namespace K24.Global

theorem real_order_bessel_foundation_proof :
    (∀ s : ℝ, SectionBanachSpace {T : LocalDistribution | BesselMem s T}
      (besselSobolevENN s)) ∧
    (∀ s : ℝ, 2 < s → ∃ A : ℝ≥0, ∀ T : LocalDistribution, BesselMem s T →
      ∃ v : Lp ℂ 1 (volume : Measure SobolevModel),
        𝓕 T = (v : LocalDistribution) ∧
        ENNReal.ofReal ‖v‖ ≤ (A : ℝ≥0∞) * besselSobolevENN s T) :=
  ⟨besselSobolev_banach_proof, bessel_fourier_L1_bound_proof⟩

end K24.Global

open K24.Global in
theorem solution :
    (∀ s : ℝ, SectionBanachSpace {T : LocalDistribution | BesselMem s T}
      (besselSobolevENN s)) ∧
    (∀ s : ℝ, 2 < s → ∃ A : ℝ≥0, ∀ T : LocalDistribution, BesselMem s T →
      ∃ v : Lp ℂ 1 (volume : Measure SobolevModel),
        𝓕 T = (v : LocalDistribution) ∧
        ENNReal.ofReal ‖v‖ ≤ (A : ℝ≥0∞) * besselSobolevENN s T) :=
  real_order_bessel_foundation_proof
