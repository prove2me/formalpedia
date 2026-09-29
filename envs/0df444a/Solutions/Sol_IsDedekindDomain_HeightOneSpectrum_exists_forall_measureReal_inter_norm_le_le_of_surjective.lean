-- Prove2me | solution 1 for IsDedekindDomain.HeightOneSpectrum.exists_forall_measureReal_inter_norm_le_le_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/51d65826-fc57-5aab-ba82-6b484428765e

import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Theorems.Thm_LanglandsTunnell_TateLocal_locallyIntegrable_log_modulus
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsDedekindDomain_HeightOneSpectrum_exists_forall_measureReal_inter_norm_le_le_of_surjective
p2m_attr_erase "simp" "NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

open MeasureTheory NumberField IsDedekindDomain NumberField.AdelicLevel
open scoped Pointwise

noncomputable section

namespace ThinSlab

variable (K : Type) [Field K] [NumberField K] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))

theorem map_mul_right [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)] (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure]
    (r : (v.adicCompletion K)) (hr : r ≠ 0) :
    Measure.map (fun z : (v.adicCompletion K) => z * r) μ = ((‖r‖₊)⁻¹ : NNReal) • μ := by
  ext A hA
  rw [Measure.map_apply (measurable_mul_const _) hA, Measure.smul_apply]
  have hset : (fun z : (v.adicCompletion K) => z * r) ⁻¹' A = ((Units.mk0 r hr)⁻¹ : (v.adicCompletion K)ˣ) • A := by
    ext x
    rw [Set.mem_preimage, Set.mem_smul_set_iff_inv_smul_mem, inv_inv, Units.smul_def, smul_eq_mul, mul_comm]; rfl
  rw [hset, ← distribHaarChar_mul, ← LanglandsTunnell.TateLocal.modulus_coe_units,
    LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm K v, Units.val_inv_eq_inv_val, nnnorm_inv]
  rfl

theorem oneDim [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)] (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure] :
    ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ R : ℝ, 0 < R → R ≤ 1 →
      IntegrableOn (fun x : (v.adicCompletion K) => 1 + |Real.log ‖x‖|) {x | ‖x‖ ≤ R} μ ∧
      ∫ x in {x : (v.adicCompletion K) | ‖x‖ ≤ R}, (1 + |Real.log ‖x‖|) ∂μ ≤ C₁ * R * (1 + |Real.log R|) := by

  have hball1 : {z : (v.adicCompletion K) | ‖z‖ ≤ 1} = (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
    ext z
    simp only [Set.mem_setOf_eq, SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers]
    exact Valued.toNormedField.norm_le_one_iff
  have hball1c : IsCompact {z : (v.adicCompletion K) | ‖z‖ ≤ 1} := by
    rw [hball1]; exact isCompact_iff_compactSpace.2 (NumberField.AdelicHaar.compactSpace_adicCompletionIntegers (𝓞 K) K v)
  have hball1m : MeasurableSet {z : (v.adicCompletion K) | ‖z‖ ≤ 1} := hball1c.isClosed.measurableSet
  have hB1fin : μ {z : (v.adicCompletion K) | ‖z‖ ≤ 1} ≠ ⊤ := hball1c.measure_lt_top.ne
  have hlogint : IntegrableOn (fun z : (v.adicCompletion K) => Real.log ‖z‖) {z | ‖z‖ ≤ 1} μ := by
    have hli := LanglandsTunnell.TateLocal.locallyIntegrable_log_modulus K v μ
    have heq : (fun y : (v.adicCompletion K) => Real.log (LanglandsTunnell.TateLocal.modulus y : ℝ)) = fun y => Real.log ‖y‖ := by
      funext y; rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm K v y, coe_nnnorm]
    rw [← heq]
    exact hli.integrableOn_isCompact hball1c
  set m₁ : ℝ := μ.real {z : (v.adicCompletion K) | ‖z‖ ≤ 1} with hm₁
  set Φ₁ : ℝ := ∫ z in {z : (v.adicCompletion K) | ‖z‖ ≤ 1}, |Real.log ‖z‖| ∂μ with hΦ₁
  have hm₁0 : 0 ≤ m₁ := by positivity
  have hΦ₁0 : 0 ≤ Φ₁ := setIntegral_nonneg hball1m fun z _ => abs_nonneg _
  clear_value m₁ Φ₁

  set ϖ : (v.adicCompletion K) := (uniformizerUnit K v : (v.adicCompletion K)) with hϖ
  have hϖ1 : ‖ϖ‖ < 1 := by
    refine Valued.toNormedField.norm_lt_one_iff.mpr ?_
    rw [hϖ, valued_uniformizerUnit, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  have hϖ0 : 0 < ‖ϖ‖ := norm_pos_iff.mpr (uniformizerUnit K v).ne_zero
  refine ⟨(m₁ * (1 + |Real.log ‖ϖ‖|) + Φ₁) * ‖ϖ‖⁻¹, by
    have : 0 ≤ m₁ * (1 + |Real.log ‖ϖ‖|) + Φ₁ := by positivity
    exact mul_nonneg this (inv_nonneg.mpr hϖ0.le), fun R hR0 hR1 => ?_⟩

  have hex : ∃ n : ℕ, ‖ϖ‖ ^ (n + 1) < R := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hR0 hϖ1
    exact ⟨n, lt_of_le_of_lt (pow_le_pow_of_le_one hϖ0.le hϖ1.le (Nat.le_succ n)) hn⟩
  classical
  let n := Nat.find hex
  have hn1 : ‖ϖ‖ ^ (n + 1) < R := Nat.find_spec hex
  have hn2 : R ≤ ‖ϖ‖ ^ n := by
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · rw [h0, pow_zero]; exact hR1
    · have := Nat.find_min hex (show n - 1 < n from Nat.sub_lt hpos one_pos)
      rw [not_lt, Nat.sub_add_cancel hpos] at this
      exact this
  set r : (v.adicCompletion K) := ϖ ^ n with hrdef
  have hrn : ‖r‖ = ‖ϖ‖ ^ n := by rw [hrdef, norm_pow]
  have hr0 : r ≠ 0 := by rw [hrdef]; exact pow_ne_zero _ (uniformizerUnit K v).ne_zero
  have hRr : R ≤ ‖r‖ := hrn ▸ hn2
  have hrR : ‖r‖ < R * ‖ϖ‖⁻¹ := by
    rw [hrn, lt_mul_inv_iff₀ hϖ0, ← pow_succ]; exact hn1
  have hr1 : ‖r‖ ≤ 1 := by rw [hrn]; exact pow_le_one₀ hϖ0.le hϖ1.le

  have hpre : (fun z : (v.adicCompletion K) => z * r) ⁻¹' {x : (v.adicCompletion K) | ‖x‖ ≤ ‖r‖} = {z : (v.adicCompletion K) | ‖z‖ ≤ 1} := by
    ext z
    simp only [Set.mem_preimage, Set.mem_setOf_eq, norm_mul]
    constructor
    · intro h; nlinarith [norm_pos_iff.mpr hr0]
    · intro h; nlinarith [norm_pos_iff.mpr hr0, norm_nonneg z]
  have hμeq : μ = (‖r‖₊ : NNReal) • Measure.map (fun z : (v.adicCompletion K) => z * r) μ := by
    rw [map_mul_right K v μ r hr0, smul_smul, mul_inv_cancel₀ (by rwa [ne_eq, nnnorm_eq_zero]), one_smul]
  have hballm : MeasurableSet {x : (v.adicCompletion K) | ‖x‖ ≤ ‖r‖} := (isClosed_le continuous_norm continuous_const).measurableSet
  have hsub : {x : (v.adicCompletion K) | ‖x‖ ≤ R} ⊆ {x : (v.adicCompletion K) | ‖x‖ ≤ ‖r‖} := fun x hx => le_trans hx hRr
  have hsub1 : {x : (v.adicCompletion K) | ‖x‖ ≤ ‖r‖} ⊆ {x : (v.adicCompletion K) | ‖x‖ ≤ 1} := fun x hx => le_trans hx hr1

  have hintBig : IntegrableOn (fun x : (v.adicCompletion K) => 1 + |Real.log ‖x‖|) {x | ‖x‖ ≤ ‖r‖} μ :=
(integrableOn_const (C := (1:ℝ)) (ne_top_of_le_ne_top hB1fin (measure_mono hsub1))).add (hlogint.mono_set hsub1).abs
  refine ⟨hintBig.mono_set hsub, ?_⟩

  have step : ∫ x in {x : (v.adicCompletion K) | ‖x‖ ≤ ‖r‖}, (1 + |Real.log ‖x‖|) ∂μ =
      ‖r‖ * ∫ z in {z : (v.adicCompletion K) | ‖z‖ ≤ 1}, (1 + |Real.log ‖z * r‖|) ∂μ := by
    let e : (v.adicCompletion K) ≃ᵐ (v.adicCompletion K) := MeasurableEquiv.mulRight₀ r hr0
    have hecoe : (⇑e : (v.adicCompletion K) → (v.adicCompletion K)) = fun z => z * r := rfl
    conv_lhs => rw [hμeq, Measure.restrict_smul, integral_smul_nnreal_measure, ← hecoe, setIntegral_map_equiv]
    simp only [hecoe, hpre, NNReal.smul_def, coe_nnnorm, smul_eq_mul]
  have hbound : ∀ z : (v.adicCompletion K), 1 + |Real.log ‖z * r‖| ≤ (1 + |Real.log R| + |Real.log ‖ϖ‖|) + |Real.log ‖z‖| := by
    intro z
    by_cases hz : z = 0
    · rw [hz, zero_mul, norm_zero, Real.log_zero, abs_zero]
      linarith [abs_nonneg (Real.log R), abs_nonneg (Real.log ‖ϖ‖)]
    · rw [norm_mul, Real.log_mul (norm_ne_zero_iff.mpr hz) (norm_ne_zero_iff.mpr hr0)]
      have hlr : |Real.log ‖r‖| ≤ |Real.log R| + |Real.log ‖ϖ‖| := by

        have h1 : Real.log R ≤ Real.log ‖r‖ := Real.log_le_log hR0 hRr
        have h2 : Real.log ‖r‖ ≤ 0 := Real.log_nonpos (norm_nonneg _) hr1
        have h3 : Real.log R ≤ 0 := Real.log_nonpos hR0.le hR1
        rw [abs_of_nonpos h2, abs_of_nonpos h3]
        linarith [abs_nonneg (Real.log ‖ϖ‖)]
      calc 1 + |Real.log ‖z‖ + Real.log ‖r‖| ≤ 1 + (|Real.log ‖z‖| + |Real.log ‖r‖|) := by gcongr; exact abs_add_le _ _
        _ ≤ (1 + |Real.log R| + |Real.log ‖ϖ‖|) + |Real.log ‖z‖| := by linarith
  calc ∫ x in {x : (v.adicCompletion K) | ‖x‖ ≤ R}, (1 + |Real.log ‖x‖|) ∂μ
      ≤ ∫ x in {x : (v.adicCompletion K) | ‖x‖ ≤ ‖r‖}, (1 + |Real.log ‖x‖|) ∂μ :=
        setIntegral_mono_set hintBig (Filter.Eventually.of_forall fun x => by positivity) hsub.eventuallyLE
    _ = ‖r‖ * ∫ z in {z : (v.adicCompletion K) | ‖z‖ ≤ 1}, (1 + |Real.log ‖z * r‖|) ∂μ := step
    _ ≤ ‖r‖ * ∫ z in {z : (v.adicCompletion K) | ‖z‖ ≤ 1}, ((1 + |Real.log R| + |Real.log ‖ϖ‖|) + |Real.log ‖z‖|) ∂μ := by
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        refine setIntegral_mono_on ?_ ((integrableOn_const (C := (1 + |Real.log R| + |Real.log ‖ϖ‖|)) hB1fin).add hlogint.abs) hball1m fun z _ => hbound z
        refine Integrable.mono' ((integrableOn_const (C := (1 + |Real.log R| + |Real.log ‖ϖ‖|)) hB1fin).add hlogint.abs) ?_ ?_
        · exact ((continuous_abs.measurable.comp (Real.measurable_log.comp ((continuous_mul_const r).norm.measurable))).const_add 1).aestronglyMeasurable
        · exact Filter.Eventually.of_forall fun z => by
            rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; exact hbound z
    _ = ‖r‖ * ((1 + |Real.log R| + |Real.log ‖ϖ‖|) * m₁ + Φ₁) := by
        rw [integral_add (integrableOn_const (C := (1 + |Real.log R| + |Real.log ‖ϖ‖|)) hB1fin) hlogint.abs, setIntegral_const, smul_eq_mul, ← hm₁, ← hΦ₁]
        ring
    _ ≤ (R * ‖ϖ‖⁻¹) * ((m₁ * (1 + |Real.log ‖ϖ‖|) + Φ₁) * (1 + |Real.log R|)) := by
        have hL : 0 ≤ |Real.log R| := abs_nonneg _
        have hP : 0 ≤ |Real.log ‖ϖ‖| := abs_nonneg _
        have hX : (1 + |Real.log R| + |Real.log ‖ϖ‖|) * m₁ + Φ₁ ≤ (m₁ * (1 + |Real.log ‖ϖ‖|) + Φ₁) * (1 + |Real.log R|) := by
          nlinarith [mul_nonneg hm₁0 (mul_nonneg hP hL), mul_nonneg hΦ₁0 hL]
        have hX0 : 0 ≤ (1 + |Real.log R| + |Real.log ‖ϖ‖|) * m₁ + Φ₁ := by positivity
        exact mul_le_mul hrR.le hX hX0 (by positivity)
    _ = (m₁ * (1 + |Real.log ‖ϖ‖|) + Φ₁) * ‖ϖ‖⁻¹ * R * (1 + |Real.log R|) := by ring

theorem oneDimMass [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)] (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure] :
    ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ R : ℝ, 0 < R → R ≤ 1 → (μ {x : (v.adicCompletion K) | ‖x‖ ≤ R}).toReal ≤ C₁ * R := by
  have hball1 : {z : (v.adicCompletion K) | ‖z‖ ≤ 1} = (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
    ext z
    simp only [Set.mem_setOf_eq, SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers]
    exact Valued.toNormedField.norm_le_one_iff
  have hball1c : IsCompact {z : (v.adicCompletion K) | ‖z‖ ≤ 1} := by
    rw [hball1]; exact isCompact_iff_compactSpace.2 (NumberField.AdelicHaar.compactSpace_adicCompletionIntegers (𝓞 K) K v)
  have hball1m : MeasurableSet {z : (v.adicCompletion K) | ‖z‖ ≤ 1} := hball1c.isClosed.measurableSet
  have hB1fin : μ {z : (v.adicCompletion K) | ‖z‖ ≤ 1} ≠ ⊤ := hball1c.measure_lt_top.ne
  set m₁ : ℝ := (μ {z : (v.adicCompletion K) | ‖z‖ ≤ 1}).toReal with hm₁
  have hm₁0 : 0 ≤ m₁ := ENNReal.toReal_nonneg
  clear_value m₁
  set ϖ : (v.adicCompletion K) := (uniformizerUnit K v : (v.adicCompletion K)) with hϖ
  have hϖ1 : ‖ϖ‖ < 1 := by
    refine Valued.toNormedField.norm_lt_one_iff.mpr ?_
    rw [hϖ, valued_uniformizerUnit, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  have hϖ0 : 0 < ‖ϖ‖ := norm_pos_iff.mpr (uniformizerUnit K v).ne_zero
  refine ⟨m₁ * ‖ϖ‖⁻¹, mul_nonneg hm₁0 (inv_nonneg.mpr hϖ0.le), fun R hR0 hR1 => ?_⟩
  have hex : ∃ n : ℕ, ‖ϖ‖ ^ (n + 1) < R := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hR0 hϖ1
    exact ⟨n, lt_of_le_of_lt (pow_le_pow_of_le_one hϖ0.le hϖ1.le (Nat.le_succ n)) hn⟩
  classical
  let n := Nat.find hex
  have hn1 : ‖ϖ‖ ^ (n + 1) < R := Nat.find_spec hex
  have hn2 : R ≤ ‖ϖ‖ ^ n := by
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · rw [h0, pow_zero]; exact hR1
    · have := Nat.find_min hex (show n - 1 < n from Nat.sub_lt hpos one_pos)
      rw [not_lt, Nat.sub_add_cancel hpos] at this
      exact this
  set r : (v.adicCompletion K) := ϖ ^ n with hrdef
  have hrn : ‖r‖ = ‖ϖ‖ ^ n := by rw [hrdef, norm_pow]
  have hr0 : r ≠ 0 := by rw [hrdef]; exact pow_ne_zero _ (uniformizerUnit K v).ne_zero
  have hRr : R ≤ ‖r‖ := hrn ▸ hn2
  have hrR : ‖r‖ < R * ‖ϖ‖⁻¹ := by
    rw [hrn, lt_mul_inv_iff₀ hϖ0, ← pow_succ]; exact hn1
  have hpre : (fun z : (v.adicCompletion K) => z * r) ⁻¹' {x : (v.adicCompletion K) | ‖x‖ ≤ ‖r‖} = {z : (v.adicCompletion K) | ‖z‖ ≤ 1} := by
    ext z
    simp only [Set.mem_preimage, Set.mem_setOf_eq, norm_mul]
    constructor
    · intro h; nlinarith [norm_pos_iff.mpr hr0]
    · intro h; nlinarith [norm_pos_iff.mpr hr0, norm_nonneg z]
  have hμeq : μ = (‖r‖₊ : NNReal) • Measure.map (fun z : (v.adicCompletion K) => z * r) μ := by
    rw [map_mul_right K v μ r hr0, smul_smul, mul_inv_cancel₀ (by rwa [ne_eq, nnnorm_eq_zero]), one_smul]
  have hballm : MeasurableSet {x : (v.adicCompletion K) | ‖x‖ ≤ ‖r‖} := (isClosed_le continuous_norm continuous_const).measurableSet
  have hsub : {x : (v.adicCompletion K) | ‖x‖ ≤ R} ⊆ {x : (v.adicCompletion K) | ‖x‖ ≤ ‖r‖} := fun x hx => le_trans hx hRr
  have hbig : (μ {x : (v.adicCompletion K) | ‖x‖ ≤ ‖r‖}).toReal = ‖r‖ * m₁ := by
    conv_lhs => rw [hμeq]
    rw [Measure.smul_apply, Measure.map_apply (measurable_mul_const _) hballm, hpre, ENNReal.smul_def, smul_eq_mul,
      ENNReal.toReal_mul, ENNReal.coe_toReal, coe_nnnorm, ← hm₁]
  have hfin : μ {x : (v.adicCompletion K) | ‖x‖ ≤ ‖r‖} ≠ ⊤ := by
    refine (Metric.isCompact_of_isClosed_isBounded (isClosed_le continuous_norm continuous_const) ?_).measure_lt_top.ne
    exact (Metric.isBounded_closedBall (x := (0 : (v.adicCompletion K))) (r := ‖r‖)).subset fun y hy => by
      simpa [Metric.mem_closedBall, dist_zero_right] using hy
  calc (μ {x : (v.adicCompletion K) | ‖x‖ ≤ R}).toReal ≤ (μ {x : (v.adicCompletion K) | ‖x‖ ≤ ‖r‖}).toReal :=
        ENNReal.toReal_mono hfin (measure_mono hsub)
    _ = ‖r‖ * m₁ := hbig
    _ ≤ (R * ‖ϖ‖⁻¹) * m₁ := mul_le_mul_of_nonneg_right hrR.le hm₁0
    _ = m₁ * ‖ϖ‖⁻¹ * R := by ring

end ThinSlab

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (E : Type) [AddCommGroup E] [Module (v.adicCompletion K) E] [FiniteDimensional (v.adicCompletion K) E]
    [TopologicalSpace E] [IsModuleTopology (v.adicCompletion K) E]
    [MeasurableSpace E] [BorelSpace E] (ν : Measure E) [ν.IsAddHaarMeasure]
    (lam : E →ₗ[(v.adicCompletion K)] (v.adicCompletion K)) (hlam : Function.Surjective lam)
    (Z : Set E) (hZ : IsCompact Z) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → R ≤ 1 →
      (ν (Z ∩ {z | ‖lam z‖ ≤ R})).toReal ≤ C * R := by
  classical

  letI mK : MeasurableSpace (v.adicCompletion K) := borel _
  haveI : BorelSpace (v.adicCompletion K) := ⟨rfl⟩
  haveI : IsTopologicalAddGroup E := IsModuleTopology.topologicalAddGroup (v.adicCompletion K) E
  haveI : ContinuousSMul (v.adicCompletion K) E := IsModuleTopology.toContinuousSMul (v.adicCompletion K) E

  obtain ⟨e₀, he₀⟩ := hlam 1
  let W : Submodule (v.adicCompletion K) E := LinearMap.ker lam
  let m : ℕ := Module.finrank (v.adicCompletion K) W
  let bW := Module.finBasis (v.adicCompletion K) W
  have hπmem : ∀ z : E, z - lam z • e₀ ∈ W := fun z => by
    simp [W, LinearMap.mem_ker, map_sub, map_smul, he₀]
  let π : E →ₗ[(v.adicCompletion K)] W := LinearMap.codRestrict W (LinearMap.id - (LinearMap.toSpanSingleton (v.adicCompletion K) E e₀).comp lam) (fun z => hπmem z)
  let P := (v.adicCompletion K) × (Fin m → (v.adicCompletion K))
  let f : E →ₗ[(v.adicCompletion K)] P := LinearMap.prod lam (bW.equivFun.toLinearMap.comp π)
  let g : P →ₗ[(v.adicCompletion K)] E := LinearMap.coprod (LinearMap.toSpanSingleton (v.adicCompletion K) E e₀) (W.subtype.comp bW.equivFun.symm.toLinearMap)
  have hπ : ∀ z : E, (π z : E) = z - lam z • e₀ := fun z => rfl
  have hg : ∀ (x : (v.adicCompletion K)) (c : Fin m → (v.adicCompletion K)), g (x, c) = x • e₀ + ((bW.equivFun.symm c : W) : E) := fun x c => rfl
  have hf : ∀ z : E, f z = (lam z, bW.equivFun (π z)) := fun z => rfl
  have hfg : f.comp g = LinearMap.id := by
    refine LinearMap.ext fun p => ?_
    obtain ⟨x, c⟩ := p
    rw [LinearMap.comp_apply, hg, hf, LinearMap.id_apply]
    have hw : lam ((bW.equivFun.symm c : W) : E) = 0 := (bW.equivFun.symm c).2
    refine Prod.ext ?_ ?_
    · show lam (x • e₀ + ((bW.equivFun.symm c : W) : E)) = x
      rw [map_add, map_smul, he₀, hw, smul_eq_mul, mul_one, add_zero]
    · show bW.equivFun (π (x • e₀ + ((bW.equivFun.symm c : W) : E))) = c
      have : π (x • e₀ + ((bW.equivFun.symm c : W) : E)) = bW.equivFun.symm c := by
        apply Subtype.ext
        rw [hπ, map_add, map_smul, he₀, hw, smul_eq_mul, mul_one, add_zero, add_sub_cancel_left]
      rw [this, LinearEquiv.apply_symm_apply]
  have hgf : g.comp f = LinearMap.id := by
    refine LinearMap.ext fun z => ?_
    rw [LinearMap.comp_apply, hf, hg, LinearMap.id_apply, LinearEquiv.symm_apply_apply, hπ, add_sub_cancel]
  let Φ : E ≃ₗ[(v.adicCompletion K)] P := LinearEquiv.ofLinear f g hfg hgf
  let Φc : E ≃L[(v.adicCompletion K)] P := IsModuleTopology.continuousLinearEquiv Φ
  have hΦ1 : ∀ z : E, (Φc z).1 = lam z := fun z => rfl
  let eM : E ≃ᵐ P := Φc.toHomeomorph.toMeasurableEquiv
  have heM : ∀ z, eM z = Φc z := fun z => rfl

  let μK : Measure (v.adicCompletion K) := Measure.addHaar
  let μQ : Measure (Fin m → (v.adicCompletion K)) := Measure.pi fun _ => μK
  let μP : Measure P := μK.prod μQ
  haveI : μP.IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure μK μQ
  let ν' : Measure P := Measure.map eM ν
  haveI hν'H : ν'.IsAddHaarMeasure := by
    show (Measure.map (⇑Φc) ν).IsAddHaarMeasure
    exact ContinuousLinearEquiv.isAddHaarMeasure_map Φc ν
  obtain ⟨c, hc⟩ : ∃ c : NNReal, ν' = c • μP := ⟨_, Measure.isAddLeftInvariant_eq_smul ν' μP⟩

  obtain ⟨C₁, hC₁0, hC₁⟩ := ThinSlab.oneDimMass K v μK

  have hZ' : IsCompact (eM '' Z) := by rw [show eM '' Z = Φc '' Z from rfl]; exact hZ.image Φc.continuous
  let Y : Set (Fin m → (v.adicCompletion K)) := Prod.snd '' (eM '' Z)
  have hYc : IsCompact Y := hZ'.image continuous_snd
  have hYfin : μQ Y ≠ ⊤ := hYc.measure_lt_top.ne
  refine ⟨(c : ℝ) * C₁ * (μQ Y).toReal, by positivity, fun R hR0 hR1 => ?_⟩
  have hle1 := hC₁ R hR0 hR1
  set S : Set E := Z ∩ {z | ‖lam z‖ ≤ R} with hS
  set Bx : Set (v.adicCompletion K) := {x | ‖x‖ ≤ R} with hBx
  have hBxm : MeasurableSet Bx := (isClosed_le continuous_norm continuous_const).measurableSet
  have hsub : eM '' S ⊆ Bx ×ˢ Y := by
    rintro p ⟨z, ⟨hzZ, hzR⟩, rfl⟩
    refine ⟨?_, ⟨eM z, ⟨z, hzZ, rfl⟩, rfl⟩⟩
    show ‖(Φc z).1‖ ≤ R
    rw [hΦ1]; exact hzR
  have hνS : ν S = ν' (eM '' S) := by
    show ν S = (Measure.map eM ν) (eM '' S)
    rw [eM.map_apply, eM.injective.preimage_image]
  have hbox : ν' (Bx ×ˢ Y) = (c : ENNReal) * (μK Bx * μQ Y) := by
    rw [hc, Measure.smul_apply, show μP (Bx ×ˢ Y) = (μK.prod μQ) (Bx ×ˢ Y) from rfl,
      Measure.prod_prod, ENNReal.smul_def, smul_eq_mul]
  have hBxfin : μK Bx ≠ ⊤ := by
    refine (Metric.isCompact_of_isClosed_isBounded (isClosed_le continuous_norm continuous_const) ?_).measure_lt_top.ne
    exact (Metric.isBounded_closedBall (x := (0 : (v.adicCompletion K))) (r := R)).subset fun y hy => by
      simpa [Metric.mem_closedBall, dist_zero_right] using hy
  calc (ν S).toReal = (ν' (eM '' S)).toReal := by rw [hνS]
    _ ≤ (ν' (Bx ×ˢ Y)).toReal := by
        refine ENNReal.toReal_mono ?_ (measure_mono hsub)
        rw [hbox]; exact ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.mul_ne_top hBxfin hYfin)
    _ = (c : ℝ) * ((μK Bx).toReal * (μQ Y).toReal) := by
        rw [hbox, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.coe_toReal]
    _ ≤ (c : ℝ) * ((C₁ * R) * (μQ Y).toReal) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hle1 ENNReal.toReal_nonneg) (NNReal.coe_nonneg c)
    _ = (c : ℝ) * C₁ * (μQ Y).toReal * R := by ring

end

end S_IsDedekindDomain_HeightOneSpectrum_exists_forall_measureReal_inter_norm_le_le_of_surjective
end P2MW
export P2MW.S_IsDedekindDomain_HeightOneSpectrum_exists_forall_measureReal_inter_norm_le_le_of_surjective (solution)
