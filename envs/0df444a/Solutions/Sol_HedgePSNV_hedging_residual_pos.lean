-- Prove2me | solution 1 for HedgePSNV.hedging_residual_pos
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-07T23:15:44.160674+00:00
-- url     : https://prove2.me/submissions/7d3aedad-7bbf-4d71-8c8b-03ee83bc04ec

import Mathlib
import Definitions.Def_HedgePSNV_Hedging

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace HedgePSNVResPos

open HedgePSNV

lemma I_zero_ae {p : Params} {Ω : Type*} [MeasurableSpace Ω] (M : Model p Ω)
    (hM : M.Standing) : M.I 0 =ᵐ[M.P] fun _ => (0 : ℝ) := by
  obtain ⟨a, -, -, -, hlim⟩ := hM.I_ito.2 0
  have hsum : ∀ n, EthierKurtz.itoStepSum M.B 0 n (a n) = fun _ => (0 : ℝ) := by
    intro n
    funext ω
    unfold EthierKurtz.itoStepSum
    simp
  have h0 : TendstoInMeasure M.P (fun n => EthierKurtz.itoStepSum M.B 0 n (a n)) Filter.atTop
      (fun _ => (0 : ℝ)) := by
    intro ε hε
    simp [hsum, not_le.mpr hε]
  exact tendstoInMeasure_ae_unique hlim h0

lemma PM_prob {p : Params} {Ω : Type*} [MeasurableSpace Ω] (M : Model p Ω)
    (hM : M.Standing) (h5 : M.Assumption5) : IsProbabilityMeasure M.PM := by
  have := hM.prob
  have hZ0 : M.Z 0 =ᵐ[M.P] fun _ => (1 : ℝ) := by
    filter_upwards [I_zero_ae M hM] with ω hω
    simp [Model.Z, hω]
  have hint : Integrable (M.Z p.T) M.P := (h5.1.2.1 p.T le_rfl)
  have hce := h5.1.2.2 0 p.T zero_le le_rfl
  have hE : ∫ ω, M.Z p.T ω ∂M.P = 1 := by
    rw [← integral_condExp (M.F.le 0)]
    rw [integral_congr_ae (hce.trans hZ0)]
    simp
  constructor
  unfold Model.PM
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le), hE, ENNReal.ofReal_one]

lemma AT_aemeas {p : Params} {Ω : Type*} [MeasurableSpace Ω] (M : Model p Ω)
    (hM : M.Standing) : AEMeasurable M.AT M.P := by
  have hCm : Measurable (M.C p.T) := ((hM.C_adapted p.T).mono (M.G.le p.T)).measurable
  have hBm : AEMeasurable (M.Bt p.T) M.P :=
    (hM.brownBt.toIsPreBrownianReal.hasLaw_eval p.T).aemeasurable
  show AEMeasurable (fun ω => M.C p.T ω + p.σt * M.Bt p.T ω) M.P
  fun_prop

lemma PM_ac {p : Params} {Ω : Type*} [MeasurableSpace Ω] (M : Model p Ω) : M.PM ≪ M.P :=
  withDensity_absolutelyContinuous _ _

lemma Z_pos {p : Params} {Ω : Type*} [MeasurableSpace Ω] (M : Model p Ω) (t : ℝ≥0) (ω : Ω) :
    0 < M.Z t ω := Real.exp_pos _

lemma Z_T_measurable {p : Params} {Ω : Type*} [MeasurableSpace Ω] (M : Model p Ω)
    (h5 : M.Assumption5) : Measurable (M.Z p.T) :=
  ((h5.1.1 p.T le_rfl).mono (M.F.le p.T)).measurable

/-- `∫ Z_T g dP = ∫ g dP^M` (density `Z_T`). -/
lemma integral_PM {p : Params} {Ω : Type*} [MeasurableSpace Ω] (M : Model p Ω)
    (h5 : M.Assumption5) (g : Ω → ℝ) :
    ∫ ω, M.Z p.T ω * g ω ∂M.P = ∫ ω, g ω ∂M.PM := by
  have hm : Measurable (fun ω => (M.Z p.T ω).toNNReal) :=
    (Z_T_measurable M h5).real_toNNReal
  unfold Model.PM
  have hden : (fun ω => ENNReal.ofReal (M.Z p.T ω)) =
      (fun ω => (((M.Z p.T ω).toNNReal : ℝ≥0) : ℝ≥0∞)) := rfl
  rw [hden, integral_withDensity_eq_integral_smul hm]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  simp only [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (Z_pos M p.T ω).le]

lemma ZT_int_PM {p : Params} {Ω : Type*} [MeasurableSpace Ω] (M : Model p Ω)
    (h5 : M.Assumption5) : Integrable (M.Z p.T) M.PM := by
  have hm : Measurable (fun ω => (M.Z p.T ω).toNNReal) :=
    (Z_T_measurable M h5).real_toNNReal
  have hL2 : MemLp (M.Z p.T) 2 M.P := h5.2 p.T le_rfl
  unfold Model.PM
  have hden : (fun ω => ENNReal.ofReal (M.Z p.T ω)) =
      (fun ω => (((M.Z p.T ω).toNNReal : ℝ≥0) : ℝ≥0∞)) := rfl
  rw [hden, integrable_withDensity_iff_integrable_smul hm]
  refine hL2.integrable_sq.congr (Filter.Eventually.of_forall fun ω => ?_)
  simp only [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (Z_pos M p.T ω).le, sq]

lemma cdf_strictMono (ν : Measure ℝ) [IsProbabilityMeasure ν] (h1 : Assumption1 ν) :
    StrictMono (cdf ν) := by
  obtain ⟨f, r, r', hf, hr, hr', hpos, -, -⟩ := h1
  refine (monotone_cdf ν).strictMono_of_injective fun x y hxy => ?_
  by_contra hne
  wlog hlt : x < y generalizing x y
  · exact this y x hxy.symm (Ne.symm hne) (lt_of_le_of_ne (not_lt.1 hlt) (Ne.symm hne))
  have hconst : ∀ z ∈ Set.Ioo x y, cdf ν z = cdf ν x := fun z hz =>
    le_antisymm (hxy ▸ monotone_cdf ν hz.2.le) (monotone_cdf ν hz.1.le)
  have hf0 : ∀ z ∈ Set.Ioo x y, f z = 0 := by
    intro z hz
    have hev : (fun _ : ℝ => cdf ν x) =ᶠ[𝓝 z] fun w => cdf ν w :=
      Filter.mem_of_superset (Ioo_mem_nhds hz.1 hz.2) fun w hw => (hconst w hw).symm
    exact (hf z).unique ((hasDerivAt_const z (cdf ν x)).congr_of_eventuallyEq hev.symm)
  have hr0 : ∀ z ∈ Set.Ioo x y, r z = 0 := fun z hz => by rw [hr z, hf0 z hz, zero_div]
  set a := (x + y) / 2
  have ha : a ∈ Set.Ioo x y := ⟨by simp only [a]; linarith, by simp only [a]; linarith⟩
  have hev : (fun _ : ℝ => (0 : ℝ)) =ᶠ[𝓝 a] r :=
    Filter.mem_of_superset (Ioo_mem_nhds ha.1 ha.2) fun w hw => (hr0 w hw).symm
  have hr'0 : r' a = 0 := (hr' a).unique ((hasDerivAt_const a (0 : ℝ)).congr_of_eventuallyEq hev.symm)
  have := hpos a
  rw [hr0 a ha, hr'0] at this
  norm_num at this

/-- Uniform lower bound for the inner expectation:
`E[(Z_t/Z^M_t) δ_t²] ≥ c² F⁴/(8 Z^M_0)` with `c = σ̃(P-s)`, `F = P^M(A_T ≤ R)`. -/
theorem inner_bound {p : Params} {Ω : Type*} [MeasurableSpace Ω] (M : Model p Ω)
    (hM : M.Standing) (h5 : M.Assumption5) (h1M : Assumption1 (M.PM.map M.AT))
    (P R : ℝ) (hP : p.s < P) (t : ℝ≥0) (ht : t ≤ p.T) :
    0 < (p.σt * (P - p.s)) ^ 2 * cdf (M.PM.map M.AT) R ^ 4 / (8 * M.ZM0) ∧
    ENNReal.ofReal ((p.σt * (P - p.s)) ^ 2 * cdf (M.PM.map M.AT) R ^ 4 / (8 * M.ZM0)) ≤
      ∫⁻ ω, ENNReal.ofReal (M.Z t ω / M.ZM t ω * M.delta P R t ω ^ 2) ∂M.P := by
  have hPprob := hM.prob
  have hPM : IsProbabilityMeasure M.PM := PM_prob M hM h5
  have hAM : AEMeasurable M.AT M.PM := (AT_aemeas M hM).mono_ac (PM_ac M)
  have hν : IsProbabilityMeasure (M.PM.map M.AT) := Measure.isProbabilityMeasure_map hAM
  set c := p.σt * (P - p.s) with hc_def
  have hc : 0 < c := mul_pos p.hσt (by linarith)
  set Fv := cdf (M.PM.map M.AT) R with hFv_def
  have hFpos : 0 < Fv :=
    lt_of_le_of_lt (cdf_nonneg _ _) (cdf_strictMono _ h1M (show R - 1 < R by linarith))
  have hF1 : Fv ≤ 1 := cdf_le_one _ _
  have hZT_int : Integrable (M.Z p.T) M.PM := ZT_int_PM M h5
  set Z0 := M.ZM0 with hZ0_def
  have hZ0pos : 0 < Z0 := by
    rw [hZ0_def]
    unfold Model.ZM0
    rw [integral_pos_iff_support_of_nonneg (fun ω => (Z_pos M p.T ω).le) hZT_int]
    have : Function.support (M.Z p.T) = Set.univ := by
      ext ω; simp [(Z_pos M p.T ω).ne']
    rw [this, measure_univ]; exact one_pos
  -- the indicator and its conditional expectation
  set ind : Ω → ℝ := Set.indicator {x | M.AT x ≤ R} (fun _ => (1 : ℝ)) with hind_def
  have hind_eq : ind = fun ω => (Set.Iic R).indicator (fun _ => (1 : ℝ)) (M.AT ω) := by
    funext x; simp [ind, Set.indicator]
  have hgm : Measurable ((Set.Iic R).indicator (fun _ : ℝ => (1 : ℝ))) :=
    measurable_const.indicator measurableSet_Iic
  have hind_int : Integrable ind M.PM := by
    rw [hind_eq]
    refine Integrable.of_bound (C := 1) (hgm.comp_aemeasurable hAM).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    simp only [Set.indicator]; split_ifs <;> simp
  have hind_integral : ∫ ω, ind ω ∂M.PM = Fv := by
    rw [hind_eq, ← integral_map hAM hgm.aestronglyMeasurable,
      integral_indicator measurableSet_Iic, setIntegral_const, smul_eq_mul, mul_one, hFv_def,
      cdf_eq_real]
  set q := M.PM[ind | M.F t] with hq_def
  have hq_nn : 0 ≤ᵐ[M.PM] q :=
    condExp_nonneg (μ := M.PM) (m := M.F t) (f := ind)
      (Filter.Eventually.of_forall fun x => by
        show (0 : ℝ) ≤ Set.indicator {x | M.AT x ≤ R} (fun _ => (1 : ℝ)) x
        simp only [Set.indicator]; split_ifs <;> norm_num)
  have hq_le : q ≤ᵐ[M.PM] fun _ => (1 : ℝ) := by
    have h1 := condExp_mono (m := M.F t) hind_int (integrable_const (1 : ℝ))
      (Filter.Eventually.of_forall fun x => by
        show Set.indicator {x | M.AT x ≤ R} (fun _ => (1 : ℝ)) x ≤ (1 : ℝ)
        simp only [Set.indicator]; split_ifs <;> norm_num)
    rwa [condExp_const (M.F.le t)] at h1
  have hq_int : ∫ ω, q ω ∂M.PM = Fv := by
    rw [hq_def, integral_condExp (M.F.le t)]; exact hind_integral
  have hq_sm : StronglyMeasurable[M.F t] q := stronglyMeasurable_condExp
  set mm : Ω → ℝ := fun ω => min |q ω| 1 with hmm_def
  have hmm_m : Measurable[M.F t] mm := Measurable.min (continuous_abs.measurable.comp hq_sm.measurable) measurable_const
  have hmm_nn : ∀ ω, 0 ≤ mm ω := fun ω => le_min (abs_nonneg _) zero_le_one
  have hmm_le : ∀ ω, mm ω ≤ 1 := fun ω => min_le_right _ _
  have hmm_eq : mm =ᵐ[M.PM] q := by
    filter_upwards [hq_nn, hq_le] with ω h1 h2
    simp only [hmm_def, abs_of_nonneg h1]
    exact min_eq_left h2
  have hmm_int : Integrable mm M.PM :=
    Integrable.of_bound (C := 1) (hmm_m.mono (M.F.le t) le_rfl).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hmm_nn ω)]; exact hmm_le ω)
  have hmm_integral : ∫ ω, mm ω ∂M.PM = Fv := by rw [integral_congr_ae hmm_eq]; exact hq_int
  -- the density martingale `Z^M_t`
  set Y := M.ZM t with hY_def
  have hY_sm : StronglyMeasurable[M.F t] Y := stronglyMeasurable_condExp
  have hY_int : Integrable Y M.PM := integrable_condExp
  have hY_integral : ∫ ω, Y ω ∂M.PM = Z0 := by
    rw [hY_def]; unfold Model.ZM; rw [integral_condExp (M.F.le t)]; rfl
  have hY_nn : 0 ≤ᵐ[M.PM] Y := by
    rw [hY_def]; unfold Model.ZM
    exact condExp_nonneg (Filter.Eventually.of_forall fun ω => by
      show (0 : ℝ) ≤ M.Z p.T ω
      exact (Z_pos M p.T ω).le)
  set K := 2 * Z0 / Fv ^ 2 with hK_def
  have hK : 0 < K := by positivity
  -- P^M(Z^M_t ≤ 0) = 0
  set N : Set Ω := {ω | Y ω ≤ 0} with hN_def
  have hN_meas : MeasurableSet[M.F t] N := measurableSet_le hY_sm.measurable measurable_const
  have hN0 : M.PM N = 0 := by
    by_contra hne
    have h1 : ∫ ω in N, Y ω ∂M.PM = ∫ ω in N, M.Z p.T ω ∂M.PM := by
      rw [hY_def]; unfold Model.ZM
      exact setIntegral_condExp (M.F.le t) hZT_int hN_meas
    have h2 : ∫ ω in N, Y ω ∂M.PM ≤ 0 :=
      setIntegral_nonpos (M.F.le t N hN_meas) (fun ω hω => hω)
    have h3 : 0 < ∫ ω in N, M.Z p.T ω ∂M.PM := by
      rw [setIntegral_pos_iff_support_of_nonneg_ae
        (Filter.Eventually.of_forall fun ω => (Z_pos M p.T ω).le) hZT_int.integrableOn]
      have : Function.support (M.Z p.T) = Set.univ := by
        ext ω; simp [(Z_pos M p.T ω).ne']
      rw [this, Set.univ_inter]; exact pos_iff_ne_zero.2 hne
    linarith
  -- Markov: P^M(Z^M_t ≥ K) ≤ Z0 / K
  set L : Set Ω := {ω | K ≤ Y ω} with hL_def
  have hL_meas : MeasurableSet[M.F t] L := measurableSet_le measurable_const hY_sm.measurable
  have hL : K * M.PM.real L ≤ Z0 := by
    rw [← hY_integral]; exact mul_meas_ge_le_integral_of_nonneg hY_nn hY_int K
  -- the test function
  set S : Set Ω := {ω | 0 < Y ω ∧ Y ω < K} with hS_def
  have hS_meas : MeasurableSet[M.F t] S :=
    (measurableSet_lt measurable_const hY_sm.measurable).inter
      (measurableSet_lt hY_sm.measurable measurable_const)
  set h : Ω → ℝ := S.indicator (fun ω => c ^ 2 * mm ω ^ 2 / K) with hh_def
  have h_m : Measurable[M.F t] h :=
    ((measurable_const.mul (hmm_m.pow_const 2)).div_const K).indicator hS_meas
  have h_sm : StronglyMeasurable[M.F t] h := h_m.stronglyMeasurable
  have h_nn : ∀ ω, 0 ≤ h ω := by
    intro ω
    simp only [hh_def, Set.indicator]
    split_ifs
    · positivity
    · exact le_rfl
  have h_bd : ∀ ω, ‖h ω‖ ≤ c ^ 2 / K := by
    intro ω
    rw [Real.norm_eq_abs, abs_of_nonneg (h_nn ω)]
    simp only [hh_def, Set.indicator]
    split_ifs
    · have : mm ω ^ 2 ≤ 1 := pow_le_one₀ (hmm_nn ω) (hmm_le ω)
      have hc2 : 0 ≤ c ^ 2 := by positivity
      exact div_le_div_of_nonneg_right (by nlinarith) hK.le
    · positivity
  -- Step A: pointwise comparison
  have hA : ∀ ω, ENNReal.ofReal (M.Z t ω * h ω) ≤
      ENNReal.ofReal (M.Z t ω / M.ZM t ω * M.delta P R t ω ^ 2) := by
    intro ω
    by_cases hω : ω ∈ S
    · apply ENNReal.ofReal_le_ofReal
      simp only [hh_def, Set.indicator_of_mem hω]
      have hY0 : 0 < Y ω := hω.1
      have hYK : Y ω < K := hω.2
      have hdel : M.delta P R t ω = c * q ω := rfl
      rw [hdel, ← hY_def]
      have hmq : mm ω ^ 2 ≤ q ω ^ 2 := by
        rw [← sq_abs (q ω)]
        exact pow_le_pow_left₀ (hmm_nn ω) (min_le_left _ _) 2
      have hZ := Z_pos M t ω
      have e1 : c ^ 2 * mm ω ^ 2 / K ≤ c ^ 2 * q ω ^ 2 / K :=
        div_le_div_of_nonneg_right (by nlinarith [sq_nonneg c]) hK.le
      have e2 : c ^ 2 * q ω ^ 2 / K ≤ c ^ 2 * q ω ^ 2 / Y ω :=
        div_le_div_of_nonneg_left (by positivity) hY0 hYK.le
      calc M.Z t ω * (c ^ 2 * mm ω ^ 2 / K) ≤ M.Z t ω * (c ^ 2 * q ω ^ 2 / Y ω) :=
            mul_le_mul_of_nonneg_left (e1.trans e2) hZ.le
        _ = M.Z t ω / Y ω * (c * q ω) ^ 2 := by field_simp
    · simp [hh_def, Set.indicator_of_notMem hω]
  -- Step B
  have hZt_int : Integrable (M.Z t) M.P := h5.1.2.1 t ht
  have hZh_int : Integrable (fun ω => M.Z t ω * h ω) M.P := by
    refine Integrable.mono' (hZt_int.norm.const_mul (c ^ 2 / K))
      (hZt_int.aestronglyMeasurable.mul (h_sm.mono (M.F.le t)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [norm_mul, mul_comm (c ^ 2 / K)]
    exact mul_le_mul_of_nonneg_left (h_bd ω) (norm_nonneg _)
  have hB : ∫⁻ ω, ENNReal.ofReal (M.Z t ω * h ω) ∂M.P =
      ENNReal.ofReal (∫ ω, M.Z t ω * h ω ∂M.P) :=
    (ofReal_integral_eq_lintegral_ofReal hZh_int
      (Filter.Eventually.of_forall fun ω => mul_nonneg (Z_pos M t ω).le (h_nn ω))).symm
  -- Step C: martingale property of `Z`
  have hC : ∫ ω, M.Z t ω * h ω ∂M.P = ∫ ω, M.Z p.T ω * h ω ∂M.P := by
    have hce : M.P[M.Z p.T | M.F t] =ᵐ[M.P] M.Z t := h5.1.2.2 t p.T ht le_rfl
    have hZT_intP : Integrable (M.Z p.T) M.P := h5.1.2.1 p.T le_rfl
    have hm := condExp_stronglyMeasurable_mul_of_bound (M.F.le t) h_sm hZT_intP (c ^ 2 / K)
      (Filter.Eventually.of_forall h_bd)
    calc ∫ ω, M.Z t ω * h ω ∂M.P = ∫ ω, (h * M.P[M.Z p.T | M.F t]) ω ∂M.P := by
          refine integral_congr_ae ?_
          filter_upwards [hce] with ω hω
          simp only [Pi.mul_apply, hω]; ring
      _ = ∫ ω, (M.P[h * M.Z p.T | M.F t]) ω ∂M.P := (integral_congr_ae hm).symm
      _ = ∫ ω, (h * M.Z p.T) ω ∂M.P := integral_condExp (M.F.le t)
      _ = ∫ ω, M.Z p.T ω * h ω ∂M.P := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
          simp only [Pi.mul_apply]; ring
  -- Step D: change of measure
  have hD : ∫ ω, M.Z p.T ω * h ω ∂M.P = ∫ ω, h ω ∂M.PM := integral_PM M h5 h
  -- Step E: lower bound under `P^M`
  have hNi : Integrable (N.indicator (1 : Ω → ℝ)) M.PM :=
    (integrable_const (1 : ℝ)).indicator (M.F.le t N hN_meas)
  have hLi : Integrable (L.indicator (1 : Ω → ℝ)) M.PM :=
    (integrable_const (1 : ℝ)).indicator (M.F.le t L hL_meas)
  set g : Ω → ℝ := fun ω => Fv * mm ω - Fv ^ 2 / 4 - N.indicator 1 ω - L.indicator 1 ω
    with hg_def
  have hg_int : Integrable g M.PM :=
    (((hmm_int.const_mul Fv).sub (integrable_const _)).sub hNi).sub hLi
  have hg_integral : ∫ ω, g ω ∂M.PM = Fv * Fv - Fv ^ 2 / 4 - M.PM.real N - M.PM.real L := by
    have e1 : ∫ ω, g ω ∂M.PM = ∫ ω, (Fv * mm ω - Fv ^ 2 / 4 - N.indicator 1 ω) ∂M.PM -
        ∫ ω, L.indicator 1 ω ∂M.PM :=
      integral_sub (((hmm_int.const_mul Fv).sub (integrable_const _)).sub hNi) hLi
    have e2 : ∫ ω, (Fv * mm ω - Fv ^ 2 / 4 - N.indicator 1 ω) ∂M.PM =
        ∫ ω, (Fv * mm ω - Fv ^ 2 / 4) ∂M.PM - ∫ ω, N.indicator 1 ω ∂M.PM :=
      integral_sub ((hmm_int.const_mul Fv).sub (integrable_const _)) hNi
    have e3 : ∫ ω, (Fv * mm ω - Fv ^ 2 / 4) ∂M.PM =
        ∫ ω, Fv * mm ω ∂M.PM - ∫ _ω, Fv ^ 2 / 4 ∂M.PM :=
      integral_sub (hmm_int.const_mul Fv) (integrable_const _)
    have e4 : ∫ ω, Fv * mm ω ∂M.PM = Fv * Fv := by
      rw [integral_const_mul, hmm_integral]
    rw [e1, e2, e3, e4, integral_const, integral_indicator_one (M.F.le t N hN_meas),
      integral_indicator_one (M.F.le t L hL_meas)]
    simp
  have hpt : ∀ ω, c ^ 2 / K * g ω ≤ h ω := by
    intro ω
    have hcK : 0 ≤ c ^ 2 / K := by positivity
    have hm0 := hmm_nn ω
    have hm1 := hmm_le ω
    by_cases hω : ω ∈ S
    · simp only [hh_def, Set.indicator_of_mem hω]
      have hNn : 0 ≤ N.indicator (1 : Ω → ℝ) ω := Set.indicator_nonneg (fun _ _ => zero_le_one) ω
      have hLn : 0 ≤ L.indicator (1 : Ω → ℝ) ω := Set.indicator_nonneg (fun _ _ => zero_le_one) ω
      have hgle : g ω ≤ mm ω ^ 2 := by
        simp only [hg_def]; nlinarith [sq_nonneg (mm ω - Fv / 2)]
      calc c ^ 2 / K * g ω ≤ c ^ 2 / K * mm ω ^ 2 := mul_le_mul_of_nonneg_left hgle hcK
        _ = c ^ 2 * mm ω ^ 2 / K := by ring
    · simp only [hh_def, Set.indicator_of_notMem hω]
      have hcases : ω ∈ N ∨ ω ∈ L := by
        simp only [hS_def, Set.mem_ofPred_eq, not_and_or, not_lt] at hω
        rcases hω with h1 | h1
        · exact Or.inl h1
        · exact Or.inr h1
      have hsum : 1 ≤ N.indicator (1 : Ω → ℝ) ω + L.indicator (1 : Ω → ℝ) ω := by
        have hNn : 0 ≤ N.indicator (1 : Ω → ℝ) ω := Set.indicator_nonneg (fun _ _ => zero_le_one) ω
        have hLn : 0 ≤ L.indicator (1 : Ω → ℝ) ω := Set.indicator_nonneg (fun _ _ => zero_le_one) ω
        rcases hcases with h1 | h1
        · rw [Set.indicator_of_mem h1]; simp only [Pi.one_apply]; linarith
        · rw [Set.indicator_of_mem h1 (1 : Ω → ℝ)]; simp only [Pi.one_apply]; linarith
      have hgle : g ω ≤ 0 := by
        simp only [hg_def]; nlinarith [mul_le_mul hF1 hm1 hm0 zero_le_one]
      exact mul_nonpos_of_nonneg_of_nonpos hcK hgle
  have hE : c ^ 2 / K * (Fv ^ 2 / 4) ≤ ∫ ω, h ω ∂M.PM := by
    have hh_int : Integrable h M.PM :=
      Integrable.of_bound (C := c ^ 2 / K) (h_sm.mono (M.F.le t)).aestronglyMeasurable
        (Filter.Eventually.of_forall h_bd)
    have hmono : ∫ ω, c ^ 2 / K * g ω ∂M.PM ≤ ∫ ω, h ω ∂M.PM :=
      integral_mono (hg_int.const_mul _) hh_int hpt
    rw [integral_const_mul, hg_integral] at hmono
    have hNr : M.PM.real N = 0 := by simp [Measure.real, hN0]
    have hLr : M.PM.real L ≤ Fv ^ 2 / 2 := by
      have : M.PM.real L ≤ Z0 / K := by rw [le_div_iff₀ hK]; linarith
      calc M.PM.real L ≤ Z0 / K := this
        _ = Fv ^ 2 / 2 := by rw [hK_def]; field_simp
    have hcK : 0 ≤ c ^ 2 / K := by positivity
    calc c ^ 2 / K * (Fv ^ 2 / 4) ≤ c ^ 2 / K * (Fv * Fv - Fv ^ 2 / 4 - M.PM.real N - M.PM.real L) := by
          refine mul_le_mul_of_nonneg_left ?_ hcK
          rw [hNr]; nlinarith
      _ ≤ _ := hmono
  have hκ : c ^ 2 * Fv ^ 4 / (8 * Z0) = c ^ 2 / K * (Fv ^ 2 / 4) := by
    rw [hK_def]; field_simp; ring
  refine ⟨by positivity, ?_⟩
  rw [hκ]
  calc ENNReal.ofReal (c ^ 2 / K * (Fv ^ 2 / 4)) ≤ ENNReal.ofReal (∫ ω, h ω ∂M.PM) :=
        ENNReal.ofReal_le_ofReal hE
    _ = ∫⁻ ω, ENNReal.ofReal (M.Z t ω * h ω) ∂M.P := by rw [hB, hC, hD]
    _ ≤ _ := lintegral_mono hA

end HedgePSNVResPos

open HedgePSNVResPos in
open HedgePSNV in
theorem solution (p : Params) {Ω : Type*} [MeasurableSpace Ω] (M : Model p Ω)
    (hM : M.Standing) (h5 : M.Assumption5) (h1M : Assumption1 (M.PM.map M.AT))
    (P R : ℝ) (hP : p.s < P) :
    0 < ∫⁻ u in Set.Icc (0 : ℝ) (p.T : ℝ), ∫⁻ ω,
        ENNReal.ofReal (M.Z u.toNNReal ω / M.ZM u.toNNReal ω * M.delta P R u.toNNReal ω ^ 2)
          ∂M.P := by
  set κ := (p.σt * (P - p.s)) ^ 2 * cdf (M.PM.map M.AT) R ^ 4 / (8 * M.ZM0) with hκ_def
  have hκ : 0 < κ := (inner_bound M hM h5 h1M P R hP 0 zero_le).1
  have key : ∀ u ∈ Set.Icc (0 : ℝ) (p.T : ℝ), ENNReal.ofReal κ ≤ ∫⁻ ω,
      ENNReal.ofReal (M.Z u.toNNReal ω / M.ZM u.toNNReal ω * M.delta P R u.toNNReal ω ^ 2)
        ∂M.P := by
    intro u hu
    have hu' : u.toNNReal ≤ p.T := by
      rw [Real.toNNReal_le_iff_le_coe]; exact hu.2
    exact (inner_bound M hM h5 h1M P R hP u.toNNReal hu').2
  have hvol : (volume (Set.Icc (0 : ℝ) (p.T : ℝ))) ≠ 0 := by
    rw [Real.volume_Icc, sub_zero, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact_mod_cast p.hT
  calc (0 : ℝ≥0∞) < ENNReal.ofReal κ * volume (Set.Icc (0 : ℝ) (p.T : ℝ)) :=
        ENNReal.mul_pos (by simpa using hκ) hvol
    _ = ∫⁻ _u in Set.Icc (0 : ℝ) (p.T : ℝ), ENNReal.ofReal κ := (setLIntegral_const _ _).symm
    _ ≤ _ := setLIntegral_mono' measurableSet_Icc key
