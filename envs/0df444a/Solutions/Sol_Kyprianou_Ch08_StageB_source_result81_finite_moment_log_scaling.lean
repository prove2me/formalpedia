-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result81_finite_moment_log_scaling
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T19:17:04.871426+00:00
-- url     : https://prove2.me/submissions/98de62cf-7e4a-476b-ba45-46e265f67236

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_ProbabilityTheory_IsLevyProcess_indepFun_increment
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_scalar_moment_exp
open MeasureTheory ProbabilityTheory Filter Set Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

private theorem source_marginal_aemeasurable
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    (X : ℝ≥0 → Ω → ℝ) (hX : IsLevyProcess X P) (t : ℝ≥0) :
    AEMeasurable (X t) P := by
  have hi := (hX.stationary_increments 0 t).aemeasurable_snd
  change AEMeasurable (fun ω => X t ω - X 0 ω) P at hi
  simpa only [hX.start_zero, sub_zero] using hi

private theorem source_extended_moment_mul
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    (X : ℝ≥0 → Ω → ℝ) (hX : IsLevyProcess X P) (θ : ℝ) (s u : ℝ≥0) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * X (s + u) ω)) ∂P =
      (∫⁻ ω, ENNReal.ofReal (Real.exp (θ * X s ω)) ∂P) *
        ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * X u ω)) ∂P := by
  let f : ℝ → ℝ≥0∞ := fun z => ENNReal.ofReal (Real.exp (θ * z))
  have hf : Measurable f := by fun_prop
  have hind := hX.indepFun_increment (s := 0) (t := s) (u := s + u) (by positivity) le_self_add
  change IndepFun (fun ω => X s ω - X 0 ω) (fun ω => X (s + u) ω - X s ω) P at hind
  simp only [hX.start_zero, sub_zero] at hind
  have hs := source_marginal_aemeasurable X hX s
  have hpow (ω : Ω) :
      f (X (s + u) ω) = f (X s ω) * f (X (s + u) ω - X s ω) := by
    dsimp [f]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2 <;> ring
  have heq := ((hX.stationary_increments s u).comp hf).lintegral_eq
  change (∫⁻ ω, f (X (s + u) ω - X s ω) ∂P) = (∫⁻ ω, f (X u ω - X 0 ω) ∂P) at heq
  simp only [hX.start_zero, sub_zero] at heq
  change (∫⁻ ω, f (X (s + u) ω) ∂P) = (∫⁻ ω, f (X s ω) ∂P) * ∫⁻ ω, f (X u ω) ∂P
  simp_rw [hpow]
  rw [← heq]
  exact lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun' (hf.comp_aemeasurable hs)
    (hf.comp_aemeasurable ((source_marginal_aemeasurable X hX (s + u)).sub hs)) (hind.comp hf hf)

private theorem extended_moment_finite_of_one_time
    (G : ℝ≥0 → ℝ≥0∞) (hG0 : G 0 = 1)
    (hMul : ∀ s u, G (s + u) = G s * G u)
    (hne : ∀ s, G s ≠ 0) (t : ℝ≥0) (ht : 0 < t) (hfin : G t ≠ ⊤) :
    ∀ s, G s ≠ ⊤ := by
  have hpow : ∀ n : ℕ, G (n * t) = G t ^ n := by
    intro n
    induction n with
    | zero => simp [hG0]
    | succ n ih =>
      rw [show ((n+1 : ℕ) : ℝ≥0) * t = n * t + t by push_cast; ring, hMul, ih, pow_succ]
  intro s hs
  obtain ⟨n, hn⟩ := exists_nat_ge (s / t)
  have hsn : s ≤ n * t := (div_le_iff₀ ht).mp hn
  have h := hMul s (n * t - s)
  rw [add_tsub_cancel_of_le hsn, hs, ENNReal.top_mul (hne _), hpow] at h
  exact ENNReal.pow_ne_top hfin h

private theorem source_moment_right_fatou
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    (X : ℝ≥0 → Ω → ℝ) (hX : IsLevyProcess X P)
    (θ : ℝ) (s : ℝ≥0) (sn : ℕ → ℝ≥0)
    (hge : ∀ n, s ≤ sn n) (ht : Tendsto sn atTop (nhds s)) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp (θ * X s ω)) ∂P) ≤
      Filter.liminf (fun n => ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * X (sn n) ω)) ∂P) atTop := by
  let f : ℝ → ℝ≥0∞ := fun z => ENNReal.ofReal (Real.exp (θ * z))
  have hreal : Continuous (fun z : ℝ => Real.exp (θ * z)) := by fun_prop
  have hc : Continuous f := ENNReal.continuous_ofReal.comp hreal
  have hwithin : Tendsto sn atTop (nhdsWithin s (Ici s)) :=
    tendsto_nhdsWithin_iff.2 ⟨ht, Eventually.of_forall hge⟩
  have hlim : (fun ω => Filter.liminf (fun n => f (X (sn n) ω)) atTop)
      =ᵐ[P] fun ω => f (X s ω) := by
    filter_upwards [hX.cadlag_ae] with ω hcad
    exact ((hc.tendsto _).comp (((hcad s).1).tendsto.comp hwithin)).liminf_eq
  calc
    (∫⁻ ω, f (X s ω) ∂P) =
        ∫⁻ ω, Filter.liminf (fun n => f (X (sn n) ω)) atTop ∂P :=
      lintegral_congr_ae hlim.symm
    _ ≤ _ := lintegral_liminf_le' (fun n =>
      hc.measurable.comp_aemeasurable (source_marginal_aemeasurable X hX (sn n)))

theorem solution
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (D : SpectrallyNegativeModel Ω P) (t : ℝ≥0) (ht : 0 < t) (c : ℝ)
    (hint : Integrable (fun ω => Real.exp (c * D.X t ω)) P) :
    0 < (∫ ω, Real.exp (c * D.X t ω) ∂P) ∧
      Real.log (∫ ω, Real.exp (c * D.X 1 ω) ∂P) =
        Real.log (∫ ω, Real.exp (c * D.X t ω) ∂P) / (t : ℝ) := by
  let G : ℝ≥0 → ℝ≥0∞ := fun s => ∫⁻ ω, ENNReal.ofReal (Real.exp (c * D.X s ω)) ∂P
  have hmeas (s : ℝ≥0) : AEMeasurable (fun ω => Real.exp (c * D.X s ω)) P :=
    Real.measurable_exp.comp_aemeasurable
      (aemeasurable_const.mul (source_marginal_aemeasurable D.X D.levy s))
  have hne (s : ℝ≥0) : G s ≠ 0 := by
    intro hs
    obtain ⟨ω, hω⟩ := ((lintegral_eq_zero_iff' (ENNReal.measurable_ofReal.comp_aemeasurable
      (hmeas s))).1 hs).exists
    exact (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne' hω
  have hG0 : G 0 = 1 := by simp [G, D.levy.start_zero]
  have hMul := source_extended_moment_mul D.X D.levy c
  have hfin := extended_moment_finite_of_one_time G hG0 hMul hne t ht hint.lintegral_lt_top.ne
  have hReal (s : ℝ≥0) :
      (∫ ω, Real.exp (c * D.X s ω) ∂P) = (G s).toReal :=
    integral_eq_lintegral_of_nonneg_ae
      (Eventually.of_forall fun ω => (Real.exp_pos _).le) (hmeas s).aestronglyMeasurable
  refine ⟨by rw [hReal t]; exact ENNReal.toReal_pos (hne t) (hfin t), ?_⟩
  have he := source_result81_scalar_moment_exp G hG0 hMul hne hfin
    (source_moment_right_fatou D.X D.levy c) t
  rw [hReal 1, hReal t, he, Real.log_exp]
  exact (eq_div_iff (show (t : ℝ) ≠ 0 by exact_mod_cast ht.ne')).2 (mul_comm _ _)
