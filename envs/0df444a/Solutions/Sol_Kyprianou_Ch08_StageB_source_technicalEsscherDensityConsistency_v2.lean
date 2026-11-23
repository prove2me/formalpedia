-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_technicalEsscherDensityConsistency_v2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T14:37:32.540109+00:00
-- url     : https://prove2.me/submissions/9c538d23-75fd-4bb6-91cf-791572bd59a2

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_ProbabilityTheory_IsLevyProcess_indepFun_increment
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
open Kyprianou.Ch08 Kyprianou.Ch08.StageB

private theorem marginal_aemeasurable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (X : ℝ≥0 → Ω → ℝ) (hX : IsLevyProcess X P) (t : ℝ≥0) : AEMeasurable (X t) P := by
  have hi := (hX.stationary_increments 0 t).aemeasurable_snd
  simpa only [hX.start_zero, sub_zero] using (show AEMeasurable (fun ω => X t ω - X 0 ω) P from hi)

private theorem extended_moment_mul {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (X : ℝ≥0 → Ω → ℝ) (hX : IsLevyProcess X P) (θ : ℝ) (s u : ℝ≥0) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp (θ * X (s + u) ω)) ∂P) =
      (∫⁻ ω, ENNReal.ofReal (Real.exp (θ * X s ω)) ∂P) *
        (∫⁻ ω, ENNReal.ofReal (Real.exp (θ * X u ω)) ∂P) := by
  let f : ℝ → ℝ≥0∞ := fun z => ENNReal.ofReal (Real.exp (θ * z))
  have hf : Measurable f := by fun_prop
  have hind := hX.indepFun_increment (s := 0) (t := s) (u := s + u) (by positivity) le_self_add
  change IndepFun (fun ω => X s ω - X 0 ω) (fun ω => X (s + u) ω - X s ω) P at hind
  simp only [hX.start_zero, sub_zero] at hind
  have hs := marginal_aemeasurable X hX s
  have hpow (ω : Ω) : f (X (s + u) ω) = f (X s ω) * f (X (s + u) ω - X s ω) := by
    dsimp [f]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2 <;> ring
  have heq := ((hX.stationary_increments s u).comp hf).lintegral_eq
  change (∫⁻ ω, f (X (s + u) ω - X s ω) ∂P) = (∫⁻ ω, f (X u ω - X 0 ω) ∂P) at heq
  simp only [hX.start_zero, sub_zero] at heq
  change (∫⁻ ω, f (X (s + u) ω) ∂P) = (∫⁻ ω, f (X s ω) ∂P) * ∫⁻ ω, f (X u ω) ∂P
  simp_rw [hpow]
  rw [← heq]
  exact lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun'
    (hf.comp_aemeasurable hs) (hf.comp_aemeasurable ((marginal_aemeasurable X hX (s + u)).sub hs)) (hind.comp hf hf)

private theorem finite_of_one_time (G : ℝ≥0 → ℝ≥0∞) (hG0 : G 0 = 1)
    (hMul : ∀ s u, G (s + u) = G s * G u) (hne : ∀ s, G s ≠ 0)
    (t : ℝ≥0) (ht : 0 < t) (hfin : G t ≠ ⊤) : ∀ s, G s ≠ ⊤ := by
  have hpow : ∀ n : ℕ, G (n * t) = G t ^ n := by
    intro n; induction n with
    | zero => simp [hG0]
    | succ n ih =>
      rw [show ((n + 1 : ℕ) : ℝ≥0) * t = n * t + t by push_cast; ring, hMul, ih, pow_succ]
  intro s hs
  obtain ⟨n, hn⟩ := exists_nat_ge (s / t)
  have hsn : s ≤ n * t := (div_le_iff₀ ht).mp hn
  have h := hMul s (n * t - s)
  rw [add_tsub_cancel_of_le hsn, hs, ENNReal.top_mul (hne _), hpow] at h
  exact ENNReal.pow_ne_top hfin h

private theorem exp_integrable_all_times {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (D : SpectrallyNegativeModel Ω P) (c : ℝ)
    (hc1 : Integrable (fun ω => Real.exp (c * D.X 1 ω)) P) :
    ∀ t : ℝ≥0, Integrable (fun ω => Real.exp (c * D.X t ω)) P := by
  let G : ℝ≥0 → ℝ≥0∞ := fun s => ∫⁻ ω, ENNReal.ofReal (Real.exp (c * D.X s ω)) ∂P
  have hmeas (s : ℝ≥0) : AEMeasurable (fun ω => Real.exp (c * D.X s ω)) P :=
    Real.measurable_exp.comp_aemeasurable (aemeasurable_const.mul (marginal_aemeasurable D.X D.levy s))
  have hne (s : ℝ≥0) : G s ≠ 0 := by
    intro hs
    obtain ⟨ω, hω⟩ := ((lintegral_eq_zero_iff' (ENNReal.measurable_ofReal.comp_aemeasurable (hmeas s))).1 hs).exists
    exact (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne' hω
  have hfin : ∀ s, G s ≠ ⊤ := finite_of_one_time G (by simp [G, D.levy.start_zero])
    (extended_moment_mul D.X D.levy c) hne 1 (by norm_num) hc1.lintegral_lt_top.ne
  intro t
  exact (lintegral_ofReal_ne_top_iff_integrable (hmeas t).aestronglyMeasurable
    (Eventually.of_forall fun ω => (Real.exp_pos _).le)).mp (hfin t)

private theorem time_consequence {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ) (c : ℝ)
    (hfull : IsFullMomentLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
    (t : ℝ≥0) (ht : 0 < t) (hbase : Integrable (fun ω => Real.exp (c * D.X t ω)) P) :
    Integrable (fun ω => Real.exp (c * D.X t ω - ψ c * (t : ℝ))) P ∧
    (∀ ω, 0 < Real.exp (c * D.X t ω - ψ c * (t : ℝ))) ∧
    (∫ ω, Real.exp (c * D.X t ω - ψ c * (t : ℝ)) ∂P) = 1 := by
  have hm := hfull.2 c t ht (by simpa [SpectrallyNegativeModel.toData] using hbase)
  have hpos : 0 < ∫ ω, Real.exp (c * D.X t ω) ∂P := by simpa [SpectrallyNegativeModel.toData] using hm.1
  have hpsi : ψ c = Real.log (∫ ω, Real.exp (c * D.X t ω) ∂P) / (t : ℝ) := by simpa [SpectrallyNegativeModel.toData] using hm.2
  have hfac (ω : Ω) : Real.exp (c * D.X t ω - ψ c * (t : ℝ)) =
      Real.exp (-(ψ c * (t : ℝ))) * Real.exp (c * D.X t ω) := by
    rw [← Real.exp_add]
    congr 1 <;> ring
  have hshift : Integrable (fun ω => Real.exp (c * D.X t ω - ψ c * (t : ℝ))) P :=
    (hbase.const_mul (Real.exp (-(ψ c * (t : ℝ))))).congr (Eventually.of_forall fun ω => (hfac ω).symm)
  have hlog : ψ c * (t : ℝ) = Real.log (∫ ω, Real.exp (c * D.X t ω) ∂P) := by
    rw [hpsi, div_mul_cancel₀]; exact_mod_cast ht.ne'
  refine ⟨hshift, (fun ω => Real.exp_pos _), ?_⟩
  calc
    (∫ ω, Real.exp (c * D.X t ω - ψ c * (t : ℝ)) ∂P) =
        Real.exp (-(ψ c * (t : ℝ))) * (∫ ω, Real.exp (c * D.X t ω) ∂P) := by
          rw [integral_congr_ae (Eventually.of_forall hfac), integral_const_mul]
    _ = 1 := by
      rw [hlog, Real.exp_neg, Real.exp_log hpos, inv_mul_cancel₀ (ne_of_gt hpos)]

private theorem conclude {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ) (c : ℝ)
    (hfull : IsFullMomentLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
    (hc1 : Integrable (fun ω => Real.exp (c * D.X 1 ω)) P)
    (hint : ∀ t : ℝ≥0, Integrable (fun ω => Real.exp (c * D.X t ω)) P) :
    HasLawfulEsscherDensities (SpectrallyNegativeModel.toData P D) ψ c := by
  constructor
  · exact ⟨by simpa [SpectrallyNegativeModel.toData] using hfull,
      by simpa [SpectrallyNegativeModel.toData] using hc1,
      by simpa [SpectrallyNegativeModel.toData] using
        (hfull.2 c 1 (by norm_num) (by simpa [SpectrallyNegativeModel.toData] using hint 1)).1⟩
  · intro t ht
    have h := time_consequence (P := P) D ψ c hfull t ht (hint t)
    exact ⟨by simpa [SpectrallyNegativeModel.toData] using hint t,
      by simpa [SpectrallyNegativeModel.toData] using h.1, h.2.1, h.2.2⟩

theorem solution : Kyprianou.Ch08.StageB.technicalEsscherDensityConsistency := by
  intro Ω mΩ P hP D ψ c hfull hc1
  exact conclude (P := P) D ψ c hfull hc1 (exp_integrable_all_times (P := P) D c hc1)
