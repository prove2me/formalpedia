-- Prove2me | solution 1 for Kyprianou.Ch02.prmCampbellIdentityImpliesUniformL2V1
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-23T19:13:39.289638+00:00
-- url     : https://prove2.me/submissions/96e7baf5-825c-4e2d-b215-6dec60871bdd

import Mathlib
import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_LeanLevy_Processes_LevyProcess

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

set_option autoImplicit false

private lemma eLpNorm_two_eq_ofReal_integral_sq {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {g : α → ℝ} (hg : Integrable (fun x => (g x) ^ 2) μ) :
    eLpNorm g 2 μ = (ENNReal.ofReal (∫ x, (g x) ^ 2 ∂μ)) ^ (1 / (2 : ℝ)) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) ENNReal.ofNat_ne_top]
  have h2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  rw [h2]
  have hpoint : (fun x => ‖g x‖ₑ ^ (2 : ℝ)) = fun x => ENNReal.ofReal ((g x) ^ 2) := by
    funext x
    rw [Real.enorm_eq_ofReal_abs, ENNReal.rpow_two, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
  rw [hpoint, ← ofReal_integral_eq_lintegral_ofReal hg (Eventually.of_forall fun _ => sq_nonneg _)]

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (_hB : MeasurableSet B) (hfinite : ν B < ⊤)
    (hsecond : MemLp (fun x : ℝ => x) 2 (ν.restrict B))
    (f : ℕ → SimpleFunc ℝ ℝ)
    (hfL2 : Filter.Tendsto
      (fun n => eLpNorm (fun x : ℝ => (f n) x - x) 2 (ν.restrict B))
      Filter.atTop (nhds 0))
    (hrawL2 : ∀ t : ℝ≥0, ∀ n,
      MemLp (fun ω =>
        ∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B),
          (f n) z.2 ∂(N.N ω)) 2 P)
    (hCampbell : ∀ (n : ℕ) (t : ℝ≥0),
      (∫ ω, (∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B),
        (f n) z.2 ∂(N.N ω)) ^ 2 ∂P) =
        (t : ℝ) * (∫ x in B, ((f n) x) ^ 2 ∂ν) +
          ((t : ℝ) * (∫ x in B, (f n) x ∂ν)) ^ 2) :
    ∀ t : ℝ≥0, Filter.liminf
      (fun n => eLpNorm
        (fun ω => ∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B),
          (f n) z.2 ∂(N.N ω)) 2 P)
      Filter.atTop < ⊤ := by
  intro t
  let μB : Measure ℝ := ν.restrict B
  have hμB_fin : IsFiniteMeasure μB := ⟨by rw [Measure.restrict_apply_univ]; exact hfinite⟩
  have hev_diff : ∀ᶠ n in atTop, eLpNorm (fun x : ℝ => (f n) x - x) 2 μB ≤ 1 := by
    have hlt : ∀ᶠ n in atTop, eLpNorm (fun x : ℝ => (f n) x - x) 2 μB < 1 :=
      hfL2.eventually (Iio_mem_nhds zero_lt_one)
    exact hlt.mono fun _ h => le_of_lt h
  let K_enn : ℝ≥0∞ := 1 + eLpNorm (fun x : ℝ => x) 2 μB
  have hK_ne_top : K_enn ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨ENNReal.one_ne_top, hsecond.eLpNorm_lt_top.ne⟩
  let K : ℝ := K_enn.toReal
  have hK_nn : 0 ≤ K := ENNReal.toReal_nonneg
  have hK_ofReal : ENNReal.ofReal K = K_enn := ENNReal.ofReal_toReal hK_ne_top
  let C : ℝ := (t : ℝ) * K ^ 2 + ((t : ℝ) * ((ν B).toReal + K ^ 2)) ^ 2
  have hC_nn : 0 ≤ C := by
    have ht : 0 ≤ (t : ℝ) := t.coe_nonneg
    positivity
  let M : ℝ≥0∞ := (ENNReal.ofReal C) ^ (1 / (2 : ℝ))
  have hM_lt_top : M < ⊤ := ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
  have hev_bound : ∀ᶠ n in atTop,
      eLpNorm (fun ω => ∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B), (f n) z.2 ∂(N.N ω)) 2 P ≤ M := by
    filter_upwards [hev_diff] with n hdiff
    have hfn_bound : ∃ R : ℝ, ∀ x : ℝ, |(f n) x| ≤ R := by
      by_cases hne : (f n).range.Nonempty
      · refine ⟨(f n).range.sup' hne (fun r => |r|), fun x => ?_⟩
        exact Finset.le_sup' (fun r => |r|) ((f n).mem_range_self x)
      · refine ⟨0, fun x => absurd ⟨(f n) x, (f n).mem_range_self x⟩ hne⟩
    obtain ⟨R, hR⟩ := hfn_bound
    have hfn_int : Integrable (fun x : ℝ => (f n) x) μB :=
      Integrable.of_bound (f n).measurable.aestronglyMeasurable R
        (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hR x)
    have hfn_sq_int : Integrable (fun x : ℝ => ((f n) x) ^ 2) μB :=
      Integrable.of_bound ((continuous_pow 2).measurable.comp (f n).measurable).aestronglyMeasurable (R ^ 2)
        (Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (hR x) 2)
    have hfn_eLp : eLpNorm (fun x : ℝ => (f n) x) 2 μB ≤ ENNReal.ofReal K := by
      have hsplit : (fun x : ℝ => (f n) x) = (fun x : ℝ => (f n) x - x) + (fun x : ℝ => x) := by
        funext x; simp
      rw [hsplit, hK_ofReal]
      have htri := eLpNorm_add_le
        ((f n).measurable.aestronglyMeasurable.sub hsecond.aestronglyMeasurable)
        hsecond.aestronglyMeasurable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      exact le_trans htri (add_le_add hdiff le_rfl)
    have hsq_le : (∫ x in B, ((f n) x) ^ 2 ∂ν) ≤ K ^ 2 := by
      have hnorm_eq := eLpNorm_two_eq_ofReal_integral_sq hfn_sq_int
      have hpow_le : (eLpNorm (fun x : ℝ => (f n) x) 2 μB) ^ (2 : ℝ) ≤ (ENNReal.ofReal K) ^ (2 : ℝ) :=
        ENNReal.rpow_le_rpow hfn_eLp (by norm_num)
      rw [hnorm_eq, ← ENNReal.rpow_mul, one_div_mul_cancel (by norm_num : (2 : ℝ) ≠ 0),
        ENNReal.rpow_one, ENNReal.rpow_two, ← ENNReal.ofReal_pow hK_nn] at hpow_le
      exact (ENNReal.ofReal_le_ofReal_iff (sq_nonneg K)).mp hpow_le
    have hl1_le : |∫ x in B, (f n) x ∂ν| ≤ (ν B).toReal + K ^ 2 := by
      have h1 : |∫ x in B, (f n) x ∂ν| ≤ ∫ x in B, |(f n) x| ∂ν := by
        simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (f := fun x => (f n) x) (μ := μB)
      have h2 : ∫ x in B, |(f n) x| ∂ν ≤ ∫ x in B, (1 + ((f n) x) ^ 2) ∂ν := by
        refine integral_mono hfn_int.abs ((integrable_const (1 : ℝ)).add hfn_sq_int) fun x => ?_
        have : 0 ≤ (|(f n) x| - 1) ^ 2 := sq_nonneg _
        nlinarith [sq_abs ((f n) x)]
      have h3 : ∫ x in B, (1 + ((f n) x) ^ 2) ∂ν = (ν B).toReal + ∫ x in B, ((f n) x) ^ 2 ∂ν := by
        rw [integral_add (integrable_const (1 : ℝ)) hfn_sq_int, integral_const, smul_eq_mul, mul_one,
          Measure.real, Measure.restrict_apply_univ]
      linarith
    have hcamp_le : (∫ ω, (∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B), (f n) z.2 ∂(N.N ω)) ^ 2 ∂P) ≤ C := by
      rw [hCampbell n t]
      have ht : 0 ≤ (t : ℝ) := t.coe_nonneg
      have hterm1 : (t : ℝ) * (∫ x in B, ((f n) x) ^ 2 ∂ν) ≤ (t : ℝ) * K ^ 2 :=
        mul_le_mul_of_nonneg_left hsq_le ht
      have hterm2 : ((t : ℝ) * (∫ x in B, (f n) x ∂ν)) ^ 2 ≤ ((t : ℝ) * ((ν B).toReal + K ^ 2)) ^ 2 := by
        rw [← sq_abs ((t : ℝ) * (∫ x in B, (f n) x ∂ν)), abs_mul, abs_of_nonneg ht]
        exact pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hl1_le ht) 2
      dsimp [C]
      linarith
    have hY_sq_int : Integrable (fun ω => (∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B), (f n) z.2 ∂(N.N ω)) ^ 2) P :=
      (memLp_two_iff_integrable_sq (hrawL2 t n).aestronglyMeasurable).mp (hrawL2 t n)
    rw [eLpNorm_two_eq_ofReal_integral_sq hY_sq_int]
    exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hcamp_le) (by norm_num)
  exact lt_of_le_of_lt (Filter.liminf_le_of_frequently_le' hev_bound.frequently) hM_lt_top
