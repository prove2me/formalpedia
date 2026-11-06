-- Prove2me | solution 1 for LinParamBandits.UEFinite.ue_regret_bound_finite
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T20:29:11.494314+00:00
-- url     : https://prove2.me/submissions/556b4152-95ec-41e2-8464-5779475e3202
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LinParamBandits_UEFinite_Model
import Definitions.Def_LinParamBandits_UEFinite_UEPolicy
import Theorems.Thm_LinParamBandits_UEFinite_pull_count_bound
import Theorems.Thm_LinParamBandits_UEFinite_regret_eq_sum_gap_pulls
import Theorems.Thm_LinParamBandits_UEFinite_gap_min_expectation_bound

open MeasureTheory ProbabilityTheory

namespace UEFinGoalAux

open LinParamBandits.UEFinite

variable {r : ℕ}

/-- The extension map, with the parameter `z` as an extra input, is jointly measurable. -/
lemma measurable_stepZ (ψ : LinParamBandits.UEGeneral.Policy r) (n : ℕ) :
    Measurable (fun q : LinParamBandits.LowerBound.Vec r × (LinParamBandits.LowerBound.History r n × ℝ) =>
      Fin.snoc (α := fun _ => LinParamBandits.LowerBound.Vec r × ℝ) q.2.1
        (ψ.act n q.2.1, inner ℝ (ψ.act n q.2.1) q.1 + q.2.2)) := by
  rw [measurable_pi_iff]
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.snoc_last]
    have ha : Measurable (fun q : LinParamBandits.LowerBound.Vec r ×
        (LinParamBandits.LowerBound.History r n × ℝ) => ψ.act n q.2.1) :=
      (ψ.measurable_act n).comp (measurable_fst.comp measurable_snd)
    refine ha.prodMk ?_
    exact (Measurable.inner ha measurable_fst).add (measurable_snd.comp measurable_snd)
  · simp only [Fin.snoc_castSucc]
    exact (measurable_pi_apply j).comp (measurable_fst.comp measurable_snd)

lemma measurable_step (ψ : LinParamBandits.UEGeneral.Policy r) (z : LinParamBandits.LowerBound.Vec r) (n : ℕ) :
    Measurable (fun p : LinParamBandits.LowerBound.History r n × ℝ =>
      Fin.snoc (α := fun _ => LinParamBandits.LowerBound.Vec r × ℝ) p.1
        (ψ.act n p.1, inner ℝ (ψ.act n p.1) z + p.2)) :=
  (measurable_stepZ ψ n).comp (measurable_const.prodMk measurable_id)

lemma isProb_histMeasure (ν : Kernel (LinParamBandits.LowerBound.Vec r) ℝ) [IsMarkovKernel ν]
    (z : LinParamBandits.LowerBound.Vec r) (ψ : LinParamBandits.UEGeneral.Policy r) :
    ∀ n, IsProbabilityMeasure (LinParamBandits.UEGeneral.histMeasure ν z ψ n)
  | 0 => by
      simp only [LinParamBandits.UEGeneral.histMeasure]; infer_instance
  | n + 1 => by
      have := isProb_histMeasure ν z ψ n
      simp only [LinParamBandits.UEGeneral.histMeasure]
      exact Measure.isProbabilityMeasure_map (measurable_step ψ z n).aemeasurable

/-- The history law depends measurably on the parameter: it is a Markov kernel in `z`. -/
lemma exists_kernel (ν : Kernel (LinParamBandits.LowerBound.Vec r) ℝ) [IsMarkovKernel ν]
    (ψ : LinParamBandits.UEGeneral.Policy r) :
    ∀ n, ∃ K : Kernel (LinParamBandits.LowerBound.Vec r) (LinParamBandits.LowerBound.History r n),
      IsMarkovKernel K ∧ ∀ z, K z = LinParamBandits.UEGeneral.histMeasure ν z ψ n
  | 0 => ⟨Kernel.const _ (Measure.dirac (Fin.elim0 : LinParamBandits.LowerBound.History r 0)),
      inferInstance, fun z => by simp [LinParamBandits.UEGeneral.histMeasure]⟩
  | n + 1 => by
      obtain ⟨K, hK, hKz⟩ := exists_kernel ν ψ n
      let η : Kernel (LinParamBandits.LowerBound.Vec r × LinParamBandits.LowerBound.History r n) ℝ :=
        ν.comap (fun p => ψ.act n p.2) ((ψ.measurable_act n).comp measurable_snd)
      let C := K ⊗ₖ η
      let D := (Kernel.deterministic (fun z : LinParamBandits.LowerBound.Vec r => z) measurable_id) ×ₖ C
      refine ⟨D.map (fun q : LinParamBandits.LowerBound.Vec r × (LinParamBandits.LowerBound.History r n × ℝ) =>
          Fin.snoc (α := fun _ => LinParamBandits.LowerBound.Vec r × ℝ) q.2.1
            (ψ.act n q.2.1, inner ℝ (ψ.act n q.2.1) q.1 + q.2.2)),
        Kernel.IsMarkovKernel.map _ (measurable_stepZ ψ n), fun z => ?_⟩
      rw [Kernel.map_apply _ (measurable_stepZ ψ n), Kernel.prod_apply, Kernel.deterministic_apply,
        Measure.dirac_prod, Measure.map_map (measurable_stepZ ψ n) measurable_prodMk_left]
      have hC : C z = (LinParamBandits.UEGeneral.histMeasure ν z ψ n) ⊗ₘ
          (ν.comap (ψ.act n) (ψ.measurable_act n)) := by
        simp only [C]
        rw [Kernel.compProd_apply_eq_compProd_sectR, hKz]
        congr 1
      rw [hC]
      simp only [LinParamBandits.UEGeneral.histMeasure]
      rfl

lemma bestValue_ge (𝒰 : Set (LinParamBandits.LowerBound.Vec r)) (h𝒰fin : 𝒰.Finite)
    (u : LinParamBandits.LowerBound.Vec r) (hu : u ∈ 𝒰) (z : LinParamBandits.LowerBound.Vec r) :
    inner ℝ u z ≤ LinParamBandits.UEGeneral.bestValue 𝒰 z :=
  le_csSup (h𝒰fin.image _).bddAbove ⟨u, hu, rfl⟩

lemma bestValue_le (𝒰 : Set (LinParamBandits.LowerBound.Vec r)) (h𝒰ne : 𝒰.Nonempty) (ū : ℝ)
    (hnorm : ∀ u ∈ 𝒰, ‖u‖ ≤ ū) (z : LinParamBandits.LowerBound.Vec r) :
    LinParamBandits.UEGeneral.bestValue 𝒰 z ≤ ū * ‖z‖ := by
  unfold LinParamBandits.UEGeneral.bestValue
  apply csSup_le (h𝒰ne.image _)
  rintro _ ⟨v, hv, rfl⟩
  calc inner ℝ v z ≤ ‖v‖ * ‖z‖ := real_inner_le_norm v z
    _ ≤ ū * ‖z‖ := by gcongr; exact hnorm v hv

lemma gap_nonneg (𝒰 : Set (LinParamBandits.LowerBound.Vec r)) (h𝒰fin : 𝒰.Finite)
    (u : LinParamBandits.LowerBound.Vec r) (hu : u ∈ 𝒰) (z : LinParamBandits.LowerBound.Vec r) :
    0 ≤ gap 𝒰 u z := by
  have := bestValue_ge 𝒰 h𝒰fin u hu z
  unfold gap; linarith

lemma gap_le (𝒰 : Set (LinParamBandits.LowerBound.Vec r)) (h𝒰ne : 𝒰.Nonempty) (ū : ℝ)
    (hnorm : ∀ u ∈ 𝒰, ‖u‖ ≤ ū) (u : LinParamBandits.LowerBound.Vec r) (hu : u ∈ 𝒰)
    (z : LinParamBandits.LowerBound.Vec r) :
    gap 𝒰 u z ≤ 2 * ū * ‖z‖ := by
  have h1 := bestValue_le 𝒰 h𝒰ne ū hnorm z
  have h2 : -inner ℝ u z ≤ ū * ‖z‖ := by
    calc -inner ℝ u z ≤ |inner ℝ u z| := neg_le_abs _
      _ ≤ ‖u‖ * ‖z‖ := abs_real_inner_le_norm u z
      _ ≤ ū * ‖z‖ := by gcongr; exact hnorm u hu
  unfold gap; linarith

lemma bestValue_eq_sup' (𝒰 : Set (LinParamBandits.LowerBound.Vec r)) (h𝒰fin : 𝒰.Finite)
    (h𝒰ne : 𝒰.Nonempty) (z : LinParamBandits.LowerBound.Vec r) :
    LinParamBandits.UEGeneral.bestValue 𝒰 z =
      h𝒰fin.toFinset.sup' (by simpa using h𝒰ne) (fun v => inner ℝ v z) := by
  rw [Finset.sup'_eq_csSup_image, Set.Finite.coe_toFinset]
  rfl

lemma continuous_bestValue (𝒰 : Set (LinParamBandits.LowerBound.Vec r)) (h𝒰fin : 𝒰.Finite)
    (h𝒰ne : 𝒰.Nonempty) :
    Continuous (fun z => LinParamBandits.UEGeneral.bestValue 𝒰 z) := by
  have : (fun z => LinParamBandits.UEGeneral.bestValue 𝒰 z) = fun z =>
      h𝒰fin.toFinset.sup' (by simpa using h𝒰ne) (fun v => inner ℝ v z) := by
    funext z; rw [bestValue_eq_sup' 𝒰 h𝒰fin h𝒰ne]
  rw [this]
  exact Continuous.finset_sup'_apply _ (fun v _ => by fun_prop)

lemma pullCount_le (u : LinParamBandits.LowerBound.Vec r) {n : ℕ}
    (h : LinParamBandits.LowerBound.History r n) : pullCount u h ≤ n := by
  classical
  simp only [pullCount]
  exact (Finset.card_filter_le _ _).trans (by simp)

lemma expected_pull_le (ν : Kernel (LinParamBandits.LowerBound.Vec r) ℝ) [IsMarkovKernel ν]
    (z : LinParamBandits.LowerBound.Vec r) (ψ : LinParamBandits.UEGeneral.Policy r)
    (u : LinParamBandits.LowerBound.Vec r) (T : ℕ) :
    ∫ h, (pullCount u h : ℝ) ∂(LinParamBandits.UEGeneral.histMeasure ν z ψ T) ≤ T := by
  have := isProb_histMeasure ν z ψ T
  have h := norm_integral_le_of_norm_le_const (μ := LinParamBandits.UEGeneral.histMeasure ν z ψ T)
    (C := (T : ℝ)) (f := fun h => (pullCount u h : ℝ)) (Filter.Eventually.of_forall (fun h => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; exact_mod_cast pullCount_le u h))
  rw [probReal_univ, mul_one] at h
  exact (le_abs_self _).trans h

/-- The per-arm bound `Δ E[N] ≤ 6Δ + max(4α²|𝒰|, 1) min{log T/Δ, TΔ}`. -/
lemma term_bound (g E T L K a ū nz : ℝ) (hg : 0 ≤ g) (hE0 : E ≤ T)
    (hE1 : 0 < g → E ≤ 6 + K * L / g ^ 2) (hK : K ≤ a) (ha : 1 ≤ a) (hL : 0 ≤ L) (hT : 0 ≤ T)
    (hgle : g ≤ 2 * ū * nz) (hnz : 0 ≤ nz) (hū : 0 < ū) :
    g * E ≤ 12 * ū * nz + a * min (L / g) (T * g) := by
  rcases hg.lt_or_eq with hg | hg
  · have hE1 := hE1 hg
    rcases le_total (L / g) (T * g) with hm | hm
    · rw [min_eq_left hm]
      have h1 : g * E ≤ g * (6 + K * L / g ^ 2) := mul_le_mul_of_nonneg_left hE1 hg.le
      have h2 : g * (6 + K * L / g ^ 2) = 6 * g + K * (L / g) := by field_simp
      have h3 : K * (L / g) ≤ a * (L / g) := mul_le_mul_of_nonneg_right hK (div_nonneg hL hg.le)
      nlinarith
    · rw [min_eq_right hm]
      have h1 : g * E ≤ g * T := mul_le_mul_of_nonneg_left hE0 hg.le
      have h2 : T * g ≤ a * (T * g) := le_mul_of_one_le_left (mul_nonneg hT hg.le) ha
      nlinarith
  · subst hg
    simp only [div_zero, mul_zero, min_self, zero_mul]
    positivity

end UEFinGoalAux

open UEFinGoalAux in
theorem solution :
    (∀ σ₀ ū lam₀ : ℝ, 0 < σ₀ → 0 < ū → 0 < lam₀ →
      ∃ a₆ a₇ : ℝ, 0 < a₆ ∧ 0 < a₇ ∧
        ∀ (r : ℕ), 2 ≤ r → ∀ (𝒰 : Set (LinParamBandits.LowerBound.Vec r)) (h𝒰fin : 𝒰.Finite), 𝒰.Nonempty →
        ∀ (ν : Kernel (LinParamBandits.LowerBound.Vec r) ℝ), IsMarkovKernel ν → LinParamBandits.UEFinite.NoiseAssumption 𝒰 ν σ₀ →
        ∀ (b : Fin r → LinParamBandits.LowerBound.Vec r), LinParamBandits.UEFinite.ArmAssumption 𝒰 b ū lam₀ →
        ∀ (ψ : LinParamBandits.UEGeneral.Policy r), LinParamBandits.UEFinite.IsUE 𝒰 b σ₀ ū lam₀ ψ →
        ∀ (T : ℕ), r + 1 ≤ T → ∀ z : LinParamBandits.LowerBound.Vec r,
          LinParamBandits.UEFinite.Regret 𝒰 ν ψ z T ≤
            a₆ * (𝒰.ncard : ℝ) * ‖z‖ +
              a₇ * (𝒰.ncard : ℝ) *
                ∑ u ∈ h𝒰fin.toFinset, min (Real.log T / LinParamBandits.UEFinite.gap 𝒰 u z) (T * LinParamBandits.UEFinite.gap 𝒰 u z)) ∧
    (∀ σ₀ ū lam₀ M₀ : ℝ, 0 < σ₀ → 0 < ū → 0 < lam₀ → 0 < M₀ →
      ∃ a₈ a₉ : ℝ, 0 < a₈ ∧ 0 < a₉ ∧
        ∀ (r : ℕ), 2 ≤ r → ∀ (𝒰 : Set (LinParamBandits.LowerBound.Vec r)), 𝒰.Finite → 𝒰.Nonempty →
        ∀ (ν : Kernel (LinParamBandits.LowerBound.Vec r) ℝ), IsMarkovKernel ν → LinParamBandits.UEFinite.NoiseAssumption 𝒰 ν σ₀ →
        ∀ (b : Fin r → LinParamBandits.LowerBound.Vec r), LinParamBandits.UEFinite.ArmAssumption 𝒰 b ū lam₀ →
        ∀ (ψ : LinParamBandits.UEGeneral.Policy r), LinParamBandits.UEFinite.IsUE 𝒰 b σ₀ ū lam₀ ψ →
        ∀ (μ : Measure (LinParamBandits.LowerBound.Vec r)), IsProbabilityMeasure μ →
          (∫⁻ z, (‖z‖₊ : ENNReal) ∂μ) < ⊤ → (∀ u ∈ 𝒰, LinParamBandits.UEFinite.GapDensityLe 𝒰 μ M₀ u) →
        ∀ (T : ℕ), r + 1 ≤ T →
          Integrable (fun z => LinParamBandits.UEFinite.Regret 𝒰 ν ψ z T) μ ∧
          LinParamBandits.UEFinite.Risk 𝒰 ν ψ μ T ≤
            a₈ * (𝒰.ncard : ℝ) * ∫ z, ‖z‖ ∂μ + a₉ * (𝒰.ncard : ℝ) ^ 2 * Real.log T ^ 2) := by
  -- Part 1: the regret bound, with a₆ = 12 ū and a₇ = 4 α² + 1.
  have part1 : ∀ σ₀ ū lam₀ : ℝ, 0 < σ₀ → 0 < ū → 0 < lam₀ →
      ∀ (r : ℕ), 2 ≤ r → ∀ (𝒰 : Set (LinParamBandits.LowerBound.Vec r)) (h𝒰fin : 𝒰.Finite), 𝒰.Nonempty →
        ∀ (ν : Kernel (LinParamBandits.LowerBound.Vec r) ℝ), IsMarkovKernel ν → LinParamBandits.UEFinite.NoiseAssumption 𝒰 ν σ₀ →
        ∀ (b : Fin r → LinParamBandits.LowerBound.Vec r), LinParamBandits.UEFinite.ArmAssumption 𝒰 b ū lam₀ →
        ∀ (ψ : LinParamBandits.UEGeneral.Policy r), LinParamBandits.UEFinite.IsUE 𝒰 b σ₀ ū lam₀ ψ →
        ∀ (T : ℕ), r + 1 ≤ T → ∀ z : LinParamBandits.LowerBound.Vec r,
          LinParamBandits.UEFinite.Regret 𝒰 ν ψ z T ≤
            (12 * ū) * (𝒰.ncard : ℝ) * ‖z‖ +
              (4 * LinParamBandits.UEFinite.alpha σ₀ ū lam₀ ^ 2 + 1) * (𝒰.ncard : ℝ) *
                ∑ u ∈ h𝒰fin.toFinset, min (Real.log T / LinParamBandits.UEFinite.gap 𝒰 u z) (T * LinParamBandits.UEFinite.gap 𝒰 u z) := by
    intro σ₀ ū lam₀ hσ₀ hū hlam₀ r hr 𝒰 h𝒰fin h𝒰ne ν hν hnoise b harms ψ hψ T hT z
    haveI := hν
    rw [LinParamBandits.UEFinite.regret_eq_sum_gap_pulls σ₀ ū lam₀ hσ₀ hū hlam₀ r hr 𝒰 h𝒰fin h𝒰ne
      ν hν hnoise b harms ψ hψ T z]
    have hcard : (𝒰.ncard : ℝ) = (h𝒰fin.toFinset.card : ℝ) := by
      rw [Set.ncard_eq_toFinset_card 𝒰 h𝒰fin]
    have hncard1 : (1 : ℝ) ≤ 𝒰.ncard := by
      have := (Set.ncard_pos h𝒰fin).mpr h𝒰ne
      exact_mod_cast this
    have hL : 0 ≤ Real.log T := Real.log_natCast_nonneg T
    calc ∑ u ∈ h𝒰fin.toFinset, LinParamBandits.UEFinite.gap 𝒰 u z *
          ∫ h, (LinParamBandits.UEFinite.pullCount u h : ℝ) ∂(LinParamBandits.UEGeneral.histMeasure ν z ψ T)
        ≤ ∑ u ∈ h𝒰fin.toFinset, (12 * ū * ‖z‖ +
            ((4 * LinParamBandits.UEFinite.alpha σ₀ ū lam₀ ^ 2 + 1) * (𝒰.ncard : ℝ)) *
              min (Real.log T / LinParamBandits.UEFinite.gap 𝒰 u z) (T * LinParamBandits.UEFinite.gap 𝒰 u z)) := by
          apply Finset.sum_le_sum
          intro u hu
          have hu' : u ∈ 𝒰 := by simpa using hu
          apply term_bound _ _ _ _ (4 * LinParamBandits.UEFinite.alpha σ₀ ū lam₀ ^ 2 * (𝒰.ncard : ℝ))
          · exact gap_nonneg 𝒰 h𝒰fin u hu' z
          · exact expected_pull_le ν z ψ u T
          · intro hg
            have := LinParamBandits.UEFinite.pull_count_bound σ₀ ū lam₀ hσ₀ hū hlam₀ r hr 𝒰 h𝒰fin h𝒰ne
              ν hν hnoise b harms ψ hψ T hT z u hu' hg
            calc _ ≤ _ := this
              _ = _ := by ring
          · nlinarith [sq_nonneg (LinParamBandits.UEFinite.alpha σ₀ ū lam₀)]
          · nlinarith [sq_nonneg (LinParamBandits.UEFinite.alpha σ₀ ū lam₀)]
          · exact hL
          · positivity
          · exact gap_le 𝒰 h𝒰ne ū harms.1 u hu' z
          · exact norm_nonneg z
          · exact hū
      _ = _ := by
          rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum, ← hcard]
          ring
  refine ⟨?_, ?_⟩
  · intro σ₀ ū lam₀ hσ₀ hū hlam₀
    refine ⟨12 * ū, 4 * LinParamBandits.UEFinite.alpha σ₀ ū lam₀ ^ 2 + 1, by positivity, by positivity, ?_⟩
    exact part1 σ₀ ū lam₀ hσ₀ hū hlam₀
  · intro σ₀ ū lam₀ M₀ hσ₀ hū hlam₀ hM₀
    set a₇ := 4 * LinParamBandits.UEFinite.alpha σ₀ ū lam₀ ^ 2 + 1 with ha₇
    have ha₇pos : 0 < a₇ := by positivity
    refine ⟨12 * ū, a₇ * (2 * M₀ + 1), by positivity, by positivity, ?_⟩
    intro r hr 𝒰 h𝒰fin h𝒰ne ν hν hnoise b harms ψ hψ μ hμ hZ hdens T hT
    haveI := hν
    have hTpos : (3 : ℝ) ≤ T := by exact_mod_cast (show 3 ≤ T by omega)
    set L := Real.log T with hLdef
    have hL1 : 1 ≤ L := by
      rw [hLdef, Real.le_log_iff_exp_le (by linarith)]
      have := Real.exp_one_lt_d9
      linarith
    have hcard : (𝒰.ncard : ℝ) = (h𝒰fin.toFinset.card : ℝ) := by
      rw [Set.ncard_eq_toFinset_card 𝒰 h𝒰fin]
    -- the bound function
    set m : LinParamBandits.LowerBound.Vec r → LinParamBandits.LowerBound.Vec r → ℝ :=
      fun u z => min (L / LinParamBandits.UEFinite.gap 𝒰 u z) (T * LinParamBandits.UEFinite.gap 𝒰 u z) with hm
    have hmint : ∀ u ∈ h𝒰fin.toFinset, Integrable (fun z => m u z) μ ∧
        ∫ z, m u z ∂μ ≤ (M₀ + 1) * L + M₀ * L ^ 2 := by
      intro u hu
      have hu' : u ∈ 𝒰 := by simpa using hu
      exact LinParamBandits.UEFinite.gap_min_expectation_bound r hr 𝒰 h𝒰fin h𝒰ne u hu' μ hμ M₀ hM₀
        (hdens u hu') T hT
    have hnormint : Integrable (fun z : LinParamBandits.LowerBound.Vec r => ‖z‖) μ := by
      refine ⟨continuous_norm.aestronglyMeasurable, ?_⟩
      unfold HasFiniteIntegral
      simpa [enorm_norm, enorm_eq_nnnorm] using hZ
    set B : LinParamBandits.LowerBound.Vec r → ℝ := fun z =>
      (12 * ū) * (𝒰.ncard : ℝ) * ‖z‖ + a₇ * (𝒰.ncard : ℝ) * ∑ u ∈ h𝒰fin.toFinset, m u z with hB
    have hBint : Integrable B μ := by
      refine (hnormint.const_mul _).add ((integrable_finsetSum _ (fun u hu => (hmint u hu).1)).const_mul _)
    have hRle : ∀ z, LinParamBandits.UEFinite.Regret 𝒰 ν ψ z T ≤ B z := fun z =>
      part1 σ₀ ū lam₀ hσ₀ hū hlam₀ r hr 𝒰 h𝒰fin h𝒰ne ν hν hnoise b harms ψ hψ T hT z
    have hRnn : ∀ z, 0 ≤ LinParamBandits.UEFinite.Regret 𝒰 ν ψ z T := by
      intro z
      rw [LinParamBandits.UEFinite.regret_eq_sum_gap_pulls σ₀ ū lam₀ hσ₀ hū hlam₀ r hr 𝒰 h𝒰fin h𝒰ne
        ν hν hnoise b harms ψ hψ T z]
      apply Finset.sum_nonneg
      intro u hu
      have hu' : u ∈ 𝒰 := by simpa using hu
      exact mul_nonneg (gap_nonneg 𝒰 h𝒰fin u hu' z) (integral_nonneg (fun h => by positivity))
    -- measurability of the regret in z
    obtain ⟨K, hK, hKz⟩ := exists_kernel ν ψ T
    haveI := hK
    have hRmeas : StronglyMeasurable (fun z => LinParamBandits.UEFinite.Regret 𝒰 ν ψ z T) := by
      have heq : (fun z => LinParamBandits.UEFinite.Regret 𝒰 ν ψ z T) = fun z =>
          (T : ℝ) * LinParamBandits.UEGeneral.bestValue 𝒰 z -
            ∫ h, (fun p : LinParamBandits.LowerBound.Vec r × LinParamBandits.LowerBound.History r T =>
              ∑ s, inner ℝ (p.2 s).1 p.1) (z, h) ∂(K z) := by
        funext z
        unfold LinParamBandits.UEFinite.Regret
        rw [hKz z]
      rw [heq]
      refine StronglyMeasurable.sub ?_ ?_
      · exact (continuous_const.mul (continuous_bestValue 𝒰 h𝒰fin h𝒰ne)).stronglyMeasurable
      · refine StronglyMeasurable.integral_kernel_prod_right' (κ := K)
          (f := fun p : LinParamBandits.LowerBound.Vec r × LinParamBandits.LowerBound.History r T =>
            ∑ s, inner ℝ (p.2 s).1 p.1) ?_
        apply Continuous.stronglyMeasurable
        fun_prop
    have hRint : Integrable (fun z => LinParamBandits.UEFinite.Regret 𝒰 ν ψ z T) μ := by
      refine Integrable.mono' hBint hRmeas.aestronglyMeasurable
        (Filter.Eventually.of_forall (fun z => ?_))
      rw [Real.norm_eq_abs, abs_of_nonneg (hRnn z)]
      exact hRle z
    refine ⟨hRint, ?_⟩
    unfold LinParamBandits.UEFinite.Risk
    calc ∫ z, LinParamBandits.UEFinite.Regret 𝒰 ν ψ z T ∂μ ≤ ∫ z, B z ∂μ :=
          integral_mono hRint hBint hRle
      _ = (12 * ū) * (𝒰.ncard : ℝ) * ∫ z, ‖z‖ ∂μ +
            a₇ * (𝒰.ncard : ℝ) * ∑ u ∈ h𝒰fin.toFinset, ∫ z, m u z ∂μ := by
          simp only [hB]
          rw [integral_add (hnormint.const_mul _)
            ((integrable_finsetSum _ (fun u hu => (hmint u hu).1)).const_mul _),
            integral_const_mul, integral_const_mul, integral_finsetSum _ (fun u hu => (hmint u hu).1)]
      _ ≤ (12 * ū) * (𝒰.ncard : ℝ) * ∫ z, ‖z‖ ∂μ +
            a₇ * (𝒰.ncard : ℝ) * ∑ u ∈ h𝒰fin.toFinset, ((M₀ + 1) * L + M₀ * L ^ 2) := by
          gcongr with u hu
          exact (hmint u hu).2
      _ ≤ (12 * ū) * (𝒰.ncard : ℝ) * ∫ z, ‖z‖ ∂μ + a₇ * (2 * M₀ + 1) * (𝒰.ncard : ℝ) ^ 2 * L ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul, ← hcard]
          have hn : (0 : ℝ) ≤ 𝒰.ncard := by positivity
          have hLL : (M₀ + 1) * L + M₀ * L ^ 2 ≤ (2 * M₀ + 1) * L ^ 2 := by
            nlinarith [mul_le_mul_of_nonneg_left hL1 (by positivity : 0 ≤ (M₀ + 1) * L)]
          have : a₇ * (𝒰.ncard : ℝ) * ((𝒰.ncard : ℝ) * ((M₀ + 1) * L + M₀ * L ^ 2)) ≤
              a₇ * (𝒰.ncard : ℝ) * ((𝒰.ncard : ℝ) * ((2 * M₀ + 1) * L ^ 2)) := by gcongr
          nlinarith
