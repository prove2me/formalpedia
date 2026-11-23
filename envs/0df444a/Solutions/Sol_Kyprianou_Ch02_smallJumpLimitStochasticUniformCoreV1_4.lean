-- Prove2me | solution 4 for Kyprianou.Ch02.smallJumpLimitStochasticUniformCoreV1
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-23T20:48:21.550629+00:00
-- url     : https://prove2.me/submissions/4745966d-cf26-49a2-b12d-6889f29c9cee

import Mathlib
import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
import Definitions.Def_Kyprianou_Ch02_IndependentComponents
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Theorems.Thm_Kyprianou_compensatedGeneralRegionMartingaleCh02V3
import Theorems.Thm_Kyprianou_Ch02_prmSimpleMarkRawCampbellSecondMomentV1
import Theorems.Thm_Kyprianou_Ch02_prmMarkedIntegralMeasurableAmbientV1
import Theorems.Thm_Kyprianou_Ch02_completedPoissonFiltrationExistsGeneralV1
import Theorems.Thm_Kyprianou_Ch02_compensatedFiniteRegionMartingaleUnderCompletedFiltrationV1
import Theorems.Thm_Kyprianou_Ch02_cadlagOfSmallJumpUniformApproxV1
import Theorems.Thm_Kyprianou_finiteRegionPoissonIntegralCh02V3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

set_option autoImplicit false

namespace CompensatedSmallJumpLimitHelpers

/-! ### Section 1: Poisson first moment and reference intensity on `(0, t] × A` -/

private lemma referenceIntensity_Ioc_prod (ν : Measure ℝ) [SigmaFinite ν]
    (t : ℝ≥0) {A : Set ℝ} :
    LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ A) =
      ENNReal.ofReal (t : ℝ) * ν A := by
  unfold LevyStochCalc.Poisson.referenceIntensity
  rw [Measure.prod_prod, Measure.restrict_apply measurableSet_Ioc]
  have hsub : Set.Ioc (0 : ℝ) (t : ℝ) ∩ Set.Ici (0 : ℝ) = Set.Ioc (0 : ℝ) (t : ℝ) :=
    Set.inter_eq_left.mpr fun _ hx => le_of_lt hx.1
  rw [hsub, Real.volume_Ioc, sub_zero]

private lemma referenceIntensity_Ioc_prod_ne_top (ν : Measure ℝ) [SigmaFinite ν]
    (t : ℝ≥0) {A : Set ℝ} (hAfin : ν A < ⊤) :
    LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ A) ≠ ⊤ := by
  rw [referenceIntensity_Ioc_prod ν t]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hAfin.ne

private lemma hasSum_poisson_first (μ : ℝ≥0) :
    HasSum (fun n : ℕ => Real.exp (-(μ : ℝ)) * (μ : ℝ) ^ n / (n.factorial : ℝ) * (n : ℝ)) (μ : ℝ) := by
  rw [← hasSum_nat_add_iff' 1]
  simp only [Finset.sum_range_one, pow_zero, Nat.factorial_zero, Nat.cast_one, Nat.cast_zero,
    mul_zero, sub_zero]
  have hterm : (fun n : ℕ =>
      Real.exp (-(μ : ℝ)) * (μ : ℝ) ^ (n + 1) / ((n + 1).factorial : ℝ) * ((n + 1 : ℕ) : ℝ)) =
      fun n : ℕ => (Real.exp (-(μ : ℝ)) * (μ : ℝ)) * ((μ : ℝ) ^ n / (n.factorial : ℝ)) := by
    funext n
    rw [pow_succ, Nat.factorial_succ]
    push_cast
    have hne : ((n : ℝ) + 1) ≠ 0 := by positivity
    field_simp
  rw [hterm]
  have hexp : HasSum (fun n : ℕ => (μ : ℝ) ^ n / (n.factorial : ℝ)) (Real.exp (μ : ℝ)) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp (μ : ℝ)
  have h := hexp.mul_left (Real.exp (-(μ : ℝ)) * (μ : ℝ))
  have hval : Real.exp (-(μ : ℝ)) * (μ : ℝ) * Real.exp (μ : ℝ) = (μ : ℝ) := by
    calc Real.exp (-(μ : ℝ)) * (μ : ℝ) * Real.exp (μ : ℝ)
        = (μ : ℝ) * (Real.exp (-(μ : ℝ)) * Real.exp (μ : ℝ)) := by ring
      _ = (μ : ℝ) * Real.exp (-(μ : ℝ) + (μ : ℝ)) := by rw [← Real.exp_add]
      _ = (μ : ℝ) := by simp
  rwa [hval] at h

private lemma prm_count_int_and_mean {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ν : Measure ℝ} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (t : ℝ≥0) {A : Set ℝ} (hA : MeasurableSet A) (hAfin : ν A < ⊤) :
    Integrable (fun ω => (N.N ω (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ A)).toReal) P ∧
      ∫ ω, (N.N ω (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ A)).toReal ∂P = (t : ℝ) * (ν A).toReal := by
  let S := Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ A
  have hS : MeasurableSet S := measurableSet_Ioc.prod hA
  have hSfin : LevyStochCalc.Poisson.referenceIntensity ν S ≠ ⊤ :=
    referenceIntensity_Ioc_prod_ne_top ν t hAfin
  let μ : ℝ≥0 := (LevyStochCalc.Poisson.referenceIntensity ν S).toNNReal
  have hμ_eq : (μ : ℝ) = (t : ℝ) * (ν A).toReal := by
    have h1 : (μ : ℝ) = (LevyStochCalc.Poisson.referenceIntensity ν S).toReal := rfl
    rw [h1, referenceIntensity_Ioc_prod ν t, ENNReal.toReal_mul, ENNReal.toReal_ofReal t.coe_nonneg]
  have hN_meas : Measurable (fun ω => N.N ω S) := N.measurable_eval hS
  have hcast_meas : Measurable (fun n : ℕ => (n : ℝ≥0∞)) := measurable_of_countable _
  have hlaw : P.map (fun ω => N.N ω S) =
      (ProbabilityTheory.poissonMeasure μ).map (fun n : ℕ => (n : ℝ≥0∞)) :=
    N.poisson_law hS hSfin
  have htoReal_meas : Measurable (fun r : ℝ≥0∞ => r.toReal) := ENNReal.measurable_toReal
  have hpois_int : Integrable (fun n : ℕ => (n : ℝ)) (ProbabilityTheory.poissonMeasure μ) := by
    rw [ProbabilityTheory.integrable_poissonMeasure_iff]
    exact (hasSum_poisson_first μ).summable.congr fun n => by rw [Real.norm_eq_abs, Nat.abs_cast]
  have hpois_mean : ∫ n : ℕ, (n : ℝ) ∂(ProbabilityTheory.poissonMeasure μ) = (μ : ℝ) := by
    rw [ProbabilityTheory.integral_poissonMeasure]
    simpa only [smul_eq_mul] using (hasSum_poisson_first μ).tsum_eq
  have hint : Integrable (fun ω => (N.N ω S).toReal) P := by
    change Integrable ((fun r : ℝ≥0∞ => r.toReal) ∘ fun ω => N.N ω S) P
    rw [← integrable_map_measure htoReal_meas.aestronglyMeasurable hN_meas.aemeasurable, hlaw,
      integrable_map_measure htoReal_meas.aestronglyMeasurable hcast_meas.aemeasurable]
    simpa only [Function.comp_def, ENNReal.toReal_natCast] using hpois_int
  have hmean : ∫ ω, (N.N ω S).toReal ∂P = (t : ℝ) * (ν A).toReal := by
    have h1 : ∫ ω, (N.N ω S).toReal ∂P = ∫ r, r.toReal ∂(P.map (fun ω => N.N ω S)) :=
      (integral_map hN_meas.aemeasurable htoReal_meas.aestronglyMeasurable).symm
    have h2 : ∫ r, r.toReal ∂((ProbabilityTheory.poissonMeasure μ).map (fun n : ℕ => (n : ℝ≥0∞))) =
        ∫ n : ℕ, ((n : ℝ≥0∞).toReal) ∂(ProbabilityTheory.poissonMeasure μ) :=
      integral_map hcast_meas.aemeasurable htoReal_meas.aestronglyMeasurable
    rw [h1, hlaw, h2]
    simp only [ENNReal.toReal_natCast, hpois_mean, hμ_eq]
  exact ⟨hint, hmean⟩

/-! ### Section 2: Lévy measure band properties and deterministic fast-decay sequence `ε` -/

private lemma band_measurableSet (a b : ℝ) :
    MeasurableSet {x : ℝ | a ≤ |x| ∧ |x| < b} :=
  continuous_abs.measurable (measurableSet_Ico : MeasurableSet (Set.Ico a b))

private lemma band_measure_lt_top {ν : Measure ℝ} (hν : ProbabilityTheory.IsLevyMeasure ν)
    {a : ℝ} (ha : 0 < a) (b : ℝ) :
    ν {x : ℝ | a ≤ |x| ∧ |x| < b} < ⊤ :=
  lt_of_le_of_lt (measure_mono fun _ hx => hx.1) (hν.measure_setOf_abs_ge_lt_top ha)

private lemma band_integrable_and_memLp {ν : Measure ℝ} (hν : ProbabilityTheory.IsLevyMeasure ν)
    {a b : ℝ} (ha : 0 < a) (hb : b ≤ 1) :
    Integrable (fun x : ℝ => x) (ν.restrict {x : ℝ | a ≤ |x| ∧ |x| < b}) ∧
      MemLp (fun x : ℝ => x) 2 (ν.restrict {x : ℝ | a ≤ |x| ∧ |x| < b}) := by
  let A := {x : ℝ | a ≤ |x| ∧ |x| < b}
  have hA : MeasurableSet A := band_measurableSet a b
  have hAfin : ν A < ⊤ := band_measure_lt_top hν ha b
  haveI : IsFiniteMeasure (ν.restrict A) := ⟨by rw [Measure.restrict_apply_univ]; exact hAfin⟩
  have hbd : ∀ᵐ x ∂(ν.restrict A), ‖x‖ ≤ (1 : ℝ) := by
    filter_upwards [ae_restrict_mem hA] with x hx
    rw [Real.norm_eq_abs]
    exact hx.2.le.trans hb
  refine ⟨Integrable.mono' (integrable_const 1) measurable_id.aestronglyMeasurable hbd,
    MemLp.of_bound measurable_id.aestronglyMeasurable 1 hbd⟩

private lemma levy_sq_integrable_unit {ν : Measure ℝ} (hν : ProbabilityTheory.IsLevyMeasure ν) :
    Integrable (fun x : ℝ => x ^ 2) (ν.restrict {x : ℝ | |x| < 1}) := by
  let U := {x : ℝ | |x| < 1}
  have hU : MeasurableSet U := continuous_abs.measurable measurableSet_Iio
  refine ⟨(measurable_id.pow_const 2).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have hle : ∀ᵐ x ∂(ν.restrict U), ‖x ^ 2‖ₑ ≤ ENNReal.ofReal (min 1 (x ^ 2)) := by
    filter_upwards [ae_restrict_mem hU] with x hx
    rw [Real.enorm_of_nonneg (sq_nonneg x)]
    have hxsq : x ^ 2 ≤ 1 := by
      have h1 : |x| ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ (abs_nonneg x) hx.le 2
      simpa [sq_abs] using h1
    rw [min_eq_right hxsq]
  calc
    ∫⁻ x in U, ‖x ^ 2‖ₑ ∂ν ≤ ∫⁻ x in U, ENNReal.ofReal (min 1 (x ^ 2)) ∂ν :=
      lintegral_mono_ae hle
    _ ≤ ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂ν := setLIntegral_le_lintegral _ _
    _ < ⊤ := hν.2

private lemma exists_small_jump_seq {ν : Measure ℝ} (hν : ProbabilityTheory.IsLevyMeasure ν) :
    ∃ ε : ℕ → ℝ,
      StrictAnti ε ∧
      (∀ n, 0 < ε n ∧ ε n < 1) ∧
      Tendsto ε atTop (𝓝 0) ∧
      (∀ n, ∫ x in {x : ℝ | 0 < |x| ∧ |x| < ε n}, x ^ 2 ∂ν ≤ 1 / (16 : ℝ) ^ n) := by
  let U := {x : ℝ | |x| < 1}
  have hU : MeasurableSet U := continuous_abs.measurable measurableSet_Iio
  have hsq_int : Integrable (fun x : ℝ => x ^ 2) (ν.restrict U) := levy_sq_integrable_unit hν
  -- Show `∫_{|x| < 1/(k+2)} x^2 dν → 0` as `k → ∞`
  have htail_zero : ∀ δ : ℝ, 0 < δ → ∀ r : ℝ, 0 < r →
      ∃ e : ℝ, 0 < e ∧ e < r ∧ e < 1 ∧
        ∫ x in {x : ℝ | 0 < |x| ∧ |x| < e}, x ^ 2 ∂ν ≤ δ := by
    intro δ hδ r hr
    let S : ℕ → Set ℝ := fun k => {x : ℝ | 0 < |x| ∧ |x| < 1 / ((k : ℝ) + 2)}
    have hS_meas : ∀ k, MeasurableSet (S k) := fun k =>
      continuous_abs.measurable (measurableSet_Ioo : MeasurableSet (Set.Ioo (0 : ℝ) _))
    have hS_sub : ∀ k, S k ⊆ U := fun k x hx => by
      have h1 : (1 : ℝ) / ((k : ℝ) + 2) < 1 := by
        rw [div_lt_one (by positivity)]; linarith [Nat.cast_nonneg (α := ℝ) k]
      exact hx.2.trans h1
    have htend : Tendsto (fun k => ∫ x in U, (S k).indicator (fun y => y ^ 2) x ∂ν) atTop (𝓝 0) := by
      have h0 : (0 : ℝ) = ∫ _ in U, (0 : ℝ) ∂ν := by simp
      rw [h0]
      refine MeasureTheory.tendsto_integral_of_dominated_convergence (fun x => x ^ 2)
        (fun k => ((measurable_id.pow_const 2).indicator (hS_meas k)).aestronglyMeasurable)
        hsq_int
        (fun k => Filter.Eventually.of_forall fun x => by
          by_cases hx : x ∈ S k
          · simp [hx, Real.norm_of_nonneg (sq_nonneg x)]
          · simp [hx, sq_nonneg x])
        (Filter.Eventually.of_forall fun x => ?_)
      by_cases hx0 : x = 0
      · subst hx0; simp [S]
      · have habs : 0 < |x| := abs_pos.mpr hx0
        obtain ⟨K, hK⟩ := exists_nat_gt (1 / |x|)
        refine tendsto_atTop_of_eventually_const (i₀ := K) fun k hk => ?_
        have hnot : x ∉ S k := by
          intro hmem
          have h1 : 1 / |x| < (k : ℝ) + 2 := by
            have : (K : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
            linarith
          have h2 : 1 / ((k : ℝ) + 2) < |x| := by
            rw [div_lt_iff₀ (by positivity)]
            rw [div_lt_iff₀ habs] at h1
            linarith
          exact not_lt_of_ge h2.le hmem.2
        simp [hnot]
    have hev1 : ∀ᶠ k : ℕ in atTop, ∫ x in U, (S k).indicator (fun y => y ^ 2) x ∂ν < δ :=
      htend.eventually (gt_mem_nhds hδ)
    have hinv : Tendsto (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 2)) atTop (𝓝 0) := by
      simpa [one_div, Function.comp_def] using
        tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    have hev2 : ∀ᶠ k : ℕ in atTop, (1 : ℝ) / ((k : ℝ) + 2) < r :=
      hinv.eventually (gt_mem_nhds hr)
    obtain ⟨k, hk1, hk2⟩ := (hev1.and hev2).exists
    refine ⟨1 / ((k : ℝ) + 2), by positivity, hk2, ?_, ?_⟩
    · rw [div_lt_one (by positivity)]; linarith [Nat.cast_nonneg (α := ℝ) k]
    · have heq : ∫ x in S k, x ^ 2 ∂ν = ∫ x in U, (S k).indicator (fun y => y ^ 2) x ∂ν := by
        rw [integral_indicator (hS_meas k), Measure.restrict_restrict (hS_meas k),
          Set.inter_eq_left.mpr (hS_sub k)]
      rw [heq]
      exact hk1.le
  -- Recursive construction of `ε : ℕ → ℝ`
  have hstep : ∀ (n : ℕ) (prev : ℝ), 0 < prev →
      ∃ e : ℝ, 0 < e ∧ e < min prev (1 / ((n : ℝ) + 2)) ∧ e < 1 ∧
        ∫ x in {x : ℝ | 0 < |x| ∧ |x| < e}, x ^ 2 ∂ν ≤ 1 / (16 : ℝ) ^ n := fun n prev hp =>
    htail_zero (1 / (16 : ℝ) ^ n) (by positivity) (min prev (1 / ((n : ℝ) + 2)))
      (lt_min hp (by positivity))
  choose next hnext_pos hnext_lt hnext_lt1 hnext_int using hstep
  let seq : ℕ → {e : ℝ // 0 < e} :=
    Nat.rec ⟨next 0 1 one_pos, hnext_pos 0 1 one_pos⟩
      fun n acc => ⟨next (n + 1) acc.1 acc.2, hnext_pos (n + 1) acc.1 acc.2⟩
  let ε : ℕ → ℝ := fun n => (seq n).1
  have hε_pos : ∀ n, 0 < ε n := fun n => (seq n).2
  have hε_lt_min : ∀ n, ε (n + 1) < min (ε n) (1 / (((n + 1 : ℕ) : ℝ) + 2)) :=
    fun n => hnext_lt (n + 1) (seq n).1 (seq n).2
  have hε_anti : StrictAnti ε :=
    strictAnti_nat_of_succ_lt fun n => lt_of_lt_of_le (hε_lt_min n) (min_le_left _ _)
  have hε_lt1 : ∀ n, ε n < 1 := by
    intro n
    cases n with
    | zero => exact hnext_lt1 0 1 one_pos
    | succ k => exact hnext_lt1 (k + 1) (seq k).1 (seq k).2
  have hε_le_inv : ∀ n, ε n ≤ 1 / ((n : ℝ) + 2) := by
    intro n
    cases n with
    | zero => exact (lt_of_lt_of_le (hnext_lt 0 1 one_pos) (min_le_right _ _)).le
    | succ k => exact (lt_of_lt_of_le (hε_lt_min k) (min_le_right _ _)).le
  have hε_tendsto : Tendsto ε atTop (𝓝 0) := by
    refine squeeze_zero (fun n => (hε_pos n).le) hε_le_inv ?_
    simpa [one_div, Function.comp_def] using
      tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have hε_int : ∀ n, ∫ x in {x : ℝ | 0 < |x| ∧ |x| < ε n}, x ^ 2 ∂ν ≤ 1 / (16 : ℝ) ^ n := by
    intro n
    cases n with
    | zero => exact hnext_int 0 1 one_pos
    | succ k => exact hnext_int (k + 1) (seq k).1 (seq k).2
  exact ⟨ε, hε_anti, fun n => ⟨hε_pos n, hε_lt1 n⟩, hε_tendsto, hε_int⟩

/-! ### Section 3: Towards-zero dyadic `SimpleFunc` and compensated `L²` isometry bound -/

private def truncCell (A : Set ℝ) (m : ℕ) (i : Bool × Fin (2 ^ m)) : Set ℝ :=
  if i.1 then
    A ∩ {x : ℝ | 0 ≤ x ∧ ((i.2.1 : ℝ) / (2 : ℝ) ^ m) ≤ x ∧ x < (((i.2.1 : ℝ) + 1) / (2 : ℝ) ^ m)}
  else
    A ∩ {x : ℝ | x < 0 ∧ ((i.2.1 : ℝ) / (2 : ℝ) ^ m) ≤ -x ∧ -x < (((i.2.1 : ℝ) + 1) / (2 : ℝ) ^ m)}

private noncomputable def truncVal (m : ℕ) (i : Bool × Fin (2 ^ m)) : ℝ :=
  if i.1 then (i.2.1 : ℝ) / (2 : ℝ) ^ m else -((i.2.1 : ℝ) / (2 : ℝ) ^ m)

private lemma truncCell_measurableSet {A : Set ℝ} (hA : MeasurableSet A) (m : ℕ)
    (i : Bool × Fin (2 ^ m)) : MeasurableSet (truncCell A m i) := by
  unfold truncCell
  split_ifs
  · exact hA.inter (measurableSet_Ici.inter measurableSet_Ico)
  · have h1 : MeasurableSet {x : ℝ | x < 0} := measurableSet_Iio
    have h2 : MeasurableSet {x : ℝ | ((i.2.1 : ℝ) / (2 : ℝ) ^ m) ≤ -x ∧ -x < (((i.2.1 : ℝ) + 1) / (2 : ℝ) ^ m)} :=
      measurable_neg (measurableSet_Ico : MeasurableSet (Set.Ico _ _))
    exact hA.inter (h1.inter h2)

private lemma truncCell_pairwise_disjoint (A : Set ℝ) (m : ℕ) :
    Pairwise fun i j : Bool × Fin (2 ^ m) => Disjoint (truncCell A m i) (truncCell A m j) := by
  intro i j hne
  rw [Set.disjoint_left]
  intro x hxi hxj
  have hpos : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
  rcases i with ⟨bi, ki⟩
  rcases j with ⟨bj, kj⟩
  cases bi <;> cases bj
  · simp only [truncCell, Bool.false_eq_true, ↓reduceIte, Set.mem_inter_iff, Set.mem_setOf_eq] at hxi hxj
    have h1 : (ki.1 : ℝ) < (kj.1 : ℝ) + 1 :=
      (div_lt_div_iff_of_pos_right hpos).mp (lt_of_le_of_lt hxi.2.2.1 hxj.2.2.2)
    have h2 : (kj.1 : ℝ) < (ki.1 : ℝ) + 1 :=
      (div_lt_div_iff_of_pos_right hpos).mp (lt_of_le_of_lt hxj.2.2.1 hxi.2.2.2)
    have hk1 : ki.1 < kj.1 + 1 := Nat.cast_lt.mp (by exact_mod_cast h1)
    have hk2 : kj.1 < ki.1 + 1 := Nat.cast_lt.mp (by exact_mod_cast h2)
    exact hne (Prod.ext rfl (Fin.ext (Nat.le_antisymm (Nat.lt_succ_iff.mp hk1) (Nat.lt_succ_iff.mp hk2))))
  · simp only [truncCell, Bool.false_eq_true, ↓reduceIte, Set.mem_inter_iff, Set.mem_setOf_eq] at hxi hxj
    linarith [hxi.2.1, hxj.2.1]
  · simp only [truncCell, Bool.false_eq_true, ↓reduceIte, Set.mem_inter_iff, Set.mem_setOf_eq] at hxi hxj
    linarith [hxi.2.1, hxj.2.1]
  · simp only [truncCell, ↓reduceIte, Set.mem_inter_iff, Set.mem_setOf_eq] at hxi hxj
    have h1 : (ki.1 : ℝ) < (kj.1 : ℝ) + 1 :=
      (div_lt_div_iff_of_pos_right hpos).mp (lt_of_le_of_lt hxi.2.2.1 hxj.2.2.2)
    have h2 : (kj.1 : ℝ) < (ki.1 : ℝ) + 1 :=
      (div_lt_div_iff_of_pos_right hpos).mp (lt_of_le_of_lt hxj.2.2.1 hxi.2.2.2)
    have hk1 : ki.1 < kj.1 + 1 := Nat.cast_lt.mp (by exact_mod_cast h1)
    have hk2 : kj.1 < ki.1 + 1 := Nat.cast_lt.mp (by exact_mod_cast h2)
    exact hne (Prod.ext rfl (Fin.ext (Nat.le_antisymm (Nat.lt_succ_iff.mp hk1) (Nat.lt_succ_iff.mp hk2))))

private noncomputable def truncSimpleFunc (A : Set ℝ) (m : ℕ) : SimpleFunc ℝ ℝ :=
  ∑ i : Bool × Fin (2 ^ m), (SimpleFunc.const ℝ (truncVal m i)).restrict (truncCell A m i)

private lemma simpleFunc_finset_sum_apply {α ι : Type*} [MeasurableSpace α]
    (s : Finset ι) (f : ι → SimpleFunc α ℝ) (x : α) :
    (∑ i ∈ s, f i) x = ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert ha, ih]

private lemma truncSimpleFunc_apply {A : Set ℝ} (hA : MeasurableSet A) (m : ℕ) (x : ℝ) :
    truncSimpleFunc A m x =
      ∑ i : Bool × Fin (2 ^ m), (truncCell A m i).indicator (fun _ => truncVal m i) x := by
  unfold truncSimpleFunc
  rw [simpleFunc_finset_sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [SimpleFunc.coe_restrict _ (truncCell_measurableSet hA m i)]
  rfl

private lemma abs_truncSimpleFunc_le {A : Set ℝ} (hA : MeasurableSet A) (m : ℕ) (x : ℝ) :
    |truncSimpleFunc A m x| ≤ |x| := by
  rw [truncSimpleFunc_apply hA]
  by_cases h : ∃ i : Bool × Fin (2 ^ m), x ∈ truncCell A m i
  · rcases h with ⟨i₀, hi₀⟩
    have heval : (∑ i : Bool × Fin (2 ^ m), (truncCell A m i).indicator (fun _ => truncVal m i) x) =
        truncVal m i₀ := by
      rw [Finset.sum_eq_single i₀]
      · exact Set.indicator_of_mem hi₀ _
      · intro i _ hine
        exact Set.indicator_of_notMem
          (Set.disjoint_left.mp (truncCell_pairwise_disjoint A m hine.symm) hi₀) _
      · intro hnot; exact absurd (Finset.mem_univ i₀) hnot
    rw [heval]
    rcases i₀ with ⟨b, k⟩
    cases b
    · simp only [truncCell, truncVal, Bool.false_eq_true, ↓reduceIte, Set.mem_inter_iff,
        Set.mem_setOf_eq] at hi₀ ⊢
      rw [abs_neg, abs_of_nonneg (by positivity), abs_of_neg hi₀.2.1]
      exact hi₀.2.2.1
    · simp only [truncCell, truncVal, ↓reduceIte, Set.mem_inter_iff, Set.mem_setOf_eq] at hi₀ ⊢
      rw [abs_of_nonneg (by positivity), abs_of_nonneg hi₀.2.1]
      exact hi₀.2.2.1
  · push Not at h
    have heval : (∑ i : Bool × Fin (2 ^ m), (truncCell A m i).indicator (fun _ => truncVal m i) x) = 0 :=
      Finset.sum_eq_zero fun i _ => Set.indicator_of_notMem (h i) _
    rw [heval, abs_zero]
    exact abs_nonneg x

private lemma truncSimpleFunc_sub_le {A : Set ℝ} (hA : MeasurableSet A)
    (hAsub : A ⊆ {x : ℝ | |x| < 1}) (m : ℕ) {x : ℝ} (hxA : x ∈ A) :
    |truncSimpleFunc A m x - x| ≤ 1 / (2 : ℝ) ^ m := by
  have hpos : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
  have hxlt : |x| < 1 := hAsub hxA
  set k₀ : ℕ := ⌊|x| * (2 : ℝ) ^ m⌋₊
  have hk₀_lt : k₀ < 2 ^ m := by
    have hlt : |x| * (2 : ℝ) ^ m < ((2 ^ m : ℕ) : ℝ) := by
      push_cast; linarith [mul_lt_mul_of_pos_right hxlt hpos]
    exact (Nat.floor_lt (by positivity)).mpr hlt
  let i₀ : Bool × Fin (2 ^ m) := (decide (0 ≤ x), ⟨k₀, hk₀_lt⟩)
  have hi₀ : x ∈ truncCell A m i₀ := by
    have hfl_le : (k₀ : ℝ) ≤ |x| * (2 : ℝ) ^ m := Nat.floor_le (by positivity)
    have hfl_lt : |x| * (2 : ℝ) ^ m < (k₀ : ℝ) + 1 := Nat.lt_floor_add_one (|x| * (2 : ℝ) ^ m)
    by_cases h0 : 0 ≤ x
    · have hfl1 : (k₀ : ℝ) ≤ x * (2 : ℝ) ^ m := by rwa [abs_of_nonneg h0] at hfl_le
      have hfl2 : x * (2 : ℝ) ^ m < (k₀ : ℝ) + 1 := by rwa [abs_of_nonneg h0] at hfl_lt
      have hd : decide (0 ≤ x) = true := decide_eq_true h0
      unfold truncCell
      dsimp only [i₀]
      rw [if_pos hd]
      exact ⟨hxA, h0, (div_le_iff₀ hpos).mpr hfl1, (lt_div_iff₀ hpos).mpr hfl2⟩
    · have hneg : x < 0 := lt_of_not_ge h0
      have hfl1 : (k₀ : ℝ) ≤ (-x) * (2 : ℝ) ^ m := by rwa [abs_of_neg hneg] at hfl_le
      have hfl2 : (-x) * (2 : ℝ) ^ m < (k₀ : ℝ) + 1 := by rwa [abs_of_neg hneg] at hfl_lt
      have hd : decide (0 ≤ x) = false := decide_eq_false h0
      unfold truncCell
      dsimp only [i₀]
      rw [if_neg (by simp [hd])]
      exact ⟨hxA, hneg, (div_le_iff₀ hpos).mpr hfl1, (lt_div_iff₀ hpos).mpr hfl2⟩
  rw [truncSimpleFunc_apply hA]
  have heval : (∑ i : Bool × Fin (2 ^ m), (truncCell A m i).indicator (fun _ => truncVal m i) x) =
      truncVal m i₀ := by
    rw [Finset.sum_eq_single i₀]
    · exact Set.indicator_of_mem hi₀ _
    · intro i _ hine
      exact Set.indicator_of_notMem
        (Set.disjoint_left.mp (truncCell_pairwise_disjoint A m hine.symm) hi₀) _
    · intro hnot; exact absurd (Finset.mem_univ i₀) hnot
  rw [heval]
  by_cases h0 : 0 ≤ x
  · simp only [i₀, h0, decide_true, truncCell, truncVal, ↓reduceIte, Set.mem_inter_iff,
      Set.mem_setOf_eq] at hi₀ ⊢
    have h1 := hi₀.2.2.1
    have h2 : x < (k₀ : ℝ) / (2 : ℝ) ^ m + 1 / (2 : ℝ) ^ m := by
      linarith [hi₀.2.2.2, add_div (k₀ : ℝ) 1 ((2 : ℝ) ^ m)]
    rw [abs_le]; constructor <;> linarith
  · have hneg : x < 0 := lt_of_not_ge h0
    simp only [i₀, h0, decide_false, truncCell, truncVal, Bool.false_eq_true, ↓reduceIte,
      Set.mem_inter_iff, Set.mem_setOf_eq] at hi₀ ⊢
    have h1 := hi₀.2.2.1
    have h2 : -x < (k₀ : ℝ) / (2 : ℝ) ^ m + 1 / (2 : ℝ) ^ m := by
      linarith [hi₀.2.2.2, add_div (k₀ : ℝ) 1 ((2 : ℝ) ^ m)]
    rw [abs_le]; constructor <;> linarith

private lemma compensated_band_sq_integral_le
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    {A : Set ℝ} (hA : MeasurableSet A) (hAsub : A ⊆ {x : ℝ | |x| < 1})
    (hAfin : ν A < ⊤) (K : ℝ≥0)
    (hDL2 : MemLp (fun ω =>
      (∫ z in (Set.Ioc (0 : ℝ) (K : ℝ) ×ˢ A), z.2 ∂(N.N ω)) -
        (K : ℝ) * (∫ x in A, x ∂ν)) 2 P) :
    ∫ ω, ((∫ z in (Set.Ioc (0 : ℝ) (K : ℝ) ×ˢ A), z.2 ∂(N.N ω)) -
        (K : ℝ) * (∫ x in A, x ∂ν)) ^ 2 ∂P ≤
      (K : ℝ) * ∫ x in A, x ^ 2 ∂ν := by
  let I : Set ℝ := Set.Ioc (0 : ℝ) (K : ℝ)
  let W : Set (ℝ × ℝ) := I ×ˢ A
  have hW : MeasurableSet W := measurableSet_Ioc.prod hA
  have hWfin : LevyStochCalc.Poisson.referenceIntensity ν W ≠ ⊤ :=
    referenceIntensity_Ioc_prod_ne_top ν K hAfin
  let D : Ω → ℝ := fun ω => (∫ z in W, z.2 ∂(N.N ω)) - (K : ℝ) * (∫ x in A, x ∂ν)
  let Xm : ℕ → Ω → ℝ := fun m ω => ∫ z in W, truncSimpleFunc A m z.2 ∂(N.N ω)
  let μm : ℕ → ℝ := fun m => (K : ℝ) * ∫ x in A, truncSimpleFunc A m x ∂ν
  let Ym : ℕ → Ω → ℝ := fun m ω => Xm m ω - μm m
  haveI : IsFiniteMeasure (ν.restrict A) := ⟨by rw [Measure.restrict_apply_univ]; exact hAfin⟩
  have hν_sq_int : Integrable (fun x : ℝ => x ^ 2) (ν.restrict A) :=
    Integrable.mono' (integrable_const 1) (measurable_id.pow_const 2).aestronglyMeasurable
      (by
        filter_upwards [ae_restrict_mem hA] with x hx
        rw [Real.norm_of_nonneg (sq_nonneg x)]
        have h1 : |x| ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ (abs_nonneg x) (hAsub hx).le 2
        simpa [sq_abs] using h1)
  have hXm_eq_sum : ∀ m : ℕ, ∀ᵐ ω ∂P,
      Xm m ω = ∑ i : Bool × Fin (2 ^ m),
        truncVal m i * (N.N ω (I ×ˢ truncCell A m i)).toReal := by
    intro m
    filter_upwards [N.integer_valued hW hWfin] with ω ⟨nW, hnW⟩
    haveI : IsFiniteMeasure ((N.N ω).restrict W) :=
      ⟨by rw [Measure.restrict_apply_univ, hnW]; exact (ENNReal.natCast_ne_top nW).lt_top⟩
    have hind_int : ∀ i ∈ (Finset.univ : Finset (Bool × Fin (2 ^ m))),
        Integrable (fun z : ℝ × ℝ =>
          (truncCell A m i).indicator (fun _ => truncVal m i) z.2) ((N.N ω).restrict W) :=
      fun i _ => by
        have heq : (fun z : ℝ × ℝ => (truncCell A m i).indicator (fun _ => truncVal m i) z.2) =
            ((Prod.snd : ℝ × ℝ → ℝ) ⁻¹' truncCell A m i).indicator (fun _ => truncVal m i) := by
          funext z; by_cases hz : z.2 ∈ truncCell A m i <;> simp [hz]
        rw [heq]
        exact (integrable_const _).indicator ((truncCell_measurableSet hA m i).preimage measurable_snd)
    have hfun : (fun z : ℝ × ℝ => truncSimpleFunc A m z.2) =
        fun z : ℝ × ℝ => ∑ i : Bool × Fin (2 ^ m),
          (truncCell A m i).indicator (fun _ => truncVal m i) z.2 := by
      funext z; exact truncSimpleFunc_apply hA m z.2
    change ∫ z in W, truncSimpleFunc A m z.2 ∂(N.N ω) = _
    rw [hfun, integral_finset_sum _ hind_int]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hkm : MeasurableSet ((Prod.snd : ℝ × ℝ → ℝ) ⁻¹' truncCell A m i) :=
      (truncCell_measurableSet hA m i).preimage measurable_snd
    have heq : (fun z : ℝ × ℝ => (truncCell A m i).indicator (fun _ => truncVal m i) z.2) =
        ((Prod.snd : ℝ × ℝ → ℝ) ⁻¹' truncCell A m i).indicator (fun _ => truncVal m i) := by
      funext z; by_cases hz : z.2 ∈ truncCell A m i <;> simp [hz]
    rw [heq, integral_indicator_const _ hkm, Measure.real, Measure.restrict_apply hkm]
    have hinter : ((Prod.snd : ℝ × ℝ → ℝ) ⁻¹' truncCell A m i) ∩ W = I ×ˢ truncCell A m i := by
      ext z
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_prod, W]
      refine ⟨fun h => ⟨h.2.1, h.1⟩, fun h => ⟨h.2, h.1, ?_⟩⟩
      unfold truncCell at h
      split_ifs at h <;> exact h.2.1
    rw [hinter, smul_eq_mul, mul_comm]
  have hXm_int_mean : ∀ m : ℕ, Integrable (Xm m) P ∧ ∫ ω, Xm m ω ∂P = μm m := by
    intro m
    let Sm : Ω → ℝ := fun ω => ∑ i : Bool × Fin (2 ^ m),
      truncVal m i * (N.N ω (I ×ˢ truncCell A m i)).toReal
    have hterm : ∀ i : Bool × Fin (2 ^ m),
        Integrable (fun ω => truncVal m i * (N.N ω (I ×ˢ truncCell A m i)).toReal) P ∧
          ∫ ω, truncVal m i * (N.N ω (I ×ˢ truncCell A m i)).toReal ∂P =
            (K : ℝ) * (truncVal m i * (ν (truncCell A m i)).toReal) := fun i => by
      have hci := truncCell_measurableSet hA m i
      have hci_sub : truncCell A m i ⊆ A := by
        intro x hx; unfold truncCell at hx; split_ifs at hx <;> exact hx.1
      have hci_fin : ν (truncCell A m i) < ⊤ := lt_of_le_of_lt (measure_mono hci_sub) hAfin
      obtain ⟨hint, hmean⟩ := prm_count_int_and_mean N K hci hci_fin
      refine ⟨hint.const_mul _, ?_⟩
      rw [integral_const_mul, hmean]; ring
    have hSm_int : Integrable Sm P := integrable_finset_sum _ fun i _ => (hterm i).1
    have hSm_mean : ∫ ω, Sm ω ∂P = μm m := by
      rw [integral_finset_sum _ fun i _ => (hterm i).1]
      have hsum : ∑ i : Bool × Fin (2 ^ m), ∫ ω, truncVal m i * (N.N ω (I ×ˢ truncCell A m i)).toReal ∂P =
          (K : ℝ) * ∑ i : Bool × Fin (2 ^ m), truncVal m i * (ν (truncCell A m i)).toReal := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => (hterm i).2
      rw [hsum]
      unfold μm
      congr 1
      have hfun : (fun x : ℝ => truncSimpleFunc A m x) =
          fun x : ℝ => ∑ i : Bool × Fin (2 ^ m), (truncCell A m i).indicator (fun _ => truncVal m i) x := by
        funext x; exact truncSimpleFunc_apply hA m x
      have hind_int : ∀ i ∈ (Finset.univ : Finset (Bool × Fin (2 ^ m))),
          Integrable ((truncCell A m i).indicator (fun _ => truncVal m i)) (ν.restrict A) :=
        fun i _ => (integrable_const _).indicator (truncCell_measurableSet hA m i)
      rw [hfun, integral_finset_sum _ hind_int]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hci := truncCell_measurableSet hA m i
      have hci_sub : truncCell A m i ⊆ A := by
        intro x hx; unfold truncCell at hx; split_ifs at hx <;> exact hx.1
      rw [integral_indicator_const _ hci, Measure.real, Measure.restrict_apply hci,
        Set.inter_eq_left.mpr hci_sub, smul_eq_mul, mul_comm]
    refine ⟨hSm_int.congr ((hXm_eq_sum m).mono fun _ h => h.symm), ?_⟩
    rw [integral_congr_ae (hXm_eq_sum m), hSm_mean]
  have hXm_sq_int : ∀ m : ℕ, Integrable (fun ω => (Xm m ω) ^ 2) P := by
    intro m
    have hcamp :=
      Kyprianou.Ch02.prmSimpleMarkRawCampbellSecondMomentV1 P ν N A hA hAfin (truncSimpleFunc A m) K
    -- Also show `Xm m` is `MemLp 2` directly from `hXm_eq_sum`? Even simpler: `∫ Xm^2` is finite?
    -- No: `prmSimpleMarkRawCampbellSecondMomentV1` gives the exact integral; prove `Integrable (Xm m ^ 2)` via `Sm`!
    -- Wait: `Sm` is a finite sum of `truncVal * N(I × cell)`, and `N(I × cell)` has finite 2nd moment from Campbell!
    have hcell_sq : ∀ i : Bool × Fin (2 ^ m), Integrable (fun ω => ((N.N ω (I ×ˢ truncCell A m i)).toReal) ^ 2) P := by
      intro i
      have hci := truncCell_measurableSet hA m i
      have hci_sub : truncCell A m i ⊆ A := by
        intro x hx; unfold truncCell at hx; split_ifs at hx <;> exact hx.1
      have hci_fin : ν (truncCell A m i) < ⊤ := lt_of_le_of_lt (measure_mono hci_sub) hAfin
      let S := I ×ˢ truncCell A m i
      have hS : MeasurableSet S := measurableSet_Ioc.prod hci
      have hSfin : LevyStochCalc.Poisson.referenceIntensity ν S ≠ ⊤ :=
        referenceIntensity_Ioc_prod_ne_top ν K hci_fin
      let μ : ℝ≥0 := (LevyStochCalc.Poisson.referenceIntensity ν S).toNNReal
      have hN_meas : Measurable (fun ω => N.N ω S) := N.measurable_eval hS
      have hcast_meas : Measurable (fun n : ℕ => (n : ℝ≥0∞)) := measurable_of_countable _
      have hlaw : P.map (fun ω => N.N ω S) =
          (ProbabilityTheory.poissonMeasure μ).map (fun n : ℕ => (n : ℝ≥0∞)) :=
        N.poisson_law hS hSfin
      have hsq_meas : Measurable (fun r : ℝ≥0∞ => (r.toReal) ^ 2) :=
        ENNReal.measurable_toReal.pow_const 2
      have hpois_sq : Integrable (fun n : ℕ => (n : ℝ) ^ 2) (ProbabilityTheory.poissonMeasure μ) := by
        rw [ProbabilityTheory.integrable_poissonMeasure_iff]
        have hsum1 : Summable (fun n : ℕ => Real.exp (-(μ : ℝ)) * (μ : ℝ) ^ n / (n.factorial : ℝ) * (n : ℝ)) :=
          (hasSum_poisson_first μ).summable
        have hsum2 : Summable (fun n : ℕ => Real.exp (-(μ : ℝ)) * (μ : ℝ) ^ n / (n.factorial : ℝ) * ((n : ℝ) * ((n : ℝ) - 1))) := by
          rw [← summable_nat_add_iff 2]
          have hterm : (fun n : ℕ =>
              Real.exp (-(μ : ℝ)) * (μ : ℝ) ^ (n + 2) / ((n + 2).factorial : ℝ) *
                (((n + 2 : ℕ) : ℝ) * (((n + 2 : ℕ) : ℝ) - 1))) =
              fun n : ℕ => (Real.exp (-(μ : ℝ)) * (μ : ℝ) ^ 2) * ((μ : ℝ) ^ n / (n.factorial : ℝ)) := by
            funext n
            rw [Nat.factorial_succ, Nat.factorial_succ]
            push_cast
            have h1 : ((n : ℝ) + 1) ≠ 0 := by positivity
            have h2 : ((n : ℝ) + 2) ≠ 0 := by positivity
            field_simp
            ring
          rw [hterm]
          exact (NormedSpace.expSeries_div_hasSum_exp (μ : ℝ)).summable.mul_left _
        exact (hsum2.add hsum1).congr fun n => by
          rw [Real.norm_of_nonneg (sq_nonneg _)]; ring
      change Integrable ((fun r : ℝ≥0∞ => (r.toReal) ^ 2) ∘ fun ω => N.N ω S) P
      rw [← integrable_map_measure hsq_meas.aestronglyMeasurable hN_meas.aemeasurable, hlaw,
        integrable_map_measure hsq_meas.aestronglyMeasurable hcast_meas.aemeasurable]
      simpa only [Function.comp_def, ENNReal.toReal_natCast] using hpois_sq
    have hSm_L2 : MemLp (fun ω => ∑ i : Bool × Fin (2 ^ m),
        truncVal m i * (N.N ω (I ×ˢ truncCell A m i)).toReal) 2 P := by
      refine memLp_finset_sum _ fun i _ => ?_
      have hci := truncCell_measurableSet hA m i
      have hm_i : Measurable (fun ω => (N.N ω (I ×ˢ truncCell A m i)).toReal) :=
        ENNReal.measurable_toReal.comp (N.measurable_eval (measurableSet_Ioc.prod hci))
      have hL2_i : MemLp (fun ω => (N.N ω (I ×ˢ truncCell A m i)).toReal) 2 P :=
        (memLp_two_iff_integrable_sq hm_i.aestronglyMeasurable).mpr (hcell_sq i)
      exact hL2_i.const_mul (truncVal m i)
    have hXm_L2 : MemLp (Xm m) 2 P := hSm_L2.ae_eq ((hXm_eq_sum m).mono fun _ h => h.symm)
    exact hXm_L2.integrable_sq
  have hYm_sq_bound : ∀ m : ℕ, ∫ ω, (Ym m ω) ^ 2 ∂P ≤ (K : ℝ) * ∫ x in A, x ^ 2 ∂ν := by
    intro m
    have hcamp :=
      Kyprianou.Ch02.prmSimpleMarkRawCampbellSecondMomentV1 P ν N A hA hAfin (truncSimpleFunc A m) K
    have hexp : (fun ω => (Ym m ω) ^ 2) =
        fun ω => ((Xm m ω) ^ 2 - (2 * μm m) * Xm m ω) + (μm m) ^ 2 := by
      funext ω; unfold Ym; ring
    have hXm_int := (hXm_int_mean m).1
    have hXm_mean := (hXm_int_mean m).2
    have hsub_int : Integrable (fun ω => (Xm m ω) ^ 2 - (2 * μm m) * Xm m ω) P :=
      (hXm_sq_int m).sub (hXm_int.const_mul _)
    have h1 : ∫ ω, (Ym m ω) ^ 2 ∂P = (K : ℝ) * ∫ x in A, (truncSimpleFunc A m x) ^ 2 ∂ν := by
      rw [hexp, integral_add hsub_int (integrable_const _),
        integral_sub (hXm_sq_int m) (hXm_int.const_mul _), integral_const_mul,
        integral_const, probReal_univ, one_smul]
      change (∫ ω, (∫ z in W, truncSimpleFunc A m z.2 ∂(N.N ω)) ^ 2 ∂P) -
          2 * μm m * (∫ ω, Xm m ω ∂P) + (μm m) ^ 2 = _
      rw [hcamp, hXm_mean]
      dsimp only [μm]
      ring
    rw [h1]
    refine mul_le_mul_of_nonneg_left ?_ K.coe_nonneg
    have happrox_sq_int : Integrable (fun x : ℝ => (truncSimpleFunc A m x) ^ 2) (ν.restrict A) :=
      Integrable.mono' hν_sq_int
        ((truncSimpleFunc A m).measurable.pow_const 2).aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => by
          rw [Real.norm_of_nonneg (sq_nonneg _)]
          have := pow_le_pow_left₀ (abs_nonneg _) (abs_truncSimpleFunc_le hA m x) 2
          simpa [sq_abs] using this)
    exact integral_mono happrox_sq_int hν_sq_int fun x => by
      have := pow_le_pow_left₀ (abs_nonneg _) (abs_truncSimpleFunc_le hA m x) 2
      simpa [sq_abs] using this
  -- Pointwise a.e. convergence `Ym m ω → D ω`
  have hμm_tendsto : Tendsto μm atTop (𝓝 ((K : ℝ) * ∫ x in A, x ∂ν)) := by
    refine Tendsto.const_mul (K : ℝ) ?_
    refine MeasureTheory.tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
      (fun m => (truncSimpleFunc A m).measurable.aestronglyMeasurable)
      (integrable_const 1)
      (fun m => by
        filter_upwards [ae_restrict_mem hA] with x hx
        rw [Real.norm_eq_abs]
        exact (abs_truncSimpleFunc_le hA m x).trans (hAsub hx).le)
      ?_
    filter_upwards [ae_restrict_mem hA] with x hx
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N₀, hN₀⟩ := exists_nat_gt (1 / ε)
    refine ⟨N₀ + 1, fun m hm => ?_⟩
    have hdist := truncSimpleFunc_sub_le hA hAsub m hx
    have hlt : 1 / (2 : ℝ) ^ m < ε := by
      have h1 : 1 / ε < (m : ℝ) := lt_of_lt_of_le hN₀ (by exact_mod_cast (Nat.le_succ N₀).trans hm)
      have h2 : (m : ℝ) < (2 : ℝ) ^ m := by exact_mod_cast Nat.lt_two_pow_self
      have h3 : 1 / ε < (2 : ℝ) ^ m := lt_trans h1 h2
      rw [div_lt_iff₀ hε] at h3
      rw [div_lt_iff₀ (by positivity)]
      linarith
    exact lt_of_le_of_lt (by simpa [Real.dist_eq] using hdist) hlt
  have hYm_tendsto_ae : ∀ᵐ ω ∂P, Tendsto (fun m => Ym m ω) atTop (𝓝 (D ω)) := by
    filter_upwards [N.integer_valued hW hWfin] with ω ⟨nW, hnW⟩
    haveI : IsFiniteMeasure ((N.N ω).restrict W) :=
      ⟨by rw [Measure.restrict_apply_univ, hnW]; exact (ENNReal.natCast_ne_top nW).lt_top⟩
    have hXm_tendsto : Tendsto (fun m => Xm m ω) atTop (𝓝 (∫ z in W, z.2 ∂(N.N ω))) := by
      refine MeasureTheory.tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
        (fun m => ((truncSimpleFunc A m).measurable.comp measurable_snd).aestronglyMeasurable)
        (integrable_const 1)
        (fun m => by
          filter_upwards [ae_restrict_mem hW] with z hz
          rw [Real.norm_eq_abs]
          exact (abs_truncSimpleFunc_le hA m z.2).trans (hAsub hz.2).le)
        ?_
      filter_upwards [ae_restrict_mem hW] with z hz
      rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨N₀, hN₀⟩ := exists_nat_gt (1 / ε)
      refine ⟨N₀ + 1, fun m hm => ?_⟩
      have hdist := truncSimpleFunc_sub_le hA hAsub m hz.2
      have hlt : 1 / (2 : ℝ) ^ m < ε := by
        have h1 : 1 / ε < (m : ℝ) := lt_of_lt_of_le hN₀ (by exact_mod_cast (Nat.le_succ N₀).trans hm)
        have h2 : (m : ℝ) < (2 : ℝ) ^ m := by exact_mod_cast Nat.lt_two_pow_self
        have h3 : 1 / ε < (2 : ℝ) ^ m := lt_trans h1 h2
        rw [div_lt_iff₀ hε] at h3
        rw [div_lt_iff₀ (by positivity)]
        linarith
      exact lt_of_le_of_lt (by simpa [Real.dist_eq] using hdist) hlt
    exact hXm_tendsto.sub hμm_tendsto
  -- Apply Fatou's lemma (`lintegral_liminf_le`) on `(Ym m)^2`
  have hYm_meas : ∀ m : ℕ, Measurable (fun ω =>
      (∑ i : Bool × Fin (2 ^ m), truncVal m i * (N.N ω (I ×ˢ truncCell A m i)).toReal) - μm m) :=
    fun m => (Finset.measurable_sum Finset.univ fun i _ =>
      measurable_const.mul (ENNReal.measurable_toReal.comp
        (N.measurable_eval (measurableSet_Ioc.prod (truncCell_measurableSet hA m i))))).sub measurable_const
  let Zm : ℕ → Ω → ℝ := fun m ω =>
    (∑ i : Bool × Fin (2 ^ m), truncVal m i * (N.N ω (I ×ˢ truncCell A m i)).toReal) - μm m
  have hZm_ae : ∀ m, Zm m =ᵐ[P] Ym m := fun m => by
    filter_upwards [hXm_eq_sum m] with ω hω
    dsimp only [Zm, Ym]
    rw [hω]
  have hZm_tendsto_ae : ∀ᵐ ω ∂P, Tendsto (fun m => Zm m ω) atTop (𝓝 (D ω)) := by
    have hall : ∀ᵐ ω ∂P, ∀ m, Zm m ω = Ym m ω := ae_all_iff.mpr hZm_ae
    filter_upwards [hall, hYm_tendsto_ae] with ω h1 h2
    simpa [h1] using h2
  have hfatou : ∫⁻ ω, liminf (fun m => ENNReal.ofReal ((Zm m ω) ^ 2)) atTop ∂P ≤
      liminf (fun m => ∫⁻ ω, ENNReal.ofReal ((Zm m ω) ^ 2) ∂P) atTop :=
    MeasureTheory.lintegral_liminf_le fun m => ENNReal.measurable_ofReal.comp ((hYm_meas m).pow_const 2)
  have hpoint : (fun ω => ENNReal.ofReal ((D ω) ^ 2)) =ᵐ[P]
      fun ω => liminf (fun m => ENNReal.ofReal ((Zm m ω) ^ 2)) atTop := by
    filter_upwards [hZm_tendsto_ae] with ω hω
    have ht : Tendsto (fun m => ENNReal.ofReal ((Zm m ω) ^ 2)) atTop (𝓝 (ENNReal.ofReal ((D ω) ^ 2))) :=
      (ENNReal.continuous_ofReal.tendsto _).comp (hω.pow 2)
    exact ht.liminf_eq.symm
  have hZm_sq_int : ∀ m : ℕ, Integrable (fun ω => (Zm m ω) ^ 2) P := fun m => by
    have hYm_sq_int : Integrable (fun ω => (Ym m ω) ^ 2) P := by
      have hexp : (fun ω => (Ym m ω) ^ 2) =
          fun ω => (Xm m ω) ^ 2 - (2 * μm m) * Xm m ω + (μm m) ^ 2 := by
        funext ω; unfold Ym; ring
      rw [hexp]
      exact ((hXm_sq_int m).sub ((hXm_int_mean m).1.const_mul _)).add (integrable_const _)
    exact hYm_sq_int.congr (by filter_upwards [hZm_ae m] with ω hω; rw [hω])
  have hbound_l : ∀ m : ℕ,
      ∫⁻ ω, ENNReal.ofReal ((Zm m ω) ^ 2) ∂P ≤ ENNReal.ofReal ((K : ℝ) * ∫ x in A, x ^ 2 ∂ν) := fun m => by
    rw [← ofReal_integral_eq_lintegral_ofReal (hZm_sq_int m) (Filter.Eventually.of_forall fun _ => sq_nonneg _)]
    have heq : ∫ ω, (Zm m ω) ^ 2 ∂P = ∫ ω, (Ym m ω) ^ 2 ∂P :=
      integral_congr_ae (by filter_upwards [hZm_ae m] with ω hω; rw [hω])
    rw [heq]
    exact ENNReal.ofReal_le_ofReal (hYm_sq_bound m)
  have hlim_le : liminf (fun m => ∫⁻ ω, ENNReal.ofReal ((Zm m ω) ^ 2) ∂P) atTop ≤
      ENNReal.ofReal ((K : ℝ) * ∫ x in A, x ^ 2 ∂ν) :=
    Filter.liminf_le_of_frequently_le' (Filter.Eventually.of_forall hbound_l).frequently
  have hD_sq_int : Integrable (fun ω => (D ω) ^ 2) P := hDL2.integrable_sq
  have hofReal_le : ENNReal.ofReal (∫ ω, (D ω) ^ 2 ∂P) ≤ ENNReal.ofReal ((K : ℝ) * ∫ x in A, x ^ 2 ∂ν) := by
    rw [ofReal_integral_eq_lintegral_ofReal hD_sq_int (Filter.Eventually.of_forall fun _ => sq_nonneg _),
      lintegral_congr_ae hpoint]
    exact hfatou.trans hlim_le
  have hRHS_nn : 0 ≤ (K : ℝ) * ∫ x in A, x ^ 2 ∂ν :=
    mul_nonneg K.coe_nonneg (integral_nonneg fun _ => sq_nonneg _)
  exact (ENNReal.ofReal_le_ofReal_iff hRHS_nn).mp hofReal_le

/-! ### Section 4: Discrete Doob `L²` maximal inequality on nested dyadic grids -/

private noncomputable def dyadGrid (K : ℝ≥0) (m j : ℕ) : ℝ≥0 :=
  min K ((j : ℝ≥0) * K / ((2 : ℝ≥0) ^ m))

private lemma dyadGrid_mono (K : ℝ≥0) (m : ℕ) : Monotone (dyadGrid K m) := by
  intro i j hij
  unfold dyadGrid
  gcongr

private lemma dyadGrid_top (K : ℝ≥0) (m : ℕ) : dyadGrid K m (2 ^ m) = K := by
  unfold dyadGrid
  have hne : ((2 : ℝ≥0) ^ m) ≠ 0 := by positivity
  have h1 : (((2 ^ m : ℕ) : ℝ≥0) * K / ((2 : ℝ≥0) ^ m)) = K := by
    push_cast
    exact mul_div_cancel_left₀ K hne
  rw [h1, min_self]

private lemma dyadGrid_double (K : ℝ≥0) (m j : ℕ) :
    dyadGrid K (m + 1) (2 * j) = dyadGrid K m j := by
  unfold dyadGrid
  congr 1
  push_cast
  rw [pow_succ']
  have h2 : (2 : ℝ≥0) ≠ 0 := by positivity
  have h2m : (2 : ℝ≥0) ^ m ≠ 0 := by positivity
  rw [mul_assoc, mul_div_mul_left _ _ h2]

private lemma martingale_sq_doob_dyadic_bound
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {D : ℝ≥0 → Ω → ℝ} (hM : Martingale D ℱ P) (hL2 : ∀ t : ℝ≥0, MemLp (D t) 2 P)
    (K : ℝ≥0) {c : ℝ≥0} (hc : 0 < c) :
    P (⋃ m : ℕ, {ω | ∃ j ≤ 2 ^ m, (c : ℝ) ≤ |D (dyadGrid K m j) ω|}) ≤
      ENNReal.ofReal ((∫ ω, (D K ω) ^ 2 ∂P) / (c : ℝ) ^ 2) := by
  let Bad : ℕ → Set Ω := fun m => {ω | ∃ j ≤ 2 ^ m, (c : ℝ) ≤ |D (dyadGrid K m j) ω|}
  have hBad_mono : Monotone Bad := by
    intro m₁ m₂ hm ω ⟨j, hj, hle⟩
    induction hm with
    | refl => exact ⟨j, hj, hle⟩
    | step _ ih =>
      rcases ih with ⟨j', hj', hle'⟩
      refine ⟨2 * j', ?_, ?_⟩
      · rw [pow_succ']; omega
      · rwa [dyadGrid_double]
  have hstep_bd : ∀ m : ℕ,
      ((c ^ 2 : ℝ≥0) : ℝ≥0∞) * P (Bad m) ≤ ENNReal.ofReal (∫ ω, (D K ω) ^ 2 ∂P) := by
    intro m
    let 𝒢 : Filtration ℕ (inferInstance : MeasurableSpace Ω) :=
      { seq := fun j => ℱ (dyadGrid K m j)
        mono' := fun _ _ h => ℱ.mono (dyadGrid_mono K m h)
        le' := fun j => ℱ.le (dyadGrid K m j) }
    let f : ℕ → Ω → ℝ := fun j ω => (D (dyadGrid K m j) ω) ^ 2
    have hSub : Submartingale f 𝒢 P := by
      refine submartingale_of_setIntegral_le
        (fun j => (hM.stronglyAdapted (dyadGrid K m j)).pow 2)
        (fun j => (hL2 (dyadGrid K m j)).integrable_sq)
        ?_
      intro i j hij s hs
      let X := D (dyadGrid K m i)
      let Y := D (dyadGrid K m j)
      have hX_sm : StronglyMeasurable[ℱ (dyadGrid K m i)] X := hM.stronglyAdapted (dyadGrid K m i)
      have hX_L2 : MemLp X 2 P := hL2 (dyadGrid K m i)
      have hY_L2 : MemLp Y 2 P := hL2 (dyadGrid K m j)
      have hYX_L2 : MemLp (Y - X) 2 P := hY_L2.sub hX_L2
      have hprod_int : Integrable (X * (Y - X)) P := hX_L2.integrable_mul hYX_L2
      have hce_diff : P[Y - X | ℱ (dyadGrid K m i)] =ᵐ[P] 0 := by
        have h1 := condExp_sub (hM.integrable (dyadGrid K m j)) (hM.integrable (dyadGrid K m i))
          (ℱ (dyadGrid K m i))
        have h2 := hM.condExp_ae_eq (dyadGrid_mono K m hij)
        have h3 := condExp_of_stronglyMeasurable (ℱ.le (dyadGrid K m i)) hX_sm
          (hM.integrable (dyadGrid K m i))
        filter_upwards [h1, h2] with ω hω1 hω2
        simp only [Pi.sub_apply, Pi.zero_apply] at hω1 hω2 ⊢
        rw [hω1, hω2, h3, sub_self]
      have hce_prod : P[X * (Y - X) | ℱ (dyadGrid K m i)] =ᵐ[P] 0 := by
        have h1 := condExp_mul_of_stronglyMeasurable_left hX_sm hprod_int
          ((hM.integrable (dyadGrid K m j)).sub (hM.integrable (dyadGrid K m i)))
        filter_upwards [h1, hce_diff] with ω hω1 hω2
        simp only [Pi.mul_apply, Pi.zero_apply] at hω1 hω2 ⊢
        rw [hω1, hω2, mul_zero]
      have hcross_zero : ∫ ω in s, X ω * (Y ω - X ω) ∂P = 0 := by
        have h1 := setIntegral_condExp (ℱ.le (dyadGrid K m i)) hprod_int hs
        have h2 : ∫ ω in s, P[X * (Y - X) | ℱ (dyadGrid K m i)] ω ∂P = 0 := by
          rw [integral_congr_ae (ae_restrict_of_ae hce_prod)]
          simp
        exact h1.symm.trans h2
      have hident : (fun ω => (Y ω) ^ 2 - (X ω) ^ 2) =
          fun ω => (Y ω - X ω) ^ 2 + 2 * (X ω * (Y ω - X ω)) := by
        funext ω; ring
      have hsub_nn : 0 ≤ ∫ ω in s, ((Y ω) ^ 2 - (X ω) ^ 2) ∂P := by
        have h1 : Integrable (fun ω => (Y ω - X ω) ^ 2) (P.restrict s) :=
          hYX_L2.integrable_sq.integrableOn
        have h2 : Integrable (fun ω => 2 * (X ω * (Y ω - X ω))) (P.restrict s) :=
          (hprod_int.const_mul 2).integrableOn
        rw [hident, integral_add h1 h2, integral_const_mul, hcross_zero, mul_zero, add_zero]
        exact integral_nonneg fun _ => sq_nonneg _
      have hsub_eq : ∫ ω in s, ((Y ω) ^ 2 - (X ω) ^ 2) ∂P =
          (∫ ω in s, (Y ω) ^ 2 ∂P) - ∫ ω in s, (X ω) ^ 2 ∂P :=
        integral_sub hY_L2.integrable_sq.integrableOn hX_L2.integrable_sq.integrableOn
      linarith
    have hmax := MeasureTheory.maximal_ineq hSub (fun _ _ => sq_nonneg _) (ε := c ^ 2) (2 ^ m)
    have hset_eq : Bad m =
        {ω | ((c ^ 2 : ℝ≥0) : ℝ) ≤ (Finset.range (2 ^ m + 1)).sup' Finset.nonempty_range_add_one
          fun j => f j ω} := by
      ext ω
      simp only [Bad, Set.mem_setOf_eq, Finset.le_sup'_iff, Finset.mem_range, Nat.lt_succ_iff, f]
      refine ⟨fun ⟨j, hj, hle⟩ => ⟨j, hj, ?_⟩, fun ⟨j, hj, hle⟩ => ⟨j, hj, ?_⟩⟩
      · have := pow_le_pow_left₀ c.coe_nonneg hle 2
        simpa [sq_abs] using this
      · have h1 : (c : ℝ) ^ 2 ≤ |D (dyadGrid K m j) ω| ^ 2 := by simpa [sq_abs] using hle
        nlinarith [abs_nonneg (D (dyadGrid K m j) ω), c.coe_nonneg]
    rw [hset_eq]
    have hint_le : ∫ ω in {ω | ((c ^ 2 : ℝ≥0) : ℝ) ≤
        (Finset.range (2 ^ m + 1)).sup' Finset.nonempty_range_add_one fun j => f j ω},
        f (2 ^ m) ω ∂P ≤ ∫ ω, (D K ω) ^ 2 ∂P := by
      have hfn : f (2 ^ m) = fun ω => (D K ω) ^ 2 := by
        funext ω; simp [f, dyadGrid_top]
      rw [hfn]
      exact setIntegral_le_integral (hL2 K).integrable_sq
        (Filter.Eventually.of_forall fun _ => sq_nonneg _)
    exact hmax.trans (ENNReal.ofReal_le_ofReal hint_le)
  have hUnion_le : ((c ^ 2 : ℝ≥0) : ℝ≥0∞) * P (⋃ m : ℕ, Bad m) ≤
      ENNReal.ofReal (∫ ω, (D K ω) ^ 2 ∂P) := by
    have ht : Tendsto (fun m => ((c ^ 2 : ℝ≥0) : ℝ≥0∞) * P (Bad m)) atTop
        (𝓝 (((c ^ 2 : ℝ≥0) : ℝ≥0∞) * P (⋃ m : ℕ, Bad m))) :=
      ENNReal.Tendsto.const_mul (MeasureTheory.tendsto_measure_iUnion_atTop hBad_mono)
        (Or.inr ENNReal.coe_ne_top)
    exact le_of_tendsto ht (Filter.Eventually.of_forall hstep_bd)
  have hc2_pos : (0 : ℝ≥0∞) < ((c ^ 2 : ℝ≥0) : ℝ≥0∞) := by
    exact_mod_cast pow_pos hc 2
  have hc2_ne_top : ((c ^ 2 : ℝ≥0) : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast pow_pos hc 2)]
  rw [ENNReal.le_div_iff_mul_le (Or.inl (by positivity)) (Or.inl ENNReal.ofReal_ne_top)]
  have hcast : ENNReal.ofReal ((c : ℝ) ^ 2) = ((c ^ 2 : ℝ≥0) : ℝ≥0∞) := by
    rw [← NNReal.coe_pow, ENNReal.ofReal_coe_nnreal]
  rw [hcast, mul_comm]
  exact hUnion_le

/-! ### Section 5: Right-continuity lifts dyadic uniform bound to all real `t ≤ K` -/

private lemma right_continuous_band_bound
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure ℝ} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    {A : Set ℝ} (hA : MeasurableSet A) (hAsub : A ⊆ {x : ℝ | |x| < 1})
    (K : ℝ≥0) (hK : 0 < K) {c : ℝ≥0} {ω : Ω}
    (hfin : N.N ω (Set.Ioc (0 : ℝ) (K : ℝ) ×ˢ A) ≠ ⊤)
    (hdyad : ∀ m : ℕ, ∀ j ≤ 2 ^ m,
      |(∫ z in (Set.Ioc (0 : ℝ) (dyadGrid K m j : ℝ) ×ˢ A), z.2 ∂(N.N ω)) -
        (dyadGrid K m j : ℝ) * (∫ x in A, x ∂ν)| < (c : ℝ)) :
    ∀ t : ℝ≥0, t ≤ K →
      |(∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ A), z.2 ∂(N.N ω)) -
        (t : ℝ) * (∫ x in A, x ∂ν)| ≤ (c : ℝ) := by
  let D : ℝ≥0 → ℝ := fun r =>
    (∫ z in (Set.Ioc (0 : ℝ) (r : ℝ) ×ˢ A), z.2 ∂(N.N ω)) - (r : ℝ) * (∫ x in A, x ∂ν)
  let W := Set.Ioc (0 : ℝ) (K : ℝ) ×ˢ A
  have hW : MeasurableSet W := measurableSet_Ioc.prod hA
  haveI : IsFiniteMeasure ((N.N ω).restrict W) := ⟨by rw [Measure.restrict_apply_univ]; exact hfin.lt_top⟩
  have hz_int_W : Integrable (fun z : ℝ × ℝ => z.2) ((N.N ω).restrict W) :=
    Integrable.mono' (integrable_const 1) measurable_snd.aestronglyMeasurable
      (by
        filter_upwards [ae_restrict_mem hW] with z hz
        rw [Real.norm_eq_abs]; exact (hAsub hz.2).le)
  intro t ht
  rcases eq_or_lt_of_le ht with rfl | ht_lt
  · have hKeq : dyadGrid t 0 1 = t := by simpa using dyadGrid_top t 0
    have h0 := hdyad 0 1 (by norm_num)
    simpa [hKeq] using h0.le
  · -- Approximate `t < K` from the right by dyadic grid points `q m := dyadGrid K m (j m)`
    let j : ℕ → ℕ := fun m => ⌊((t : ℝ) / (K : ℝ)) * (2 : ℝ) ^ m⌋₊ + 1
    have hj_le : ∀ m : ℕ, j m ≤ 2 ^ m := fun m => by
      have hfrac : (t : ℝ) / (K : ℝ) < 1 := (div_lt_one (by exact_mod_cast hK)).mpr (by exact_mod_cast ht_lt)
      have hmul : ((t : ℝ) / (K : ℝ)) * (2 : ℝ) ^ m < ((2 ^ m : ℕ) : ℝ) := by
        push_cast; linarith [mul_lt_mul_of_pos_right hfrac (by positivity : (0 : ℝ) < (2 : ℝ) ^ m)]
      have hfl : ⌊((t : ℝ) / (K : ℝ)) * (2 : ℝ) ^ m⌋₊ < 2 ^ m :=
        (Nat.floor_lt (by positivity)).mpr hmul
      dsimp only [j]
      omega
    let q : ℕ → ℝ≥0 := fun m => dyadGrid K m (j m)
    have hq_bounds : ∀ m : ℕ, (t : ℝ) < (q m : ℝ) ∧ (q m : ℝ) ≤ (t : ℝ) + (K : ℝ) / (2 : ℝ) ^ m := by
      intro m
      have h2m : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
      have hK_pos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
      have hratio_le : ((j m : ℝ) * (K : ℝ)) / (2 : ℝ) ^ m ≤ (K : ℝ) := by
        rw [div_le_iff₀ h2m]
        have hj_r : (j m : ℝ) ≤ (2 : ℝ) ^ m := by exact_mod_cast hj_le m
        nlinarith
      have hq_val : (q m : ℝ) = ((j m : ℝ) * (K : ℝ)) / (2 : ℝ) ^ m := by
        have hmin : (j m : ℝ≥0) * K / ((2 : ℝ≥0) ^ m) ≤ K := by exact_mod_cast hratio_le
        have hqeq : q m = (j m : ℝ≥0) * K / ((2 : ℝ≥0) ^ m) := min_eq_right hmin
        rw [hqeq]
        push_cast; rfl
      rw [hq_val]
      constructor
      · have hfl : ((t : ℝ) / (K : ℝ)) * (2 : ℝ) ^ m < (j m : ℝ) := by
          dsimp only [j]; push_cast
          exact Nat.lt_floor_add_one (((t : ℝ) / (K : ℝ)) * (2 : ℝ) ^ m)
        rw [lt_div_iff₀ h2m]
        have := mul_lt_mul_of_pos_right hfl hK_pos
        field_simp [hK_pos.ne'] at this
        linarith
      · have hfl : (j m : ℝ) ≤ ((t : ℝ) / (K : ℝ)) * (2 : ℝ) ^ m + 1 := by
          dsimp only [j]; push_cast
          linarith [Nat.floor_le (by positivity : (0 : ℝ) ≤ ((t : ℝ) / (K : ℝ)) * (2 : ℝ) ^ m)]
        have := mul_le_mul_of_nonneg_right hfl hK_pos.le
        rw [div_le_iff₀ h2m]
        have h1 : (((t : ℝ) / (K : ℝ)) * (2 : ℝ) ^ m + 1) * (K : ℝ) =
            (t : ℝ) * (2 : ℝ) ^ m + (K : ℝ) := by field_simp [hK_pos.ne']
        have h2 : ((t : ℝ) + (K : ℝ) / (2 : ℝ) ^ m) * (2 : ℝ) ^ m =
            (t : ℝ) * (2 : ℝ) ^ m + (K : ℝ) := by field_simp [h2m.ne']
        linarith
    have hq_le_K : ∀ m : ℕ, q m ≤ K := fun m => min_le_left _ _
    have hq_tendsto : Tendsto (fun m => (q m : ℝ)) atTop (𝓝 (t : ℝ)) := by
      have hgeom : Tendsto (fun m : ℕ => (K : ℝ) / (2 : ℝ) ^ m) atTop (𝓝 0) := by
        have h1 : Tendsto (fun m : ℕ => (1 / 2 : ℝ) ^ m) atTop (𝓝 0) :=
          tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
        simpa [div_eq_mul_inv, one_div, inv_pow] using h1.const_mul (K : ℝ)
      have hhi : Tendsto (fun m : ℕ => (t : ℝ) + (K : ℝ) / (2 : ℝ) ^ m) atTop (𝓝 (t : ℝ)) := by
        simpa using (tendsto_const_nhds (x := (t : ℝ))).add hgeom
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hhi
        (fun m => (hq_bounds m).1.le) (fun m => (hq_bounds m).2)
    -- Antitone envelope `Senv m` covering `(t, q m] × A` with empty intersection
    let Senv : ℕ → Set (ℝ × ℝ) := fun m =>
      Set.Ioc (t : ℝ) (min (K : ℝ) ((t : ℝ) + (K : ℝ) / (2 : ℝ) ^ m)) ×ˢ A
    have hSenv_meas : ∀ m, MeasurableSet (Senv m) := fun _ => measurableSet_Ioc.prod hA
    have hSenv_sub : ∀ m, Senv m ⊆ W := fun m =>
      Set.prod_mono (Set.Ioc_subset_Ioc t.coe_nonneg (min_le_left _ _)) le_rfl
    have hSenv_anti : Antitone Senv := fun m₁ m₂ hm => by
      refine Set.prod_mono (Set.Ioc_subset_Ioc_right (min_le_min le_rfl ?_)) le_rfl
      gcongr
      norm_num
    have hSenv_iInter : (⋂ m : ℕ, Senv m) = ∅ := by
      ext z
      simp only [Set.mem_iInter, Set.mem_empty_iff_false, iff_false, not_forall]
      by_cases hzt : (t : ℝ) < z.1
      · have hgeom : Tendsto (fun m : ℕ => (t : ℝ) + (K : ℝ) / (2 : ℝ) ^ m) atTop (𝓝 (t : ℝ)) := by
          have h1 : Tendsto (fun m : ℕ => (1 / 2 : ℝ) ^ m) atTop (𝓝 0) :=
            tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
          have h2 : Tendsto (fun m : ℕ => (K : ℝ) / (2 : ℝ) ^ m) atTop (𝓝 0) := by
            simpa [div_eq_mul_inv, one_div, inv_pow] using h1.const_mul (K : ℝ)
          simpa using (tendsto_const_nhds (x := (t : ℝ))).add h2
        obtain ⟨m, hm⟩ := (hgeom.eventually (gt_mem_nhds hzt)).exists
        refine ⟨m, fun hz => ?_⟩
        exact not_lt_of_ge (hz.1.2.trans (min_le_right _ _)) hm
      · exact ⟨0, fun hz => hzt hz.1.1⟩
    have hSenv_tendsto : Tendsto (fun m => N.N ω (Senv m)) atTop (𝓝 0) := by
      have ht' := MeasureTheory.tendsto_measure_iInter_atTop
        (fun m => (hSenv_meas m).nullMeasurableSet) hSenv_anti
        ⟨0, ne_top_of_le_ne_top hfin (measure_mono (hSenv_sub 0))⟩
      simpa [hSenv_iInter, Function.comp_def] using ht'
    have hSenv_toReal : Tendsto (fun m => (N.N ω (Senv m)).toReal) atTop (𝓝 0) := by
      simpa [Function.comp_def] using (ENNReal.continuousAt_toReal (by simp)).tendsto.comp hSenv_tendsto
    have hgap_int_zero : Tendsto (fun m => ∫ z in (Set.Ioc (t : ℝ) (q m : ℝ) ×ˢ A), z.2 ∂(N.N ω))
        atTop (𝓝 0) := by
      refine squeeze_zero_norm (fun m => ?_) hSenv_toReal
      rw [Real.norm_eq_abs]
      let Ggap := Set.Ioc (t : ℝ) (q m : ℝ) ×ˢ A
      have hGgap_sub_env : Ggap ⊆ Senv m :=
        Set.prod_mono (Set.Ioc_subset_Ioc_right (le_min (by exact_mod_cast hq_le_K m) (hq_bounds m).2)) le_rfl
      have hGgap_sub_W : Ggap ⊆ W := hGgap_sub_env.trans (hSenv_sub m)
      haveI : IsFiniteMeasure ((N.N ω).restrict Ggap) :=
        ⟨by rw [Measure.restrict_apply_univ]; exact lt_of_le_of_lt (measure_mono hGgap_sub_W) hfin.lt_top⟩
      have h1 : |∫ z in Ggap, z.2 ∂(N.N ω)| ≤ ∫ z in Ggap, |z.2| ∂(N.N ω) :=
        abs_integral_le_integral_abs
      have h2 : ∫ z in Ggap, |z.2| ∂(N.N ω) ≤ ∫ _ in Ggap, (1 : ℝ) ∂(N.N ω) := by
        refine integral_mono_ae (MeasureTheory.IntegrableOn.mono_set hz_int_W.abs hGgap_sub_W)
          (integrable_const 1) ?_
        filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod hA)] with z hz
        exact (hAsub hz.2).le
      have h3 : ∫ _ in Ggap, (1 : ℝ) ∂(N.N ω) = (N.N ω Ggap).toReal := by
        rw [setIntegral_const, Measure.real, smul_eq_mul, mul_one]
      have h4 : (N.N ω Ggap).toReal ≤ (N.N ω (Senv m)).toReal :=
        ENNReal.toReal_mono (ne_top_of_le_ne_top hfin (measure_mono (hSenv_sub m)))
          (measure_mono hGgap_sub_env)
      linarith
    have hD_split : ∀ m : ℕ,
        D (q m) = D t + (∫ z in (Set.Ioc (t : ℝ) (q m : ℝ) ×ˢ A), z.2 ∂(N.N ω)) -
          ((q m : ℝ) - (t : ℝ)) * (∫ x in A, x ∂ν) := fun m => by
      have hunion : (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ A) ∪ (Set.Ioc (t : ℝ) (q m : ℝ) ×ˢ A) =
          Set.Ioc (0 : ℝ) (q m : ℝ) ×ˢ A := by
        rw [← Set.union_prod, Set.Ioc_union_Ioc_eq_Ioc t.coe_nonneg (hq_bounds m).1.le]
      have hdisj : Disjoint (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ A) (Set.Ioc (t : ℝ) (q m : ℝ) ×ˢ A) := by
        rw [Set.disjoint_left]; intro z hz1 hz2; exact not_lt_of_ge hz1.1.2 hz2.1.1
      have hsub1 : Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ A ⊆ W :=
        Set.prod_mono (Set.Ioc_subset_Ioc_right (by exact_mod_cast ht_lt.le)) le_rfl
      have hsub2 : Set.Ioc (t : ℝ) (q m : ℝ) ×ˢ A ⊆ W :=
        Set.prod_mono (Set.Ioc_subset_Ioc t.coe_nonneg (by exact_mod_cast hq_le_K m)) le_rfl
      have hadd := setIntegral_union hdisj (measurableSet_Ioc.prod hA)
        (MeasureTheory.IntegrableOn.mono_set hz_int_W hsub1)
        (MeasureTheory.IntegrableOn.mono_set hz_int_W hsub2)
      rw [hunion] at hadd
      dsimp only [D]
      rw [hadd]
      ring
    have hD_tendsto : Tendsto (fun m => D (q m)) atTop (𝓝 (D t)) := by
      simp_rw [hD_split]
      have hdrift : Tendsto (fun m => ((q m : ℝ) - (t : ℝ)) * (∫ x in A, x ∂ν)) atTop (𝓝 0) := by
        simpa using (hq_tendsto.sub (tendsto_const_nhds (x := (t : ℝ)))).mul_const (∫ x in A, x ∂ν)
      have h1 := (tendsto_const_nhds (x := D t)).add hgap_int_zero
      simpa using h1.sub hdrift
    have hD_abs_tendsto : Tendsto (fun m => |D (q m)|) atTop (𝓝 |D t|) :=
      continuous_abs.continuousAt.tendsto.comp hD_tendsto
    exact le_of_tendsto hD_abs_tendsto (Filter.Eventually.of_forall fun m => (hdyad m (j m) (hj_le m)).le)

end CompensatedSmallJumpLimitHelpers

namespace SmallJumpCoreHelpers

/-! ### Section 6: Preservation of `IdentDistrib` and `iIndepFun` under a.e. limits -/

private lemma cexp_norm_one (r : ℝ) :
    ‖Complex.exp ((r : ℂ) * Complex.I)‖ = 1 := by
  exact Complex.norm_exp_ofReal_mul_I r

private lemma identDistrib_of_tendsto_ae
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {f_n g_n : ℕ → Ω → ℝ} {f g : Ω → ℝ}
    (hfn : ∀ n, Measurable (f_n n)) (hgn : ∀ n, Measurable (g_n n))
    (hf : Measurable f) (hg : Measurable g)
    (hid : ∀ n, IdentDistrib (f_n n) (g_n n) P P)
    (hconvf : ∀ᵐ ω ∂P, Tendsto (fun n => f_n n ω) atTop (𝓝 (f ω)))
    (hconvg : ∀ᵐ ω ∂P, Tendsto (fun n => g_n n ω) atTop (𝓝 (g ω))) :
    IdentDistrib f g P P := by
  refine ⟨hf.aemeasurable, hg.aemeasurable, ?_⟩
  apply Measure.ext_of_charFun
  ext ξ
  have hchar : ∀ h : Ω → ℝ, Measurable h →
      charFun (P.map h) ξ = ∫ ω, Complex.exp (((ξ * h ω : ℝ) : ℂ) * Complex.I) ∂P := by
    intro h hh
    rw [charFun_apply_real]
    have hcont : Continuous (fun x : ℝ => Complex.exp ((ξ : ℂ) * (x : ℂ) * Complex.I)) := by
      fun_prop
    rw [integral_map hh.aemeasurable hcont.aestronglyMeasurable]
    congr 1; funext ω; push_cast; rfl
  have htf : Tendsto (fun n => charFun (P.map (f_n n)) ξ) atTop (𝓝 (charFun (P.map f) ξ)) := by
    simp_rw [hchar _ (hfn _), hchar f hf]
    refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ)) ?_ (integrable_const 1) ?_ ?_
    · intro n
      have hcont : Continuous (fun x : ℝ => Complex.exp (((ξ * x : ℝ) : ℂ) * Complex.I)) := by
        fun_prop
      exact (hcont.measurable.comp (hfn n)).aestronglyMeasurable
    · intro n
      exact Filter.Eventually.of_forall fun ω => by rw [cexp_norm_one]
    · filter_upwards [hconvf] with ω hω
      have hcont : Continuous (fun x : ℝ => Complex.exp (((ξ * x : ℝ) : ℂ) * Complex.I)) := by
        fun_prop
      exact hcont.continuousAt.tendsto.comp hω
  have htg : Tendsto (fun n => charFun (P.map (g_n n)) ξ) atTop (𝓝 (charFun (P.map g) ξ)) := by
    simp_rw [hchar _ (hgn _), hchar g hg]
    refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ)) ?_ (integrable_const 1) ?_ ?_
    · intro n
      have hcont : Continuous (fun x : ℝ => Complex.exp (((ξ * x : ℝ) : ℂ) * Complex.I)) := by
        fun_prop
      exact (hcont.measurable.comp (hgn n)).aestronglyMeasurable
    · intro n
      exact Filter.Eventually.of_forall fun ω => by rw [cexp_norm_one]
    · filter_upwards [hconvg] with ω hω
      have hcont : Continuous (fun x : ℝ => Complex.exp (((ξ * x : ℝ) : ℂ) * Complex.I)) := by
        fun_prop
      exact hcont.continuousAt.tendsto.comp hω
  have heq : (fun n => charFun (P.map (f_n n)) ξ) = (fun n => charFun (P.map (g_n n)) ξ) := by
    funext n
    rw [(hid n).map_eq]
  rw [heq] at htf
  exact tendsto_nhds_unique htf htg

private lemma iIndepFun_of_tendsto_ae
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {k : ℕ} {f_n : ℕ → Fin k → Ω → ℝ} {f : Fin k → Ω → ℝ}
    (hfn : ∀ n i, Measurable (f_n n i)) (hf : ∀ i, Measurable (f i))
    (hind : ∀ n, iIndepFun (f_n n) P)
    (hconv : ∀ i, ∀ᵐ ω ∂P, Tendsto (fun n => f_n n i ω) atTop (𝓝 (f i ω))) :
    iIndepFun f P := by
  rw [iIndepFun_iff_map_fun_eq_pi_map (fun i => (hf i).aemeasurable)]
  haveI : ∀ i, IsProbabilityMeasure (P.map (f i)) := fun i =>
    Measure.isProbabilityMeasure_map (hf i).aemeasurable
  haveI : IsProbabilityMeasure (P.map (fun ω i => f i ω)) :=
    Measure.isProbabilityMeasure_map (measurable_pi_lambda _ hf).aemeasurable
  apply Measure.ext_of_charFunDual
  ext L
  have hL_sum : ∀ x : Fin k → ℝ, L x = ∑ i : Fin k, x i * L (Pi.single i 1) := by
    intro x
    have hx : x = ∑ i : Fin k, x i • Pi.single i (1 : ℝ) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hx]
    rw [map_sum]
    congr 1; funext i
    rw [map_smul, smul_eq_mul]
  have hL_exp : ∀ x : Fin k → ℝ,
      Complex.exp ((L x : ℂ) * Complex.I) =
        ∏ i : Fin k, Complex.exp (((L (Pi.single i 1) * x i : ℝ) : ℂ) * Complex.I) := by
    intro x
    rw [hL_sum x, ← Complex.exp_sum]
    congr 1
    push_cast
    rw [Finset.sum_mul]
    congr 1; funext i; ring
  have hLHS : ∀ g : Fin k → Ω → ℝ, (∀ i, Measurable (g i)) →
      charFunDual (P.map (fun ω i => g i ω)) L =
        ∫ ω, Complex.exp ((L (fun i => g i ω) : ℂ) * Complex.I) ∂P := by
    intro g hg
    rw [charFunDual_apply]
    have hcont : Continuous (fun v : Fin k → ℝ => Complex.exp ((L v : ℂ) * Complex.I)) := by
      fun_prop
    exact integral_map (measurable_pi_lambda _ hg).aemeasurable hcont.aestronglyMeasurable
  have hRHS : ∀ g : Fin k → Ω → ℝ, (∀ i, Measurable (g i)) →
      charFunDual (Measure.pi (fun i => P.map (g i))) L =
        ∏ i : Fin k, ∫ ω, Complex.exp (((L (Pi.single i 1) * g i ω : ℝ) : ℂ) * Complex.I) ∂P := by
    intro g hg
    haveI : ∀ i, IsProbabilityMeasure (P.map (g i)) := fun i =>
      Measure.isProbabilityMeasure_map (hg i).aemeasurable
    rw [charFunDual_apply]
    simp_rw [hL_exp]
    rw [integral_fintype_prod_eq_prod (f := fun i (x : ℝ) =>
      Complex.exp (((L (Pi.single i 1) * x : ℝ) : ℂ) * Complex.I))]
    congr 1; funext i
    have hcont : Continuous (fun x : ℝ => Complex.exp (((L (Pi.single i 1) * x : ℝ) : ℂ) * Complex.I)) := by
      fun_prop
    exact integral_map (hg i).aemeasurable hcont.aestronglyMeasurable
  have heq_n : ∀ n,
      charFunDual (P.map (fun ω i => f_n n i ω)) L =
        charFunDual (Measure.pi (fun i => P.map (f_n n i))) L := by
    intro n
    rw [(iIndepFun_iff_map_fun_eq_pi_map (fun i => (hfn n i).aemeasurable)).mp (hind n)]
  have hconv_all : ∀ᵐ ω ∂P, ∀ i : Fin k, Tendsto (fun n => f_n n i ω) atTop (𝓝 (f i ω)) :=
    ae_all_iff.mpr hconv
  have htL : Tendsto (fun n => charFunDual (P.map (fun ω i => f_n n i ω)) L) atTop
      (𝓝 (charFunDual (P.map (fun ω i => f i ω)) L)) := by
    simp_rw [hLHS _ (hfn _), hLHS f hf]
    refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ)) ?_ (integrable_const 1) ?_ ?_
    · intro n
      have hcont : Continuous (fun v : Fin k → ℝ => Complex.exp ((L v : ℂ) * Complex.I)) := by
        fun_prop
      exact (hcont.measurable.comp (measurable_pi_lambda _ (hfn n))).aestronglyMeasurable
    · intro n
      exact Filter.Eventually.of_forall fun ω => by rw [cexp_norm_one]
    · filter_upwards [hconv_all] with ω hω
      have hcont : Continuous (fun v : Fin k → ℝ => Complex.exp ((L v : ℂ) * Complex.I)) := by
        fun_prop
      exact hcont.continuousAt.tendsto.comp (tendsto_pi_nhds.mpr hω)
  have htR : Tendsto (fun n => charFunDual (Measure.pi (fun i => P.map (f_n n i))) L) atTop
      (𝓝 (charFunDual (Measure.pi (fun i => P.map (f i))) L)) := by
    simp_rw [hRHS _ (hfn _), hRHS f hf]
    refine tendsto_finset_prod Finset.univ fun i _ => ?_
    refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ)) ?_ (integrable_const 1) ?_ ?_
    · intro n
      have hcont : Continuous (fun x : ℝ => Complex.exp (((L (Pi.single i 1) * x : ℝ) : ℂ) * Complex.I)) := by
        fun_prop
      exact (hcont.measurable.comp (hfn n i)).aestronglyMeasurable
    · intro n
      exact Filter.Eventually.of_forall fun ω => by rw [cexp_norm_one]
    · filter_upwards [hconv i] with ω hω
      have hcont : Continuous (fun x : ℝ => Complex.exp (((L (Pi.single i 1) * x : ℝ) : ℂ) * Complex.I)) := by
        fun_prop
      exact hcont.continuousAt.tendsto.comp hω
  have htL' : Tendsto (fun n => charFunDual (Measure.pi (fun i => P.map (f_n n i))) L) atTop
      (𝓝 (charFunDual (P.map (fun ω i => f i ω)) L)) := by
    simpa only [heq_n] using htL
  exact tendsto_nhds_unique htL' htR

/-! ### Section 7: `L²` integrability and `L¹` convergence helper from `lintegral` square bound -/

private lemma memLp_two_and_sq_integral_le_of_lintegral_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {g : Ω → ℝ} (hg : Measurable g) {C : ℝ} (hC : 0 ≤ C)
    (hlint : ∫⁻ ω, ENNReal.ofReal ((g ω) ^ 2) ∂P ≤ ENNReal.ofReal C) :
    MemLp g 2 P ∧ ∫ ω, (g ω) ^ 2 ∂P ≤ C := by
  have hfin_sq : HasFiniteIntegral (fun ω => (g ω) ^ 2) P := by
    rw [HasFiniteIntegral]
    have heq : (fun ω => ‖(g ω) ^ 2‖ₑ) = (fun ω => ENNReal.ofReal ((g ω) ^ 2)) := by
      funext ω
      rw [Real.enorm_eq_ofReal (sq_nonneg _)]
    rw [heq]
    exact lt_of_le_of_lt hlint ENNReal.ofReal_lt_top
  have hint_sq : Integrable (fun ω => (g ω) ^ 2) P :=
    ⟨(hg.pow_const 2).aestronglyMeasurable, hfin_sq⟩
  have hmem2 : MemLp g 2 P :=
    (memLp_two_iff_integrable_sq hg.aestronglyMeasurable).mpr hint_sq
  have hint_le : ∫ ω, (g ω) ^ 2 ∂P ≤ C := by
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun _ => sq_nonneg _)
      (hg.pow_const 2).aestronglyMeasurable]
    have h1 := ENNReal.toReal_mono ENNReal.ofReal_ne_top hlint
    rwa [ENNReal.toReal_ofReal hC] at h1
  exact ⟨hmem2, hint_le⟩

end SmallJumpCoreHelpers

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (levyMeasure : Measure ℝ) [SigmaFinite levyMeasure]
    (hlevyMeasure : ProbabilityTheory.IsLevyMeasure levyMeasure)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P levyMeasure) :
    ∃ (M : ℝ≥0 → Ω → ℝ)
      (ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)),
      ProbabilityTheory.IsLevyProcess M P ∧
      Kyprianou.Ch02.IsCompletedPoissonFiltration P levyMeasure N ℱ ∧
      MeasureTheory.Martingale M ℱ P ∧
      (∀ t, MemLp (M t) 2 P) ∧
      ∀ T : ℝ≥0, 0 < T →
        ∃ ε : ℕ → ℝ,
          StrictAnti ε ∧
          (∀ n, 0 < ε n ∧ ε n < 1) ∧
          Tendsto ε Filter.atTop (nhds 0) ∧
          (∀ᵐ ω ∂P, ∀ δ : ℝ, 0 < δ →
            ∃ n₀ : ℕ, ∀ n ≥ n₀,
              ∀ t : ℝ≥0, t ≤ T →
                |Kyprianou.compensatedSmallJumpBand P levyMeasure N (ε n) t ω -
                    M t ω| < δ) := by
  -- Step 1: Completed Poisson filtration `ℱ` from already-`Proved` `completedPoissonFiltrationExistsGeneralV1`
  obtain ⟨ℱ, hℱ⟩ :=
    Kyprianou.Ch02.completedPoissonFiltrationExistsGeneralV1 P levyMeasure N
  -- Step 2: Global rapidly-decaying cutoff sequence `ε n ↓ 0` with `∫_{0 < |x| < ε n} x^2 ∂ν ≤ 1 / 16^n`
  obtain ⟨ε, hε_anti, hε_bounds, hε_tendsto, hε_int⟩ :=
    CompensatedSmallJumpLimitHelpers.exists_small_jump_seq hlevyMeasure
  let B : ℕ → Set ℝ := fun n => {x : ℝ | ε n ≤ |x| ∧ |x| < 1}
  let A : ℕ → Set ℝ := fun n => {x : ℝ | ε (n + 1) ≤ |x| ∧ |x| < ε n}
  have hB_meas : ∀ n, MeasurableSet (B n) := fun n =>
    CompensatedSmallJumpLimitHelpers.band_measurableSet (ε n) 1
  have hA_meas : ∀ n, MeasurableSet (A n) := fun n =>
    CompensatedSmallJumpLimitHelpers.band_measurableSet (ε (n + 1)) (ε n)
  have hB_fin : ∀ n, levyMeasure (B n) < ⊤ := fun n =>
    CompensatedSmallJumpLimitHelpers.band_measure_lt_top hlevyMeasure (hε_bounds n).1 1
  have hA_fin : ∀ n, levyMeasure (A n) < ⊤ := fun n =>
    CompensatedSmallJumpLimitHelpers.band_measure_lt_top hlevyMeasure (hε_bounds (n + 1)).1 (ε n)
  have hA_sub_unit : ∀ n, A n ⊆ {x : ℝ | |x| < 1} := fun n _ hx =>
    hx.2.trans (hε_bounds n).2
  have hB_sub_unit : ∀ n, B n ⊆ {x : ℝ | |x| < 1} := fun _ _ hx => hx.2
  have hA_props : ∀ n,
      Integrable (fun x : ℝ => x) (levyMeasure.restrict (A n)) ∧
        MemLp (fun x : ℝ => x) 2 (levyMeasure.restrict (A n)) := fun n =>
    CompensatedSmallJumpLimitHelpers.band_integrable_and_memLp hlevyMeasure
      (hε_bounds (n + 1)).1 (hε_bounds n).2.le
  have hB_props : ∀ n,
      Integrable (fun x : ℝ => x) (levyMeasure.restrict (B n)) ∧
        MemLp (fun x : ℝ => x) 2 (levyMeasure.restrict (B n)) := fun n =>
    CompensatedSmallJumpLimitHelpers.band_integrable_and_memLp hlevyMeasure
      (hε_bounds n).1 le_rfl
  let X : ℕ → ℝ≥0 → Ω → ℝ := fun n =>
    Kyprianou.compensatedSmallJumpBand P levyMeasure N (ε n)
  let D : ℕ → ℝ≥0 → Ω → ℝ := fun n t ω =>
    (∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ A n), z.2 ∂(N.N ω)) -
      (t : ℝ) * (∫ x in A n, x ∂levyMeasure)
  -- Each `X n` is a `ℱ`-martingale under our fixed `ℱ`, and `MemLp 2`
  have hX_mart : ∀ n : ℕ, Martingale (X n) ℱ P := fun n =>
    Kyprianou.Ch02.compensatedFiniteRegionMartingaleUnderCompletedFiltrationV1 P levyMeasure N
      (B n) (hB_meas n) (hB_fin n) (hB_props n).1 ℱ hℱ
  have hX_L2 : ∀ n : ℕ, ∀ t : ℝ≥0, MemLp (X n t) 2 P := fun n => by
    obtain ⟨_, _, _, hL2⟩ :=
      Kyprianou.compensatedGeneralRegionMartingaleCh02V3 P levyMeasure N (B n) (hB_meas n)
        (hB_fin n) (hB_props n).1
    exact hL2 (hB_props n).2
  have hX_meas : ∀ n t, Measurable (X n t) := fun n t =>
    ((hX_mart n).1 t).measurable.mono (ℱ.le t) le_rfl
  -- Each band difference `D n` is a martingale with `MemLp 2`
  have hmart : ∀ n : ℕ,
      ∃ 𝒢 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω),
        Martingale (D n) 𝒢 P ∧ ∀ t : ℝ≥0, MemLp (D n t) 2 P := fun n => by
    obtain ⟨𝒢, _, hM, hL2⟩ :=
      Kyprianou.compensatedGeneralRegionMartingaleCh02V3 P levyMeasure N (A n) (hA_meas n)
        (hA_fin n) (hA_props n).1
    exact ⟨𝒢, hM, hL2 (hA_props n).2⟩
  -- Step 3: Borel-Cantelli uniform Cauchy & construction of `M`
  have hA_sq_le : ∀ n : ℕ, ∫ x in A n, x ^ 2 ∂levyMeasure ≤ 1 / (16 : ℝ) ^ n := fun n => by
    have hsub : A n ⊆ {x : ℝ | 0 < |x| ∧ |x| < ε n} := fun _ hx =>
      ⟨lt_of_lt_of_le (hε_bounds (n + 1)).1 hx.1, hx.2⟩
    have hsubU : {x : ℝ | 0 < |x| ∧ |x| < ε n} ⊆ {x : ℝ | |x| < 1} := fun _ hx =>
      hx.2.trans (hε_bounds n).2
    have hsq_int : Integrable (fun x : ℝ => x ^ 2)
        (levyMeasure.restrict {x : ℝ | 0 < |x| ∧ |x| < ε n}) :=
      MeasureTheory.IntegrableOn.mono_set
        (CompensatedSmallJumpLimitHelpers.levy_sq_integrable_unit hlevyMeasure) hsubU
    exact (setIntegral_mono_set hsq_int (Filter.Eventually.of_forall fun _ => sq_nonneg _)
      (Filter.Eventually.of_forall hsub)).trans (hε_int n)
  let Kof : ℕ → ℝ≥0 := fun k => ((k + 1 : ℕ) : ℝ≥0)
  have hKof_pos : ∀ k : ℕ, 0 < Kof k := fun k => by positivity
  let BadGrid : ℕ → ℕ → Set Ω := fun k n =>
    ⋃ m : ℕ, {ω | ∃ j ≤ 2 ^ m,
      ((((1 / 2 : ℝ≥0) ^ n : ℝ≥0)) : ℝ) ≤ |D n (CompensatedSmallJumpLimitHelpers.dyadGrid (Kof k) m j) ω|}
  have hBC : ∀ k : ℕ, ∀ᵐ ω ∂P, ∃ N₀ : ℕ, ∀ n ≥ N₀, ω ∉ BadGrid k n := by
    intro k
    have hP_bd : ∀ n : ℕ, P (BadGrid k n) ≤ ENNReal.ofReal ((Kof k : ℝ) * (1 / 4 : ℝ) ^ n) := by
      intro n
      obtain ⟨𝒢, hM, hL2⟩ := hmart n
      have hc : (0 : ℝ≥0) < (1 / 2 : ℝ≥0) ^ n := by positivity
      have hdoob := CompensatedSmallJumpLimitHelpers.martingale_sq_doob_dyadic_bound hM hL2 (Kof k) hc
      have hl2 := CompensatedSmallJumpLimitHelpers.compensated_band_sq_integral_le P levyMeasure N
        (hA_meas n) (hA_sub_unit n) (hA_fin n) (Kof k) (hL2 (Kof k))
      have hnum : ∫ ω, (D n (Kof k) ω) ^ 2 ∂P ≤ (Kof k : ℝ) * (1 / (16 : ℝ) ^ n) :=
        hl2.trans (mul_le_mul_of_nonneg_left (hA_sq_le n) (Kof k).coe_nonneg)
      have hden_pos : (0 : ℝ) < (((1 / 2 : ℝ≥0) ^ n : ℝ≥0) : ℝ) ^ 2 := by positivity
      have hquot : (∫ ω, (D n (Kof k) ω) ^ 2 ∂P) / (((1 / 2 : ℝ≥0) ^ n : ℝ≥0) : ℝ) ^ 2 ≤
          (Kof k : ℝ) * (1 / 4 : ℝ) ^ n := by
        have hcalc : ((Kof k : ℝ) * (1 / (16 : ℝ) ^ n)) / (((1 / 2 : ℝ≥0) ^ n : ℝ≥0) : ℝ) ^ 2 =
            (Kof k : ℝ) * (1 / 4 : ℝ) ^ n := by
          push_cast
          have hden : ((1 / 2 : ℝ) ^ n) ^ 2 = (1 / 4 : ℝ) ^ n := by
            rw [← pow_mul, mul_comm n 2, pow_mul]; norm_num
          have h16 : (16 : ℝ) ^ n = (4 : ℝ) ^ n * (4 : ℝ) ^ n := by
            rw [← mul_pow]; norm_num
          have h4n : (4 : ℝ) ^ n ≠ 0 := by positivity
          rw [hden, div_pow, one_pow, h16]
          field_simp [h4n]
        calc
          (∫ ω, (D n (Kof k) ω) ^ 2 ∂P) / (((1 / 2 : ℝ≥0) ^ n : ℝ≥0) : ℝ) ^ 2
              ≤ ((Kof k : ℝ) * (1 / (16 : ℝ) ^ n)) / (((1 / 2 : ℝ≥0) ^ n : ℝ≥0) : ℝ) ^ 2 :=
            div_le_div_of_nonneg_right hnum hden_pos.le
          _ = (Kof k : ℝ) * (1 / 4 : ℝ) ^ n := hcalc
      exact hdoob.trans (ENNReal.ofReal_le_ofReal hquot)
    have hsum_ne_top : ∑' n : ℕ, P (BadGrid k n) ≠ ⊤ := by
      have hsumm : Summable (fun n : ℕ => (Kof k : ℝ) * (1 / 4 : ℝ) ^ n) :=
        (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
      have hle : ∑' n : ℕ, P (BadGrid k n) ≤ ∑' n : ℕ, ENNReal.ofReal ((Kof k : ℝ) * (1 / 4 : ℝ) ^ n) :=
        ENNReal.tsum_le_tsum hP_bd
      have hfin_tsum : ∑' n : ℕ, ENNReal.ofReal ((Kof k : ℝ) * (1 / 4 : ℝ) ^ n) < ⊤ := by
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsumm]
        exact ENNReal.ofReal_lt_top
      exact (lt_of_le_of_lt hle hfin_tsum).ne
    have hlimsup : P (Filter.limsup (BadGrid k) Filter.atTop) = 0 :=
      MeasureTheory.measure_limsup_atTop_eq_zero hsum_ne_top
    rw [ae_iff]
    have hsub : {ω | ¬ ∃ N₀ : ℕ, ∀ n ≥ N₀, ω ∉ BadGrid k n} ⊆ Filter.limsup (BadGrid k) Filter.atTop := by
      intro ω hω
      simp only [Set.mem_setOf_eq, not_exists, not_forall, not_not] at hω
      rw [Filter.limsup_eq_iInf_iSup_of_nat]
      simp only [Set.iInf_eq_iInter, Set.iSup_eq_iUnion, Set.mem_iInter, Set.mem_iUnion]
      intro N₀
      obtain ⟨n, hn, hmem⟩ := hω N₀
      exact ⟨n, hn, hmem⟩
    exact measure_mono_null hsub hlimsup
  have hae_fin : ∀ᵐ ω ∂P, ∀ k n : ℕ, N.N ω (Set.Ioc (0 : ℝ) (Kof k : ℝ) ×ˢ B n) ≠ ⊤ := by
    rw [ae_all_iff]; intro k
    rw [ae_all_iff]; intro n
    have hSfin := CompensatedSmallJumpLimitHelpers.referenceIntensity_Ioc_prod_ne_top
      levyMeasure (Kof k) (hB_fin n)
    filter_upwards [N.integer_valued (measurableSet_Ioc.prod (hB_meas n)) hSfin] with ω ⟨m, hm⟩
    simp [hm]
  have hae_all_BC : ∀ᵐ ω ∂P, ∀ k : ℕ, ∃ N₀ : ℕ, ∀ n ≥ N₀, ω ∉ BadGrid k n :=
    ae_all_iff.mpr hBC
  -- General additive split: for `n ≤ m`, `X m t ω - X n t ω` equals compensated integral on `{ε m ≤ |x| < ε n}`
  have hband_diff_gen : ∀ (n m : ℕ) (_ : n ≤ m) (t : ℝ≥0) (ω : Ω),
      N.N ω (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B m) ≠ ⊤ →
      X m t ω - X n t ω =
        (∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | ε m ≤ |x| ∧ |x| < ε n}), z.2 ∂(N.N ω)) -
          (t : ℝ) * (∫ x in {x : ℝ | ε m ≤ |x| ∧ |x| < ε n}, x ∂levyMeasure) := by
    intro n m hnm t ω hfin
    let Anm : Set ℝ := {x : ℝ | ε m ≤ |x| ∧ |x| < ε n}
    have hε_le : ε m ≤ ε n := hε_anti.antitone hnm
    have hAnm_meas : MeasurableSet Anm :=
      CompensatedSmallJumpLimitHelpers.band_measurableSet (ε m) (ε n)
    have hAnm_fin : levyMeasure Anm < ⊤ :=
      CompensatedSmallJumpLimitHelpers.band_measure_lt_top hlevyMeasure (hε_bounds m).1 (ε n)
    have hAnm_int : Integrable (fun x : ℝ => x) (levyMeasure.restrict Anm) :=
      (CompensatedSmallJumpLimitHelpers.band_integrable_and_memLp hlevyMeasure
        (hε_bounds m).1 (hε_bounds n).2.le).1
    have hunion_set : Anm ∪ B n = B m := by
      ext x
      simp only [Set.mem_union, Set.mem_setOf_eq, Anm, B]
      constructor
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact ⟨h1, h2.trans (hε_bounds n).2⟩
        · exact ⟨hε_le.trans h1, h2⟩
      · rintro ⟨h1, h2⟩
        by_cases hlt : |x| < ε n
        · exact Or.inl ⟨h1, hlt⟩
        · exact Or.inr ⟨le_of_not_gt hlt, h2⟩
    have hdisj_set : Disjoint Anm (B n) := Set.disjoint_left.mpr fun _ hx1 hx2 =>
      not_le_of_gt hx1.2 hx2.1
    have hdet : ∫ x in B m, x ∂levyMeasure =
        (∫ x in Anm, x ∂levyMeasure) + (∫ x in B n, x ∂levyMeasure) := by
      rw [← hunion_set]
      exact setIntegral_union hdisj_set (hB_meas n) hAnm_int (hB_props n).1
    have hprod_union : (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ Anm) ∪ (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B n) =
        Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B m := by
      rw [← Set.prod_union, hunion_set]
    have hprod_disj : Disjoint (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ Anm)
        (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B n) :=
      Set.disjoint_left.mpr fun z hz1 hz2 => Set.disjoint_left.mp hdisj_set hz1.2 hz2.2
    have hfin_A : N.N ω (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ Anm) < ⊤ :=
      lt_of_le_of_lt (measure_mono (Set.prod_mono_right (fun _ hx =>
        hunion_set ▸ Or.inl hx))) hfin.lt_top
    have hfin_B : N.N ω (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B n) < ⊤ :=
      lt_of_le_of_lt (measure_mono (Set.prod_mono_right (fun _ hx =>
        hunion_set ▸ Or.inr hx))) hfin.lt_top
    haveI : IsFiniteMeasure ((N.N ω).restrict (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ Anm)) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hfin_A⟩
    haveI : IsFiniteMeasure ((N.N ω).restrict (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B n)) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hfin_B⟩
    have hint_A : IntegrableOn (fun z : ℝ × ℝ => z.2) (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ Anm) (N.N ω) := by
      refine Integrable.mono' (integrable_const (1 : ℝ)) (continuous_snd.measurable.aestronglyMeasurable) ?_
      filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod hAnm_meas)] with z hz
      exact (hz.2.2.trans (hε_bounds n).2).le
    have hint_B : IntegrableOn (fun z : ℝ × ℝ => z.2) (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B n) (N.N ω) := by
      refine Integrable.mono' (integrable_const (1 : ℝ)) (continuous_snd.measurable.aestronglyMeasurable) ?_
      filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod (hB_meas n))] with z hz
      exact hz.2.2.le
    have hraw : ∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B m), z.2 ∂(N.N ω) =
        (∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ Anm), z.2 ∂(N.N ω)) +
        (∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B n), z.2 ∂(N.N ω)) := by
      rw [← hprod_union]
      exact setIntegral_union hprod_disj (measurableSet_Ioc.prod (hB_meas n)) hint_A hint_B
    change ((∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B m), z.2 ∂(N.N ω)) -
        (t : ℝ) * (∫ x in B m, x ∂levyMeasure)) -
      ((∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B n), z.2 ∂(N.N ω)) -
        (t : ℝ) * (∫ x in B n, x ∂levyMeasure)) = _
    rw [hraw, hdet]
    ring
  -- Define the common limit process `M`
  let M : ℝ≥0 → Ω → ℝ := fun t ω =>
    if t = 0 then 0 else Filter.limUnder Filter.atTop (fun n => X n t ω)
  have hM_zero : M 0 = fun _ => 0 := by
    funext ω; simp [M]
  -- `M` is `ℱ`-strongly adapted (since each `X n t` is `StronglyMeasurable[ℱ t]`) and ambient-measurable
  have hM_adapted : StronglyAdapted ℱ M := by
    intro t
    by_cases ht0 : t = 0
    · subst ht0
      rw [hM_zero]
      exact stronglyMeasurable_const
    · have hsm_lim : StronglyMeasurable[ℱ t] (fun ω => Filter.limUnder Filter.atTop (fun n => X n t ω)) :=
        @StronglyMeasurable.limUnder ℕ Ω ℝ (ℱ t) _ _ _ _ (fun n => X n t) _ _ (fun n => (hX_mart n).1 t)
      have heq : M t = fun ω => Filter.limUnder Filter.atTop (fun n => X n t ω) := by
        funext ω; simp [M, ht0]
      rw [heq]
      exact hsm_lim
  have hM_meas : ∀ t : ℝ≥0, Measurable (M t) := fun t =>
    (hM_adapted t).measurable.mono (ℱ.le t) le_rfl
  -- Uniform a.s. convergence on `[0, T]` for every `T > 0`
  have huniform : ∀ T : ℝ≥0, 0 < T →
      ∃ ε' : ℕ → ℝ,
        StrictAnti ε' ∧
        (∀ n, 0 < ε' n ∧ ε' n < 1) ∧
        Tendsto ε' Filter.atTop (nhds 0) ∧
        (∀ᵐ ω ∂P, ∀ δ : ℝ, 0 < δ →
          ∃ n₀ : ℕ, ∀ n ≥ n₀,
            ∀ t : ℝ≥0, t ≤ T →
              |Kyprianou.compensatedSmallJumpBand P levyMeasure N (ε' n) t ω - M t ω| < δ) := by
    intro T _
    refine ⟨ε, hε_anti, hε_bounds, hε_tendsto, ?_⟩
    obtain ⟨k, hk⟩ := exists_nat_gt (T : ℝ)
    have hTK : T ≤ Kof k := by
      change (T : ℝ) ≤ ((k + 1 : ℕ) : ℝ)
      push_cast; linarith
    filter_upwards [hae_fin, hae_all_BC] with ω hfin hBCω
    obtain ⟨N₀, hN₀⟩ := hBCω k
    have hstep_unif : ∀ n ≥ N₀, ∀ t : ℝ≥0, t ≤ Kof k →
        |X (n + 1) t ω - X n t ω| ≤ (1 / 2 : ℝ) ^ n := by
      intro n hn t ht
      have hfin_t : N.N ω (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B (n + 1)) ≠ ⊤ := by
        intro htop
        have hle : N.N ω (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B (n + 1)) ≤
            N.N ω (Set.Ioc (0 : ℝ) (Kof k : ℝ) ×ˢ B (n + 1)) :=
          measure_mono (Set.prod_mono_left (Set.Ioc_subset_Ioc_right (by exact_mod_cast ht)))
        exact hfin k (n + 1) (top_unique (htop ▸ hle))
      rw [hband_diff_gen n (n + 1) (Nat.le_succ n) t ω hfin_t]
      have hfinA : N.N ω (Set.Ioc (0 : ℝ) (Kof k : ℝ) ×ˢ A n) ≠ ⊤ := by
        intro htop
        have hsub : A n ⊆ B (n + 1) := fun _ hx => ⟨hx.1, hx.2.trans (hε_bounds n).2⟩
        have hle : N.N ω (Set.Ioc (0 : ℝ) (Kof k : ℝ) ×ˢ A n) ≤
            N.N ω (Set.Ioc (0 : ℝ) (Kof k : ℝ) ×ˢ B (n + 1)) :=
          measure_mono (Set.prod_mono_right hsub)
        exact hfin k (n + 1) (top_unique (htop ▸ hle))
      have hnotBad : ω ∉ BadGrid k n := hN₀ n hn
      have hdyad : ∀ m j, j ≤ 2 ^ m →
          |D n (CompensatedSmallJumpLimitHelpers.dyadGrid (Kof k) m j) ω| <
            ((((1 / 2 : ℝ≥0) ^ n : ℝ≥0)) : ℝ) := by
        intro m j hj
        by_contra hge
        push Not at hge
        exact hnotBad (Set.mem_iUnion.mpr ⟨m, j, hj, hge⟩)
      have hbd := CompensatedSmallJumpLimitHelpers.right_continuous_band_bound N (hA_meas n)
        (hA_sub_unit n) (Kof k) (hKof_pos k) hfinA hdyad t ht
      simpa using hbd
    have htele : ∀ {n m : ℕ}, N₀ ≤ n → n ≤ m → ∀ t : ℝ≥0, t ≤ Kof k →
        |X m t ω - X n t ω| ≤ 2 * (1 / 2 : ℝ) ^ n := by
      intro n m hn hnm t ht
      have hsum_bd : ∀ d : ℕ, |X (n + d) t ω - X n t ω| ≤
          2 * (1 / 2 : ℝ) ^ n - 2 * (1 / 2 : ℝ) ^ (n + d) := by
        intro d
        induction d with
        | zero => simp
        | succ d ih =>
          have htri : |X (n + (d + 1)) t ω - X n t ω| ≤
              |X (n + d + 1) t ω - X (n + d) t ω| + |X (n + d) t ω - X n t ω| := by
            have heq : X (n + (d + 1)) t ω - X n t ω =
                (X (n + d + 1) t ω - X (n + d) t ω) + (X (n + d) t ω - X n t ω) := by
              rw [Nat.add_assoc]; ring
            rw [heq]; exact abs_add_le _ _
          have hnext := hstep_unif (n + d) (hn.trans (Nat.le_add_right n d)) t ht
          have hpow : 2 * (1 / 2 : ℝ) ^ (n + (d + 1)) = (1 / 2 : ℝ) ^ (n + d) := by
            rw [← Nat.add_assoc, pow_succ]; ring
          linarith
      rcases Nat.exists_eq_add_of_le hnm with ⟨d, rfl⟩
      have h1 := hsum_bd d
      have h2 : (0 : ℝ) ≤ 2 * (1 / 2 : ℝ) ^ (n + d) := by positivity
      linarith
    have hconv : ∀ t : ℝ≥0, t ≤ Kof k → Tendsto (fun n => X n t ω) atTop (𝓝 (M t ω)) := by
      intro t ht
      by_cases ht0 : t = 0
      · subst ht0
        have hzero : ∀ n : ℕ, X n 0 ω = 0 := fun n => by
          unfold X Kyprianou.compensatedSmallJumpBand; simp
        simp [M, hzero]
      · have hcauchy_shift : CauchySeq (fun j => X (N₀ + j) t ω) := by
          refine cauchySeq_of_le_geometric (1 / 2 : ℝ) ((1 / 2 : ℝ) ^ N₀) (by norm_num) fun j => ?_
          rw [Real.dist_eq, abs_sub_comm]
          have h1 := hstep_unif (N₀ + j) (Nat.le_add_right N₀ j) t ht
          simpa [pow_add, Nat.add_assoc] using h1
        obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcauchy_shift
        have hL_full : Tendsto (fun n => X n t ω) atTop (𝓝 L) :=
          (tendsto_add_atTop_iff_nat N₀).mp (by simpa [Nat.add_comm] using hL)
        have hlim := tendsto_nhds_limUnder ⟨L, hL_full⟩
        simpa [M, ht0] using hlim
    intro δ hδ
    have hgeom : Tendsto (fun n : ℕ => 2 * (1 / 2 : ℝ) ^ n) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)).const_mul 2
    obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp (hgeom.eventually (gt_mem_nhds hδ))
    refine ⟨max N₀ N₁, fun n hn t ht => ?_⟩
    have htK : t ≤ Kof k := ht.trans hTK
    have hn0 : N₀ ≤ n := (le_max_left _ _).trans hn
    have hn1 : N₁ ≤ n := (le_max_right _ _).trans hn
    have hdist_tendsto : Tendsto (fun m => |X m t ω - X n t ω|) atTop (𝓝 |M t ω - X n t ω|) :=
      continuous_abs.continuousAt.tendsto.comp ((hconv t htK).sub tendsto_const_nhds)
    have hle : |M t ω - X n t ω| ≤ 2 * (1 / 2 : ℝ) ^ n :=
      le_of_tendsto hdist_tendsto
        (Filter.eventually_atTop.mpr ⟨n, fun m hm => htele hn0 hm t htK⟩)
    rw [abs_sub_comm]
    exact lt_of_le_of_lt hle (hN₁ n hn1)
  -- Pointwise a.e. convergence `X n t ω → M t ω` for our fixed global `ε`
  have hconv_ae : ∀ t : ℝ≥0, ∀ᵐ ω ∂P, Tendsto (fun n => X n t ω) atTop (𝓝 (M t ω)) := by
    intro t
    have hpos : (0 : ℝ≥0) < t + 1 := by positivity
    -- Extract directly using `hae_fin` & `hae_all_BC` for `k` with `t ≤ Kof k`
    obtain ⟨k, hk⟩ := exists_nat_gt (t : ℝ)
    have htK : t ≤ Kof k := by
      change (t : ℝ) ≤ ((k + 1 : ℕ) : ℝ); push_cast; linarith
    filter_upwards [hae_fin, hae_all_BC] with ω hfin hBCω
    obtain ⟨N₀, hN₀⟩ := hBCω k
    by_cases ht0 : t = 0
    · subst ht0
      have hzero : ∀ n : ℕ, X n 0 ω = 0 := fun n => by
        unfold X Kyprianou.compensatedSmallJumpBand; simp
      simp [M, hzero]
    · have hstep_unif : ∀ n ≥ N₀, |X (n + 1) t ω - X n t ω| ≤ (1 / 2 : ℝ) ^ n := by
        intro n hn
        have hfin_t : N.N ω (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B (n + 1)) ≠ ⊤ := by
          intro htop
          have hle : N.N ω (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B (n + 1)) ≤
              N.N ω (Set.Ioc (0 : ℝ) (Kof k : ℝ) ×ˢ B (n + 1)) :=
            measure_mono (Set.prod_mono_left (Set.Ioc_subset_Ioc_right (by exact_mod_cast htK)))
          exact hfin k (n + 1) (top_unique (htop ▸ hle))
        rw [hband_diff_gen n (n + 1) (Nat.le_succ n) t ω hfin_t]
        have hfinA : N.N ω (Set.Ioc (0 : ℝ) (Kof k : ℝ) ×ˢ A n) ≠ ⊤ := by
          intro htop
          have hsub : A n ⊆ B (n + 1) := fun _ hx => ⟨hx.1, hx.2.trans (hε_bounds n).2⟩
          have hle : N.N ω (Set.Ioc (0 : ℝ) (Kof k : ℝ) ×ˢ A n) ≤
              N.N ω (Set.Ioc (0 : ℝ) (Kof k : ℝ) ×ˢ B (n + 1)) :=
            measure_mono (Set.prod_mono_right hsub)
          exact hfin k (n + 1) (top_unique (htop ▸ hle))
        have hnotBad : ω ∉ BadGrid k n := hN₀ n hn
        have hdyad : ∀ m j, j ≤ 2 ^ m →
            |D n (CompensatedSmallJumpLimitHelpers.dyadGrid (Kof k) m j) ω| <
              ((((1 / 2 : ℝ≥0) ^ n : ℝ≥0)) : ℝ) := by
          intro m j hj
          by_contra hge
          push Not at hge
          exact hnotBad (Set.mem_iUnion.mpr ⟨m, j, hj, hge⟩)
        have hbd := CompensatedSmallJumpLimitHelpers.right_continuous_band_bound N (hA_meas n)
          (hA_sub_unit n) (Kof k) (hKof_pos k) hfinA hdyad t htK
        simpa using hbd
      have hcauchy_shift : CauchySeq (fun j => X (N₀ + j) t ω) := by
        refine cauchySeq_of_le_geometric (1 / 2 : ℝ) ((1 / 2 : ℝ) ^ N₀) (by norm_num) fun j => ?_
        rw [Real.dist_eq, abs_sub_comm]
        have h1 := hstep_unif (N₀ + j) (Nat.le_add_right N₀ j)
        simpa [pow_add, Nat.add_assoc] using h1
      obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcauchy_shift
      have hL_full : Tendsto (fun n => X n t ω) atTop (𝓝 L) :=
        (tendsto_add_atTop_iff_nat N₀).mp (by simpa [Nat.add_comm] using hL)
      have hlim := tendsto_nhds_limUnder ⟨L, hL_full⟩
      simpa [M, ht0] using hlim
  -- Step 4: `L²` bound for `M t - X n t` via Fatou on `compensated_band_sq_integral_le`
  have hL2_tail : ∀ (t : ℝ≥0) (n : ℕ),
      MemLp (fun ω => M t ω - X n t ω) 2 P ∧
        ∫ ω, (M t ω - X n t ω) ^ 2 ∂P ≤ (t : ℝ) * (1 / (16 : ℝ) ^ n) := by
    intro t n
    have hbd_m : ∀ m ≥ n,
        ∫⁻ ω, ENNReal.ofReal ((X m t ω - X n t ω) ^ 2) ∂P ≤
          ENNReal.ofReal ((t : ℝ) * (1 / (16 : ℝ) ^ n)) := by
      intro m hnm
      let Anm : Set ℝ := {x : ℝ | ε m ≤ |x| ∧ |x| < ε n}
      have hAnm_meas : MeasurableSet Anm :=
        CompensatedSmallJumpLimitHelpers.band_measurableSet (ε m) (ε n)
      have hAnm_fin : levyMeasure Anm < ⊤ :=
        CompensatedSmallJumpLimitHelpers.band_measure_lt_top hlevyMeasure (hε_bounds m).1 (ε n)
      have hAnm_sub_unit : Anm ⊆ {x : ℝ | |x| < 1} := fun _ hx =>
        hx.2.trans (hε_bounds n).2
      have hAnm_props := CompensatedSmallJumpLimitHelpers.band_integrable_and_memLp hlevyMeasure
        (hε_bounds m).1 (hε_bounds n).2.le
      let Dnm : ℝ≥0 → Ω → ℝ := fun r ω =>
        (∫ z in (Set.Ioc (0 : ℝ) (r : ℝ) ×ˢ Anm), z.2 ∂(N.N ω)) -
          (r : ℝ) * (∫ x in Anm, x ∂levyMeasure)
      obtain ⟨_, _, _, hDnm_L2⟩ :=
        Kyprianou.compensatedGeneralRegionMartingaleCh02V3 P levyMeasure N Anm hAnm_meas
          hAnm_fin hAnm_props.1
      have hl2 := CompensatedSmallJumpLimitHelpers.compensated_band_sq_integral_le P levyMeasure N
        hAnm_meas hAnm_sub_unit hAnm_fin t (hDnm_L2 hAnm_props.2 t)
      have hAnm_sq_le : ∫ x in Anm, x ^ 2 ∂levyMeasure ≤ 1 / (16 : ℝ) ^ n := by
        have hsub : Anm ⊆ {x : ℝ | 0 < |x| ∧ |x| < ε n} := fun _ hx =>
          ⟨lt_of_lt_of_le (hε_bounds m).1 hx.1, hx.2⟩
        have hsubU : {x : ℝ | 0 < |x| ∧ |x| < ε n} ⊆ {x : ℝ | |x| < 1} := fun _ hx =>
          hx.2.trans (hε_bounds n).2
        have hsq_int : Integrable (fun x : ℝ => x ^ 2)
            (levyMeasure.restrict {x : ℝ | 0 < |x| ∧ |x| < ε n}) :=
          MeasureTheory.IntegrableOn.mono_set
            (CompensatedSmallJumpLimitHelpers.levy_sq_integrable_unit hlevyMeasure) hsubU
        exact (setIntegral_mono_set hsq_int (Filter.Eventually.of_forall fun _ => sq_nonneg _)
          (Filter.Eventually.of_forall hsub)).trans (hε_int n)
      have hsq_int_D : Integrable (fun ω => (Dnm t ω) ^ 2) P :=
        (memLp_two_iff_integrable_sq (hDnm_L2 hAnm_props.2 t).aestronglyMeasurable).mp
          (hDnm_L2 hAnm_props.2 t)
      have hlint_D : ∫⁻ ω, ENNReal.ofReal ((Dnm t ω) ^ 2) ∂P ≤
          ENNReal.ofReal ((t : ℝ) * (1 / (16 : ℝ) ^ n)) := by
        rw [← ofReal_integral_eq_lintegral_ofReal hsq_int_D
          (Filter.Eventually.of_forall fun _ => sq_nonneg _)]
        exact ENNReal.ofReal_le_ofReal (hl2.trans (mul_le_mul_of_nonneg_left hAnm_sq_le t.coe_nonneg))
      have hae_eq : (fun ω => ENNReal.ofReal ((X m t ω - X n t ω) ^ 2)) =ᵐ[P]
          (fun ω => ENNReal.ofReal ((Dnm t ω) ^ 2)) := by
        have hSfin := CompensatedSmallJumpLimitHelpers.referenceIntensity_Ioc_prod_ne_top
          levyMeasure t (hB_fin m)
        filter_upwards [N.integer_valued (measurableSet_Ioc.prod (hB_meas m)) hSfin] with ω ⟨c, hc⟩
        have hfin_ω : N.N ω (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B m) ≠ ⊤ := by simp [hc]
        rw [hband_diff_gen n m hnm t ω hfin_ω]
      rw [lintegral_congr_ae hae_eq]
      exact hlint_D
    -- Fatou as `m → ∞`
    have hlint_tail : ∫⁻ ω, ENNReal.ofReal ((M t ω - X n t ω) ^ 2) ∂P ≤
        ENNReal.ofReal ((t : ℝ) * (1 / (16 : ℝ) ^ n)) := by
      have hae_lim : ∀ᵐ ω ∂P,
          ENNReal.ofReal ((M t ω - X n t ω) ^ 2) =
            Filter.liminf (fun m => ENNReal.ofReal ((X (n + m) t ω - X n t ω) ^ 2)) atTop := by
        filter_upwards [hconv_ae t] with ω hω
        have hshift : Tendsto (fun m => X (n + m) t ω) atTop (𝓝 (M t ω)) :=
          hω.comp ((tendsto_add_atTop_nat n).congr (fun m => Nat.add_comm m n))
        have hsq : Tendsto (fun m => ENNReal.ofReal ((X (n + m) t ω - X n t ω) ^ 2)) atTop
            (𝓝 (ENNReal.ofReal ((M t ω - X n t ω) ^ 2))) :=
          ENNReal.continuous_ofReal.continuousAt.tendsto.comp
            (((hshift.sub tendsto_const_nhds).pow 2))
        exact hsq.liminf_eq.symm
      rw [lintegral_congr_ae hae_lim]
      refine (lintegral_liminf_le fun m =>
        ENNReal.continuous_ofReal.measurable.comp
          (((hX_meas (n + m) t).sub (hX_meas n t)).pow_const 2)).trans ?_
      exact liminf_le_of_frequently_le'
        (Filter.Eventually.frequently (Filter.Eventually.of_forall fun m => hbd_m (n + m) (Nat.le_add_right n m)))
    exact SmallJumpCoreHelpers.memLp_two_and_sq_integral_le_of_lintegral_le P
      ((hM_meas t).sub (hX_meas n t)) (by positivity) hlint_tail
  have hM_L2 : ∀ t : ℝ≥0, MemLp (M t) 2 P := fun t => by
    have h1 := (hL2_tail t 0).1.add (hX_L2 0 t)
    have heq : (fun ω => M t ω - X 0 t ω) + X 0 t = M t := by
      funext ω; simp [Pi.add_apply]
    rwa [heq] at h1
  -- Step 5: `L¹` convergence `∫ |X n t - M t| ∂P → 0` via elementary AM-GM `|y| ≤ δ + y^2 / (4δ)`
  have hL1_conv : ∀ t : ℝ≥0, Tendsto (fun n => ∫ ω, |X n t ω - M t ω| ∂P) atTop (𝓝 0) := by
    intro t
    rw [Metric.tendsto_atTop]
    intro η hη
    let δ : ℝ := η / 2
    have hδ : 0 < δ := by positivity
    have hgeom : Tendsto (fun n : ℕ => ((t : ℝ) * (1 / (16 : ℝ) ^ n)) / (4 * δ)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n : ℕ => (1 / 16 : ℝ) ^ n) atTop (𝓝 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
      have h2 := (h1.const_mul (t : ℝ)).div_const (4 * δ)
      simpa [one_div_pow] using h2
    obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp (hgeom.eventually (gt_mem_nhds hδ))
    refine ⟨N₁, fun n hn => ?_⟩
    rw [Real.dist_eq, sub_zero]
    have hnonneg : 0 ≤ ∫ ω, |X n t ω - M t ω| ∂P :=
      integral_nonneg fun _ => abs_nonneg _
    rw [abs_of_nonneg hnonneg]
    have hpt : ∀ ω, |X n t ω - M t ω| ≤ δ + (M t ω - X n t ω) ^ 2 / (4 * δ) := by
      intro ω
      have hsq : 0 ≤ (|M t ω - X n t ω| - 2 * δ) ^ 2 := sq_nonneg _
      have habs : |X n t ω - M t ω| = |M t ω - X n t ω| := abs_sub_comm _ _
      have hsq2 : |M t ω - X n t ω| ^ 2 = (M t ω - X n t ω) ^ 2 := sq_abs _
      have h4δ : 0 < 4 * δ := by positivity
      rw [habs]
      have hmul : (4 * δ) * |M t ω - X n t ω| ≤ (4 * δ) * δ + (M t ω - X n t ω) ^ 2 := by
        nlinarith
      have hdiv := (div_le_div_of_nonneg_right hmul h4δ.le)
      have h4δne : 4 * δ ≠ 0 := h4δ.ne'
      calc
        |M t ω - X n t ω| = (4 * δ) * |M t ω - X n t ω| / (4 * δ) := by field_simp [h4δne]
        _ ≤ ((4 * δ) * δ + (M t ω - X n t ω) ^ 2) / (4 * δ) := hdiv
        _ = δ + (M t ω - X n t ω) ^ 2 / (4 * δ) := by rw [add_div]; field_simp [h4δne]
    have hint_lhs : Integrable (fun ω => |X n t ω - M t ω|) P :=
      (((hX_L2 n t).integrable (by norm_num)).sub ((hM_L2 t).integrable (by norm_num))).abs
    have hint_sq : Integrable (fun ω => (M t ω - X n t ω) ^ 2) P :=
      (memLp_two_iff_integrable_sq ((hM_meas t).sub (hX_meas n t)).aestronglyMeasurable).mp
        (hL2_tail t n).1
    have hint_rhs : Integrable (fun ω => δ + (M t ω - X n t ω) ^ 2 / (4 * δ)) P :=
      (integrable_const δ).add (hint_sq.div_const (4 * δ))
    have hint_le : ∫ ω, |X n t ω - M t ω| ∂P ≤
        δ + (∫ ω, (M t ω - X n t ω) ^ 2 ∂P) / (4 * δ) := by
      calc
        ∫ ω, |X n t ω - M t ω| ∂P
            ≤ ∫ ω, (δ + (M t ω - X n t ω) ^ 2 / (4 * δ)) ∂P :=
          integral_mono hint_lhs hint_rhs hpt
        _ = (∫ _ : Ω, δ ∂P) + ∫ ω, (M t ω - X n t ω) ^ 2 / (4 * δ) ∂P :=
          integral_add (integrable_const δ) (hint_sq.div_const (4 * δ))
        _ = δ + (∫ ω, (M t ω - X n t ω) ^ 2 ∂P) / (4 * δ) := by
          rw [integral_const, probReal_univ, one_smul, integral_div]
    have h4δ : 0 < 4 * δ := by positivity
    have hbd2 : (∫ ω, (M t ω - X n t ω) ^ 2 ∂P) / (4 * δ) ≤
        ((t : ℝ) * (1 / (16 : ℝ) ^ n)) / (4 * δ) :=
      div_le_div_of_nonneg_right (hL2_tail t n).2 h4δ.le
    have hlt := hN₁ n hn
    have h2δ : δ + δ = η := by dsimp [δ]; ring
    linarith
  -- Step 6: Martingale conditional expectation `P[M t | ℱ s] =ᵐ[P] M s`
  have hM_mart : Martingale M ℱ P := by
    refine ⟨hM_adapted, fun s t hst => ?_⟩
    have hMt_int : Integrable (M t) P := (hM_L2 t).integrable (by norm_num)
    have hMs_int : Integrable (M s) P := (hM_L2 s).integrable (by norm_num)
    symm
    refine ae_eq_condExp_of_forall_setIntegral_eq (ℱ.le s) hMt_int
      (fun E _ _ => hMs_int.integrableOn) ?_ (hM_adapted s).aestronglyMeasurable
    intro E hE _
    have hE_amb : MeasurableSet E := ℱ.le s E hE
    have hX_seteq : ∀ n, ∫ ω in E, X n s ω ∂P = ∫ ω in E, X n t ω ∂P := by
      intro n
      have hce := (hX_mart n).2 s t hst
      have h1 : ∫ ω in E, X n s ω ∂P = ∫ ω in E, P[X n t | ℱ s] ω ∂P :=
        setIntegral_congr_ae hE_amb (hce.symm.mono fun _ h _ => h)
      rw [h1, setIntegral_condExp (ℱ.le s) ((hX_L2 n t).integrable (by norm_num)) hE]
    have ht_lim : ∀ r : ℝ≥0, Tendsto (fun n => ∫ ω in E, X n r ω ∂P) atTop (𝓝 (∫ ω in E, M r ω ∂P)) := by
      intro r
      rw [Metric.tendsto_atTop]
      intro ε' hε'
      obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.mp (hL1_conv r) ε' hε'
      refine ⟨N₁, fun n hn => ?_⟩
      rw [Real.dist_eq]
      have hdiff : (∫ ω in E, X n r ω ∂P) - (∫ ω in E, M r ω ∂P) =
          ∫ ω in E, (X n r ω - M r ω) ∂P :=
        (integral_sub ((hX_L2 n r).integrable (by norm_num)).integrableOn
          ((hM_L2 r).integrable (by norm_num)).integrableOn).symm
      rw [hdiff]
      have h1 : |∫ ω in E, (X n r ω - M r ω) ∂P| ≤ ∫ ω in E, |X n r ω - M r ω| ∂P := by
        simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun ω => X n r ω - M r ω)
      have h2 : ∫ ω in E, |X n r ω - M r ω| ∂P ≤ ∫ ω, |X n r ω - M r ω| ∂P :=
        setIntegral_le_integral (((hX_L2 n r).integrable (by norm_num)).sub ((hM_L2 r).integrable (by norm_num))).abs
          (Filter.Eventually.of_forall fun _ => abs_nonneg _)
      have h3 : |∫ ω, |X n r ω - M r ω| ∂P - 0| < ε' := by
        simpa [Real.dist_eq] using hN₁ n hn
      have h4 : ∫ ω, |X n r ω - M r ω| ∂P < ε' := by
        rwa [sub_zero, abs_of_nonneg (integral_nonneg fun _ => abs_nonneg _)] at h3
      exact lt_of_le_of_lt (h1.trans h2) h4
    have ht_s := ht_lim s
    have ht_t := ht_lim t
    simp_rw [hX_seteq] at ht_s
    exact tendsto_nhds_unique ht_s ht_t
  -- Step 7: `IsLevyProcess M P` (independent increments, stationary increments, càdlàg paths)
  have hY_levy : ∀ n : ℕ,
      IsLevyProcess (fun t ω => ∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B n), z.2 ∂(N.N ω)) P := fun n =>
    (Kyprianou.finiteRegionPoissonIntegralCh02V3 P levyMeasure N (B n) (hB_meas n) (hB_fin n)).1
  have hX_indep : ∀ n : ℕ, HasIndependentIncrements (X n) P := by
    intro n k t ht
    have hYi := (hY_levy n).indep_increments k t ht
    let c : ℝ := ∫ x in B n, x ∂levyMeasure
    let g : Fin k → ℝ → ℝ := fun i y => y - ((t i.succ : ℝ) - (t i.castSucc : ℝ)) * c
    have hg_meas : ∀ i, Measurable (g i) := fun i => measurable_id.sub measurable_const
    have hcomp := hYi.comp g hg_meas
    convert hcomp using 1
    funext i ω
    simp only [Function.comp_apply, g, ProbabilityTheory.increment, X, Kyprianou.compensatedSmallJumpBand, c]
    ring
  have hX_stat : ∀ n : ℕ, HasStationaryIncrements (X n) P := by
    intro n s h
    have hYs := (hY_levy n).stationary_increments s h
    let c : ℝ := ∫ x in B n, x ∂levyMeasure
    have hcomp := hYs.comp (u := fun y : ℝ => y - (h : ℝ) * c) (measurable_id.sub measurable_const)
    convert hcomp using 1
    · funext ω
      simp only [Function.comp_apply, ProbabilityTheory.increment, X, Kyprianou.compensatedSmallJumpBand, c,
        NNReal.coe_add]
      ring
    · funext ω
      simp only [Function.comp_apply, ProbabilityTheory.increment, X, Kyprianou.compensatedSmallJumpBand, c,
        NNReal.coe_zero]
      ring
  have hM_indep : HasIndependentIncrements M P := by
    intro k t ht
    refine SmallJumpCoreHelpers.iIndepFun_of_tendsto_ae P
      (f_n := fun n i => ProbabilityTheory.increment (X n) (t i.castSucc) (t i.succ))
      (f := fun i => ProbabilityTheory.increment M (t i.castSucc) (t i.succ))
      (fun n i => (hX_meas n (t i.succ)).sub (hX_meas n (t i.castSucc)))
      (fun i => (hM_meas (t i.succ)).sub (hM_meas (t i.castSucc)))
      (fun n => hX_indep n k t ht)
      (fun i => ?_)
    filter_upwards [hconv_ae (t i.succ), hconv_ae (t i.castSucc)] with ω h1 h2
    exact h1.sub h2
  have hM_stat : HasStationaryIncrements M P := by
    intro s h
    refine SmallJumpCoreHelpers.identDistrib_of_tendsto_ae P
      (f_n := fun n => ProbabilityTheory.increment (X n) s (s + h))
      (g_n := fun n => ProbabilityTheory.increment (X n) 0 h)
      (f := ProbabilityTheory.increment M s (s + h))
      (g := ProbabilityTheory.increment M 0 h)
      (fun n => (hX_meas n (s + h)).sub (hX_meas n s))
      (fun n => (hX_meas n h).sub (hX_meas n 0))
      ((hM_meas (s + h)).sub (hM_meas s))
      ((hM_meas h).sub (hM_meas 0))
      (fun n => hX_stat n s h)
      ?_ ?_
    · filter_upwards [hconv_ae (s + h), hconv_ae s] with ω h1 h2
      exact h1.sub h2
    · filter_upwards [hconv_ae h, hconv_ae 0] with ω h1 h2
      exact h1.sub h2
  have hM_cadlag : ∀ᵐ ω ∂P, ProbabilityTheory.IsCadlag (fun t => M t ω) := by
    have hcad := Kyprianou.Ch02.cadlagOfSmallJumpUniformApproxV1 P levyMeasure hlevyMeasure N M huniform
    filter_upwards [hcad] with ω ⟨hrc, hll⟩
    intro t
    refine ⟨hrc t, ?_⟩
    by_cases ht0 : t = 0
    · subst ht0
      refine ⟨0, ?_⟩
      have hemp : Set.Iio (0 : ℝ≥0) = ∅ :=
        Set.eq_empty_of_forall_notMem fun x hx => not_lt_of_ge (zero_le' : (0 : ℝ≥0) ≤ x) hx
      rw [hemp, nhdsWithin_empty]
      exact tendsto_bot
    · exact hll t (pos_iff_ne_zero.mpr ht0)
  have hM_levy : ProbabilityTheory.IsLevyProcess M P :=
    ⟨hM_zero, hM_indep, hM_stat, hM_cadlag⟩
  exact ⟨M, ℱ, hM_levy, hℱ, hM_mart, hM_L2, huniform⟩
