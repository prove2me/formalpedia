-- Prove2me | solution 1 for Kyprianou.Ch02.prmFiniteCompensatedConditionalExpectationV1
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-23T19:45:01.542875+00:00
-- url     : https://prove2.me/submissions/372b1a1c-a8e1-42bf-96f2-80af47bcd241

import Mathlib
import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch02_prmFiniteCompensatedStronglyAdaptedIntegrableV1
import Theorems.Thm_Kyprianou_Ch02_prmMarkedIntegralMeasurableAmbientV1

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

set_option autoImplicit false

namespace PrmFiniteCompensatedCondExpHelpers

/-! ### Section 1: Reference intensity and Poisson first moment on `(a, b] × A` -/

private lemma referenceIntensity_Ioc_prod (ν : Measure ℝ) [SigmaFinite ν]
    {a b : ℝ} (ha : 0 ≤ a) {A : Set ℝ} :
    LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ A) =
      ENNReal.ofReal (b - a) * ν A := by
  unfold LevyStochCalc.Poisson.referenceIntensity
  rw [Measure.prod_prod, Measure.restrict_apply measurableSet_Ioc]
  have hsub : Set.Ioc a b ∩ Set.Ici (0 : ℝ) = Set.Ioc a b :=
    Set.inter_eq_left.mpr fun _ hx => ha.trans (le_of_lt hx.1)
  rw [hsub, Real.volume_Ioc]

private lemma referenceIntensity_Ioc_prod_ne_top (ν : Measure ℝ) [SigmaFinite ν]
    {a b : ℝ} (ha : 0 ≤ a) {A : Set ℝ} (hAfin : ν A < ⊤) :
    LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ A) ≠ ⊤ := by
  rw [referenceIntensity_Ioc_prod ν ha]
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
    {S : Set (ℝ × ℝ)} (hS : MeasurableSet S)
    (hSfin : LevyStochCalc.Poisson.referenceIntensity ν S ≠ ⊤) :
    Integrable (fun ω => (N.N ω S).toReal) P ∧
      ∫ ω, (N.N ω S).toReal ∂P = (LevyStochCalc.Poisson.referenceIntensity ν S).toReal := by
  let μ : ℝ≥0 := (LevyStochCalc.Poisson.referenceIntensity ν S).toNNReal
  have hμ_eq : (μ : ℝ) = (LevyStochCalc.Poisson.referenceIntensity ν S).toReal := rfl
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
  have hmean : ∫ ω, (N.N ω S).toReal ∂P = (LevyStochCalc.Poisson.referenceIntensity ν S).toReal := by
    have h1 : ∫ ω, (N.N ω S).toReal ∂P = ∫ r, r.toReal ∂(P.map (fun ω => N.N ω S)) :=
      (integral_map hN_meas.aemeasurable htoReal_meas.aestronglyMeasurable).symm
    have h2 : ∫ r, r.toReal ∂((ProbabilityTheory.poissonMeasure μ).map (fun n : ℕ => (n : ℝ≥0∞))) =
        ∫ n : ℕ, ((n : ℝ≥0∞).toReal) ∂(ProbabilityTheory.poissonMeasure μ) :=
      integral_map hcast_meas.aemeasurable htoReal_meas.aestronglyMeasurable
    rw [h1, hlaw, h2]
    simp only [ENNReal.toReal_natCast, hpois_mean, hμ_eq]
  exact ⟨hint, hmean⟩

private lemma prm_count_integrable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ν : Measure ℝ} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    {S : Set (ℝ × ℝ)} (hS : MeasurableSet S)
    (hSfin : LevyStochCalc.Poisson.referenceIntensity ν S ≠ ⊤) :
    Integrable (fun ω => (N.N ω S).toReal) P :=
  (prm_count_int_and_mean N hS hSfin).1

private lemma prm_count_first_moment {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ν : Measure ℝ} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    {S : Set (ℝ × ℝ)} (hS : MeasurableSet S)
    (hSfin : LevyStochCalc.Poisson.referenceIntensity ν S ≠ ⊤) :
    ∫ ω, (N.N ω S).toReal ∂P = (LevyStochCalc.Poisson.referenceIntensity ν S).toReal :=
  (prm_count_int_and_mean N hS hSfin).2

/-! ### Section 2: Dyadic mark partitions (signed & nonnegative) -/

private noncomputable def dyadIdx (m : ℕ) : Finset ℤ :=
  Finset.Ico (-(m * 2 ^ m : ℤ)) (m * 2 ^ m : ℤ)

private def dyadCell (B : Set ℝ) (m : ℕ) (k : ℤ) : Set ℝ :=
  B ∩ Set.Ico ((k : ℝ) / (2 : ℝ) ^ m) (((k : ℝ) + 1) / (2 : ℝ) ^ m)

private noncomputable def dyadVal (m : ℕ) (k : ℤ) : ℝ :=
  (k : ℝ) / (2 : ℝ) ^ m

private noncomputable def dyadApprox (B : Set ℝ) (m : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ dyadIdx m, (dyadCell B m k).indicator (fun _ => dyadVal m k) x

private lemma dyadCell_measurableSet {B : Set ℝ} (hB : MeasurableSet B) (m : ℕ) (k : ℤ) :
    MeasurableSet (dyadCell B m k) :=
  hB.inter measurableSet_Ico

private lemma dyadApprox_measurable {B : Set ℝ} (hB : MeasurableSet B) (m : ℕ) :
    Measurable (dyadApprox B m) :=
  Finset.measurable_sum (dyadIdx m) fun k _ =>
    measurable_const.indicator (dyadCell_measurableSet hB m k)

private lemma dyadCell_pairwise_disjoint (B : Set ℝ) (m : ℕ) :
    Pairwise fun k₁ k₂ : ℤ => Disjoint (dyadCell B m k₁) (dyadCell B m k₂) := by
  intro k₁ k₂ hne
  rw [Set.disjoint_left]
  intro x hx₁ hx₂
  have hpos : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
  have h1 : (k₁ : ℝ) < (k₂ : ℝ) + 1 := by
    have := lt_of_le_of_lt hx₁.2.1 hx₂.2.2
    exact (div_lt_div_iff_of_pos_right hpos).mp this
  have h2 : (k₂ : ℝ) < (k₁ : ℝ) + 1 := by
    have := lt_of_le_of_lt hx₂.2.1 hx₁.2.2
    exact (div_lt_div_iff_of_pos_right hpos).mp this
  have hk1 : k₁ < k₂ + 1 := by exact_mod_cast h1
  have hk2 : k₂ < k₁ + 1 := by exact_mod_cast h2
  omega

private lemma dyadApprox_sub_le {B : Set ℝ} {m : ℕ} {x : ℝ}
    (hxB : x ∈ B) (hxlo : -(m : ℝ) ≤ x) (hxhi : x < (m : ℝ)) :
    |dyadApprox B m x - x| ≤ 1 / (2 : ℝ) ^ m := by
  have hpos : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
  set k₀ : ℤ := ⌊x * (2 : ℝ) ^ m⌋
  have hk₀_mem : k₀ ∈ dyadIdx m := by
    rw [dyadIdx, Finset.mem_Ico]
    constructor
    · have h1 : ((-(m * 2 ^ m : ℤ) : ℤ) : ℝ) ≤ x * (2 : ℝ) ^ m := by
        push_cast
        have := mul_le_mul_of_nonneg_right hxlo hpos.le
        linarith
      exact Int.le_floor.mpr h1
    · have h2 : x * (2 : ℝ) ^ m < ((m * 2 ^ m : ℤ) : ℝ) := by
        push_cast
        exact mul_lt_mul_of_pos_right hxhi hpos
      exact Int.floor_lt.mpr h2
  have hx_mem : x ∈ dyadCell B m k₀ := by
    refine ⟨hxB, ?_, ?_⟩
    · rw [div_le_iff₀ hpos]
      exact Int.floor_le (x * (2 : ℝ) ^ m)
    · rw [lt_div_iff₀ hpos]
      exact Int.lt_floor_add_one (x * (2 : ℝ) ^ m)
  have heval : dyadApprox B m x = dyadVal m k₀ := by
    unfold dyadApprox
    rw [Finset.sum_eq_single k₀]
    · exact Set.indicator_of_mem hx_mem _
    · intro k _ hkne
      have hnot : x ∉ dyadCell B m k :=
        Set.disjoint_left.mp (dyadCell_pairwise_disjoint B m hkne.symm) hx_mem
      exact Set.indicator_of_notMem hnot _
    · intro hnot; exact absurd hk₀_mem hnot
  rw [heval]
  have hle : dyadVal m k₀ ≤ x := hx_mem.2.1
  have hlt : x < dyadVal m k₀ + 1 / (2 : ℝ) ^ m := by
    have := hx_mem.2.2
    unfold dyadVal
    linarith [add_div (k₀ : ℝ) 1 ((2 : ℝ) ^ m)]
  rw [abs_le]
  constructor <;> linarith

private lemma abs_dyadApprox_le (B : Set ℝ) (m : ℕ) (x : ℝ) :
    |dyadApprox B m x| ≤ |x| + 1 := by
  by_cases h : ∃ k ∈ dyadIdx m, x ∈ dyadCell B m k
  · rcases h with ⟨k₀, hk₀, hx₀⟩
    have heval : dyadApprox B m x = dyadVal m k₀ := by
      unfold dyadApprox
      rw [Finset.sum_eq_single k₀]
      · exact Set.indicator_of_mem hx₀ _
      · intro k _ hkne
        exact Set.indicator_of_notMem
          (Set.disjoint_left.mp (dyadCell_pairwise_disjoint B m hkne.symm) hx₀) _
      · intro hnot; exact absurd hk₀ hnot
    rw [heval]
    have hle : dyadVal m k₀ ≤ x := hx₀.2.1
    have hlt : x < dyadVal m k₀ + 1 / (2 : ℝ) ^ m := by
      have := hx₀.2.2
      unfold dyadVal
      linarith [add_div (k₀ : ℝ) 1 ((2 : ℝ) ^ m)]
    have hpow : (1 : ℝ) / (2 : ℝ) ^ m ≤ 1 := by
      rw [div_le_one (by positivity)]
      exact one_le_pow₀ (by norm_num)
    have hdiff : |dyadVal m k₀ - x| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith
    have htri : |dyadVal m k₀| ≤ |dyadVal m k₀ - x| + |x| := by
      simpa [sub_add_cancel] using abs_add_le (dyadVal m k₀ - x) x
    linarith
  · push_neg at h
    have heval : dyadApprox B m x = 0 := by
      unfold dyadApprox
      exact Finset.sum_eq_zero fun k hk => Set.indicator_of_notMem (h k hk) _
    rw [heval, abs_zero]
    positivity

private def absCell (B : Set ℝ) (m k : ℕ) : Set ℝ :=
  B ∩ {x : ℝ | ((k : ℝ) / (2 : ℝ) ^ m) ≤ |x| ∧ |x| < (((k : ℝ) + 1) / (2 : ℝ) ^ m)}

private noncomputable def absApprox (B : Set ℝ) (m : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (m * 2 ^ m), (absCell B m k).indicator (fun _ => (k : ℝ) / (2 : ℝ) ^ m) x

private lemma absCell_measurableSet {B : Set ℝ} (hB : MeasurableSet B) (m k : ℕ) :
    MeasurableSet (absCell B m k) := by
  have h1 : MeasurableSet {x : ℝ | ((k : ℝ) / (2 : ℝ) ^ m) ≤ |x| ∧ |x| < (((k : ℝ) + 1) / (2 : ℝ) ^ m)} :=
    (continuous_abs.measurable (measurableSet_Ico : MeasurableSet (Set.Ico _ _)))
  exact hB.inter h1

private lemma absCell_pairwise_disjoint (B : Set ℝ) (m : ℕ) :
    Pairwise fun k₁ k₂ : ℕ => Disjoint (absCell B m k₁) (absCell B m k₂) := by
  intro k₁ k₂ hne
  rw [Set.disjoint_left]
  intro x hx₁ hx₂
  have hpos : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
  have h1 : (k₁ : ℝ) < (k₂ : ℝ) + 1 :=
    (div_lt_div_iff_of_pos_right hpos).mp (lt_of_le_of_lt hx₁.2.1 hx₂.2.2)
  have h2 : (k₂ : ℝ) < (k₁ : ℝ) + 1 :=
    (div_lt_div_iff_of_pos_right hpos).mp (lt_of_le_of_lt hx₂.2.1 hx₁.2.2)
  have hk1 : k₁ < k₂ + 1 := by exact_mod_cast h1
  have hk2 : k₂ < k₁ + 1 := by exact_mod_cast h2
  omega

private lemma absApprox_nonneg (B : Set ℝ) (m : ℕ) (x : ℝ) : 0 ≤ absApprox B m x := by
  unfold absApprox
  exact Finset.sum_nonneg fun k _ => Set.indicator_nonneg (fun _ _ => by positivity) x

private lemma absApprox_le_abs (B : Set ℝ) (m : ℕ) (x : ℝ) : absApprox B m x ≤ |x| := by
  by_cases h : ∃ k ∈ Finset.range (m * 2 ^ m), x ∈ absCell B m k
  · rcases h with ⟨k₀, hk₀, hx₀⟩
    have heval : absApprox B m x = (k₀ : ℝ) / (2 : ℝ) ^ m := by
      unfold absApprox
      rw [Finset.sum_eq_single k₀]
      · exact Set.indicator_of_mem hx₀ _
      · intro k _ hkne
        exact Set.indicator_of_notMem
          (Set.disjoint_left.mp (absCell_pairwise_disjoint B m hkne.symm) hx₀) _
      · intro hnot; exact absurd hk₀ hnot
    rw [heval]
    exact hx₀.2.1
  · push_neg at h
    have heval : absApprox B m x = 0 := by
      unfold absApprox
      exact Finset.sum_eq_zero fun k hk => Set.indicator_of_notMem (h k hk) _
    rw [heval]
    exact abs_nonneg x

private lemma absApprox_sub_le {B : Set ℝ} {m : ℕ} {x : ℝ} (hxB : x ∈ B) (hxbd : |x| < (m : ℝ)) :
    |absApprox B m x - abs x| ≤ 1 / (2 : ℝ) ^ m := by
  have hpos : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
  set k₀ : ℕ := ⌊|x| * (2 : ℝ) ^ m⌋₊
  have hk₀_mem : k₀ ∈ Finset.range (m * 2 ^ m) := by
    rw [Finset.mem_range]
    have hlt : |x| * (2 : ℝ) ^ m < ((m * 2 ^ m : ℕ) : ℝ) := by
      push_cast
      exact mul_lt_mul_of_pos_right hxbd hpos
    exact (Nat.floor_lt (by positivity)).mpr hlt
  have hx_mem : x ∈ absCell B m k₀ := by
    refine ⟨hxB, ?_, ?_⟩
    · rw [div_le_iff₀ hpos]
      exact Nat.floor_le (by positivity)
    · rw [lt_div_iff₀ hpos]
      exact Nat.lt_floor_add_one (|x| * (2 : ℝ) ^ m)
  have heval : absApprox B m x = (k₀ : ℝ) / (2 : ℝ) ^ m := by
    unfold absApprox
    rw [Finset.sum_eq_single k₀]
    · exact Set.indicator_of_mem hx_mem _
    · intro k _ hkne
      exact Set.indicator_of_notMem
        (Set.disjoint_left.mp (absCell_pairwise_disjoint B m hkne.symm) hx_mem) _
    · intro hnot; exact absurd hk₀_mem hnot
  rw [heval]
  have hle : (k₀ : ℝ) / (2 : ℝ) ^ m ≤ |x| := hx_mem.2.1
  have hlt : |x| < (k₀ : ℝ) / (2 : ℝ) ^ m + 1 / (2 : ℝ) ^ m := by
    have := hx_mem.2.2
    linarith [add_div (k₀ : ℝ) 1 ((2 : ℝ) ^ m)]
  rw [abs_le]
  constructor <;> linarith

private lemma absApprox_measurable {B : Set ℝ} (hB : MeasurableSet B) (m : ℕ) :
    Measurable (absApprox B m) :=
  Finset.measurable_sum (Finset.range (m * 2 ^ m)) fun k _ =>
    measurable_const.indicator (absCell_measurableSet hB m k)

/-! ### Section 3: Right-continuous completed natural filtration bound -/

private noncomputable def natMeasSpace
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure ℝ} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (r : ℝ≥0) : MeasurableSpace Ω :=
  ⨆ (v : ℝ≥0) (_ : v ≤ r) (A : Set ℝ) (_ : MeasurableSet A),
    MeasurableSpace.comap (fun ω => N.N ω (Set.Ioc (0 : ℝ) (v : ℝ) ×ˢ A)) inferInstance

private lemma natMeasSpace_le
    {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure ℝ} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (r : ℝ≥0) : natMeasSpace N r ≤ mΩ := by
  refine iSup₂_le fun v _ => iSup₂_le fun A hA => ?_
  exact (N.measurable_eval (measurableSet_Ioc.prod hA)).comap_le

private lemma natMeasSpace_mono
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure ℝ} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    {r₁ r₂ : ℝ≥0} (hr : r₁ ≤ r₂) : natMeasSpace N r₁ ≤ natMeasSpace N r₂ := by
  refine iSup₂_le fun v hv => iSup₂_le fun A hA => ?_
  exact le_iSup₂_of_le v (hv.trans hr) (le_iSup₂_of_le A hA le_rfl)

private lemma natMeasSpace_count_measurable
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure ℝ} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    {r v : ℝ≥0} (hv : v ≤ r) {A : Set ℝ} (hA : MeasurableSet A) :
    @Measurable Ω ℝ≥0∞ (natMeasSpace N r) inferInstance
      (fun ω => N.N ω (Set.Ioc (0 : ℝ) (v : ℝ) ×ˢ A)) := by
  have hle :
      MeasurableSpace.comap (fun ω => N.N ω (Set.Ioc (0 : ℝ) (v : ℝ) ×ˢ A)) inferInstance ≤
        natMeasSpace N r :=
    le_iSup₂_of_le v hv (le_iSup₂_of_le A hA le_rfl)
  exact Measurable.mono (comap_measurable _) hle le_rfl

private def completedMeasSpace
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (m : MeasurableSpace Ω) : MeasurableSpace Ω where
  MeasurableSet' E :=
    @MeasurableSet Ω mΩ E ∧ ∃ A : Set Ω, @MeasurableSet Ω m A ∧ P (symmDiff E A) = 0
  measurableSet_empty :=
    ⟨@MeasurableSet.empty Ω mΩ, ∅, @MeasurableSet.empty Ω m, by simp⟩
  measurableSet_compl E hE := by
    rcases hE with ⟨hEm, A, hAm, hAE⟩
    refine ⟨MeasurableSet.compl (m := mΩ) hEm, Aᶜ, MeasurableSet.compl (m := m) hAm, ?_⟩
    have hsym : symmDiff Eᶜ Aᶜ = symmDiff E A := by
      ext x; simp only [Set.mem_symmDiff, Set.mem_compl_iff]; tauto
    rw [hsym]
    exact hAE
  measurableSet_iUnion f hf := by
    refine ⟨MeasurableSet.iUnion (m := mΩ) (fun n => (hf n).1), ?_⟩
    choose A hAm hAE using fun n => (hf n).2
    refine ⟨⋃ n, A n, MeasurableSet.iUnion (m := m) hAm, ?_⟩
    have hsub : symmDiff (⋃ n, f n) (⋃ n, A n) ⊆ ⋃ n, symmDiff (f n) (A n) := by
      intro x hx
      simp only [Set.mem_symmDiff, Set.mem_iUnion] at hx ⊢
      rcases hx with ⟨⟨n, hfn⟩, hnot⟩ | ⟨⟨n, hAn⟩, hnot⟩
      · exact ⟨n, Or.inl ⟨hfn, fun h => hnot ⟨n, h⟩⟩⟩
      · exact ⟨n, Or.inr ⟨hAn, fun h => hnot ⟨n, h⟩⟩⟩
    exact measure_mono_null hsub (measure_iUnion_null hAE)

private noncomputable def completedNatFiltration
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {ν : Measure ℝ} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν) :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω) where
  seq r := completedMeasSpace P (natMeasSpace N r)
  mono' r₁ r₂ hr E hE :=
    ⟨hE.1, let ⟨A, hAm, hAE⟩ := hE.2; ⟨A, natMeasSpace_mono N hr A hAm, hAE⟩⟩
  le' _ _ hE := hE.1

private lemma filtration_le_completed_of_lt
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure ℝ} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    (hℱ : Kyprianou.Ch02.IsCompletedPoissonFiltration P ν N ℱ)
    {s u : ℝ≥0} (hsu : s < u) :
    ℱ s ≤ completedMeasSpace P (natMeasSpace N u) := by
  let 𝒞 := completedNatFiltration P N
  have h1 : ∀ t v : ℝ≥0, v ≤ t → ∀ A : Set ℝ, MeasurableSet A →
      @Measurable Ω ℝ≥0∞ (𝒞.rightCont t) inferInstance
        (fun ω => N.N ω (Set.Ioc (0 : ℝ) (v : ℝ) ×ˢ A)) := by
    intro t v hv A hA
    have hbase : @Measurable Ω ℝ≥0∞ (𝒞 t) inferInstance
        (fun ω => N.N ω (Set.Ioc (0 : ℝ) (v : ℝ) ×ˢ A)) := by
      intro S hS
      have hm_nat : @MeasurableSet Ω (natMeasSpace N t)
          ((fun ω => N.N ω (Set.Ioc (0 : ℝ) (v : ℝ) ×ˢ A)) ⁻¹' S) :=
        natMeasSpace_count_measurable N hv hA hS
      exact ⟨natMeasSpace_le N t _ hm_nat, _, hm_nat, by simp⟩
    exact hbase.mono (𝒞.le_rightCont t) le_rfl
  have h2 : ∀ t (S : Set Ω), MeasurableSet S → P S = 0 →
      @MeasurableSet Ω (𝒞.rightCont t) S := by
    intro t S hS hPS
    have hbase : @MeasurableSet Ω (𝒞 t) S :=
      ⟨hS, ∅, @MeasurableSet.empty Ω (natMeasSpace N t), by simpa using hPS⟩
    exact 𝒞.le_rightCont t S hbase
  have h3 : 𝒞.rightCont.IsRightContinuous := ⟨le_of_eq 𝒞.rightCont_self⟩
  have hle : ℱ ≤ 𝒞.rightCont := hℱ.2.2.2 𝒞.rightCont h1 h2 h3
  have hrc : 𝒞.rightCont s = ⨅ (j : ℝ≥0) (_ : j > s), 𝒞 j := by
    rw [Filtration.rightCont_apply]
    simp [nhdsWithin_Ioi_neBot (le_refl s)]
  calc
    ℱ s ≤ 𝒞.rightCont s := hle s
    _ = ⨅ (j : ℝ≥0) (_ : j > s), 𝒞 j := hrc
    _ ≤ 𝒞 u := iInf₂_le u hsu

/-! ### Section 4: Past-future independence and single-count set integral -/

private lemma natMeasSpace_indep_future_count
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure ℝ} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    {u t : ℝ≥0} (hut : u < t) {C : Set ℝ} (hC : MeasurableSet C) (hCfin : ν C ≠ ⊤) :
    ProbabilityTheory.Indep (natMeasSpace N u)
      (MeasurableSpace.comap (fun ω => N.N ω (Set.Ioc (u : ℝ) (t : ℝ) ×ˢ C)) inferInstance) P := by
  have hind := N.joint_past_future_independent (NNReal.coe_nonneg u) (by exact_mod_cast hut) hC hCfin
  refine ProbabilityTheory.indep_of_indep_of_le_left hind ?_
  refine iSup₂_le fun v hv => iSup₂_le fun A hA => ?_
  have hmem : Set.Ioc (0 : ℝ) (v : ℝ) ×ˢ A ∈
      {D : Set (ℝ × ℝ) | D ⊆ Set.Iic (u : ℝ) ×ˢ Set.univ ∧ MeasurableSet D} := by
    refine ⟨?_, measurableSet_Ioc.prod hA⟩
    intro z hz
    exact ⟨hz.1.2.trans (by exact_mod_cast hv), trivial⟩
  exact le_iSup₂_of_le (Set.Ioc (0 : ℝ) (v : ℝ) ×ˢ A) hmem le_rfl

private lemma setIntegral_future_count_eq
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure ℝ} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    {u t : ℝ≥0} (hut : u < t) {C : Set ℝ} (hC : MeasurableSet C) (hCfin : ν C < ⊤)
    {A : Set Ω} (hA : @MeasurableSet Ω (natMeasSpace N u) A) :
    ∫ ω in A, (N.N ω (Set.Ioc (u : ℝ) (t : ℝ) ×ˢ C)).toReal ∂P =
      P.real A * (((t : ℝ) - (u : ℝ)) * (ν C).toReal) := by
  have hA_amb : MeasurableSet A := natMeasSpace_le N u A hA
  let f : Ω → ℝ := A.indicator (fun _ => (1 : ℝ))
  let g : Ω → ℝ := fun ω => (N.N ω (Set.Ioc (u : ℝ) (t : ℝ) ×ˢ C)).toReal
  have hind : ProbabilityTheory.Indep (natMeasSpace N u)
      (MeasurableSpace.comap (fun ω => N.N ω (Set.Ioc (u : ℝ) (t : ℝ) ×ˢ C)) inferInstance) P :=
    natMeasSpace_indep_future_count N hut hC hCfin.ne
  have hf_nat : @Measurable Ω ℝ (natMeasSpace N u) inferInstance f :=
    (@measurable_const ℝ Ω _ (natMeasSpace N u) _).indicator hA
  have hg_comap : @Measurable Ω ℝ
      (MeasurableSpace.comap (fun ω => N.N ω (Set.Ioc (u : ℝ) (t : ℝ) ×ˢ C)) inferInstance)
      inferInstance g :=
    ENNReal.measurable_toReal.comp (comap_measurable _)
  have hindFun : f ⟂ᵢ[P] g := by
    rw [ProbabilityTheory.indepFun_iff_measure_inter_preimage_eq_mul]
    intro s₁ s₂ hs₁ hs₂
    exact (ProbabilityTheory.Indep_iff _ _ _).mp hind _ _ (hf_nat hs₁) (hg_comap hs₂)
  have hf_meas : Measurable f := measurable_const.indicator hA_amb
  have hg_meas : Measurable g :=
    ENNReal.measurable_toReal.comp (N.measurable_eval (measurableSet_Ioc.prod hC))
  have hmul : (fun ω => A.indicator g ω) = (fun ω => f ω * g ω) := by
    funext ω
    by_cases hω : ω ∈ A <;> simp [f, hω]
  rw [← integral_indicator hA_amb, hmul,
    hindFun.integral_fun_mul_eq_mul_integral hf_meas.aestronglyMeasurable hg_meas.aestronglyMeasurable]
  have hf_int : ∫ ω, f ω ∂P = P.real A := by
    simp only [f, integral_indicator_const (1 : ℝ) hA_amb, smul_eq_mul, mul_one]
  have hg_int : ∫ ω, g ω ∂P = ((t : ℝ) - (u : ℝ)) * (ν C).toReal := by
    have hSfin := referenceIntensity_Ioc_prod_ne_top ν (a := (u : ℝ)) (b := (t : ℝ))
      (NNReal.coe_nonneg u) hCfin
    rw [prm_count_first_moment N (measurableSet_Ioc.prod hC) hSfin,
      referenceIntensity_Ioc_prod ν (NNReal.coe_nonneg u),
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (sub_nonneg.mpr (by exact_mod_cast hut.le))]
  rw [hf_int, hg_int]

end PrmFiniteCompensatedCondExpHelpers

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hfinite : ν B < ⊤)
    (hfirst : Integrable (fun x : ℝ => x) (ν.restrict B))
    (ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (hℱ : Kyprianou.Ch02.IsCompletedPoissonFiltration P ν N ℱ) :
    ∀ (s t : ℝ≥0), s ≤ t →
      P[((fun (t : ℝ≥0) ω =>
      (∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B), z.2 ∂(N.N ω)) -
      (t : ℝ) * (∫ x in B, x ∂ν)) t) | ℱ s] =ᵐ[P]
        ((fun (t : ℝ≥0) ω =>
      (∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B), z.2 ∂(N.N ω)) -
      (t : ℝ) * (∫ x in B, x ∂ν)) s) := by
  let M : ℝ≥0 → Ω → ℝ := fun r ω =>
    (∫ z in (Set.Ioc (0 : ℝ) (r : ℝ) ×ˢ B), z.2 ∂(N.N ω)) - (r : ℝ) * (∫ x in B, x ∂ν)
  have hAI :=
    Kyprianou.Ch02.prmFiniteCompensatedStronglyAdaptedIntegrableV1 P ν N B hB hfinite hfirst ℱ hℱ
  have hM_sm : ∀ r : ℝ≥0, StronglyMeasurable[ℱ r] (M r) := fun r => hAI.1 r
  have hM_int : ∀ r : ℝ≥0, Integrable (M r) P := fun r => hAI.2 r
  intro s t hst
  rcases eq_or_lt_of_le hst with rfl | hst_lt
  · exact Filter.EventuallyEq.of_eq
      (condExp_of_stronglyMeasurable (ℱ.le s) (hM_sm s) (hM_int s))
  · -- Reduce via `ae_eq_condExp_of_forall_setIntegral_eq` to showing `∫_E M s = ∫_E M t` for `E ∈ ℱ s`
    refine (ae_eq_condExp_of_forall_setIntegral_eq (ℱ.le s) (hM_int t)
      (fun E _ _ => (hM_int s).integrableOn) ?_
      (hM_sm s).aestronglyMeasurable).symm
    -- Shared full-measure good event `G` on `W := (0, t] × B`
    let I0 : Set ℝ := Set.Ioc (0 : ℝ) (t : ℝ)
    let W : Set (ℝ × ℝ) := I0 ×ˢ B
    have hW : MeasurableSet W := measurableSet_Ioc.prod hB
    have hWfin : LevyStochCalc.Poisson.referenceIntensity ν W ≠ ⊤ :=
      PrmFiniteCompensatedCondExpHelpers.referenceIntensity_Ioc_prod_ne_top ν le_rfl hfinite
    let Etail : ℕ → Set (ℝ × ℝ) := fun R => I0 ×ˢ (B \ Set.Icc (-(R : ℝ)) (R : ℝ))
    have hEtail_meas : ∀ R : ℕ, MeasurableSet (Etail R) := fun R =>
      measurableSet_Ioc.prod (hB.diff measurableSet_Icc)
    have hEtail_sub : ∀ R : ℕ, Etail R ⊆ W := fun R =>
      Set.prod_mono le_rfl Set.diff_subset
    have hEtail_fin : ∀ R : ℕ, LevyStochCalc.Poisson.referenceIntensity ν (Etail R) ≠ ⊤ := fun R =>
      ne_top_of_le_ne_top hWfin (measure_mono (hEtail_sub R))
    have hEtail_anti : Antitone Etail := by
      intro R₁ R₂ hR
      refine Set.prod_mono le_rfl (Set.diff_subset_diff_right ?_)
      exact Set.Icc_subset_Icc (by exact_mod_cast Int.neg_le_neg (Int.ofNat_le.mpr hR))
        (by exact_mod_cast hR)
    have hEtail_iInter : (⋂ R : ℕ, Etail R) = ∅ := by
      ext z
      simp only [Set.mem_iInter, Set.mem_empty_iff_false, iff_false, not_forall]
      obtain ⟨R, hR⟩ := exists_nat_gt |z.2|
      refine ⟨R, fun hz => ?_⟩
      have hle : |z.2| ≤ (R : ℝ) := le_of_lt hR
      exact hz.2.2 (abs_le.mp hle)
    let G : Set Ω :=
      {ω | (∃ n : ℕ, N.N ω W = (n : ℝ≥0∞)) ∧ (∀ R : ℕ, ∃ k : ℕ, N.N ω (Etail R) = (k : ℝ≥0∞))}
    have hae_G : ∀ᵐ ω ∂P, ω ∈ G := by
      have h1 : ∀ᵐ ω ∂P, ∃ n : ℕ, N.N ω W = (n : ℝ≥0∞) := N.integer_valued hW hWfin
      have h2 : ∀ᵐ ω ∂P, ∀ R : ℕ, ∃ k : ℕ, N.N ω (Etail R) = (k : ℝ≥0∞) :=
        ae_all_iff.mpr fun R => N.integer_valued (hEtail_meas R) (hEtail_fin R)
      filter_upwards [h1, h2] with ω hω1 hω2
      exact ⟨hω1, hω2⟩
    have hG_compact : ∀ ω ∈ G,
        ∃ (nW R₀ : ℕ), N.N ω W = (nW : ℝ≥0∞) ∧
          ∀ᵐ z ∂((N.N ω).restrict W), z.2 ∈ B ∧ |z.2| ≤ (R₀ : ℝ) := by
      intro ω ⟨⟨nW, hnW⟩, hRint⟩
      have hfin_W : N.N ω W ≠ ⊤ := by simp [hnW]
      have hnull_meas : ∀ R, NullMeasurableSet (Etail R) (N.N ω) := fun R =>
        (hEtail_meas R).nullMeasurableSet
      have htend : Tendsto (fun R => N.N ω (Etail R)) atTop (𝓝 (N.N ω (⋂ R, Etail R))) :=
        MeasureTheory.tendsto_measure_iInter_atTop hnull_meas hEtail_anti
          ⟨0, ne_top_of_le_ne_top hfin_W (measure_mono (hEtail_sub 0))⟩
      rw [hEtail_iInter, measure_empty] at htend
      have hlt1 : ∀ᶠ R in atTop, N.N ω (Etail R) < 1 :=
        htend.eventually (gt_mem_nhds zero_lt_one)
      obtain ⟨R₀, hR₀⟩ := Filter.eventually_atTop.mp hlt1
      have hzero : N.N ω (Etail R₀) = 0 := by
        obtain ⟨k, hk⟩ := hRint R₀
        have hklt : (k : ℝ≥0∞) < 1 := by simpa [hk] using hR₀ R₀ le_rfl
        have hk0 : k = 0 := by
          have : k < 1 := by exact_mod_cast hklt
          omega
        simp [hk, hk0]
      refine ⟨nW, R₀, hnW, ?_⟩
      have hmemW : ∀ᵐ z ∂((N.N ω).restrict W), z ∈ W := ae_restrict_mem hW
      have hnotE : ∀ᵐ z ∂((N.N ω).restrict W), z ∉ Etail R₀ := by
        rw [ae_iff]
        have hset : {z | ¬ z ∉ Etail R₀} = Etail R₀ := by
          ext z; simp
        rw [hset, Measure.restrict_apply (hEtail_meas R₀),
          Set.inter_eq_left.mpr (hEtail_sub R₀), hzero]
      filter_upwards [hmemW, hnotE] with z hzW hznotE
      refine ⟨hzW.2, ?_⟩
      by_contra hgt
      push_neg at hgt
      have hnotIcc : z.2 ∉ Set.Icc (-(R₀ : ℝ)) (R₀ : ℝ) := by
        intro hIcc
        exact not_le_of_gt hgt (abs_le.mpr hIcc)
      exact hznotE ⟨hzW.1, hzW.2, hnotIcc⟩
    -- Nonnegative dyadic Fatou: `Z ω := ∫ z in W, |z.2| ∂(N.N ω)` is `P`-integrable
    let Z : Ω → ℝ := fun ω => ∫ z in W, |z.2| ∂(N.N ω)
    let Ym : ℕ → Ω → ℝ := fun m ω =>
      ∑ k ∈ Finset.range (m * 2 ^ m),
        ((k : ℝ) / (2 : ℝ) ^ m) *
          (N.N ω (I0 ×ˢ PrmFiniteCompensatedCondExpHelpers.absCell B m k)).toReal
    have hYm_meas : ∀ m : ℕ, Measurable (Ym m) := fun m =>
      Finset.measurable_sum (Finset.range (m * 2 ^ m)) fun k _ =>
        measurable_const.mul
          (ENNReal.measurable_toReal.comp
            (N.measurable_eval (measurableSet_Ioc.prod
              (PrmFiniteCompensatedCondExpHelpers.absCell_measurableSet hB m k))))
    have hYm_nn : ∀ m ω, 0 ≤ Ym m ω := fun m ω =>
      Finset.sum_nonneg fun k _ => mul_nonneg (by positivity) ENNReal.toReal_nonneg
    have hYm_mean_le : ∀ m : ℕ, ∫ ω, Ym m ω ∂P ≤ (t : ℝ) * ∫ x in B, |x| ∂ν := by
      intro m
      have hterm_int : ∀ k ∈ Finset.range (m * 2 ^ m),
          Integrable (fun ω => ((k : ℝ) / (2 : ℝ) ^ m) *
            (N.N ω (I0 ×ˢ PrmFiniteCompensatedCondExpHelpers.absCell B m k)).toReal) P := by
        intro k _
        have hck := PrmFiniteCompensatedCondExpHelpers.absCell_measurableSet hB m k
        have hck_fin : ν (PrmFiniteCompensatedCondExpHelpers.absCell B m k) < ⊤ :=
          lt_of_le_of_lt (measure_mono Set.inter_subset_left) hfinite
        exact (PrmFiniteCompensatedCondExpHelpers.prm_count_integrable N
          (measurableSet_Ioc.prod hck)
          (PrmFiniteCompensatedCondExpHelpers.referenceIntensity_Ioc_prod_ne_top ν le_rfl hck_fin)).const_mul _
      have hterm_mean : ∀ k ∈ Finset.range (m * 2 ^ m),
          ∫ ω, ((k : ℝ) / (2 : ℝ) ^ m) *
            (N.N ω (I0 ×ˢ PrmFiniteCompensatedCondExpHelpers.absCell B m k)).toReal ∂P =
            (t : ℝ) * (((k : ℝ) / (2 : ℝ) ^ m) *
              (ν (PrmFiniteCompensatedCondExpHelpers.absCell B m k)).toReal) := by
        intro k _
        have hck := PrmFiniteCompensatedCondExpHelpers.absCell_measurableSet hB m k
        have hck_fin : ν (PrmFiniteCompensatedCondExpHelpers.absCell B m k) < ⊤ :=
          lt_of_le_of_lt (measure_mono Set.inter_subset_left) hfinite
        have hSfin := PrmFiniteCompensatedCondExpHelpers.referenceIntensity_Ioc_prod_ne_top ν
          (a := (0 : ℝ)) (b := (t : ℝ)) le_rfl hck_fin
        rw [integral_const_mul,
          PrmFiniteCompensatedCondExpHelpers.prm_count_first_moment N (measurableSet_Ioc.prod hck) hSfin,
          PrmFiniteCompensatedCondExpHelpers.referenceIntensity_Ioc_prod ν le_rfl,
          sub_zero, ENNReal.toReal_mul, ENNReal.toReal_ofReal (NNReal.coe_nonneg t)]
        ring
      have hsum_eq : ∫ ω, Ym m ω ∂P =
          (t : ℝ) * ∫ x in B, PrmFiniteCompensatedCondExpHelpers.absApprox B m x ∂ν := by
        rw [integral_finset_sum _ hterm_int, Finset.sum_congr rfl hterm_mean, ← Finset.mul_sum]
        congr 1
        haveI : IsFiniteMeasure (ν.restrict B) :=
          ⟨by rw [Measure.restrict_apply_univ]; exact hfinite⟩
        have hind_int : ∀ k ∈ Finset.range (m * 2 ^ m),
            Integrable ((PrmFiniteCompensatedCondExpHelpers.absCell B m k).indicator
              (fun _ => (k : ℝ) / (2 : ℝ) ^ m)) (ν.restrict B) := fun k _ =>
          (integrable_const _).indicator (PrmFiniteCompensatedCondExpHelpers.absCell_measurableSet hB m k)
        change ∑ k ∈ Finset.range (m * 2 ^ m),
            ((k : ℝ) / (2 : ℝ) ^ m) * (ν (PrmFiniteCompensatedCondExpHelpers.absCell B m k)).toReal =
          ∫ x in B, (∑ k ∈ Finset.range (m * 2 ^ m),
            (PrmFiniteCompensatedCondExpHelpers.absCell B m k).indicator
              (fun _ => (k : ℝ) / (2 : ℝ) ^ m) x) ∂ν
        rw [integral_finset_sum _ hind_int]
        refine Finset.sum_congr rfl fun k _ => ?_
        have hkm := PrmFiniteCompensatedCondExpHelpers.absCell_measurableSet hB m k
        rw [integral_indicator_const _ hkm, Measure.real, Measure.restrict_apply hkm,
          Set.inter_eq_left.mpr (show PrmFiniteCompensatedCondExpHelpers.absCell B m k ⊆ B from Set.inter_subset_left),
          smul_eq_mul, mul_comm]
      rw [hsum_eq]
      refine mul_le_mul_of_nonneg_left ?_ (NNReal.coe_nonneg t)
      haveI : IsFiniteMeasure (ν.restrict B) :=
        ⟨by rw [Measure.restrict_apply_univ]; exact hfinite⟩
      have habs_int : Integrable (fun x : ℝ => |x|) (ν.restrict B) := hfirst.abs
      have happrox_int : Integrable (PrmFiniteCompensatedCondExpHelpers.absApprox B m) (ν.restrict B) :=
        Integrable.mono' habs_int
          (PrmFiniteCompensatedCondExpHelpers.absApprox_measurable hB m).aestronglyMeasurable
          (Filter.Eventually.of_forall fun x => by
            rw [Real.norm_of_nonneg (PrmFiniteCompensatedCondExpHelpers.absApprox_nonneg B m x)]
            exact PrmFiniteCompensatedCondExpHelpers.absApprox_le_abs B m x)
      exact integral_mono happrox_int habs_int fun x =>
        PrmFiniteCompensatedCondExpHelpers.absApprox_le_abs B m x
    have hYm_tendsto_on_G : ∀ ω ∈ G, Tendsto (fun m => Ym m ω) atTop (𝓝 (Z ω)) := by
      intro ω hω
      obtain ⟨nW, R₀, hnW, hae_z⟩ := hG_compact ω hω
      haveI : IsFiniteMeasure ((N.N ω).restrict W) :=
        ⟨by rw [Measure.restrict_apply_univ, hnW]; exact ENNReal.natCast_ne_top nW |>.lt_top⟩
      have hYm_eq : ∀ m : ℕ,
          Ym m ω = ∫ z in W, PrmFiniteCompensatedCondExpHelpers.absApprox B m z.2 ∂(N.N ω) := by
        intro m
        have hind_int : ∀ k ∈ Finset.range (m * 2 ^ m),
            Integrable (fun z : ℝ × ℝ =>
              (PrmFiniteCompensatedCondExpHelpers.absCell B m k).indicator
                (fun _ => (k : ℝ) / (2 : ℝ) ^ m) z.2) ((N.N ω).restrict W) := fun k _ => by
          have heq : (fun z : ℝ × ℝ =>
              (PrmFiniteCompensatedCondExpHelpers.absCell B m k).indicator
                (fun _ => (k : ℝ) / (2 : ℝ) ^ m) z.2) =
              (Prod.snd ⁻¹' PrmFiniteCompensatedCondExpHelpers.absCell B m k).indicator
                (fun _ => (k : ℝ) / (2 : ℝ) ^ m) := by
            funext z; by_cases hz : z.2 ∈ PrmFiniteCompensatedCondExpHelpers.absCell B m k <;> simp [hz]
          rw [heq]
          exact (integrable_const _).indicator
            ((PrmFiniteCompensatedCondExpHelpers.absCell_measurableSet hB m k).preimage measurable_snd)
        change ∑ k ∈ Finset.range (m * 2 ^ m),
            ((k : ℝ) / (2 : ℝ) ^ m) * (N.N ω (I0 ×ˢ PrmFiniteCompensatedCondExpHelpers.absCell B m k)).toReal =
          ∫ z in W, (∑ k ∈ Finset.range (m * 2 ^ m),
            (PrmFiniteCompensatedCondExpHelpers.absCell B m k).indicator
              (fun _ => (k : ℝ) / (2 : ℝ) ^ m) z.2) ∂(N.N ω)
        rw [integral_finset_sum _ hind_int]
        refine Finset.sum_congr rfl fun k _ => ?_
        have hkm : MeasurableSet ((Prod.snd : ℝ × ℝ → ℝ) ⁻¹' PrmFiniteCompensatedCondExpHelpers.absCell B m k) :=
          (PrmFiniteCompensatedCondExpHelpers.absCell_measurableSet hB m k).preimage measurable_snd
        have heq : (fun z : ℝ × ℝ =>
            (PrmFiniteCompensatedCondExpHelpers.absCell B m k).indicator
              (fun _ => (k : ℝ) / (2 : ℝ) ^ m) z.2) =
            (Prod.snd ⁻¹' PrmFiniteCompensatedCondExpHelpers.absCell B m k).indicator
              (fun _ => (k : ℝ) / (2 : ℝ) ^ m) := by
          funext z; by_cases hz : z.2 ∈ PrmFiniteCompensatedCondExpHelpers.absCell B m k <;> simp [hz]
        rw [heq, integral_indicator_const _ hkm, Measure.real, Measure.restrict_apply hkm]
        have hinter : (Prod.snd ⁻¹' PrmFiniteCompensatedCondExpHelpers.absCell B m k) ∩ W =
            I0 ×ˢ PrmFiniteCompensatedCondExpHelpers.absCell B m k := by
          ext z; simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_prod, W]
          exact ⟨fun h => ⟨h.2.1, h.1⟩, fun h => ⟨h.2, h.1, h.2.1⟩⟩
        rw [hinter, smul_eq_mul, mul_comm]
      simp_rw [hYm_eq]
      refine MeasureTheory.tendsto_integral_of_dominated_convergence
        (fun _ => (R₀ : ℝ))
        (fun m => ((PrmFiniteCompensatedCondExpHelpers.absApprox_measurable hB m).comp measurable_snd).aestronglyMeasurable)
        (integrable_const (R₀ : ℝ))
        (fun m => ?_) ?_
      · filter_upwards [hae_z] with z ⟨_, hzbd⟩
        rw [Real.norm_of_nonneg (PrmFiniteCompensatedCondExpHelpers.absApprox_nonneg B m z.2)]
        exact (PrmFiniteCompensatedCondExpHelpers.absApprox_le_abs B m z.2).trans hzbd
      · filter_upwards [hae_z] with z ⟨hzB, hzbd⟩
        rw [Metric.tendsto_atTop]
        intro ε hε
        obtain ⟨N₀, hN₀⟩ := exists_nat_gt (max (R₀ : ℝ) (1 / ε))
        refine ⟨N₀ + 1, fun m hm => ?_⟩
        have hm_gt_R : (R₀ : ℝ) < (m : ℝ) :=
          lt_of_le_of_lt (le_max_left _ _) (lt_of_lt_of_le hN₀ (by exact_mod_cast (Nat.le_succ N₀).trans hm))
        have hdist : |PrmFiniteCompensatedCondExpHelpers.absApprox B m z.2 - abs z.2| ≤ 1 / (2 : ℝ) ^ m :=
          PrmFiniteCompensatedCondExpHelpers.absApprox_sub_le hzB (lt_of_le_of_lt hzbd hm_gt_R)
        have hlt_eps : 1 / (2 : ℝ) ^ m < ε := by
          have hm_gt_inv : 1 / ε < (m : ℝ) :=
            lt_of_le_of_lt (le_max_right _ _) (lt_of_lt_of_le hN₀ (by exact_mod_cast (Nat.le_succ N₀).trans hm))
          have hmlt2 : (m : ℝ) < (2 : ℝ) ^ m := by exact_mod_cast Nat.lt_two_pow_self
          have h1 : 1 / ε < (2 : ℝ) ^ m := lt_trans hm_gt_inv hmlt2
          rw [div_lt_iff₀ hε] at h1
          rw [div_lt_iff₀ (by positivity)]
          linarith
        exact lt_of_le_of_lt (by simpa [Real.dist_eq] using hdist) hlt_eps
    have hZ_aesm : AEStronglyMeasurable Z P :=
      aestronglyMeasurable_of_tendsto_ae atTop
        (fun m => (hYm_meas m).aestronglyMeasurable)
        (hae_G.mono fun ω hω => hYm_tendsto_on_G ω hω)
    have hZ_nn : ∀ ω, 0 ≤ Z ω := fun ω =>
      integral_nonneg fun _ => abs_nonneg _
    have hZ_fin : HasFiniteIntegral Z P := by
      rw [hasFiniteIntegral_iff_enorm]
      have hfatou : ∫⁻ ω, liminf (fun m => ENNReal.ofReal (Ym m ω)) atTop ∂P ≤
          liminf (fun m => ∫⁻ ω, ENNReal.ofReal (Ym m ω) ∂P) atTop :=
        MeasureTheory.lintegral_liminf_le fun m => ENNReal.measurable_ofReal.comp (hYm_meas m)
      have hpoint_eq : (fun ω => ‖Z ω‖ₑ) =ᵐ[P]
          (fun ω => liminf (fun m => ENNReal.ofReal (Ym m ω)) atTop) := by
        filter_upwards [hae_G] with ω hω
        rw [Real.enorm_of_nonneg (hZ_nn ω)]
        have ht : Tendsto (fun m => ENNReal.ofReal (Ym m ω)) atTop (𝓝 (ENNReal.ofReal (Z ω))) :=
          (ENNReal.continuous_ofReal.tendsto (Z ω)).comp (hYm_tendsto_on_G ω hω)
        exact ht.liminf_eq.symm
      rw [lintegral_congr_ae hpoint_eq]
      have hbound : ∀ m : ℕ,
          ∫⁻ ω, ENNReal.ofReal (Ym m ω) ∂P ≤ ENNReal.ofReal ((t : ℝ) * ∫ x in B, |x| ∂ν) := fun m => by
        have hYm_int : Integrable (Ym m) P :=
          integrable_finset_sum _ fun k _ => by
            have hck := PrmFiniteCompensatedCondExpHelpers.absCell_measurableSet hB m k
            have hck_fin : ν (PrmFiniteCompensatedCondExpHelpers.absCell B m k) < ⊤ :=
              lt_of_le_of_lt (measure_mono Set.inter_subset_left) hfinite
            exact (PrmFiniteCompensatedCondExpHelpers.prm_count_integrable N
              (measurableSet_Ioc.prod hck)
              (PrmFiniteCompensatedCondExpHelpers.referenceIntensity_Ioc_prod_ne_top ν le_rfl hck_fin)).const_mul _
        rw [← ofReal_integral_eq_lintegral_ofReal hYm_int (Filter.Eventually.of_forall (hYm_nn m))]
        exact ENNReal.ofReal_le_ofReal (hYm_mean_le m)
      have hlim_le : liminf (fun m => ∫⁻ ω, ENNReal.ofReal (Ym m ω) ∂P) atTop ≤
          ENNReal.ofReal ((t : ℝ) * ∫ x in B, |x| ∂ν) :=
        Filter.liminf_le_of_frequently_le' (Filter.Eventually.of_forall hbound).frequently
      exact lt_of_le_of_lt (hfatou.trans hlim_le) ENNReal.ofReal_lt_top
    have hZ_int : Integrable Z P := ⟨hZ_aesm, hZ_fin⟩
    have hDom_int : Integrable (fun ω => Z ω + (N.N ω W).toReal) P :=
      hZ_int.add (PrmFiniteCompensatedCondExpHelpers.prm_count_integrable N hW hWfin)
    -- Step A: For any `u` with `s < u < t` and any `A ∈ natMeasSpace N u`, `∫_A Δ(u, t) = 0`
    have hfuture_zero : ∀ (u : ℝ≥0) (hut : u < t) (A : Set Ω)
        (_ : @MeasurableSet Ω (PrmFiniteCompensatedCondExpHelpers.natMeasSpace N u) A),
        ∫ ω in A, ((∫ z in (Set.Ioc (u : ℝ) (t : ℝ) ×ˢ B), z.2 ∂(N.N ω)) -
          ((t : ℝ) - (u : ℝ)) * (∫ x in B, x ∂ν)) ∂P = 0 := by
      intro u hut A hA
      have hA_amb : MeasurableSet A :=
        PrmFiniteCompensatedCondExpHelpers.natMeasSpace_le N u A hA
      let Iu : Set ℝ := Set.Ioc (u : ℝ) (t : ℝ)
      let Wu : Set (ℝ × ℝ) := Iu ×ˢ B
      have hWu_meas : MeasurableSet Wu := measurableSet_Ioc.prod hB
      have hWu_sub : Wu ⊆ W := Set.prod_mono
        (Set.Ioc_subset_Ioc_left (NNReal.coe_nonneg u)) le_rfl
      let Xu : Ω → ℝ := fun ω => ∫ z in Wu, z.2 ∂(N.N ω)
      let Xm_u : ℕ → Ω → ℝ := fun m ω =>
        ∑ k ∈ PrmFiniteCompensatedCondExpHelpers.dyadIdx m,
          PrmFiniteCompensatedCondExpHelpers.dyadVal m k *
            (N.N ω (Iu ×ˢ PrmFiniteCompensatedCondExpHelpers.dyadCell B m k)).toReal
      have hXm_u_meas : ∀ m : ℕ, Measurable (Xm_u m) := fun m =>
        Finset.measurable_sum (PrmFiniteCompensatedCondExpHelpers.dyadIdx m) fun k _ =>
          measurable_const.mul
            (ENNReal.measurable_toReal.comp
              (N.measurable_eval (measurableSet_Ioc.prod
                (PrmFiniteCompensatedCondExpHelpers.dyadCell_measurableSet hB m k))))
      have hXm_u_int_A : ∀ m : ℕ,
          ∫ ω in A, Xm_u m ω ∂P =
            P.real A * (((t : ℝ) - (u : ℝ)) *
              ∫ x in B, PrmFiniteCompensatedCondExpHelpers.dyadApprox B m x ∂ν) := by
        intro m
        have hterm_int : ∀ k ∈ PrmFiniteCompensatedCondExpHelpers.dyadIdx m,
            Integrable (fun ω => PrmFiniteCompensatedCondExpHelpers.dyadVal m k *
              (N.N ω (Iu ×ˢ PrmFiniteCompensatedCondExpHelpers.dyadCell B m k)).toReal)
              (P.restrict A) := fun k _ => by
          have hck := PrmFiniteCompensatedCondExpHelpers.dyadCell_measurableSet hB m k
          have hck_fin : ν (PrmFiniteCompensatedCondExpHelpers.dyadCell B m k) < ⊤ :=
            lt_of_le_of_lt (measure_mono Set.inter_subset_left) hfinite
          exact ((PrmFiniteCompensatedCondExpHelpers.prm_count_integrable N
            (measurableSet_Ioc.prod hck)
            (PrmFiniteCompensatedCondExpHelpers.referenceIntensity_Ioc_prod_ne_top ν
              (NNReal.coe_nonneg u) hck_fin)).const_mul _).integrableOn
        have hterm_eq : ∀ k ∈ PrmFiniteCompensatedCondExpHelpers.dyadIdx m,
            ∫ ω in A, PrmFiniteCompensatedCondExpHelpers.dyadVal m k *
              (N.N ω (Iu ×ˢ PrmFiniteCompensatedCondExpHelpers.dyadCell B m k)).toReal ∂P =
              P.real A * (((t : ℝ) - (u : ℝ)) *
                (PrmFiniteCompensatedCondExpHelpers.dyadVal m k *
                  (ν (PrmFiniteCompensatedCondExpHelpers.dyadCell B m k)).toReal)) := by
          intro k _
          have hck := PrmFiniteCompensatedCondExpHelpers.dyadCell_measurableSet hB m k
          have hck_fin : ν (PrmFiniteCompensatedCondExpHelpers.dyadCell B m k) < ⊤ :=
            lt_of_le_of_lt (measure_mono Set.inter_subset_left) hfinite
          rw [integral_const_mul,
            PrmFiniteCompensatedCondExpHelpers.setIntegral_future_count_eq N hut hck hck_fin hA]
          ring
        rw [integral_finset_sum _ hterm_int, Finset.sum_congr rfl hterm_eq, ← Finset.mul_sum,
          ← Finset.mul_sum]
        congr 2
        haveI : IsFiniteMeasure (ν.restrict B) :=
          ⟨by rw [Measure.restrict_apply_univ]; exact hfinite⟩
        have hind_int : ∀ k ∈ PrmFiniteCompensatedCondExpHelpers.dyadIdx m,
            Integrable ((PrmFiniteCompensatedCondExpHelpers.dyadCell B m k).indicator
              (fun _ => PrmFiniteCompensatedCondExpHelpers.dyadVal m k)) (ν.restrict B) := fun k _ =>
          (integrable_const _).indicator
            (PrmFiniteCompensatedCondExpHelpers.dyadCell_measurableSet hB m k)
        change ∑ k ∈ PrmFiniteCompensatedCondExpHelpers.dyadIdx m,
            PrmFiniteCompensatedCondExpHelpers.dyadVal m k *
              (ν (PrmFiniteCompensatedCondExpHelpers.dyadCell B m k)).toReal =
          ∫ x in B, (∑ k ∈ PrmFiniteCompensatedCondExpHelpers.dyadIdx m,
            (PrmFiniteCompensatedCondExpHelpers.dyadCell B m k).indicator
              (fun _ => PrmFiniteCompensatedCondExpHelpers.dyadVal m k) x) ∂ν
        rw [integral_finset_sum _ hind_int]
        refine Finset.sum_congr rfl fun k _ => ?_
        have hkm := PrmFiniteCompensatedCondExpHelpers.dyadCell_measurableSet hB m k
        rw [integral_indicator_const _ hkm, Measure.real, Measure.restrict_apply hkm,
          Set.inter_eq_left.mpr (show PrmFiniteCompensatedCondExpHelpers.dyadCell B m k ⊆ B from Set.inter_subset_left),
          smul_eq_mul, mul_comm]
      have hXm_u_on_G : ∀ ω ∈ G,
          (∀ m : ℕ, ‖Xm_u m ω‖ ≤ Z ω + (N.N ω W).toReal) ∧
            Tendsto (fun m => Xm_u m ω) atTop (𝓝 (Xu ω)) := by
        intro ω hω
        obtain ⟨nW, R₀, hnW, hae_z⟩ := hG_compact ω hω
        haveI : IsFiniteMeasure ((N.N ω).restrict W) :=
          ⟨by rw [Measure.restrict_apply_univ, hnW]; exact ENNReal.natCast_ne_top nW |>.lt_top⟩
        haveI : IsFiniteMeasure ((N.N ω).restrict Wu) :=
          ⟨by
            rw [Measure.restrict_apply_univ]
            exact lt_of_le_of_lt (measure_mono hWu_sub) (by rw [hnW]; exact ENNReal.natCast_ne_top nW |>.lt_top)⟩
        have hae_zu : ∀ᵐ z ∂((N.N ω).restrict Wu), z.2 ∈ B ∧ |z.2| ≤ (R₀ : ℝ) :=
          ae_mono (Measure.restrict_mono hWu_sub le_rfl) hae_z
        have hXm_eq : ∀ m : ℕ,
            Xm_u m ω = ∫ z in Wu, PrmFiniteCompensatedCondExpHelpers.dyadApprox B m z.2 ∂(N.N ω) := by
          intro m
          have hind_int : ∀ k ∈ PrmFiniteCompensatedCondExpHelpers.dyadIdx m,
              Integrable (fun z : ℝ × ℝ =>
                (PrmFiniteCompensatedCondExpHelpers.dyadCell B m k).indicator
                  (fun _ => PrmFiniteCompensatedCondExpHelpers.dyadVal m k) z.2)
                ((N.N ω).restrict Wu) := fun k _ => by
            have heq : (fun z : ℝ × ℝ =>
                (PrmFiniteCompensatedCondExpHelpers.dyadCell B m k).indicator
                  (fun _ => PrmFiniteCompensatedCondExpHelpers.dyadVal m k) z.2) =
                (Prod.snd ⁻¹' PrmFiniteCompensatedCondExpHelpers.dyadCell B m k).indicator
                  (fun _ => PrmFiniteCompensatedCondExpHelpers.dyadVal m k) := by
              funext z; by_cases hz : z.2 ∈ PrmFiniteCompensatedCondExpHelpers.dyadCell B m k <;> simp [hz]
            rw [heq]
            exact (integrable_const _).indicator
              ((PrmFiniteCompensatedCondExpHelpers.dyadCell_measurableSet hB m k).preimage measurable_snd)
          change ∑ k ∈ PrmFiniteCompensatedCondExpHelpers.dyadIdx m,
              PrmFiniteCompensatedCondExpHelpers.dyadVal m k *
                (N.N ω (Iu ×ˢ PrmFiniteCompensatedCondExpHelpers.dyadCell B m k)).toReal =
            ∫ z in Wu, (∑ k ∈ PrmFiniteCompensatedCondExpHelpers.dyadIdx m,
              (PrmFiniteCompensatedCondExpHelpers.dyadCell B m k).indicator
                (fun _ => PrmFiniteCompensatedCondExpHelpers.dyadVal m k) z.2) ∂(N.N ω)
          rw [integral_finset_sum _ hind_int]
          refine Finset.sum_congr rfl fun k _ => ?_
          have hkm : MeasurableSet ((Prod.snd : ℝ × ℝ → ℝ) ⁻¹' PrmFiniteCompensatedCondExpHelpers.dyadCell B m k) :=
            (PrmFiniteCompensatedCondExpHelpers.dyadCell_measurableSet hB m k).preimage measurable_snd
          have heq : (fun z : ℝ × ℝ =>
              (PrmFiniteCompensatedCondExpHelpers.dyadCell B m k).indicator
                (fun _ => PrmFiniteCompensatedCondExpHelpers.dyadVal m k) z.2) =
              (Prod.snd ⁻¹' PrmFiniteCompensatedCondExpHelpers.dyadCell B m k).indicator
                (fun _ => PrmFiniteCompensatedCondExpHelpers.dyadVal m k) := by
            funext z; by_cases hz : z.2 ∈ PrmFiniteCompensatedCondExpHelpers.dyadCell B m k <;> simp [hz]
          rw [heq, integral_indicator_const _ hkm, Measure.real, Measure.restrict_apply hkm]
          have hinter : (Prod.snd ⁻¹' PrmFiniteCompensatedCondExpHelpers.dyadCell B m k) ∩ Wu =
              Iu ×ˢ PrmFiniteCompensatedCondExpHelpers.dyadCell B m k := by
            ext z; simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_prod, Wu]
            exact ⟨fun h => ⟨h.2.1, h.1⟩, fun h => ⟨h.2, h.1, h.2.1⟩⟩
          rw [hinter, smul_eq_mul, mul_comm]
        have habs_int_W : Integrable (fun z : ℝ × ℝ => |z.2|) ((N.N ω).restrict W) :=
          Integrable.mono' (integrable_const (R₀ : ℝ))
            (continuous_abs.measurable.comp measurable_snd).aestronglyMeasurable
            (hae_z.mono fun z ⟨_, hz⟩ => by simpa [Real.norm_of_nonneg (abs_nonneg _)] using hz)
        have hdom_bd : ∀ m : ℕ, ‖Xm_u m ω‖ ≤ Z ω + (N.N ω W).toReal := fun m => by
          rw [hXm_eq m, Real.norm_eq_abs]
          have h1 : |∫ z in Wu, PrmFiniteCompensatedCondExpHelpers.dyadApprox B m z.2 ∂(N.N ω)| ≤
              ∫ z in Wu, |PrmFiniteCompensatedCondExpHelpers.dyadApprox B m z.2| ∂(N.N ω) :=
            abs_integral_le_integral_abs
          have h2 : ∫ z in Wu, |PrmFiniteCompensatedCondExpHelpers.dyadApprox B m z.2| ∂(N.N ω) ≤
              ∫ z in Wu, (|z.2| + 1) ∂(N.N ω) := by
            have hint_u : Integrable (fun z : ℝ × ℝ => |z.2| + 1) ((N.N ω).restrict Wu) :=
              (MeasureTheory.IntegrableOn.mono_set habs_int_W hWu_sub).add (integrable_const 1)
            have hint_d : Integrable (fun z : ℝ × ℝ =>
                |PrmFiniteCompensatedCondExpHelpers.dyadApprox B m z.2|) ((N.N ω).restrict Wu) :=
              Integrable.mono' hint_u
                (continuous_abs.measurable.comp
                  ((PrmFiniteCompensatedCondExpHelpers.dyadApprox_measurable hB m).comp measurable_snd)).aestronglyMeasurable
                (Filter.Eventually.of_forall fun z => by
                  rw [Real.norm_of_nonneg (abs_nonneg _)]
                  exact PrmFiniteCompensatedCondExpHelpers.abs_dyadApprox_le B m z.2)
            exact integral_mono hint_d hint_u fun z =>
              PrmFiniteCompensatedCondExpHelpers.abs_dyadApprox_le B m z.2
          have h3 : ∫ z in Wu, (|z.2| + 1) ∂(N.N ω) ≤ ∫ z in W, (|z.2| + 1) ∂(N.N ω) :=
            setIntegral_mono_set (habs_int_W.add (integrable_const 1))
              (Filter.Eventually.of_forall fun _ => by positivity)
              (Filter.Eventually.of_forall hWu_sub)
          have h4 : ∫ z in W, (|z.2| + 1) ∂(N.N ω) = Z ω + (N.N ω W).toReal := by
            rw [integral_add habs_int_W (integrable_const 1)]
            simp [Z, Measure.real]
          linarith
        refine ⟨hdom_bd, ?_⟩
        simp_rw [hXm_eq]
        refine MeasureTheory.tendsto_integral_of_dominated_convergence
          (fun _ => (R₀ : ℝ) + 1)
          (fun m => ((PrmFiniteCompensatedCondExpHelpers.dyadApprox_measurable hB m).comp measurable_snd).aestronglyMeasurable)
          (integrable_const ((R₀ : ℝ) + 1))
          (fun m => ?_) ?_
        · filter_upwards [hae_zu] with z ⟨_, hzbd⟩
          rw [Real.norm_eq_abs]
          exact (PrmFiniteCompensatedCondExpHelpers.abs_dyadApprox_le B m z.2).trans (by linarith)
        · filter_upwards [hae_zu] with z ⟨hzB, hzbd⟩
          rw [Metric.tendsto_atTop]
          intro ε hε
          obtain ⟨N₀, hN₀⟩ := exists_nat_gt (max (R₀ : ℝ) (1 / ε))
          refine ⟨N₀ + 1, fun m hm => ?_⟩
          have hm_gt_R : (R₀ : ℝ) < (m : ℝ) :=
            lt_of_le_of_lt (le_max_left _ _) (lt_of_lt_of_le hN₀ (by exact_mod_cast (Nat.le_succ N₀).trans hm))
          have hlo : -(m : ℝ) ≤ z.2 := by
            have := (abs_le.mp hzbd).1; linarith
          have hhi : z.2 < (m : ℝ) := lt_of_le_of_lt (abs_le.mp hzbd).2 hm_gt_R
          have hdist : |PrmFiniteCompensatedCondExpHelpers.dyadApprox B m z.2 - z.2| ≤ 1 / (2 : ℝ) ^ m :=
            PrmFiniteCompensatedCondExpHelpers.dyadApprox_sub_le hzB hlo hhi
          have hlt_eps : 1 / (2 : ℝ) ^ m < ε := by
            have hm_gt_inv : 1 / ε < (m : ℝ) :=
              lt_of_le_of_lt (le_max_right _ _) (lt_of_lt_of_le hN₀ (by exact_mod_cast (Nat.le_succ N₀).trans hm))
            have hmlt2 : (m : ℝ) < (2 : ℝ) ^ m := by exact_mod_cast Nat.lt_two_pow_self
            have h1 : 1 / ε < (2 : ℝ) ^ m := lt_trans hm_gt_inv hmlt2
            rw [div_lt_iff₀ hε] at h1
            rw [div_lt_iff₀ (by positivity)]
            linarith
          exact lt_of_le_of_lt (by simpa [Real.dist_eq] using hdist) hlt_eps
      have hLHS_tendsto : Tendsto (fun m => ∫ ω in A, Xm_u m ω ∂P) atTop (𝓝 (∫ ω in A, Xu ω ∂P)) := by
        refine MeasureTheory.tendsto_integral_of_dominated_convergence
          (fun ω => Z ω + (N.N ω W).toReal)
          (fun m => (hXm_u_meas m).aestronglyMeasurable)
          hDom_int.integrableOn
          (fun m => ae_restrict_of_ae (hae_G.mono fun ω hω => (hXm_u_on_G ω hω).1 m))
          (ae_restrict_of_ae (hae_G.mono fun ω hω => (hXm_u_on_G ω hω).2))
      have hν_tendsto : Tendsto (fun m => ∫ x in B, PrmFiniteCompensatedCondExpHelpers.dyadApprox B m x ∂ν)
          atTop (𝓝 (∫ x in B, x ∂ν)) := by
        haveI : IsFiniteMeasure (ν.restrict B) :=
          ⟨by rw [Measure.restrict_apply_univ]; exact hfinite⟩
        refine MeasureTheory.tendsto_integral_of_dominated_convergence
          (fun x => |x| + 1)
          (fun m => (PrmFiniteCompensatedCondExpHelpers.dyadApprox_measurable hB m).aestronglyMeasurable)
          (hfirst.abs.add (integrable_const 1))
          (fun m => Filter.Eventually.of_forall fun x => by
            rw [Real.norm_eq_abs]
            exact PrmFiniteCompensatedCondExpHelpers.abs_dyadApprox_le B m x)
          ?_
        filter_upwards [ae_restrict_mem hB] with x hxB
        rw [Metric.tendsto_atTop]
        intro ε hε
        obtain ⟨N₀, hN₀⟩ := exists_nat_gt (max |x| (1 / ε))
        refine ⟨N₀ + 1, fun m hm => ?_⟩
        have hm_gt_x : |x| < (m : ℝ) :=
          lt_of_le_of_lt (le_max_left _ _) (lt_of_lt_of_le hN₀ (by exact_mod_cast (Nat.le_succ N₀).trans hm))
        have hlo : -(m : ℝ) ≤ x := by have := (abs_le.mp hm_gt_x.le).1; linarith
        have hhi : x < (m : ℝ) := lt_of_le_of_lt (le_abs_self x) hm_gt_x
        have hdist : |PrmFiniteCompensatedCondExpHelpers.dyadApprox B m x - x| ≤ 1 / (2 : ℝ) ^ m :=
          PrmFiniteCompensatedCondExpHelpers.dyadApprox_sub_le hxB hlo hhi
        have hlt_eps : 1 / (2 : ℝ) ^ m < ε := by
          have hm_gt_inv : 1 / ε < (m : ℝ) :=
            lt_of_le_of_lt (le_max_right _ _) (lt_of_lt_of_le hN₀ (by exact_mod_cast (Nat.le_succ N₀).trans hm))
          have hmlt2 : (m : ℝ) < (2 : ℝ) ^ m := by exact_mod_cast Nat.lt_two_pow_self
          have h1 : 1 / ε < (2 : ℝ) ^ m := lt_trans hm_gt_inv hmlt2
          rw [div_lt_iff₀ hε] at h1
          rw [div_lt_iff₀ (by positivity)]
          linarith
        exact lt_of_le_of_lt (by simpa [Real.dist_eq] using hdist) hlt_eps
      have hRHS_tendsto : Tendsto (fun m => ∫ ω in A, Xm_u m ω ∂P) atTop
          (𝓝 (P.real A * (((t : ℝ) - (u : ℝ)) * ∫ x in B, x ∂ν))) := by
        simp_rw [hXm_u_int_A]
        exact (hν_tendsto.const_mul ((t : ℝ) - (u : ℝ))).const_mul (P.real A)
      have hXu_int_A : ∫ ω in A, Xu ω ∂P = P.real A * (((t : ℝ) - (u : ℝ)) * ∫ x in B, x ∂ν) :=
        tendsto_nhds_unique hLHS_tendsto hRHS_tendsto
      have hXu_integrable : Integrable Xu P := by
        have hXu_meas : Measurable Xu :=
          Kyprianou.Ch02.prmMarkedIntegralMeasurableAmbientV1 P ν N Wu hWu_meas
        refine Integrable.mono' hZ_int hXu_meas.aestronglyMeasurable ?_
        filter_upwards [hae_G] with ω hω
        obtain ⟨nW, R₀, hnW, hae_z⟩ := hG_compact ω hω
        haveI : IsFiniteMeasure ((N.N ω).restrict W) :=
          ⟨by rw [Measure.restrict_apply_univ, hnW]; exact ENNReal.natCast_ne_top nW |>.lt_top⟩
        have habs_int_W : Integrable (fun z : ℝ × ℝ => |z.2|) ((N.N ω).restrict W) :=
          Integrable.mono' (integrable_const (R₀ : ℝ))
            (continuous_abs.measurable.comp measurable_snd).aestronglyMeasurable
            (hae_z.mono fun z ⟨_, hz⟩ => by simpa [Real.norm_of_nonneg (abs_nonneg _)] using hz)
        rw [Real.norm_eq_abs]
        exact (abs_integral_le_integral_abs).trans
          (setIntegral_mono_set habs_int_W (Filter.Eventually.of_forall fun _ => abs_nonneg _)
            (Filter.Eventually.of_forall hWu_sub))
      rw [integral_sub hXu_integrable.integrableOn (integrable_const _), hXu_int_A,
        setIntegral_const, smul_eq_mul, sub_self]
    -- Step B: For any `E ∈ ℱ s`, send `u_n ↓ s` to prove `∫_E Δ(s, t) = 0`, hence `∫_E M s = ∫_E M t`
    intro E hE_Fs _
    have hE_amb : MeasurableSet E := ℱ.le s E hE_Fs
    have hts_pos : (0 : ℝ) < (t : ℝ) - (s : ℝ) := sub_pos.mpr (by exact_mod_cast hst_lt)
    let u : ℕ → ℝ≥0 := fun n =>
      ⟨(s : ℝ) + ((t : ℝ) - (s : ℝ)) / ((n : ℝ) + 2), by positivity⟩
    have hsu : ∀ n : ℕ, s < u n := fun n => by
      change (s : ℝ) < (s : ℝ) + ((t : ℝ) - (s : ℝ)) / ((n : ℝ) + 2)
      have : (0 : ℝ) < ((t : ℝ) - (s : ℝ)) / ((n : ℝ) + 2) := by positivity
      linarith
    have hut : ∀ n : ℕ, u n < t := fun n => by
      change (s : ℝ) + ((t : ℝ) - (s : ℝ)) / ((n : ℝ) + 2) < (t : ℝ)
      have hdiv : ((t : ℝ) - (s : ℝ)) / ((n : ℝ) + 2) < (t : ℝ) - (s : ℝ) :=
        div_lt_self hts_pos (by linarith [Nat.cast_nonneg (α := ℝ) n])
      linarith
    have hu_anti : Antitone u := fun m n hmn => by
      change (s : ℝ) + ((t : ℝ) - (s : ℝ)) / ((n : ℝ) + 2) ≤
        (s : ℝ) + ((t : ℝ) - (s : ℝ)) / ((m : ℝ) + 2)
      gcongr
    have hu_tendsto : Tendsto (fun n => (u n : ℝ)) atTop (𝓝 (s : ℝ)) := by
      have hzero : Tendsto (fun n : ℕ => ((t : ℝ) - (s : ℝ)) / ((n : ℝ) + 2)) atTop (𝓝 0) := by
        simpa [div_eq_mul_inv] using
          (tendsto_const_nhds (x := (t : ℝ) - (s : ℝ))).mul
            (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds))
      change Tendsto (fun n : ℕ => (s : ℝ) + ((t : ℝ) - (s : ℝ)) / ((n : ℝ) + 2)) atTop (𝓝 (s : ℝ))
      simpa using (tendsto_const_nhds (x := (s : ℝ))).add hzero
    let Δu : ℕ → Ω → ℝ := fun n ω =>
      (∫ z in (Set.Ioc (u n : ℝ) (t : ℝ) ×ˢ B), z.2 ∂(N.N ω)) -
        ((t : ℝ) - (u n : ℝ)) * (∫ x in B, x ∂ν)
    let Δs : Ω → ℝ := fun ω =>
      (∫ z in (Set.Ioc (s : ℝ) (t : ℝ) ×ˢ B), z.2 ∂(N.N ω)) -
        ((t : ℝ) - (s : ℝ)) * (∫ x in B, x ∂ν)
    have hΔu_int_zero : ∀ n : ℕ, ∫ ω in E, Δu n ω ∂P = 0 := fun n => by
      have hle := PrmFiniteCompensatedCondExpHelpers.filtration_le_completed_of_lt N hℱ (hsu n)
      rcases (hle E hE_Fs).2 with ⟨A, hA_nat, hEA⟩
      have hae_set : E =ᵐ[P] A := measure_symmDiff_eq_zero_iff.mp hEA
      rw [setIntegral_congr_set hae_set]
      exact hfuture_zero (u n) (hut n) A hA_nat
    have hΔu_meas : ∀ n : ℕ, Measurable (Δu n) := fun n =>
      (Kyprianou.Ch02.prmMarkedIntegralMeasurableAmbientV1 P ν N
        (Set.Ioc (u n : ℝ) (t : ℝ) ×ˢ B) (measurableSet_Ioc.prod hB)).sub measurable_const
    have hΔu_on_G : ∀ ω ∈ G,
        (∀ n : ℕ, ‖Δu n ω‖ ≤ Z ω + (t : ℝ) * |∫ x in B, x ∂ν|) ∧
          Tendsto (fun n => Δu n ω) atTop (𝓝 (Δs ω)) := by
      intro ω hω
      obtain ⟨nW, R₀, hnW, hae_z⟩ := hG_compact ω hω
      haveI : IsFiniteMeasure ((N.N ω).restrict W) :=
        ⟨by rw [Measure.restrict_apply_univ, hnW]; exact ENNReal.natCast_ne_top nW |>.lt_top⟩
      have habs_int_W : Integrable (fun z : ℝ × ℝ => |z.2|) ((N.N ω).restrict W) :=
        Integrable.mono' (integrable_const (R₀ : ℝ))
          (continuous_abs.measurable.comp measurable_snd).aestronglyMeasurable
          (hae_z.mono fun z ⟨_, hz⟩ => by simpa [Real.norm_of_nonneg (abs_nonneg _)] using hz)
      have hz_int_W : Integrable (fun z : ℝ × ℝ => z.2) ((N.N ω).restrict W) :=
        Integrable.mono' (integrable_const (R₀ : ℝ))
          measurable_snd.aestronglyMeasurable
          (hae_z.mono fun z ⟨_, hz⟩ => by simpa [Real.norm_eq_abs] using hz)
      have hbound : ∀ n : ℕ, ‖Δu n ω‖ ≤ Z ω + (t : ℝ) * |∫ x in B, x ∂ν| := fun n => by
        rw [Real.norm_eq_abs]
        have hsub_u : Set.Ioc (u n : ℝ) (t : ℝ) ×ˢ B ⊆ W :=
          Set.prod_mono (Set.Ioc_subset_Ioc_left (NNReal.coe_nonneg (u n))) le_rfl
        have h1 : |∫ z in (Set.Ioc (u n : ℝ) (t : ℝ) ×ˢ B), z.2 ∂(N.N ω)| ≤ Z ω :=
          (abs_integral_le_integral_abs).trans
            (setIntegral_mono_set habs_int_W (Filter.Eventually.of_forall fun _ => abs_nonneg _)
              (Filter.Eventually.of_forall hsub_u))
        have h2 : |((t : ℝ) - (u n : ℝ)) * (∫ x in B, x ∂ν)| ≤ (t : ℝ) * |∫ x in B, x ∂ν| := by
          rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast (hut n).le))]
          exact mul_le_mul_of_nonneg_right (by linarith [NNReal.coe_nonneg (u n)]) (abs_nonneg _)
        exact (abs_sub _ _).trans (add_le_add h1 h2)
      refine ⟨hbound, ?_⟩
      -- Convergence of the integral part via `tendsto_measure_iInter_atTop` on `(s, u_n] × B`
      let Sgap : ℕ → Set (ℝ × ℝ) := fun n => Set.Ioc (s : ℝ) (u n : ℝ) ×ˢ B
      have hSgap_meas : ∀ n : ℕ, MeasurableSet (Sgap n) := fun n => measurableSet_Ioc.prod hB
      have hSgap_sub : ∀ n : ℕ, Sgap n ⊆ W := fun n =>
        Set.prod_mono (Set.Ioc_subset_Ioc (NNReal.coe_nonneg s) (by exact_mod_cast (hut n).le)) le_rfl
      have hSgap_anti : Antitone Sgap := fun m n hmn =>
        Set.prod_mono (Set.Ioc_subset_Ioc_right (by exact_mod_cast hu_anti hmn)) le_rfl
      have hSgap_iInter : (⋂ n : ℕ, Sgap n) = ∅ := by
        ext z
        simp only [Set.mem_iInter, Set.mem_empty_iff_false, iff_false, not_forall]
        by_cases hzs : (s : ℝ) < z.1
        · have hev : ∀ᶠ n in atTop, (u n : ℝ) < z.1 := hu_tendsto.eventually (gt_mem_nhds hzs)
          obtain ⟨n, hn⟩ := hev.exists
          exact ⟨n, fun hz => not_lt_of_ge hz.1.2 hn⟩
        · exact ⟨0, fun hz => hzs hz.1.1⟩
      have hgap_meas_tendsto : Tendsto (fun n => N.N ω (Sgap n)) atTop (𝓝 0) := by
        have ht := MeasureTheory.tendsto_measure_iInter_atTop
          (fun n => (hSgap_meas n).nullMeasurableSet) hSgap_anti
          ⟨0, ne_top_of_le_ne_top (show N.N ω W ≠ ⊤ by simp [hnW]) (measure_mono (hSgap_sub 0))⟩
        simpa [hSgap_iInter, Function.comp_def] using ht
      have hgap_toReal : Tendsto (fun n => (N.N ω (Sgap n)).toReal) atTop (𝓝 0) := by
        simpa [Function.comp_def] using (ENNReal.continuousAt_toReal (by simp)).tendsto.comp hgap_meas_tendsto
      have hgap_int_zero : Tendsto (fun n => ∫ z in Sgap n, z.2 ∂(N.N ω)) atTop (𝓝 0) := by
        refine squeeze_zero_norm (fun n => ?_) (by simpa using hgap_toReal.const_mul (R₀ : ℝ))
        rw [Real.norm_eq_abs]
        have hae_gap : ∀ᵐ z ∂((N.N ω).restrict (Sgap n)), |z.2| ≤ (R₀ : ℝ) :=
          Filter.Eventually.mono (ae_mono (Measure.restrict_mono (hSgap_sub n) le_rfl) hae_z)
            fun _ h => h.2
        haveI : IsFiniteMeasure ((N.N ω).restrict (Sgap n)) :=
          ⟨by
            rw [Measure.restrict_apply_univ]
            exact lt_of_le_of_lt (measure_mono (hSgap_sub n)) (by rw [hnW]; exact ENNReal.natCast_ne_top nW |>.lt_top)⟩
        have hle1 : |∫ z in Sgap n, z.2 ∂(N.N ω)| ≤ ∫ z in Sgap n, |z.2| ∂(N.N ω) :=
          abs_integral_le_integral_abs
        have hle2 : ∫ z in Sgap n, |z.2| ∂(N.N ω) ≤ ∫ _ in Sgap n, (R₀ : ℝ) ∂(N.N ω) :=
          integral_mono_ae (MeasureTheory.IntegrableOn.mono_set habs_int_W (hSgap_sub n))
            (integrable_const (R₀ : ℝ)) hae_gap
        have hconst : ∫ _ in Sgap n, (R₀ : ℝ) ∂(N.N ω) = (R₀ : ℝ) * (N.N ω (Sgap n)).toReal := by
          rw [setIntegral_const, Measure.real, smul_eq_mul, mul_comm]
        linarith
      have hsplit : ∀ n : ℕ,
          ∫ z in (Set.Ioc (u n : ℝ) (t : ℝ) ×ˢ B), z.2 ∂(N.N ω) =
            (∫ z in (Set.Ioc (s : ℝ) (t : ℝ) ×ˢ B), z.2 ∂(N.N ω)) -
              ∫ z in Sgap n, z.2 ∂(N.N ω) := fun n => by
        have hunion : Sgap n ∪ (Set.Ioc (u n : ℝ) (t : ℝ) ×ˢ B) = Set.Ioc (s : ℝ) (t : ℝ) ×ˢ B := by
          rw [← Set.union_prod, Set.Ioc_union_Ioc_eq_Ioc (by exact_mod_cast (hsu n).le)
            (by exact_mod_cast (hut n).le)]
        have hdisj : Disjoint (Sgap n) (Set.Ioc (u n : ℝ) (t : ℝ) ×ˢ B) := by
          rw [Set.disjoint_left]
          intro z hz1 hz2
          exact not_lt_of_ge hz1.1.2 hz2.1.1
        have hsub_u : Set.Ioc (u n : ℝ) (t : ℝ) ×ˢ B ⊆ W :=
          Set.prod_mono (Set.Ioc_subset_Ioc_left (NNReal.coe_nonneg (u n))) le_rfl
        have hadd := setIntegral_union hdisj (measurableSet_Ioc.prod hB)
          (MeasureTheory.IntegrableOn.mono_set hz_int_W (hSgap_sub n))
          (MeasureTheory.IntegrableOn.mono_set hz_int_W hsub_u)
        rw [hunion] at hadd
        linarith
      have hint_tendsto :
          Tendsto (fun n => ∫ z in (Set.Ioc (u n : ℝ) (t : ℝ) ×ˢ B), z.2 ∂(N.N ω)) atTop
            (𝓝 (∫ z in (Set.Ioc (s : ℝ) (t : ℝ) ×ˢ B), z.2 ∂(N.N ω))) := by
        simp_rw [hsplit]
        simpa using tendsto_const_nhds.sub hgap_int_zero
      have hdrift_tendsto :
          Tendsto (fun n => ((t : ℝ) - (u n : ℝ)) * (∫ x in B, x ∂ν)) atTop
            (𝓝 (((t : ℝ) - (s : ℝ)) * (∫ x in B, x ∂ν))) :=
        (tendsto_const_nhds.sub hu_tendsto).mul_const _
      exact hint_tendsto.sub hdrift_tendsto
    have hΔs_int_E : ∫ ω in E, Δs ω ∂P = 0 := by
      have htend : Tendsto (fun n => ∫ ω in E, Δu n ω ∂P) atTop (𝓝 (∫ ω in E, Δs ω ∂P)) := by
        refine MeasureTheory.tendsto_integral_of_dominated_convergence
          (fun ω => Z ω + (t : ℝ) * |∫ x in B, x ∂ν|)
          (fun n => (hΔu_meas n).aestronglyMeasurable)
          (hZ_int.add (integrable_const _)).integrableOn
          (fun n => ae_restrict_of_ae (hae_G.mono fun ω hω => (hΔu_on_G ω hω).1 n))
          (ae_restrict_of_ae (hae_G.mono fun ω hω => (hΔu_on_G ω hω).2))
      simp_rw [hΔu_int_zero] at htend
      exact tendsto_nhds_unique htend tendsto_const_nhds
    -- Step C: `M t =ᵐ[P] M s + Δs`, so `∫_E M s = ∫_E M t`
    have hMt_ae : M t =ᵐ[P] (fun ω => M s ω + Δs ω) := by
      filter_upwards [hae_G] with ω hω
      obtain ⟨nW, R₀, hnW, hae_z⟩ := hG_compact ω hω
      haveI : IsFiniteMeasure ((N.N ω).restrict W) :=
        ⟨by rw [Measure.restrict_apply_univ, hnW]; exact ENNReal.natCast_ne_top nW |>.lt_top⟩
      have hz_int_W : Integrable (fun z : ℝ × ℝ => z.2) ((N.N ω).restrict W) :=
        Integrable.mono' (integrable_const (R₀ : ℝ))
          measurable_snd.aestronglyMeasurable
          (hae_z.mono fun z ⟨_, hz⟩ => by simpa [Real.norm_eq_abs] using hz)
      have hunion : (Set.Ioc (0 : ℝ) (s : ℝ) ×ˢ B) ∪ (Set.Ioc (s : ℝ) (t : ℝ) ×ˢ B) = W := by
        rw [← Set.union_prod, Set.Ioc_union_Ioc_eq_Ioc (NNReal.coe_nonneg s)
          (by exact_mod_cast hst_lt.le)]
      have hdisj : Disjoint (Set.Ioc (0 : ℝ) (s : ℝ) ×ˢ B) (Set.Ioc (s : ℝ) (t : ℝ) ×ˢ B) := by
        rw [Set.disjoint_left]
        intro z hz1 hz2
        exact not_lt_of_ge hz1.1.2 hz2.1.1
      have hsub1 : Set.Ioc (0 : ℝ) (s : ℝ) ×ˢ B ⊆ W :=
        Set.prod_mono (Set.Ioc_subset_Ioc_right (by exact_mod_cast hst_lt.le)) le_rfl
      have hsub2 : Set.Ioc (s : ℝ) (t : ℝ) ×ˢ B ⊆ W :=
        Set.prod_mono (Set.Ioc_subset_Ioc_left (NNReal.coe_nonneg s)) le_rfl
      have hadd := setIntegral_union hdisj (measurableSet_Ioc.prod hB)
        (MeasureTheory.IntegrableOn.mono_set hz_int_W hsub1)
        (MeasureTheory.IntegrableOn.mono_set hz_int_W hsub2)
      rw [hunion] at hadd
      dsimp only [M, Δs]
      rw [show (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B) = W from rfl, hadd]
      ring
    have hΔs_int : Integrable Δs P := by
      have hsub_ae : (fun ω => M t ω - M s ω) =ᵐ[P] Δs := by
        filter_upwards [hMt_ae] with ω hω; linarith
      exact ((hM_int t).sub (hM_int s)).congr hsub_ae
    have hEq_E : ∫ ω in E, M t ω ∂P = ∫ ω in E, (M s ω + Δs ω) ∂P :=
      integral_congr_ae (ae_restrict_of_ae hMt_ae)
    rw [hEq_E, integral_add (hM_int s).integrableOn hΔs_int.integrableOn, hΔs_int_E, add_zero]

