-- Prove2me | solution 1 for Kyprianou.Ch02.finiteRegionMarkedCharFromCountCharV2
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-23T18:44:21.089803+00:00
-- url     : https://prove2.me/submissions/9f943438-8617-4fea-8525-bc6b8e15451d

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_LeanLevy_Processes_LevyProcess

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

set_option autoImplicit false

namespace FiniteRegionMarkedCharHelpers

private lemma referenceIntensity_Ioc_prod (ν : Measure ℝ) [SigmaFinite ν]
    (t : ℝ≥0) {A : Set ℝ} (_hA : MeasurableSet A) :
    LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ A) =
      ENNReal.ofReal (t : ℝ) * ν A := by
  unfold LevyStochCalc.Poisson.referenceIntensity
  rw [Measure.prod_prod, Measure.restrict_apply measurableSet_Ioc]
  have hsub : Set.Ioc (0 : ℝ) (t : ℝ) ∩ Set.Ici (0 : ℝ) = Set.Ioc (0 : ℝ) (t : ℝ) :=
    Set.inter_eq_left.mpr fun _ hx => le_of_lt hx.1
  rw [hsub, Real.volume_Ioc, sub_zero]

private lemma referenceIntensity_Ioc_prod_ne_top (ν : Measure ℝ) [SigmaFinite ν]
    (t : ℝ≥0) {A : Set ℝ} (hA : MeasurableSet A) (hAfin : ν A < ⊤) :
    LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ A) ≠ ⊤ := by
  rw [referenceIntensity_Ioc_prod ν t hA]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hAfin.ne

private lemma referenceIntensity_Ioc_prod_toReal (ν : Measure ℝ) [SigmaFinite ν]
    (t : ℝ≥0) {A : Set ℝ} (hA : MeasurableSet A) :
    (LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ A)).toReal =
      (t : ℝ) * (ν A).toReal := by
  rw [referenceIntensity_Ioc_prod ν t hA, ENNReal.toReal_mul, ENNReal.toReal_ofReal t.coe_nonneg]

private lemma poisson_count_charFun (μ : ℝ≥0) (u : ℝ) :
    ∫ (n : ℕ), Complex.exp (Complex.I * ((u * (n : ℝ) : ℝ) : ℂ)) ∂(ProbabilityTheory.poissonMeasure μ) =
      Complex.exp (((μ : ℝ) : ℂ) * (Complex.exp (Complex.I * (u : ℂ)) - 1)) := by
  rw [ProbabilityTheory.integral_poissonMeasure]
  let z : ℂ := Complex.exp (Complex.I * (u : ℂ))
  have hterm : ∀ n : ℕ,
      (Real.exp (-(μ : ℝ)) * (μ : ℝ) ^ n / (n.factorial : ℝ)) •
        Complex.exp (Complex.I * ((u * (n : ℝ) : ℝ) : ℂ)) =
      Complex.exp (-((μ : ℝ) : ℂ)) * ((((μ : ℝ) : ℂ) * z) ^ n / (n.factorial : ℂ)) := by
    intro n
    rw [Complex.real_smul]
    have hexp_n : Complex.exp (Complex.I * ((u * (n : ℝ) : ℝ) : ℂ)) = z ^ n := by
      dsimp [z]
      rw [← Complex.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [hexp_n]
    push_cast
    rw [mul_pow]
    ring
  simp_rw [hterm]
  rw [tsum_mul_left]
  have hsum : (∑' n : ℕ, (((μ : ℝ) : ℂ) * z) ^ n / (n.factorial : ℂ)) =
      Complex.exp (((μ : ℝ) : ℂ) * z) := by
    rw [Complex.exp_eq_exp_ℂ]
    exact (NormedSpace.expSeries_div_hasSum_exp (((μ : ℝ) : ℂ) * z)).tsum_eq
  rw [hsum, ← Complex.exp_add]
  congr 1
  ring

private lemma prm_count_charFun
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (t : ℝ≥0) {A : Set ℝ} (hA : MeasurableSet A) (hAfin : ν A < ⊤) (u : ℝ) :
    ∫ ω, Complex.exp (Complex.I * ((u * (N.N ω (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ A)).toReal : ℝ) : ℂ)) ∂P =
      Complex.exp ((((t : ℝ) * (ν A).toReal : ℝ) : ℂ) * (Complex.exp (Complex.I * (u : ℂ)) - 1)) := by
  let W : Set (ℝ × ℝ) := Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ A
  have hW : MeasurableSet W := measurableSet_Ioc.prod hA
  have hWfin : LevyStochCalc.Poisson.referenceIntensity ν W ≠ ⊤ :=
    referenceIntensity_Ioc_prod_ne_top ν t hA hAfin
  let μ : ℝ≥0 := (LevyStochCalc.Poisson.referenceIntensity ν W).toNNReal
  let φ : ℝ≥0∞ → ℂ := fun r => Complex.exp (Complex.I * ((u * r.toReal : ℝ) : ℂ))
  have hφ_meas : Measurable φ := by
    refine Complex.continuous_exp.measurable.comp ?_
    refine measurable_const.mul ?_
    refine Complex.continuous_ofReal.measurable.comp ?_
    exact measurable_const.mul ENNReal.measurable_toReal
  have hN_meas : Measurable (fun ω => N.N ω W) := N.measurable_eval hW
  have hcast_meas : Measurable (fun n : ℕ => (n : ℝ≥0∞)) := measurable_of_countable _
  have h1 : ∫ ω, φ (N.N ω W) ∂P = ∫ r, φ r ∂(P.map (fun ω => N.N ω W)) :=
    (integral_map hN_meas.aemeasurable hφ_meas.aestronglyMeasurable).symm
  have h2 : P.map (fun ω => N.N ω W) =
      (ProbabilityTheory.poissonMeasure μ).map (fun n : ℕ => (n : ℝ≥0∞)) :=
    N.poisson_law hW hWfin
  have h3 : ∫ r, φ r ∂((ProbabilityTheory.poissonMeasure μ).map (fun n : ℕ => (n : ℝ≥0∞))) =
      ∫ n : ℕ, φ (n : ℝ≥0∞) ∂(ProbabilityTheory.poissonMeasure μ) :=
    integral_map hcast_meas.aemeasurable hφ_meas.aestronglyMeasurable
  have hμ_coe : ((μ : ℝ) : ℂ) = (((t : ℝ) * (ν A).toReal : ℝ) : ℂ) := by
    have hEq : (μ : ℝ) = (LevyStochCalc.Poisson.referenceIntensity ν W).toReal := rfl
    rw [hEq, referenceIntensity_Ioc_prod_toReal ν t hA]
  calc ∫ ω, φ (N.N ω W) ∂P
      = ∫ n : ℕ, φ (n : ℝ≥0∞) ∂(ProbabilityTheory.poissonMeasure μ) := by rw [h1, h2, h3]
    _ = ∫ n : ℕ, Complex.exp (Complex.I * ((u * (n : ℝ) : ℝ) : ℂ)) ∂(ProbabilityTheory.poissonMeasure μ) := by
        simp only [φ, ENNReal.toReal_natCast]
    _ = Complex.exp (((μ : ℝ) : ℂ) * (Complex.exp (Complex.I * (u : ℂ)) - 1)) :=
        poisson_count_charFun μ u
    _ = Complex.exp ((((t : ℝ) * (ν A).toReal : ℝ) : ℂ) * (Complex.exp (Complex.I * (u : ℂ)) - 1)) := by
        rw [hμ_coe]

private noncomputable def dyadIdx (m : ℕ) : Finset ℤ :=
  Finset.Ico (-((m : ℤ) * (2 : ℤ) ^ m)) ((m : ℤ) * (2 : ℤ) ^ m)

private noncomputable def dyadVal (m : ℕ) (k : ℤ) : ℝ :=
  (k : ℝ) / (2 : ℝ) ^ m

private def dyadCell (B : Set ℝ) (m : ℕ) (k : ℤ) : Set ℝ :=
  B ∩ Set.Ico ((k : ℝ) / (2 : ℝ) ^ m) (((k + 1 : ℤ) : ℝ) / (2 : ℝ) ^ m)

private noncomputable def dyadApprox (B : Set ℝ) (m : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ dyadIdx m, (dyadCell B m k).indicator (fun _ => dyadVal m k) x

private lemma dyadCell_measurableSet {B : Set ℝ} (hB : MeasurableSet B) (m : ℕ) (k : ℤ) :
    MeasurableSet (dyadCell B m k) :=
  hB.inter measurableSet_Ico

private lemma dyadCell_subset (B : Set ℝ) (m : ℕ) (k : ℤ) : dyadCell B m k ⊆ B :=
  Set.inter_subset_left

private lemma dyadCell_pairwise_disjoint (B : Set ℝ) (m : ℕ) :
    Pairwise (fun k₁ k₂ : ℤ => Disjoint (dyadCell B m k₁) (dyadCell B m k₂)) := by
  intro k₁ k₂ hne
  rw [Set.disjoint_left]
  intro x hx₁ hx₂
  have hpos : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hle : ((k₁ + 1 : ℤ) : ℝ) ≤ (k₂ : ℝ) := by exact_mod_cast Int.add_one_le_iff.mpr hlt
    have hdiv : ((k₁ + 1 : ℤ) : ℝ) / (2 : ℝ) ^ m ≤ (k₂ : ℝ) / (2 : ℝ) ^ m :=
      div_le_div_of_nonneg_right hle (le_of_lt hpos)
    linarith [hx₁.2.2, hx₂.2.1]
  · have hle : ((k₂ + 1 : ℤ) : ℝ) ≤ (k₁ : ℝ) := by exact_mod_cast Int.add_one_le_iff.mpr hgt
    have hdiv : ((k₂ + 1 : ℤ) : ℝ) / (2 : ℝ) ^ m ≤ (k₁ : ℝ) / (2 : ℝ) ^ m :=
      div_le_div_of_nonneg_right hle (le_of_lt hpos)
    linarith [hx₂.2.2, hx₁.2.1]

private lemma dyadApprox_sub_le {B : Set ℝ} {m : ℕ} {x : ℝ} (hxB : x ∈ B) (hxbd : |x| < (m : ℝ)) :
    |dyadApprox B m x - x| ≤ 1 / (2 : ℝ) ^ m := by
  have hpos : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
  let k₀ : ℤ := Int.floor ((2 : ℝ) ^ m * x)
  have hk₀_le : (k₀ : ℝ) ≤ (2 : ℝ) ^ m * x := Int.floor_le _
  have hk₀_lt : (2 : ℝ) ^ m * x < (k₀ : ℝ) + 1 := Int.lt_floor_add_one _
  have hneg_lt : -((m : ℝ) * (2 : ℝ) ^ m) < (2 : ℝ) ^ m * x := by
    have h1 : -(m : ℝ) < x := (abs_lt.mp hxbd).1
    nlinarith
  have hpos_lt : (2 : ℝ) ^ m * x < (m : ℝ) * (2 : ℝ) ^ m := by
    have h2 : x < (m : ℝ) := (abs_lt.mp hxbd).2
    nlinarith
  have hk₀_mem : k₀ ∈ dyadIdx m := by
    rw [dyadIdx, Finset.mem_Ico]
    constructor
    · rw [Int.le_floor]
      push_cast
      linarith
    · have hreal : (k₀ : ℝ) < ((m : ℤ) * (2 : ℤ) ^ m : ℤ) := by
        push_cast
        linarith
      exact_mod_cast hreal
  have hx_cell : x ∈ dyadCell B m k₀ := by
    refine ⟨hxB, ?_, ?_⟩
    · rw [div_le_iff₀ hpos]; linarith
    · rw [lt_div_iff₀ hpos]; push_cast; linarith
  have hval : dyadApprox B m x = dyadVal m k₀ := by
    unfold dyadApprox
    rw [Finset.sum_eq_single k₀]
    · exact Set.indicator_of_mem hx_cell _
    · intro k _ hne
      apply Set.indicator_of_notMem
      intro hxk
      exact Set.disjoint_left.mp (dyadCell_pairwise_disjoint B m hne) hxk hx_cell
    · intro hnot; exact absurd hk₀_mem hnot
  rw [hval, dyadVal]
  have hlo : (k₀ : ℝ) / (2 : ℝ) ^ m ≤ x := hx_cell.2.1
  have hhi : x < ((k₀ + 1 : ℤ) : ℝ) / (2 : ℝ) ^ m := hx_cell.2.2
  have hdiff : ((k₀ + 1 : ℤ) : ℝ) / (2 : ℝ) ^ m - (k₀ : ℝ) / (2 : ℝ) ^ m = 1 / (2 : ℝ) ^ m := by
    push_cast; ring
  rw [abs_le]
  constructor <;> linarith

private lemma dyadApprox_tendsto {B : Set ℝ} {x : ℝ} (hxB : x ∈ B) :
    Tendsto (fun m => dyadApprox B m x) atTop (nhds x) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨M₁, hM₁⟩ := exists_nat_gt |x|
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  obtain ⟨M₂, hM₂⟩ := (ht.eventually (gt_mem_nhds hε)).exists
  rw [Filter.eventually_atTop]
  refine ⟨max M₁ M₂, fun m hm => ?_⟩
  have hm1 : M₁ ≤ m := le_trans (le_max_left _ _) hm
  have hm2 : M₂ ≤ m := le_trans (le_max_right _ _) hm
  have hxbd : |x| < (m : ℝ) := lt_of_lt_of_le hM₁ (by exact_mod_cast hm1)
  have hbound := dyadApprox_sub_le hxB hxbd
  have hpow : (1 : ℝ) / (2 : ℝ) ^ m < ε := by
    calc (1 : ℝ) / (2 : ℝ) ^ m = (1 / 2 : ℝ) ^ m := by rw [one_div_pow]
      _ ≤ (1 / 2 : ℝ) ^ M₂ := pow_le_pow_of_le_one (by norm_num) (by norm_num) hm2
      _ < ε := hM₂
  rw [Real.dist_eq]
  exact lt_of_le_of_lt hbound hpow

private lemma dyadApprox_exp_sub_one (B : Set ℝ) (m : ℕ) (ξ x : ℝ) :
    Complex.exp (Complex.I * ((ξ * dyadApprox B m x : ℝ) : ℂ)) - 1 =
      ∑ k ∈ dyadIdx m,
        (dyadCell B m k).indicator
          (fun _ => Complex.exp (Complex.I * ((ξ * dyadVal m k : ℝ) : ℂ)) - 1) x := by
  by_cases hex : ∃ k ∈ dyadIdx m, x ∈ dyadCell B m k
  · obtain ⟨k₀, hk₀_mem, hxk₀⟩ := hex
    have hval : dyadApprox B m x = dyadVal m k₀ := by
      unfold dyadApprox
      rw [Finset.sum_eq_single k₀]
      · exact Set.indicator_of_mem hxk₀ _
      · intro k _ hne
        apply Set.indicator_of_notMem
        intro hxk
        exact Set.disjoint_left.mp (dyadCell_pairwise_disjoint B m hne) hxk hxk₀
      · intro hnot; exact absurd hk₀_mem hnot
    rw [hval, Finset.sum_eq_single k₀]
    · rw [Set.indicator_of_mem hxk₀]
    · intro k _ hne
      apply Set.indicator_of_notMem
      intro hxk
      exact Set.disjoint_left.mp (dyadCell_pairwise_disjoint B m hne) hxk hxk₀
    · intro hnot; exact absurd hk₀_mem hnot
  · push Not at hex
    have hval : dyadApprox B m x = 0 := by
      unfold dyadApprox
      exact Finset.sum_eq_zero fun k hk => Set.indicator_of_notMem (hex k hk) _
    rw [hval]
    have hrhs : (∑ k ∈ dyadIdx m,
        (dyadCell B m k).indicator
          (fun _ => Complex.exp (Complex.I * ((ξ * dyadVal m k : ℝ) : ℂ)) - 1) x) = 0 :=
      Finset.sum_eq_zero fun k hk => Set.indicator_of_notMem (hex k hk) _
    rw [hrhs]
    simp

private lemma dyadApprox_measurable {B : Set ℝ} (hB : MeasurableSet B) (m : ℕ) :
    Measurable (dyadApprox B m) :=
  Finset.measurable_sum (dyadIdx m) (f := fun k x => (dyadCell B m k).indicator (fun _ => dyadVal m k) x) fun k _ =>
    measurable_const.indicator (dyadCell_measurableSet hB m k)

end FiniteRegionMarkedCharHelpers

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hfinite : ν B < ⊤)
    (_hCount : ∀ (t : ℝ≥0) (u : ℝ),
      ∫ ω, Complex.exp (Complex.I *
      ((u * (N.N ω (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B)).toReal : ℝ) : ℂ)) ∂P =
    Complex.exp ((LevyStochCalc.Poisson.referenceIntensity ν
      (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B)).toReal *
      (Complex.exp (Complex.I * (u : ℂ)) - 1))) :
    ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map
        (fun ω => ∫ z in
          (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B), z.2 ∂(N.N ω))) ξ =
      Complex.exp ((((t : ℝ) : ℂ)) *
        ∫ x in B,
          (Complex.exp (Complex.I * (((ξ * x : ℝ) : ℂ))) - 1) ∂ν) := by
  intro t ξ
  let I : Set ℝ := Set.Ioc (0 : ℝ) (t : ℝ)
  let W : Set (ℝ × ℝ) := I ×ˢ B
  have hW : MeasurableSet W := measurableSet_Ioc.prod hB
  have hWfin : LevyStochCalc.Poisson.referenceIntensity ν W ≠ ⊤ :=
    FiniteRegionMarkedCharHelpers.referenceIntensity_Ioc_prod_ne_top ν t hB hfinite
  let X : Ω → ℝ := fun ω => ∫ z in W, z.2 ∂(N.N ω)
  let Xm : ℕ → Ω → ℝ := fun m ω =>
    ∑ k ∈ FiniteRegionMarkedCharHelpers.dyadIdx m,
      FiniteRegionMarkedCharHelpers.dyadVal m k *
        (N.N ω (I ×ˢ FiniteRegionMarkedCharHelpers.dyadCell B m k)).toReal
  have hXm_meas : ∀ m : ℕ, Measurable (Xm m) := by
    intro m
    refine Finset.measurable_sum _ fun k _ => ?_
    exact measurable_const.mul
      (ENNReal.measurable_toReal.comp
        (N.measurable_eval (measurableSet_Ioc.prod
          (FiniteRegionMarkedCharHelpers.dyadCell_measurableSet hB m k))))
  -- Step 1: Exact characteristic function of Xm m for every m
  have hXm_charFun : ∀ m : ℕ,
      ∫ ω, Complex.exp (Complex.I * ((ξ * Xm m ω : ℝ) : ℂ)) ∂P =
        Complex.exp (((t : ℝ) : ℂ) *
          ∫ x in B,
            (Complex.exp (Complex.I * ((ξ * FiniteRegionMarkedCharHelpers.dyadApprox B m x : ℝ) : ℂ)) - 1) ∂ν) := by
    intro m
    let S := FiniteRegionMarkedCharHelpers.dyadIdx m
    let ι := {k : ℤ // k ∈ S}
    let cell : ι → Set (ℝ × ℝ) := fun k => I ×ˢ FiniteRegionMarkedCharHelpers.dyadCell B m k.1
    have hcell_meas : ∀ k : ι, MeasurableSet (cell k) := fun k =>
      measurableSet_Ioc.prod (FiniteRegionMarkedCharHelpers.dyadCell_measurableSet hB m k.1)
    have hcell_disj : Pairwise (fun k₁ k₂ : ι => Disjoint (cell k₁) (cell k₂)) := by
      intro k₁ k₂ hne
      have hne' : k₁.1 ≠ k₂.1 := fun h => hne (Subtype.ext h)
      exact Set.disjoint_left.mpr fun z hz₁ hz₂ =>
        Set.disjoint_left.mp (FiniteRegionMarkedCharHelpers.dyadCell_pairwise_disjoint B m hne') hz₁.2 hz₂.2
    have hindep_raw : iIndepFun (fun (k : ι) (ω : Ω) => N.N ω (cell k)) P :=
      N.independent_disjoint cell hcell_meas hcell_disj
    let g : ι → ℝ≥0∞ → ℂ := fun k r =>
      Complex.exp (Complex.I * ((ξ * FiniteRegionMarkedCharHelpers.dyadVal m k.1 * r.toReal : ℝ) : ℂ))
    have hg_meas : ∀ k : ι, Measurable (g k) := fun k =>
      Complex.continuous_exp.measurable.comp
        (measurable_const.mul
          (Complex.continuous_ofReal.measurable.comp
            (measurable_const.mul ENNReal.measurable_toReal)))
    have hindep : iIndepFun (fun (k : ι) (ω : Ω) => g k (N.N ω (cell k))) P :=
      hindep_raw.comp g hg_meas
    have hprod_eq : ∀ ω : Ω,
        Complex.exp (Complex.I * ((ξ * Xm m ω : ℝ) : ℂ)) =
          (∏ k : ι, fun ω' => g k (N.N ω' (cell k))) ω := by
      intro ω
      rw [Finset.prod_apply]
      have hmul : ξ * Xm m ω =
          ∑ k ∈ S, ξ * FiniteRegionMarkedCharHelpers.dyadVal m k *
            (N.N ω (I ×ˢ FiniteRegionMarkedCharHelpers.dyadCell B m k)).toReal := by
        dsimp [Xm, S]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => by ring
      rw [hmul, Complex.ofReal_sum, Finset.mul_sum, Complex.exp_sum]
      rw [← Finset.prod_coe_sort S]
    have hL : ∫ ω, Complex.exp (Complex.I * ((ξ * Xm m ω : ℝ) : ℂ)) ∂P =
        ∏ k : ι, ∫ ω, g k (N.N ω (cell k)) ∂P := by
      simp_rw [hprod_eq]
      exact hindep.integral_prod_eq_prod_integral fun k =>
        ((hg_meas k).comp (N.measurable_eval (hcell_meas k))).aestronglyMeasurable
    have hfactor : ∀ k : ι,
        ∫ ω, g k (N.N ω (cell k)) ∂P =
          Complex.exp ((((t : ℝ) * (ν (FiniteRegionMarkedCharHelpers.dyadCell B m k.1)).toReal : ℝ) : ℂ) *
            (Complex.exp (Complex.I * ((ξ * FiniteRegionMarkedCharHelpers.dyadVal m k.1 : ℝ) : ℂ)) - 1)) := by
      intro k
      have hk_meas := FiniteRegionMarkedCharHelpers.dyadCell_measurableSet hB m k.1
      have hk_fin : ν (FiniteRegionMarkedCharHelpers.dyadCell B m k.1) < ⊤ :=
        lt_of_le_of_lt (measure_mono (FiniteRegionMarkedCharHelpers.dyadCell_subset B m k.1)) hfinite
      exact FiniteRegionMarkedCharHelpers.prm_count_charFun P ν N t hk_meas hk_fin
        (ξ * FiniteRegionMarkedCharHelpers.dyadVal m k.1)
    have hprod_exp :
        (∏ k : ι, ∫ ω, g k (N.N ω (cell k)) ∂P) =
          Complex.exp (((t : ℝ) : ℂ) *
            ∑ k ∈ S, ((ν (FiniteRegionMarkedCharHelpers.dyadCell B m k)).toReal : ℂ) *
              (Complex.exp (Complex.I * ((ξ * FiniteRegionMarkedCharHelpers.dyadVal m k : ℝ) : ℂ)) - 1)) := by
      simp_rw [hfactor]
      rw [← Complex.exp_sum]
      congr 1
      rw [Finset.mul_sum, ← Finset.sum_coe_sort S]
      refine Finset.sum_congr rfl fun k _ => ?_
      push_cast; ring
    have hint_rhs :
        (∫ x in B,
          (Complex.exp (Complex.I * ((ξ * FiniteRegionMarkedCharHelpers.dyadApprox B m x : ℝ) : ℂ)) - 1) ∂ν) =
        ∑ k ∈ S, ((ν (FiniteRegionMarkedCharHelpers.dyadCell B m k)).toReal : ℂ) *
          (Complex.exp (Complex.I * ((ξ * FiniteRegionMarkedCharHelpers.dyadVal m k : ℝ) : ℂ)) - 1) := by
      simp_rw [FiniteRegionMarkedCharHelpers.dyadApprox_exp_sub_one B m ξ]
      have : IsFiniteMeasure (ν.restrict B) := ⟨by rw [Measure.restrict_apply_univ]; exact hfinite⟩
      rw [integral_finsetSum]
      · refine Finset.sum_congr rfl fun k _ => ?_
        have hk_meas := FiniteRegionMarkedCharHelpers.dyadCell_measurableSet hB m k
        rw [integral_indicator_const _ hk_meas, Complex.real_smul]
        have hres : (ν.restrict B) (FiniteRegionMarkedCharHelpers.dyadCell B m k) =
            ν (FiniteRegionMarkedCharHelpers.dyadCell B m k) := by
          rw [Measure.restrict_apply hk_meas,
            Set.inter_eq_left.mpr (FiniteRegionMarkedCharHelpers.dyadCell_subset B m k)]
        rw [Measure.real, hres]
      · intro k _
        have hk_meas := FiniteRegionMarkedCharHelpers.dyadCell_measurableSet hB m k
        exact (integrable_const _).indicator hk_meas
    rw [hL, hprod_exp, hint_rhs]
  -- Step 2: Almost-sure compact mark truncation and pointwise convergence Xm m ω → X ω
  let E : ℕ → Set (ℝ × ℝ) := fun R => I ×ˢ (B \ Set.Icc (-(R : ℝ)) (R : ℝ))
  have hE_meas : ∀ R : ℕ, MeasurableSet (E R) := fun R =>
    measurableSet_Ioc.prod (hB.diff measurableSet_Icc)
  have hE_sub : ∀ R : ℕ, E R ⊆ W := fun R =>
    Set.prod_mono Set.Subset.rfl Set.sdiff_subset
  have hE_fin : ∀ R : ℕ, LevyStochCalc.Poisson.referenceIntensity ν (E R) ≠ ⊤ := fun R =>
    FiniteRegionMarkedCharHelpers.referenceIntensity_Ioc_prod_ne_top ν t (hB.diff measurableSet_Icc)
      (lt_of_le_of_lt (measure_mono Set.sdiff_subset) hfinite)
  have hE_anti : Antitone E := by
    intro R₁ R₂ hle
    refine Set.prod_mono Set.Subset.rfl ?_
    refine Set.sdiff_subset_sdiff_right ?_
    intro x hx
    exact ⟨by linarith [hx.1, (Nat.cast_le.mpr hle : (R₁ : ℝ) ≤ R₂)],
      by linarith [hx.2, (Nat.cast_le.mpr hle : (R₁ : ℝ) ≤ R₂)]⟩
  have hE_iInter : (⋂ R : ℕ, E R) = ∅ := by
    ext z
    simp only [Set.mem_iInter, Set.mem_empty_iff_false, iff_false, not_forall]
    obtain ⟨R, hR⟩ := exists_nat_gt |z.2|
    refine ⟨R, fun hz => hz.2.2 ⟨?_, ?_⟩⟩
    · linarith [(abs_lt.mp hR).1]
    · linarith [(abs_lt.mp hR).2]
  have hae_W : ∀ᵐ ω ∂P, ∃ n : ℕ, N.N ω W = n := N.integer_valued hW hWfin
  have hae_E : ∀ᵐ ω ∂P, ∀ R : ℕ, ∃ k : ℕ, N.N ω (E R) = k :=
    ae_all_iff.mpr fun R => N.integer_valued (hE_meas R) (hE_fin R)
  have hae_tendsto : ∀ᵐ ω ∂P, Tendsto (fun m => Xm m ω) atTop (nhds (X ω)) := by
    filter_upwards [hae_W, hae_E] with ω hωW hωE
    obtain ⟨nW, hnW⟩ := hωW
    have hfinW : N.N ω W ≠ ⊤ := by rw [hnW]; exact ENNReal.natCast_ne_top nW
    have : IsFiniteMeasure ((N.N ω).restrict W) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.mpr hfinW⟩
    have hE_tendsto : Tendsto (fun R => N.N ω (E R)) atTop (nhds 0) := by
      have h := MeasureTheory.tendsto_measure_iInter_atTop
        (μ := N.N ω) (s := E)
        (fun R => (hE_meas R).nullMeasurableSet)
        hE_anti
        ⟨0, ne_of_lt (lt_of_le_of_lt (measure_mono (hE_sub 0)) (lt_top_iff_ne_top.mpr hfinW))⟩
      simpa only [Function.comp_def, hE_iInter, measure_empty] using h
    have hE_lt1 : ∀ᶠ R in atTop, N.N ω (E R) < 1 :=
      hE_tendsto.eventually (Iio_mem_nhds zero_lt_one)
    obtain ⟨R₀, hR₀_lt⟩ := hE_lt1.exists
    obtain ⟨k₀, hk₀⟩ := hωE R₀
    have hk₀_zero : k₀ = 0 := by
      rw [hk₀] at hR₀_lt
      have : k₀ < 1 := by exact_mod_cast hR₀_lt
      omega
    have hER₀_zero : N.N ω (E R₀) = 0 := by rw [hk₀, hk₀_zero]; simp
    have hae_bd : ∀ᵐ z ∂((N.N ω).restrict W), z.2 ∈ B ∧ |z.2| ≤ (R₀ : ℝ) := by
      have h1 : ∀ᵐ z ∂((N.N ω).restrict W), z ∈ W := ae_restrict_mem hW
      have h2 : ∀ᵐ z ∂((N.N ω).restrict W), z ∉ E R₀ := by
        rw [ae_iff]
        have : ((N.N ω).restrict W) {z | ¬ z ∉ E R₀} = ((N.N ω).restrict W) (E R₀) := by simp
        rw [this, Measure.restrict_apply (hE_meas R₀), Set.inter_eq_left.mpr (hE_sub R₀), hER₀_zero]
      filter_upwards [h1, h2] with z hzW hznot
      refine ⟨hzW.2, ?_⟩
      by_contra hgt
      push Not at hgt
      apply hznot
      refine ⟨hzW.1, hzW.2, ?_⟩
      intro hmem
      have : |z.2| ≤ (R₀ : ℝ) := abs_le.mpr hmem
      linarith
    have hint_snd : Integrable (fun z : ℝ × ℝ => z.2) ((N.N ω).restrict W) := by
      refine Integrable.of_bound continuous_snd.aestronglyMeasurable (R₀ : ℝ) ?_
      filter_upwards [hae_bd] with z hz
      simpa only [Real.norm_eq_abs] using hz.2
    have hXm_eq_int : ∀ m : ℕ, Xm m ω = ∫ z in W, FiniteRegionMarkedCharHelpers.dyadApprox B m z.2 ∂(N.N ω) := by
      intro m
      dsimp [Xm]
      unfold FiniteRegionMarkedCharHelpers.dyadApprox
      rw [integral_finsetSum]
      · refine Finset.sum_congr rfl fun k _ => ?_
        have hk_meas := FiniteRegionMarkedCharHelpers.dyadCell_measurableSet hB m k
        have hcomp : (fun z : ℝ × ℝ =>
            (FiniteRegionMarkedCharHelpers.dyadCell B m k).indicator
              (fun _ => FiniteRegionMarkedCharHelpers.dyadVal m k) z.2) =
            (Set.univ ×ˢ FiniteRegionMarkedCharHelpers.dyadCell B m k).indicator
              (fun _ => FiniteRegionMarkedCharHelpers.dyadVal m k) := by
          funext z
          by_cases hz : z.2 ∈ FiniteRegionMarkedCharHelpers.dyadCell B m k
          · simp [Set.indicator_of_mem, hz]
          · simp [Set.indicator_of_notMem, hz]
        rw [hcomp, integral_indicator_const _ (MeasurableSet.univ.prod hk_meas)]
        rw [Measure.real, Measure.restrict_apply (MeasurableSet.univ.prod hk_meas)]
        have hinter : (Set.univ ×ˢ FiniteRegionMarkedCharHelpers.dyadCell B m k) ∩ W =
            I ×ˢ FiniteRegionMarkedCharHelpers.dyadCell B m k := by
          ext z
          simp only [W, Set.mem_inter_iff, Set.mem_prod, Set.mem_univ, true_and]
          constructor
          · rintro ⟨hz1, hz2, _⟩; exact ⟨hz2, hz1⟩
          · rintro ⟨hz1, hz2⟩; exact ⟨hz2, hz1, FiniteRegionMarkedCharHelpers.dyadCell_subset B m k hz2⟩
        rw [hinter, smul_eq_mul, mul_comm]
      · intro k _
        have hk_meas := FiniteRegionMarkedCharHelpers.dyadCell_measurableSet hB m k
        have hmeas : Measurable (fun z : ℝ × ℝ =>
            (FiniteRegionMarkedCharHelpers.dyadCell B m k).indicator
              (fun _ => FiniteRegionMarkedCharHelpers.dyadVal m k) z.2) :=
          (measurable_const.indicator hk_meas).comp measurable_snd
        refine Integrable.of_bound hmeas.aestronglyMeasurable
          |FiniteRegionMarkedCharHelpers.dyadVal m k| (Eventually.of_forall fun z => ?_)
        rw [Real.norm_eq_abs]
        by_cases hz : z.2 ∈ FiniteRegionMarkedCharHelpers.dyadCell B m k
        · simp [Set.indicator_of_mem hz]
        · simp [Set.indicator_of_notMem hz]
    -- Dominated convergence (or direct uniform bound) for Xm m ω → X ω
    rw [Metric.tendsto_nhds]
    intro ε hε
    have ht := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    obtain ⟨M₂, hM₂⟩ := (ht.eventually (gt_mem_nhds (div_pos hε (by positivity : (0 : ℝ) < (nW : ℝ) + 1)))).exists
    rw [Filter.eventually_atTop]
    refine ⟨max (R₀ + 1) M₂, fun m hm => ?_⟩
    have hmR : R₀ + 1 ≤ m := le_trans (le_max_left _ _) hm
    have hm2 : M₂ ≤ m := le_trans (le_max_right _ _) hm
    have hint_m : Integrable (fun z : ℝ × ℝ => FiniteRegionMarkedCharHelpers.dyadApprox B m z.2)
        ((N.N ω).restrict W) := by
      have hmeas : Measurable (fun z : ℝ × ℝ => FiniteRegionMarkedCharHelpers.dyadApprox B m z.2) :=
        (FiniteRegionMarkedCharHelpers.dyadApprox_measurable hB m).comp measurable_snd
      refine Integrable.of_bound hmeas.aestronglyMeasurable ((R₀ : ℝ) + 1) ?_
      filter_upwards [hae_bd] with z hz
      have hbdz : |z.2| < (m : ℝ) := lt_of_le_of_lt hz.2 (by exact_mod_cast Nat.lt_of_succ_le hmR)
      have hsub := FiniteRegionMarkedCharHelpers.dyadApprox_sub_le hz.1 hbdz
      have hpow_le : (1 : ℝ) / (2 : ℝ) ^ m ≤ 1 := by
        rw [div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num)
      rw [Real.norm_eq_abs]
      have htri : |FiniteRegionMarkedCharHelpers.dyadApprox B m z.2| ≤
          |FiniteRegionMarkedCharHelpers.dyadApprox B m z.2 - z.2| + |z.2| := by
        have := abs_add_le (FiniteRegionMarkedCharHelpers.dyadApprox B m z.2 - z.2) z.2
        simpa [sub_add_cancel] using this
      linarith [hz.2]
    rw [Real.dist_eq, hXm_eq_int m]
    dsimp [X]
    rw [← integral_sub hint_m hint_snd]
    have hnorm_le : ‖∫ z in W, (FiniteRegionMarkedCharHelpers.dyadApprox B m z.2 - z.2) ∂(N.N ω)‖ ≤
        ((1 : ℝ) / (2 : ℝ) ^ m) * ((N.N ω).restrict W).real Set.univ := by
      refine norm_integral_le_of_norm_le_const ?_
      filter_upwards [hae_bd] with z hz
      have hbdz : |z.2| < (m : ℝ) := lt_of_le_of_lt hz.2 (by exact_mod_cast Nat.lt_of_succ_le hmR)
      simpa only [Real.norm_eq_abs] using FiniteRegionMarkedCharHelpers.dyadApprox_sub_le hz.1 hbdz
    have hvol : ((N.N ω).restrict W).real Set.univ = (nW : ℝ) := by
      rw [Measure.real, Measure.restrict_apply_univ, hnW, ENNReal.toReal_natCast]
    rw [Real.norm_eq_abs, hvol] at hnorm_le
    have hpow : (1 : ℝ) / (2 : ℝ) ^ m < ε / ((nW : ℝ) + 1) := by
      calc (1 : ℝ) / (2 : ℝ) ^ m = (1 / 2 : ℝ) ^ m := by rw [one_div_pow]
        _ ≤ (1 / 2 : ℝ) ^ M₂ := pow_le_pow_of_le_one (by norm_num) (by norm_num) hm2
        _ < ε / ((nW : ℝ) + 1) := hM₂
    have hprod_lt : ((1 : ℝ) / (2 : ℝ) ^ m) * (nW : ℝ) < ε := by
      have h1 : ((1 : ℝ) / (2 : ℝ) ^ m) * (nW : ℝ) ≤ ((1 : ℝ) / (2 : ℝ) ^ m) * ((nW : ℝ) + 1) := by
        apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      have h2 : ((1 : ℝ) / (2 : ℝ) ^ m) * ((nW : ℝ) + 1) < ε := by
        rwa [lt_div_iff₀ (by positivity : (0 : ℝ) < (nW : ℝ) + 1)] at hpow
      linarith
    linarith
  -- Step 3: Pass to the limit on both sides via Dominated Convergence
  have hX_aemeas : AEMeasurable X P :=
    aemeasurable_of_tendsto_metrizable_ae atTop (fun m => (hXm_meas m).aemeasurable) hae_tendsto
  have hLHS_char : charFun (P.map X) ξ = ∫ ω, Complex.exp (Complex.I * ((ξ * X ω : ℝ) : ℂ)) ∂P := by
    rw [charFun_apply_real]
    have hcont : Continuous (fun x : ℝ => Complex.exp ((ξ : ℂ) * (x : ℂ) * Complex.I)) :=
      Complex.continuous_exp.comp ((continuous_const.mul Complex.continuous_ofReal).mul continuous_const)
    rw [integral_map hX_aemeas hcont.aestronglyMeasurable]
    congr 1; funext ω; congr 1; push_cast; ring
  have hLHS_tendsto :
      Tendsto (fun m => ∫ ω, Complex.exp (Complex.I * ((ξ * Xm m ω : ℝ) : ℂ)) ∂P)
        atTop (nhds (∫ ω, Complex.exp (Complex.I * ((ξ * X ω : ℝ) : ℂ)) ∂P)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ)) ?_ (integrable_const 1) ?_ ?_
    · intro m
      exact (Complex.continuous_exp.measurable.comp
        (measurable_const.mul
          (Complex.continuous_ofReal.measurable.comp
            (measurable_const.mul (hXm_meas m))))).aestronglyMeasurable
    · intro m
      refine Eventually.of_forall fun ω => ?_
      have hmul_comm : Complex.I * ((ξ * Xm m ω : ℝ) : ℂ) = ((ξ * Xm m ω : ℝ) : ℂ) * Complex.I := mul_comm _ _
      rw [hmul_comm, Complex.norm_exp_ofReal_mul_I]
    · filter_upwards [hae_tendsto] with ω hω
      have hcont : Continuous (fun r : ℝ => Complex.exp (Complex.I * ((ξ * r : ℝ) : ℂ))) :=
        Complex.continuous_exp.comp
          (continuous_const.mul (Complex.continuous_ofReal.comp (continuous_const.mul continuous_id)))
      exact (hcont.tendsto (X ω)).comp hω
  have hRHS_int_tendsto :
      Tendsto (fun m => ∫ x in B,
          (Complex.exp (Complex.I * ((ξ * FiniteRegionMarkedCharHelpers.dyadApprox B m x : ℝ) : ℂ)) - 1) ∂ν)
        atTop
        (nhds (∫ x in B, (Complex.exp (Complex.I * ((ξ * x : ℝ) : ℂ)) - 1) ∂ν)) := by
    have : IsFiniteMeasure (ν.restrict B) := ⟨by rw [Measure.restrict_apply_univ]; exact hfinite⟩
    refine tendsto_integral_of_dominated_convergence (fun _ => (2 : ℝ)) ?_ (integrable_const 2) ?_ ?_
    · intro m
      exact ((Complex.continuous_exp.measurable.comp
        (measurable_const.mul
          (Complex.continuous_ofReal.measurable.comp
            (measurable_const.mul (FiniteRegionMarkedCharHelpers.dyadApprox_measurable hB m))))).sub
        measurable_const).aestronglyMeasurable
    · intro m
      refine Eventually.of_forall fun x => ?_
      have hnorm_exp : ‖Complex.exp (Complex.I * ((ξ * FiniteRegionMarkedCharHelpers.dyadApprox B m x : ℝ) : ℂ))‖ = 1 := by
        rw [mul_comm, Complex.norm_exp_ofReal_mul_I]
      calc ‖Complex.exp (Complex.I * ((ξ * FiniteRegionMarkedCharHelpers.dyadApprox B m x : ℝ) : ℂ)) - 1‖
          ≤ ‖Complex.exp (Complex.I * ((ξ * FiniteRegionMarkedCharHelpers.dyadApprox B m x : ℝ) : ℂ))‖ + ‖(1 : ℂ)‖ :=
            norm_sub_le _ _
        _ = 2 := by rw [hnorm_exp, norm_one]; norm_num
    · filter_upwards [ae_restrict_mem hB] with x hxB
      have hcont : Continuous (fun r : ℝ => Complex.exp (Complex.I * ((ξ * r : ℝ) : ℂ)) - 1) :=
        (Complex.continuous_exp.comp
          (continuous_const.mul (Complex.continuous_ofReal.comp (continuous_const.mul continuous_id)))).sub
          continuous_const
      exact (hcont.tendsto x).comp (FiniteRegionMarkedCharHelpers.dyadApprox_tendsto hxB)
  have hRHS_tendsto :
      Tendsto (fun m => Complex.exp (((t : ℝ) : ℂ) *
          ∫ x in B,
            (Complex.exp (Complex.I * ((ξ * FiniteRegionMarkedCharHelpers.dyadApprox B m x : ℝ) : ℂ)) - 1) ∂ν))
        atTop
        (nhds (Complex.exp (((t : ℝ) : ℂ) *
          ∫ x in B, (Complex.exp (Complex.I * ((ξ * x : ℝ) : ℂ)) - 1) ∂ν))) :=
    (Complex.continuous_exp.comp (continuous_const.mul continuous_id)).continuousAt.tendsto.comp hRHS_int_tendsto
  rw [hLHS_char]
  have hLHS_tendsto' :
      Tendsto (fun m => Complex.exp (((t : ℝ) : ℂ) *
          ∫ x in B,
            (Complex.exp (Complex.I * ((ξ * FiniteRegionMarkedCharHelpers.dyadApprox B m x : ℝ) : ℂ)) - 1) ∂ν))
        atTop (nhds (∫ ω, Complex.exp (Complex.I * ((ξ * X ω : ℝ) : ℂ)) ∂P)) := by
    simpa only [hXm_charFun] using hLHS_tendsto
  exact tendsto_nhds_unique hLHS_tendsto' hRHS_tendsto
