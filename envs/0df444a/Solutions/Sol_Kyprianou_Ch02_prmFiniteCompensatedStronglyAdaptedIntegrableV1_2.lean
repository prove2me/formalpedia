-- Prove2me | solution 2 for Kyprianou.Ch02.prmFiniteCompensatedStronglyAdaptedIntegrableV1
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-23T19:26:36.338151+00:00
-- url     : https://prove2.me/submissions/cab454ed-dfb7-4811-88f7-f6b7e4805983

import Mathlib
import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch02_prmMarkedIntegralMeasurableAmbientV1

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

set_option autoImplicit false

namespace PrmFiniteCompensatedAdaptedHelpers

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

private lemma referenceIntensity_Ioc_prod_toReal (ν : Measure ℝ) [SigmaFinite ν]
    (t : ℝ≥0) {A : Set ℝ} :
    (LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ A)).toReal =
      (t : ℝ) * (ν A).toReal := by
  rw [referenceIntensity_Ioc_prod ν t, ENNReal.toReal_mul, ENNReal.toReal_ofReal t.coe_nonneg]

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

private lemma prm_count_first_moment
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (t : ℝ≥0) {A : Set ℝ} (hA : MeasurableSet A) (hAfin : ν A < ⊤) :
    let W := Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ A
    Integrable (fun ω => (N.N ω W).toReal) P ∧
    (∫ ω, (N.N ω W).toReal ∂P) = (t : ℝ) * (ν A).toReal := by
  intro W
  have hW : MeasurableSet W := measurableSet_Ioc.prod hA
  have hWfin : LevyStochCalc.Poisson.referenceIntensity ν W ≠ ⊤ :=
    referenceIntensity_Ioc_prod_ne_top ν t hAfin
  let μ : ℝ≥0 := (LevyStochCalc.Poisson.referenceIntensity ν W).toNNReal
  have hμ_eq : (μ : ℝ) = (t : ℝ) * (ν A).toReal := by
    have h1 : (μ : ℝ) = (LevyStochCalc.Poisson.referenceIntensity ν W).toReal := rfl
    rw [h1, referenceIntensity_Ioc_prod_toReal ν t]
  have hN_meas : Measurable (fun ω => N.N ω W) := N.measurable_eval hW
  have hcast_meas : Measurable (fun n : ℕ => (n : ℝ≥0∞)) := measurable_of_countable _
  have hlaw : P.map (fun ω => N.N ω W) =
      (ProbabilityTheory.poissonMeasure μ).map (fun n : ℕ => (n : ℝ≥0∞)) :=
    N.poisson_law hW hWfin
  have htoReal_meas : Measurable (fun r : ℝ≥0∞ => r.toReal) := ENNReal.measurable_toReal
  have hpois_int : Integrable (fun n : ℕ => (n : ℝ)) (ProbabilityTheory.poissonMeasure μ) := by
    rw [ProbabilityTheory.integrable_poissonMeasure_iff]
    exact (hasSum_poisson_first μ).summable.congr fun n => by rw [Real.norm_eq_abs, Nat.abs_cast]
  have hpois_mean : ∫ n : ℕ, (n : ℝ) ∂(ProbabilityTheory.poissonMeasure μ) = (μ : ℝ) := by
    rw [ProbabilityTheory.integral_poissonMeasure]
    simpa only [smul_eq_mul] using (hasSum_poisson_first μ).tsum_eq
  have hint : Integrable (fun ω => (N.N ω W).toReal) P := by
    change Integrable ((fun r : ℝ≥0∞ => r.toReal) ∘ fun ω => N.N ω W) P
    rw [← integrable_map_measure htoReal_meas.aestronglyMeasurable hN_meas.aemeasurable, hlaw,
      integrable_map_measure htoReal_meas.aestronglyMeasurable hcast_meas.aemeasurable]
    simpa only [Function.comp_def, ENNReal.toReal_natCast] using hpois_int
  have hmean : (∫ ω, (N.N ω W).toReal ∂P) = (t : ℝ) * (ν A).toReal := by
    have h1 : ∫ ω, (N.N ω W).toReal ∂P = ∫ r, r.toReal ∂(P.map (fun ω => N.N ω W)) :=
      (integral_map hN_meas.aemeasurable htoReal_meas.aestronglyMeasurable).symm
    have h2 : ∫ r, r.toReal ∂((ProbabilityTheory.poissonMeasure μ).map (fun n : ℕ => (n : ℝ≥0∞))) =
        ∫ n : ℕ, ((n : ℝ≥0∞).toReal) ∂(ProbabilityTheory.poissonMeasure μ) :=
      integral_map hcast_meas.aemeasurable htoReal_meas.aestronglyMeasurable
    rw [h1, hlaw, h2]
    simp only [ENNReal.toReal_natCast, hpois_mean, hμ_eq]
  exact ⟨hint, hmean⟩

-- Signed dyadic partition for Part (A): strong measurability
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
    · rw [Int.le_floor]; push_cast; linarith
    · have hreal : (k₀ : ℝ) < ((m : ℤ) * (2 : ℤ) ^ m : ℤ) := by push_cast; linarith
      exact_mod_cast hreal
  have hx_cell : x ∈ dyadCell B m k₀ := by
    refine ⟨hxB, ?_, ?_⟩
    · rw [div_le_iff₀ hpos]; linarith
    · rw [lt_div_iff₀ hpos]; push_cast; linarith
  have hval : dyadApprox B m x = dyadVal m k₀ := by
    unfold dyadApprox
    rw [Finset.sum_eq_single k₀]
    · rw [Set.indicator_of_mem hx_cell]
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

-- Nonnegative dyadic partition of |x| for Part (B): L1 integrability via Fatou
private def absCell (B : Set ℝ) (m k : ℕ) : Set ℝ :=
  B ∩ (abs ⁻¹' Set.Ico ((k : ℝ) / (2 : ℝ) ^ m) (((k + 1 : ℕ) : ℝ) / (2 : ℝ) ^ m))

private noncomputable def absApprox (B : Set ℝ) (m : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (m * 2 ^ m), (absCell B m k).indicator (fun _ => (k : ℝ) / (2 : ℝ) ^ m) x

private lemma absCell_measurableSet {B : Set ℝ} (hB : MeasurableSet B) (m k : ℕ) :
    MeasurableSet (absCell B m k) :=
  hB.inter (measurableSet_Ico.preimage continuous_abs.measurable)

private lemma absCell_pairwise_disjoint (B : Set ℝ) (m : ℕ) :
    Pairwise (fun k₁ k₂ : ℕ => Disjoint (absCell B m k₁) (absCell B m k₂)) := by
  intro k₁ k₂ hne
  rw [Set.disjoint_left]
  intro x hx₁ hx₂
  have hpos : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hle : ((k₁ + 1 : ℕ) : ℝ) ≤ (k₂ : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hlt
    have hdiv : ((k₁ + 1 : ℕ) : ℝ) / (2 : ℝ) ^ m ≤ (k₂ : ℝ) / (2 : ℝ) ^ m :=
      div_le_div_of_nonneg_right hle (le_of_lt hpos)
    linarith [hx₁.2.2, hx₂.2.1]
  · have hle : ((k₂ + 1 : ℕ) : ℝ) ≤ (k₁ : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hgt
    have hdiv : ((k₂ + 1 : ℕ) : ℝ) / (2 : ℝ) ^ m ≤ (k₁ : ℝ) / (2 : ℝ) ^ m :=
      div_le_div_of_nonneg_right hle (le_of_lt hpos)
    linarith [hx₂.2.2, hx₁.2.1]

private lemma absApprox_nonneg (B : Set ℝ) (m : ℕ) (x : ℝ) : 0 ≤ absApprox B m x := by
  unfold absApprox
  refine Finset.sum_nonneg fun k _ => ?_
  by_cases hx : x ∈ absCell B m k
  · rw [Set.indicator_of_mem hx]; positivity
  · rw [Set.indicator_of_notMem hx]

private lemma absApprox_le_abs (B : Set ℝ) (m : ℕ) (x : ℝ) : absApprox B m x ≤ |x| := by
  by_cases hex : ∃ k ∈ Finset.range (m * 2 ^ m), x ∈ absCell B m k
  · obtain ⟨k₀, hk₀_mem, hxk₀⟩ := hex
    have hval : absApprox B m x = (k₀ : ℝ) / (2 : ℝ) ^ m := by
      unfold absApprox
      rw [Finset.sum_eq_single k₀]
      · rw [Set.indicator_of_mem hxk₀]
      · intro k _ hne
        apply Set.indicator_of_notMem
        intro hxk
        exact Set.disjoint_left.mp (absCell_pairwise_disjoint B m hne) hxk hxk₀
      · intro hnot; exact absurd hk₀_mem hnot
    rw [hval]
    exact hxk₀.2.1
  · push Not at hex
    have hval : absApprox B m x = 0 := by
      unfold absApprox
      exact Finset.sum_eq_zero fun k hk => Set.indicator_of_notMem (hex k hk) _
    rw [hval]
    exact abs_nonneg x

private lemma absApprox_sub_le {B : Set ℝ} {m : ℕ} {x : ℝ} (hxB : x ∈ B) (hxbd : |x| < (m : ℝ)) :
    |absApprox B m x - abs x| ≤ 1 / (2 : ℝ) ^ m := by
  have hpos : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
  let k₀ : ℕ := Nat.floor ((2 : ℝ) ^ m * |x|)
  have hk₀_le : (k₀ : ℝ) ≤ (2 : ℝ) ^ m * |x| := Nat.floor_le (by positivity)
  have hk₀_lt : (2 : ℝ) ^ m * |x| < (k₀ : ℝ) + 1 := Nat.lt_floor_add_one _
  have hk₀_mem : k₀ ∈ Finset.range (m * 2 ^ m) := by
    rw [Finset.mem_range]
    have hreal : (k₀ : ℝ) < ((m * 2 ^ m : ℕ) : ℝ) := by
      push_cast
      nlinarith
    exact_mod_cast hreal
  have hx_cell : x ∈ absCell B m k₀ := by
    refine ⟨hxB, ?_, ?_⟩
    · rw [div_le_iff₀ hpos]; linarith
    · rw [lt_div_iff₀ hpos]; push_cast; linarith
  have hval : absApprox B m x = (k₀ : ℝ) / (2 : ℝ) ^ m := by
    unfold absApprox
    rw [Finset.sum_eq_single k₀]
    · rw [Set.indicator_of_mem hx_cell]
    · intro k _ hne
      apply Set.indicator_of_notMem
      intro hxk
      exact Set.disjoint_left.mp (absCell_pairwise_disjoint B m hne) hxk hx_cell
    · intro hnot; exact absurd hk₀_mem hnot
  rw [hval]
  have hlo : (k₀ : ℝ) / (2 : ℝ) ^ m ≤ |x| := hx_cell.2.1
  have hhi : |x| < ((k₀ + 1 : ℕ) : ℝ) / (2 : ℝ) ^ m := hx_cell.2.2
  have hdiff : ((k₀ + 1 : ℕ) : ℝ) / (2 : ℝ) ^ m - (k₀ : ℝ) / (2 : ℝ) ^ m = 1 / (2 : ℝ) ^ m := by
    push_cast; ring
  rw [abs_le]
  constructor <;> linarith

end PrmFiniteCompensatedAdaptedHelpers

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hfinite : ν B < ⊤)
    (hfirst : Integrable (fun x : ℝ => x) (ν.restrict B))
    (ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (hℱ : Kyprianou.Ch02.IsCompletedPoissonFiltration P ν N ℱ) :
    (∀ t : ℝ≥0, StronglyMeasurable[ℱ t] ((fun (t : ℝ≥0) ω =>
      (∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B), z.2 ∂(N.N ω)) -
      (t : ℝ) * (∫ x in B, x ∂ν)) t)) ∧
    (∀ t : ℝ≥0, Integrable ((fun (t : ℝ≥0) ω =>
      (∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B), z.2 ∂(N.N ω)) -
      (t : ℝ) * (∫ x in B, x ∂ν)) t) P) := by
  -- Shared setup per time t
  have hcore : ∀ t : ℝ≥0,
      StronglyMeasurable[ℱ t] (fun ω => ∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B), z.2 ∂(N.N ω)) ∧
      Integrable (fun ω => ∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B), z.2 ∂(N.N ω)) P := by
    intro t
    let I : Set ℝ := Set.Ioc (0 : ℝ) (t : ℝ)
    let W : Set (ℝ × ℝ) := I ×ˢ B
    have hW : MeasurableSet W := measurableSet_Ioc.prod hB
    have hWfin : LevyStochCalc.Poisson.referenceIntensity ν W ≠ ⊤ :=
      PrmFiniteCompensatedAdaptedHelpers.referenceIntensity_Ioc_prod_ne_top ν t hfinite
    let X : Ω → ℝ := fun ω => ∫ z in W, z.2 ∂(N.N ω)
    have hX_amb : Measurable X :=
      Kyprianou.Ch02.prmMarkedIntegralMeasurableAmbientV1 P ν N W hW
    -- Explicit ℱ t-measurable full-measure good event G
    let E : ℕ → Set (ℝ × ℝ) := fun R => I ×ˢ (B \ Set.Icc (-(R : ℝ)) (R : ℝ))
    have hE_meas : ∀ R : ℕ, MeasurableSet (E R) := fun R =>
      measurableSet_Ioc.prod (hB.diff measurableSet_Icc)
    have hE_sub : ∀ R : ℕ, E R ⊆ W := fun _ => Set.prod_mono Set.Subset.rfl Set.sdiff_subset
    have hE_fin : ∀ R : ℕ, LevyStochCalc.Poisson.referenceIntensity ν (E R) ≠ ⊤ := fun R =>
      PrmFiniteCompensatedAdaptedHelpers.referenceIntensity_Ioc_prod_ne_top ν t
        (lt_of_le_of_lt (measure_mono Set.sdiff_subset) hfinite)
    have hE_anti : Antitone E := by
      intro R₁ R₂ hle
      refine Set.prod_mono Set.Subset.rfl (Set.sdiff_subset_sdiff_right fun x hx => ?_)
      exact ⟨by linarith [hx.1, (Nat.cast_le.mpr hle : (R₁ : ℝ) ≤ R₂)],
        by linarith [hx.2, (Nat.cast_le.mpr hle : (R₁ : ℝ) ≤ R₂)]⟩
    have hE_iInter : (⋂ R : ℕ, E R) = ∅ := by
      ext z
      simp only [Set.mem_iInter, Set.mem_empty_iff_false, iff_false, not_forall]
      obtain ⟨R, hR⟩ := exists_nat_gt |z.2|
      refine ⟨R, fun hz => hz.2.2 ⟨?_, ?_⟩⟩
      · linarith [(abs_lt.mp hR).1]
      · linarith [(abs_lt.mp hR).2]
    let G : Set Ω := {ω | (∃ n : ℕ, N.N ω W = n) ∧ (∀ R : ℕ, ∃ k : ℕ, N.N ω (E R) = k)}
    have hG_F : @MeasurableSet Ω (ℱ t) G := by
      have h1 : @MeasurableSet Ω (ℱ t) {ω | ∃ n : ℕ, N.N ω W = n} := by
        have hEq : {ω | ∃ n : ℕ, N.N ω W = n} = ⋃ n : ℕ, (fun ω => N.N ω W) ⁻¹' {(n : ℝ≥0∞)} := by
          ext ω; simp
        rw [hEq]
        refine @MeasurableSet.iUnion Ω ℕ (ℱ t) _ _ fun n => ?_
        exact (hℱ.1 t t le_rfl B hB) (measurableSet_singleton (n : ℝ≥0∞))
      have h2 : @MeasurableSet Ω (ℱ t) {ω | ∀ R : ℕ, ∃ k : ℕ, N.N ω (E R) = k} := by
        have hEq : {ω | ∀ R : ℕ, ∃ k : ℕ, N.N ω (E R) = k} =
            ⋂ R : ℕ, ⋃ k : ℕ, (fun ω => N.N ω (E R)) ⁻¹' {(k : ℝ≥0∞)} := by
          ext ω; simp
        rw [hEq]
        refine @MeasurableSet.iInter Ω ℕ (ℱ t) _ _ fun R =>
          @MeasurableSet.iUnion Ω ℕ (ℱ t) _ _ fun k => ?_
        exact (hℱ.1 t t le_rfl (B \ Set.Icc (-(R : ℝ)) (R : ℝ)) (hB.diff measurableSet_Icc))
          (measurableSet_singleton (k : ℝ≥0∞))
      exact h1.inter h2
    have hae_G : ∀ᵐ ω ∂P, ω ∈ G := by
      have h1 := N.integer_valued hW hWfin
      have h2 := ae_all_iff.mpr fun R => N.integer_valued (hE_meas R) (hE_fin R)
      filter_upwards [h1, h2] with ω hω1 hω2
      exact ⟨hω1, hω2⟩
    have hP_Gc : P Gᶜ = 0 := ae_iff.mp hae_G
    -- Every ω ∈ G has compact mark support |z.2| ≤ R₀ on ((N.N ω).restrict W)
    have hG_compact : ∀ ω ∈ G, ∃ (nW R₀ : ℕ), N.N ω W = nW ∧
        (∀ᵐ z ∂((N.N ω).restrict W), z.2 ∈ B ∧ |z.2| ≤ (R₀ : ℝ)) := by
      intro ω hω
      obtain ⟨⟨nW, hnW⟩, hωE⟩ := hω
      have hfinW : N.N ω W ≠ ⊤ := by rw [hnW]; exact ENNReal.natCast_ne_top nW
      have hE_tendsto : Tendsto (fun R => N.N ω (E R)) atTop (nhds 0) := by
        have h := MeasureTheory.tendsto_measure_iInter_atTop
          (μ := N.N ω) (s := E)
          (fun R => (hE_meas R).nullMeasurableSet)
          hE_anti
          ⟨0, ne_of_lt (lt_of_le_of_lt (measure_mono (hE_sub 0)) (lt_top_iff_ne_top.mpr hfinW))⟩
        simpa only [Function.comp_def, hE_iInter, measure_empty] using h
      obtain ⟨R₀, hR₀_lt⟩ := (hE_tendsto.eventually (Iio_mem_nhds zero_lt_one)).exists
      obtain ⟨k₀, hk₀⟩ := hωE R₀
      have hk₀_zero : k₀ = 0 := by
        rw [hk₀] at hR₀_lt
        have : k₀ < 1 := by exact_mod_cast hR₀_lt
        omega
      have hER₀_zero : N.N ω (E R₀) = 0 := by rw [hk₀, hk₀_zero]; simp
      refine ⟨nW, R₀, hnW, ?_⟩
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
    -- Part (A): Strong measurability in ℱ t
    let Xm : ℕ → Ω → ℝ := fun m ω =>
      ∑ k ∈ PrmFiniteCompensatedAdaptedHelpers.dyadIdx m,
        PrmFiniteCompensatedAdaptedHelpers.dyadVal m k *
          (N.N ω (I ×ˢ PrmFiniteCompensatedAdaptedHelpers.dyadCell B m k)).toReal
    have hXm_F : ∀ m : ℕ, @Measurable Ω ℝ (ℱ t) _ (Xm m) := by
      intro m
      refine Finset.measurable_sum (m := ℱ t) (PrmFiniteCompensatedAdaptedHelpers.dyadIdx m)
        (f := fun k ω => PrmFiniteCompensatedAdaptedHelpers.dyadVal m k *
          (N.N ω (I ×ˢ PrmFiniteCompensatedAdaptedHelpers.dyadCell B m k)).toReal) fun k _ => ?_
      exact (@measurable_const ℝ Ω _ (ℱ t) _).mul
        (ENNReal.measurable_toReal.comp
          (hℱ.1 t t le_rfl (PrmFiniteCompensatedAdaptedHelpers.dyadCell B m k)
            (PrmFiniteCompensatedAdaptedHelpers.dyadCell_measurableSet hB m k)))
    have hXm_tendsto_on_G : ∀ ω ∈ G, Tendsto (fun m => Xm m ω) atTop (nhds (X ω)) := by
      intro ω hω
      obtain ⟨nW, R₀, hnW, hae_bd⟩ := hG_compact ω hω
      have hfinW : IsFiniteMeasure ((N.N ω).restrict W) :=
        ⟨by rw [Measure.restrict_apply_univ, hnW]; exact ENNReal.natCast_lt_top nW⟩
      have hint_snd : Integrable (fun z : ℝ × ℝ => z.2) ((N.N ω).restrict W) :=
        Integrable.of_bound continuous_snd.aestronglyMeasurable (R₀ : ℝ)
          (hae_bd.mono fun z hz => by simpa only [Real.norm_eq_abs] using hz.2)
      have hXm_eq_int : ∀ m : ℕ, Xm m ω =
          ∫ z in W, PrmFiniteCompensatedAdaptedHelpers.dyadApprox B m z.2 ∂(N.N ω) := by
        intro m
        dsimp [Xm]
        unfold PrmFiniteCompensatedAdaptedHelpers.dyadApprox
        rw [integral_finsetSum]
        · refine Finset.sum_congr rfl fun k _ => ?_
          have hk_meas := PrmFiniteCompensatedAdaptedHelpers.dyadCell_measurableSet hB m k
          have hcomp : (fun z : ℝ × ℝ =>
              (PrmFiniteCompensatedAdaptedHelpers.dyadCell B m k).indicator
                (fun _ => PrmFiniteCompensatedAdaptedHelpers.dyadVal m k) z.2) =
              (Set.univ ×ˢ PrmFiniteCompensatedAdaptedHelpers.dyadCell B m k).indicator
                (fun _ => PrmFiniteCompensatedAdaptedHelpers.dyadVal m k) := by
            funext z
            by_cases hz : z.2 ∈ PrmFiniteCompensatedAdaptedHelpers.dyadCell B m k
            · simp [Set.indicator_of_mem, hz]
            · simp [Set.indicator_of_notMem, hz]
          rw [hcomp, integral_indicator_const _ (MeasurableSet.univ.prod hk_meas)]
          rw [Measure.real, Measure.restrict_apply (MeasurableSet.univ.prod hk_meas)]
          have hinter : (Set.univ ×ˢ PrmFiniteCompensatedAdaptedHelpers.dyadCell B m k) ∩ W =
              I ×ˢ PrmFiniteCompensatedAdaptedHelpers.dyadCell B m k := by
            ext z
            simp only [W, Set.mem_inter_iff, Set.mem_prod, Set.mem_univ, true_and]
            constructor
            · rintro ⟨hz1, hz2, _⟩; exact ⟨hz2, hz1⟩
            · rintro ⟨hz1, hz2⟩; exact ⟨hz2, hz1, Set.inter_subset_left hz2⟩
          rw [hinter, smul_eq_mul, mul_comm]
        · intro k _
          have hk_meas := PrmFiniteCompensatedAdaptedHelpers.dyadCell_measurableSet hB m k
          have hmeas : Measurable (fun z : ℝ × ℝ =>
              (PrmFiniteCompensatedAdaptedHelpers.dyadCell B m k).indicator
                (fun _ => PrmFiniteCompensatedAdaptedHelpers.dyadVal m k) z.2) :=
            (measurable_const.indicator hk_meas).comp measurable_snd
          refine Integrable.of_bound hmeas.aestronglyMeasurable
            |PrmFiniteCompensatedAdaptedHelpers.dyadVal m k| (Eventually.of_forall fun z => ?_)
          rw [Real.norm_eq_abs]
          by_cases hz : z.2 ∈ PrmFiniteCompensatedAdaptedHelpers.dyadCell B m k
          · simp [Set.indicator_of_mem hz]
          · simp [Set.indicator_of_notMem hz]
      rw [Metric.tendsto_nhds]
      intro ε hε
      have ht := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
      obtain ⟨M₂, hM₂⟩ := (ht.eventually (gt_mem_nhds (div_pos hε (by positivity : (0 : ℝ) < (nW : ℝ) + 1)))).exists
      rw [Filter.eventually_atTop]
      refine ⟨max (R₀ + 1) M₂, fun m hm => ?_⟩
      have hmR : R₀ + 1 ≤ m := le_trans (le_max_left _ _) hm
      have hm2 : M₂ ≤ m := le_trans (le_max_right _ _) hm
      have hint_m : Integrable (fun z : ℝ × ℝ => PrmFiniteCompensatedAdaptedHelpers.dyadApprox B m z.2)
          ((N.N ω).restrict W) := by
        have hmeas : Measurable (fun z : ℝ × ℝ => PrmFiniteCompensatedAdaptedHelpers.dyadApprox B m z.2) :=
          (Finset.measurable_sum (PrmFiniteCompensatedAdaptedHelpers.dyadIdx m)
            (f := fun k x => (PrmFiniteCompensatedAdaptedHelpers.dyadCell B m k).indicator
              (fun _ => PrmFiniteCompensatedAdaptedHelpers.dyadVal m k) x)
            fun k _ => measurable_const.indicator (PrmFiniteCompensatedAdaptedHelpers.dyadCell_measurableSet hB m k)).comp
            measurable_snd
        refine Integrable.of_bound hmeas.aestronglyMeasurable ((R₀ : ℝ) + 1) ?_
        filter_upwards [hae_bd] with z hz
        have hbdz : |z.2| < (m : ℝ) := lt_of_le_of_lt hz.2 (by exact_mod_cast Nat.lt_of_succ_le hmR)
        have hsub := PrmFiniteCompensatedAdaptedHelpers.dyadApprox_sub_le hz.1 hbdz
        have hpow_le : (1 : ℝ) / (2 : ℝ) ^ m ≤ 1 := by
          rw [div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num)
        rw [Real.norm_eq_abs]
        have htri : |PrmFiniteCompensatedAdaptedHelpers.dyadApprox B m z.2| ≤
            |PrmFiniteCompensatedAdaptedHelpers.dyadApprox B m z.2 - z.2| + |z.2| := by
          have := abs_add_le (PrmFiniteCompensatedAdaptedHelpers.dyadApprox B m z.2 - z.2) z.2
          simpa [sub_add_cancel] using this
        linarith [hz.2]
      rw [Real.dist_eq, hXm_eq_int m]
      dsimp [X]
      rw [← integral_sub hint_m hint_snd]
      have hnorm_le : ‖∫ z in W, (PrmFiniteCompensatedAdaptedHelpers.dyadApprox B m z.2 - z.2) ∂(N.N ω)‖ ≤
          ((1 : ℝ) / (2 : ℝ) ^ m) * ((N.N ω).restrict W).real Set.univ := by
        refine norm_integral_le_of_norm_le_const ?_
        filter_upwards [hae_bd] with z hz
        have hbdz : |z.2| < (m : ℝ) := lt_of_le_of_lt hz.2 (by exact_mod_cast Nat.lt_of_succ_le hmR)
        simpa only [Real.norm_eq_abs] using PrmFiniteCompensatedAdaptedHelpers.dyadApprox_sub_le hz.1 hbdz
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
    have hXind_F : @Measurable Ω ℝ (ℱ t) _ (G.indicator X) := by
      refine @measurable_of_tendsto_metrizable Ω ℝ (ℱ t) _ _ _ _
        (f := fun m => G.indicator (Xm m)) (g := G.indicator X)
        (fun m => (hXm_F m).indicator hG_F) ?_
      rw [tendsto_pi_nhds]
      intro ω
      by_cases hω : ω ∈ G
      · simpa only [Set.indicator_of_mem hω] using hXm_tendsto_on_G ω hω
      · simpa only [Set.indicator_of_notMem hω] using tendsto_const_nhds
    have hX_F : @Measurable Ω ℝ (ℱ t) _ X := by
      intro s hs
      have hdecomp : X ⁻¹' s = ((G.indicator X) ⁻¹' s ∩ G) ∪ (X ⁻¹' s ∩ Gᶜ) := by
        ext ω
        by_cases hω : ω ∈ G
        · simp [hω]
        · simp [hω]
      rw [hdecomp]
      have hpart1 : @MeasurableSet Ω (ℱ t) ((G.indicator X) ⁻¹' s ∩ G) :=
        (hXind_F hs).inter hG_F
      have hpart2_amb : MeasurableSet (X ⁻¹' s ∩ Gᶜ) :=
        (hX_amb hs).inter (ℱ.le t _ hG_F.compl)
      have hpart2_null : P (X ⁻¹' s ∩ Gᶜ) = 0 :=
        measure_mono_null Set.inter_subset_right hP_Gc
      have hpart2 : @MeasurableSet Ω (ℱ t) (X ⁻¹' s ∩ Gᶜ) :=
        hℱ.2.1 t (X ⁻¹' s ∩ Gᶜ) hpart2_amb hpart2_null
      exact hpart1.union hpart2
    have hX_sm : StronglyMeasurable[ℱ t] X :=
      @Measurable.stronglyMeasurable Ω ℝ X (ℱ t) _ _ _ _ _ hX_F
    -- Part (B): L1 integrability of X via nonnegative dyadic approx of |x| + Fatou
    let Ym : ℕ → Ω → ℝ := fun m ω =>
      ∑ k ∈ Finset.range (m * 2 ^ m),
        ((k : ℝ) / (2 : ℝ) ^ m) * (N.N ω (I ×ˢ PrmFiniteCompensatedAdaptedHelpers.absCell B m k)).toReal
    have hYm_meas : ∀ m : ℕ, Measurable (Ym m) := fun m =>
      Finset.measurable_sum (Finset.range (m * 2 ^ m)) fun k _ =>
        measurable_const.mul
          (ENNReal.measurable_toReal.comp
            (N.measurable_eval (measurableSet_Ioc.prod
              (PrmFiniteCompensatedAdaptedHelpers.absCell_measurableSet hB m k))))
    have hYm_nn : ∀ m ω, 0 ≤ Ym m ω := fun m ω =>
      Finset.sum_nonneg fun k _ => mul_nonneg (by positivity) ENNReal.toReal_nonneg
    have hYm_int_bound : ∀ m : ℕ,
        ∫⁻ ω, ENNReal.ofReal (Ym m ω) ∂P ≤ ENNReal.ofReal ((t : ℝ) * ∫ x in B, |x| ∂ν) := by
      intro m
      have hterm_int : ∀ k ∈ Finset.range (m * 2 ^ m),
          Integrable (fun ω => ((k : ℝ) / (2 : ℝ) ^ m) *
            (N.N ω (I ×ˢ PrmFiniteCompensatedAdaptedHelpers.absCell B m k)).toReal) P := by
        intro k _
        have hkm := PrmFiniteCompensatedAdaptedHelpers.absCell_measurableSet hB m k
        have hkfin : ν (PrmFiniteCompensatedAdaptedHelpers.absCell B m k) < ⊤ :=
          lt_of_le_of_lt (measure_mono Set.inter_subset_left) hfinite
        exact (PrmFiniteCompensatedAdaptedHelpers.prm_count_first_moment P ν N t hkm hkfin).1.const_mul _
      have hYm_int : Integrable (Ym m) P := integrable_finsetSum _ hterm_int
      have hYm_mean : (∫ ω, Ym m ω ∂P) = (t : ℝ) * ∫ x in B, PrmFiniteCompensatedAdaptedHelpers.absApprox B m x ∂ν := by
        dsimp [Ym]
        rw [integral_finsetSum _ hterm_int]
        have hterm_mean : ∀ k ∈ Finset.range (m * 2 ^ m),
            (∫ ω, ((k : ℝ) / (2 : ℝ) ^ m) *
              (N.N ω (I ×ˢ PrmFiniteCompensatedAdaptedHelpers.absCell B m k)).toReal ∂P) =
              (t : ℝ) * (((k : ℝ) / (2 : ℝ) ^ m) *
                (ν (PrmFiniteCompensatedAdaptedHelpers.absCell B m k)).toReal) := by
          intro k _
          have hkm := PrmFiniteCompensatedAdaptedHelpers.absCell_measurableSet hB m k
          have hkfin : ν (PrmFiniteCompensatedAdaptedHelpers.absCell B m k) < ⊤ :=
            lt_of_le_of_lt (measure_mono Set.inter_subset_left) hfinite
          rw [integral_const_mul,
            (PrmFiniteCompensatedAdaptedHelpers.prm_count_first_moment P ν N t hkm hkfin).2]
          ring
        rw [Finset.sum_congr rfl hterm_mean, ← Finset.mul_sum]
        congr 1
        unfold PrmFiniteCompensatedAdaptedHelpers.absApprox
        have hνB_fin : IsFiniteMeasure (ν.restrict B) := ⟨by rw [Measure.restrict_apply_univ]; exact hfinite⟩
        rw [integral_finsetSum]
        · refine Finset.sum_congr rfl fun k _ => ?_
          have hkm := PrmFiniteCompensatedAdaptedHelpers.absCell_measurableSet hB m k
          rw [integral_indicator_const _ hkm, Measure.real, Measure.restrict_apply hkm,
            Set.inter_eq_left.mpr (show PrmFiniteCompensatedAdaptedHelpers.absCell B m k ⊆ B from Set.inter_subset_left),
            smul_eq_mul, mul_comm]
        · intro k _
          exact (integrable_const _).indicator (PrmFiniteCompensatedAdaptedHelpers.absCell_measurableSet hB m k)
      have hν_le : (∫ x in B, PrmFiniteCompensatedAdaptedHelpers.absApprox B m x ∂ν) ≤ ∫ x in B, |x| ∂ν := by
        have hνB_fin : IsFiniteMeasure (ν.restrict B) := ⟨by rw [Measure.restrict_apply_univ]; exact hfinite⟩
        have hmeas_u : Measurable (PrmFiniteCompensatedAdaptedHelpers.absApprox B m) :=
          Finset.measurable_sum (Finset.range (m * 2 ^ m))
            (f := fun k x => (PrmFiniteCompensatedAdaptedHelpers.absCell B m k).indicator
              (fun _ => (k : ℝ) / (2 : ℝ) ^ m) x)
            fun k _ => measurable_const.indicator (PrmFiniteCompensatedAdaptedHelpers.absCell_measurableSet hB m k)
        have hint_u : Integrable (PrmFiniteCompensatedAdaptedHelpers.absApprox B m) (ν.restrict B) :=
          hfirst.abs.mono' hmeas_u.aestronglyMeasurable (Eventually.of_forall fun x => by
            rw [Real.norm_eq_abs, abs_of_nonneg (PrmFiniteCompensatedAdaptedHelpers.absApprox_nonneg B m x)]
            exact PrmFiniteCompensatedAdaptedHelpers.absApprox_le_abs B m x)
        exact integral_mono hint_u hfirst.abs (PrmFiniteCompensatedAdaptedHelpers.absApprox_le_abs B m)
      rw [← ofReal_integral_eq_lintegral_ofReal hYm_int (Eventually.of_forall (hYm_nn m)), hYm_mean]
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hν_le t.coe_nonneg)
    have hYm_tendsto_on_G : ∀ ω ∈ G,
        Tendsto (fun m => Ym m ω) atTop (nhds (∫ z in W, |z.2| ∂(N.N ω))) := by
      intro ω hω
      obtain ⟨nW, R₀, hnW, hae_bd⟩ := hG_compact ω hω
      have hfinW : IsFiniteMeasure ((N.N ω).restrict W) :=
        ⟨by rw [Measure.restrict_apply_univ, hnW]; exact ENNReal.natCast_lt_top nW⟩
      have hint_abs : Integrable (fun z : ℝ × ℝ => |z.2|) ((N.N ω).restrict W) :=
        Integrable.of_bound (continuous_abs.comp continuous_snd).aestronglyMeasurable (R₀ : ℝ)
          (hae_bd.mono fun z hz => by rw [Real.norm_eq_abs, abs_abs]; exact hz.2)
      have hYm_eq_int : ∀ m : ℕ, Ym m ω =
          ∫ z in W, PrmFiniteCompensatedAdaptedHelpers.absApprox B m z.2 ∂(N.N ω) := by
        intro m
        dsimp [Ym]
        unfold PrmFiniteCompensatedAdaptedHelpers.absApprox
        rw [integral_finsetSum]
        · refine Finset.sum_congr rfl fun k _ => ?_
          have hkm := PrmFiniteCompensatedAdaptedHelpers.absCell_measurableSet hB m k
          have hcomp : (fun z : ℝ × ℝ =>
              (PrmFiniteCompensatedAdaptedHelpers.absCell B m k).indicator
                (fun _ => (k : ℝ) / (2 : ℝ) ^ m) z.2) =
              (Set.univ ×ˢ PrmFiniteCompensatedAdaptedHelpers.absCell B m k).indicator
                (fun _ => (k : ℝ) / (2 : ℝ) ^ m) := by
            funext z
            by_cases hz : z.2 ∈ PrmFiniteCompensatedAdaptedHelpers.absCell B m k
            · simp [Set.indicator_of_mem, hz]
            · simp [Set.indicator_of_notMem, hz]
          rw [hcomp, integral_indicator_const _ (MeasurableSet.univ.prod hkm)]
          rw [Measure.real, Measure.restrict_apply (MeasurableSet.univ.prod hkm)]
          have hinter : (Set.univ ×ˢ PrmFiniteCompensatedAdaptedHelpers.absCell B m k) ∩ W =
              I ×ˢ PrmFiniteCompensatedAdaptedHelpers.absCell B m k := by
            ext z
            simp only [W, Set.mem_inter_iff, Set.mem_prod, Set.mem_univ, true_and]
            constructor
            · rintro ⟨hz1, hz2, _⟩; exact ⟨hz2, hz1⟩
            · rintro ⟨hz1, hz2⟩; exact ⟨hz2, hz1, Set.inter_subset_left hz2⟩
          rw [hinter, smul_eq_mul, mul_comm]
        · intro k _
          have hkm := PrmFiniteCompensatedAdaptedHelpers.absCell_measurableSet hB m k
          have hmeas : Measurable (fun z : ℝ × ℝ =>
              (PrmFiniteCompensatedAdaptedHelpers.absCell B m k).indicator
                (fun _ => (k : ℝ) / (2 : ℝ) ^ m) z.2) :=
            (measurable_const.indicator hkm).comp measurable_snd
          refine Integrable.of_bound hmeas.aestronglyMeasurable
            ((k : ℝ) / (2 : ℝ) ^ m) (Eventually.of_forall fun z => ?_)
          rw [Real.norm_eq_abs]
          by_cases hz : z.2 ∈ PrmFiniteCompensatedAdaptedHelpers.absCell B m k
          · rw [Set.indicator_of_mem hz, abs_of_nonneg (by positivity)]
          · rw [Set.indicator_of_notMem hz, abs_zero]; positivity
      rw [Metric.tendsto_nhds]
      intro ε hε
      have ht := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
      obtain ⟨M₂, hM₂⟩ := (ht.eventually (gt_mem_nhds (div_pos hε (by positivity : (0 : ℝ) < (nW : ℝ) + 1)))).exists
      rw [Filter.eventually_atTop]
      refine ⟨max (R₀ + 1) M₂, fun m hm => ?_⟩
      have hmR : R₀ + 1 ≤ m := le_trans (le_max_left _ _) hm
      have hm2 : M₂ ≤ m := le_trans (le_max_right _ _) hm
      have hint_m : Integrable (fun z : ℝ × ℝ => PrmFiniteCompensatedAdaptedHelpers.absApprox B m z.2)
          ((N.N ω).restrict W) := by
        have hmeas : Measurable (fun z : ℝ × ℝ => PrmFiniteCompensatedAdaptedHelpers.absApprox B m z.2) :=
          (Finset.measurable_sum (Finset.range (m * 2 ^ m))
            (f := fun k x => (PrmFiniteCompensatedAdaptedHelpers.absCell B m k).indicator
              (fun _ => (k : ℝ) / (2 : ℝ) ^ m) x)
            fun k _ => measurable_const.indicator (PrmFiniteCompensatedAdaptedHelpers.absCell_measurableSet hB m k)).comp
            measurable_snd
        exact hint_abs.mono' hmeas.aestronglyMeasurable (Eventually.of_forall fun z => by
          rw [Real.norm_eq_abs, abs_of_nonneg (PrmFiniteCompensatedAdaptedHelpers.absApprox_nonneg B m z.2)]
          exact PrmFiniteCompensatedAdaptedHelpers.absApprox_le_abs B m z.2)
      rw [Real.dist_eq, hYm_eq_int m, ← integral_sub hint_m hint_abs]
      have hnorm_le : ‖∫ z in W, (PrmFiniteCompensatedAdaptedHelpers.absApprox B m z.2 - |z.2|) ∂(N.N ω)‖ ≤
          ((1 : ℝ) / (2 : ℝ) ^ m) * ((N.N ω).restrict W).real Set.univ := by
        refine norm_integral_le_of_norm_le_const ?_
        filter_upwards [hae_bd] with z hz
        have hbdz : |z.2| < (m : ℝ) := lt_of_le_of_lt hz.2 (by exact_mod_cast Nat.lt_of_succ_le hmR)
        simpa only [Real.norm_eq_abs] using PrmFiniteCompensatedAdaptedHelpers.absApprox_sub_le hz.1 hbdz
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
    have hX_fin_int : HasFiniteIntegral X P := by
      unfold HasFiniteIntegral
      have hae_le : ∀ᵐ ω ∂P, ‖X ω‖ₑ ≤ Filter.liminf (fun m => ENNReal.ofReal (Ym m ω)) atTop := by
        filter_upwards [hae_G] with ω hω
        have hlim : Filter.liminf (fun m => ENNReal.ofReal (Ym m ω)) atTop =
            ENNReal.ofReal (∫ z in W, |z.2| ∂(N.N ω)) :=
          (ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hYm_tendsto_on_G ω hω)).liminf_eq
        rw [hlim, Real.enorm_eq_ofReal_abs]
        exact ENNReal.ofReal_le_ofReal (abs_integral_le_integral_abs)
      calc ∫⁻ ω, ‖X ω‖ₑ ∂P
          ≤ ∫⁻ ω, Filter.liminf (fun m => ENNReal.ofReal (Ym m ω)) atTop ∂P := lintegral_mono_ae hae_le
        _ ≤ Filter.liminf (fun m => ∫⁻ ω, ENNReal.ofReal (Ym m ω) ∂P) atTop :=
            MeasureTheory.lintegral_liminf_le fun m => ENNReal.measurable_ofReal.comp (hYm_meas m)
        _ ≤ ENNReal.ofReal ((t : ℝ) * ∫ x in B, |x| ∂ν) :=
            Filter.liminf_le_of_frequently_le' (Eventually.of_forall hYm_int_bound).frequently
        _ < ⊤ := ENNReal.ofReal_lt_top
    exact ⟨hX_sm, ⟨hX_amb.aestronglyMeasurable, hX_fin_int⟩⟩
  exact ⟨fun t => (hcore t).1.sub stronglyMeasurable_const,
    fun t => (hcore t).2.sub (integrable_const _)⟩
