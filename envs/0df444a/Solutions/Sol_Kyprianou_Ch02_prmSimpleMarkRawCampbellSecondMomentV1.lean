-- Prove2me | solution 1 for Kyprianou.Ch02.prmSimpleMarkRawCampbellSecondMomentV1
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-23T18:55:28.164605+00:00
-- url     : https://prove2.me/submissions/76d89ffe-24ab-4641-9823-b7521930d735

import Mathlib
import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_LeanLevy_Processes_LevyProcess

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

set_option autoImplicit false

namespace PrmSimpleCampbellHelpers

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

private lemma hasSum_exp_real (x : ℝ) :
    HasSum (fun n : ℕ => x ^ n / (n.factorial : ℝ)) (Real.exp x) := by
  rw [Real.exp_eq_exp_ℝ]
  exact NormedSpace.expSeries_div_hasSum_exp x

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
  have h := (hasSum_exp_real (μ : ℝ)).mul_left (Real.exp (-(μ : ℝ)) * (μ : ℝ))
  have hval : Real.exp (-(μ : ℝ)) * (μ : ℝ) * Real.exp (μ : ℝ) = (μ : ℝ) := by
    calc Real.exp (-(μ : ℝ)) * (μ : ℝ) * Real.exp (μ : ℝ)
        = (μ : ℝ) * (Real.exp (-(μ : ℝ)) * Real.exp (μ : ℝ)) := by ring
      _ = (μ : ℝ) * Real.exp (-(μ : ℝ) + (μ : ℝ)) := by rw [← Real.exp_add]
      _ = (μ : ℝ) := by simp
  rwa [hval] at h

private lemma hasSum_poisson_falling2 (μ : ℝ≥0) :
    HasSum (fun n : ℕ => Real.exp (-(μ : ℝ)) * (μ : ℝ) ^ n / (n.factorial : ℝ) * ((n * (n - 1) : ℕ) : ℝ))
      ((μ : ℝ) ^ 2) := by
  rw [← hasSum_nat_add_iff' 2]
  have hinit : ∑ i ∈ Finset.range 2,
      Real.exp (-(μ : ℝ)) * (μ : ℝ) ^ i / (i.factorial : ℝ) * ((i * (i - 1) : ℕ) : ℝ) = 0 := by
    simp [Finset.sum_range_succ]
  rw [hinit, sub_zero]
  have hterm : (fun n : ℕ =>
      Real.exp (-(μ : ℝ)) * (μ : ℝ) ^ (n + 2) / ((n + 2).factorial : ℝ) *
        (((n + 2) * (n + 2 - 1) : ℕ) : ℝ)) =
      fun n : ℕ => (Real.exp (-(μ : ℝ)) * (μ : ℝ) ^ 2) * ((μ : ℝ) ^ n / (n.factorial : ℝ)) := by
    funext n
    have hsub : n + 2 - 1 = n + 1 := by omega
    rw [hsub, pow_add, Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    have hne1 : ((n : ℝ) + 1) ≠ 0 := by positivity
    have hne2 : ((n : ℝ) + 2) ≠ 0 := by positivity
    field_simp; ring
  rw [hterm]
  have h := (hasSum_exp_real (μ : ℝ)).mul_left (Real.exp (-(μ : ℝ)) * (μ : ℝ) ^ 2)
  have hval : Real.exp (-(μ : ℝ)) * (μ : ℝ) ^ 2 * Real.exp (μ : ℝ) = (μ : ℝ) ^ 2 := by
    calc Real.exp (-(μ : ℝ)) * (μ : ℝ) ^ 2 * Real.exp (μ : ℝ)
        = (μ : ℝ) ^ 2 * (Real.exp (-(μ : ℝ)) * Real.exp (μ : ℝ)) := by ring
      _ = (μ : ℝ) ^ 2 * Real.exp (-(μ : ℝ) + (μ : ℝ)) := by rw [← Real.exp_add]
      _ = (μ : ℝ) ^ 2 := by simp
  rwa [hval] at h

private lemma hasSum_poisson_second (μ : ℝ≥0) :
    HasSum (fun n : ℕ => Real.exp (-(μ : ℝ)) * (μ : ℝ) ^ n / (n.factorial : ℝ) * ((n : ℝ) ^ 2))
      ((μ : ℝ) + (μ : ℝ) ^ 2) := by
  have hadd := (hasSum_poisson_first μ).add (hasSum_poisson_falling2 μ)
  have hfun : (fun n : ℕ =>
      Real.exp (-(μ : ℝ)) * (μ : ℝ) ^ n / (n.factorial : ℝ) * (n : ℝ) +
      Real.exp (-(μ : ℝ)) * (μ : ℝ) ^ n / (n.factorial : ℝ) * ((n * (n - 1) : ℕ) : ℝ)) =
      fun n : ℕ => Real.exp (-(μ : ℝ)) * (μ : ℝ) ^ n / (n.factorial : ℝ) * ((n : ℝ) ^ 2) := by
    funext n
    have hnat : (n : ℝ) + ((n * (n - 1) : ℕ) : ℝ) = (n : ℝ) ^ 2 := by
      cases n with
      | zero => simp
      | succ m =>
        simp only [Nat.add_sub_cancel, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
        ring
    rw [← mul_add, hnat]
  rwa [hfun] at hadd

private lemma poisson_integrable_id (μ : ℝ≥0) :
    Integrable (fun n : ℕ => (n : ℝ)) (ProbabilityTheory.poissonMeasure μ) := by
  rw [ProbabilityTheory.integrable_poissonMeasure_iff]
  have h := (hasSum_poisson_first μ).summable
  exact h.congr fun n => by rw [Real.norm_eq_abs, Nat.abs_cast]

private lemma poisson_integrable_sq (μ : ℝ≥0) :
    Integrable (fun n : ℕ => (n : ℝ) ^ 2) (ProbabilityTheory.poissonMeasure μ) := by
  rw [ProbabilityTheory.integrable_poissonMeasure_iff]
  have h := (hasSum_poisson_second μ).summable
  exact h.congr fun n => by rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (n : ℝ))]

private lemma poisson_integral_id (μ : ℝ≥0) :
    ∫ n : ℕ, (n : ℝ) ∂(ProbabilityTheory.poissonMeasure μ) = (μ : ℝ) := by
  rw [ProbabilityTheory.integral_poissonMeasure]
  simpa only [smul_eq_mul] using (hasSum_poisson_first μ).tsum_eq

private lemma poisson_integral_sq (μ : ℝ≥0) :
    ∫ n : ℕ, ((n : ℝ) ^ 2) ∂(ProbabilityTheory.poissonMeasure μ) = (μ : ℝ) + (μ : ℝ) ^ 2 := by
  rw [ProbabilityTheory.integral_poissonMeasure]
  simpa only [smul_eq_mul] using (hasSum_poisson_second μ).tsum_eq

private lemma prm_count_moments
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (t : ℝ≥0) {A : Set ℝ} (hA : MeasurableSet A) (hAfin : ν A < ⊤) :
    let W := Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ A
    let lamA := (t : ℝ) * (ν A).toReal
    Integrable (fun ω => (N.N ω W).toReal) P ∧
    Integrable (fun ω => (N.N ω W).toReal ^ 2) P ∧
    (∫ ω, (N.N ω W).toReal ∂P) = lamA ∧
    (∫ ω, (N.N ω W).toReal ^ 2 ∂P) = lamA + lamA ^ 2 := by
  intro W lamA
  have hW : MeasurableSet W := measurableSet_Ioc.prod hA
  have hWfin : LevyStochCalc.Poisson.referenceIntensity ν W ≠ ⊤ :=
    referenceIntensity_Ioc_prod_ne_top ν t hAfin
  let μ : ℝ≥0 := (LevyStochCalc.Poisson.referenceIntensity ν W).toNNReal
  have hμ_eq : (μ : ℝ) = lamA := by
    have h1 : (μ : ℝ) = (LevyStochCalc.Poisson.referenceIntensity ν W).toReal := rfl
    rw [h1, referenceIntensity_Ioc_prod_toReal ν t]
  have hN_meas : Measurable (fun ω => N.N ω W) := N.measurable_eval hW
  have hcast_meas : Measurable (fun n : ℕ => (n : ℝ≥0∞)) := measurable_of_countable _
  have hlaw : P.map (fun ω => N.N ω W) =
      (ProbabilityTheory.poissonMeasure μ).map (fun n : ℕ => (n : ℝ≥0∞)) :=
    N.poisson_law hW hWfin
  have htoReal_meas : Measurable (fun r : ℝ≥0∞ => r.toReal) := ENNReal.measurable_toReal
  have htoReal_sq_meas : Measurable (fun r : ℝ≥0∞ => r.toReal ^ 2) :=
    (continuous_pow 2).measurable.comp ENNReal.measurable_toReal
  have hint1 : Integrable (fun ω => (N.N ω W).toReal) P := by
    change Integrable ((fun r : ℝ≥0∞ => r.toReal) ∘ fun ω => N.N ω W) P
    rw [← integrable_map_measure htoReal_meas.aestronglyMeasurable hN_meas.aemeasurable, hlaw,
      integrable_map_measure htoReal_meas.aestronglyMeasurable hcast_meas.aemeasurable]
    simpa only [Function.comp_def, ENNReal.toReal_natCast] using poisson_integrable_id μ
  have hint2 : Integrable (fun ω => (N.N ω W).toReal ^ 2) P := by
    change Integrable ((fun r : ℝ≥0∞ => r.toReal ^ 2) ∘ fun ω => N.N ω W) P
    rw [← integrable_map_measure htoReal_sq_meas.aestronglyMeasurable hN_meas.aemeasurable, hlaw,
      integrable_map_measure htoReal_sq_meas.aestronglyMeasurable hcast_meas.aemeasurable]
    simpa only [Function.comp_def, ENNReal.toReal_natCast] using poisson_integrable_sq μ
  have hmean : (∫ ω, (N.N ω W).toReal ∂P) = lamA := by
    have h1 : ∫ ω, (N.N ω W).toReal ∂P = ∫ r, r.toReal ∂(P.map (fun ω => N.N ω W)) :=
      (integral_map hN_meas.aemeasurable htoReal_meas.aestronglyMeasurable).symm
    have h2 : ∫ r, r.toReal ∂((ProbabilityTheory.poissonMeasure μ).map (fun n : ℕ => (n : ℝ≥0∞))) =
        ∫ n : ℕ, ((n : ℝ≥0∞).toReal) ∂(ProbabilityTheory.poissonMeasure μ) :=
      integral_map hcast_meas.aemeasurable htoReal_meas.aestronglyMeasurable
    rw [h1, hlaw, h2]
    simp only [ENNReal.toReal_natCast, poisson_integral_id μ, hμ_eq]
  have hsq : (∫ ω, (N.N ω W).toReal ^ 2 ∂P) = lamA + lamA ^ 2 := by
    have h1 : ∫ ω, (N.N ω W).toReal ^ 2 ∂P = ∫ r, r.toReal ^ 2 ∂(P.map (fun ω => N.N ω W)) :=
      (integral_map hN_meas.aemeasurable htoReal_sq_meas.aestronglyMeasurable).symm
    have h2 : ∫ r, r.toReal ^ 2 ∂((ProbabilityTheory.poissonMeasure μ).map (fun n : ℕ => (n : ℝ≥0∞))) =
        ∫ n : ℕ, ((n : ℝ≥0∞).toReal ^ 2) ∂(ProbabilityTheory.poissonMeasure μ) :=
      integral_map hcast_meas.aemeasurable htoReal_sq_meas.aestronglyMeasurable
    rw [h1, hlaw, h2]
    simp only [ENNReal.toReal_natCast, poisson_integral_sq μ, hμ_eq]
  exact ⟨hint1, hint2, hmean, hsq⟩

end PrmSimpleCampbellHelpers

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B) (hfinite : ν B < ⊤)
    (g : SimpleFunc ℝ ℝ) (t : ℝ≥0) :
    (∫ ω, (∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B),
      g z.2 ∂(N.N ω)) ^ 2 ∂P) =
      (t : ℝ) * (∫ x in B, (g x) ^ 2 ∂ν) +
        ((t : ℝ) * (∫ x in B, g x ∂ν)) ^ 2 := by
  let I : Set ℝ := Set.Ioc (0 : ℝ) (t : ℝ)
  let W : Set (ℝ × ℝ) := I ×ˢ B
  have hW : MeasurableSet W := measurableSet_Ioc.prod hB
  have hWfin : LevyStochCalc.Poisson.referenceIntensity ν W ≠ ⊤ :=
    PrmSimpleCampbellHelpers.referenceIntensity_Ioc_prod_ne_top ν t hfinite
  let S : Finset ℝ := g.range
  let A : ℝ → Set ℝ := fun r => B ∩ g ⁻¹' {r}
  have hA_meas : ∀ r : ℝ, MeasurableSet (A r) := fun r => hB.inter (g.measurableSet_fiber r)
  have hA_sub : ∀ r : ℝ, A r ⊆ B := fun _ => Set.inter_subset_left
  have hA_fin : ∀ r : ℝ, ν (A r) < ⊤ := fun r =>
    lt_of_le_of_lt (measure_mono (hA_sub r)) hfinite
  have hA_disj : Pairwise (fun r₁ r₂ : ℝ => Disjoint (A r₁) (A r₂)) := by
    intro r₁ r₂ hne
    rw [Set.disjoint_left]
    intro x hx₁ hx₂
    have h1 : g x = r₁ := hx₁.2
    have h2 : g x = r₂ := hx₂.2
    exact hne (h1.symm.trans h2)
  -- Pointwise fiber decomposition of g and g^2 on B
  have hg_eq : ∀ x ∈ B, g x = ∑ r ∈ S, (A r).indicator (fun _ => r) x := by
    intro x hxB
    rw [Finset.sum_eq_single (g x)]
    · rw [Set.indicator_of_mem (show x ∈ A (g x) from ⟨hxB, rfl⟩)]
    · intro r _ hne
      apply Set.indicator_of_notMem
      intro hxr
      exact hne hxr.2.symm
    · intro hnot
      exact absurd (g.mem_range_self x) hnot
  have hg2_eq : ∀ x ∈ B, (g x) ^ 2 = ∑ r ∈ S, (A r).indicator (fun _ => r ^ 2) x := by
    intro x hxB
    rw [Finset.sum_eq_single (g x)]
    · rw [Set.indicator_of_mem (show x ∈ A (g x) from ⟨hxB, rfl⟩)]
    · intro r _ hne
      apply Set.indicator_of_notMem
      intro hxr
      exact hne hxr.2.symm
    · intro hnot
      exact absurd (g.mem_range_self x) hnot
  -- RHS integrals over (B, ν)
  have hν_fin : IsFiniteMeasure (ν.restrict B) := ⟨by rw [Measure.restrict_apply_univ]; exact hfinite⟩
  have hint_g : (∫ x in B, g x ∂ν) = ∑ r ∈ S, r * (ν (A r)).toReal := by
    rw [setIntegral_congr_fun hB hg_eq, integral_finsetSum]
    · refine Finset.sum_congr rfl fun r _ => ?_
      rw [integral_indicator_const _ (hA_meas r), Measure.real, Measure.restrict_apply (hA_meas r),
        Set.inter_eq_left.mpr (hA_sub r), smul_eq_mul, mul_comm]
    · intro r _
      exact (integrable_const r).indicator (hA_meas r)
  have hint_g2 : (∫ x in B, (g x) ^ 2 ∂ν) = ∑ r ∈ S, r ^ 2 * (ν (A r)).toReal := by
    rw [setIntegral_congr_fun hB hg2_eq, integral_finsetSum]
    · refine Finset.sum_congr rfl fun r _ => ?_
      rw [integral_indicator_const _ (hA_meas r), Measure.real, Measure.restrict_apply (hA_meas r),
        Set.inter_eq_left.mpr (hA_sub r), smul_eq_mul, mul_comm]
    · intro r _
      exact (integrable_const (r ^ 2)).indicator (hA_meas r)
  -- Fiber count random variables C r ω = (N.N ω (I ×ˢ A r)).toReal and intensities λ r = t * ν(A r)
  let C : ℝ → Ω → ℝ := fun r ω => (N.N ω (I ×ˢ A r)).toReal
  let lam : ℝ → ℝ := fun r => (t : ℝ) * (ν (A r)).toReal
  have hC_meas : ∀ r : ℝ, Measurable (C r) := fun r =>
    ENNReal.measurable_toReal.comp (N.measurable_eval (measurableSet_Ioc.prod (hA_meas r)))
  have hC_mom : ∀ r : ℝ,
      Integrable (C r) P ∧ Integrable (fun ω => (C r ω) ^ 2) P ∧
      (∫ ω, C r ω ∂P) = lam r ∧ (∫ ω, (C r ω) ^ 2 ∂P) = lam r + (lam r) ^ 2 :=
    fun r => PrmSimpleCampbellHelpers.prm_count_moments P ν N t (hA_meas r) (hA_fin r)
  -- Pairwise independence of fiber counts C r₁ ⟂ᵢ C r₂ for r₁ ≠ r₂
  have hC_indep : ∀ r₁ r₂ : ℝ, r₁ ≠ r₂ → IndepFun (C r₁) (C r₂) P := by
    intro r₁ r₂ hne
    let pair : Bool → Set (ℝ × ℝ) := fun b => if b then I ×ˢ A r₁ else I ×ˢ A r₂
    have hpair_meas : ∀ b : Bool, MeasurableSet (pair b) := by
      intro b; cases b <;> exact measurableSet_Ioc.prod (hA_meas _)
    have hpair_disj : Pairwise (fun b₁ b₂ : Bool => Disjoint (pair b₁) (pair b₂)) := by
      intro b₁ b₂ hne_b
      cases b₁ <;> cases b₂
      · exact absurd rfl hne_b
      · exact Set.disjoint_left.mpr fun z hz₁ hz₂ =>
          Set.disjoint_left.mp (hA_disj hne.symm) hz₁.2 hz₂.2
      · exact Set.disjoint_left.mpr fun z hz₁ hz₂ =>
          Set.disjoint_left.mp (hA_disj hne) hz₁.2 hz₂.2
      · exact absurd rfl hne_b
    have hi := (N.independent_disjoint pair hpair_meas hpair_disj).comp
      (fun _ => ENNReal.toReal) (fun _ => ENNReal.measurable_toReal)
    have hind := hi.indepFun (by decide : (true : Bool) ≠ false)
    simpa only [Function.comp_def, pair, ite_true, Bool.false_eq_true, ite_false] using hind
  -- Pairwise product integrability and expectation formula E[C r₁ * C r₂] = δ_{r₁,r₂} λ_{r₁} + λ_{r₁} λ_{r₂}
  have hC_prod_int : ∀ r₁ r₂ : ℝ, Integrable (fun ω => C r₁ ω * C r₂ ω) P := by
    intro r₁ r₂
    by_cases h : r₁ = r₂
    · subst h
      simpa only [sq] using (hC_mom r₁).2.1
    · exact (hC_indep r₁ r₂ h).integrable_mul (hC_mom r₁).1 (hC_mom r₂).1
  have hC_prod_mean : ∀ r₁ r₂ : ℝ,
      (∫ ω, C r₁ ω * C r₂ ω ∂P) = (if r₁ = r₂ then lam r₁ else 0) + lam r₁ * lam r₂ := by
    intro r₁ r₂
    by_cases h : r₁ = r₂
    · subst h
      rw [if_pos rfl]
      have hsq : (fun ω => C r₁ ω * C r₁ ω) = fun ω => (C r₁ ω) ^ 2 := by funext ω; ring
      rw [hsq, (hC_mom r₁).2.2.2]
      ring
    · rw [if_neg h, zero_add]
      have hmul := (hC_indep r₁ r₂ h).integral_fun_mul_eq_mul_integral
        (hC_meas r₁).aestronglyMeasurable (hC_meas r₂).aestronglyMeasurable
      rw [hmul, (hC_mom r₁).2.2.1, (hC_mom r₂).2.2.1]
  -- Pathwise integral identity for P-a.e. ω: ∫ z in W, g z.2 ∂(N.N ω) = ∑ r ∈ S, r * C r ω
  have hae_int : ∀ᵐ ω ∂P,
      (∫ z in W, g z.2 ∂(N.N ω)) = ∑ r ∈ S, r * C r ω := by
    filter_upwards [N.integer_valued hW hWfin] with ω hω
    obtain ⟨nW, hnW⟩ := hω
    have hfinW : IsFiniteMeasure ((N.N ω).restrict W) :=
      ⟨by rw [Measure.restrict_apply_univ, hnW]; exact ENNReal.natCast_lt_top nW⟩
    have hcongr : (∫ z in W, g z.2 ∂(N.N ω)) =
        ∫ z in W, (∑ r ∈ S, (A r).indicator (fun _ => r) z.2) ∂(N.N ω) :=
      setIntegral_congr_fun hW fun z hz => hg_eq z.2 hz.2
    rw [hcongr, integral_finsetSum]
    · refine Finset.sum_congr rfl fun r _ => ?_
      have hcomp : (fun z : ℝ × ℝ => (A r).indicator (fun _ => r) z.2) =
          (Set.univ ×ˢ A r).indicator (fun _ => r) := by
        funext z
        by_cases hz : z.2 ∈ A r
        · simp [Set.indicator_of_mem, hz]
        · simp [Set.indicator_of_notMem, hz]
      rw [hcomp, integral_indicator_const _ (MeasurableSet.univ.prod (hA_meas r))]
      rw [Measure.real, Measure.restrict_apply (MeasurableSet.univ.prod (hA_meas r))]
      have hinter : (Set.univ ×ˢ A r) ∩ W = I ×ˢ A r := by
        ext z
        simp only [W, Set.mem_inter_iff, Set.mem_prod, Set.mem_univ, true_and]
        constructor
        · rintro ⟨hz1, hz2, _⟩; exact ⟨hz2, hz1⟩
        · rintro ⟨hz1, hz2⟩; exact ⟨hz2, hz1, hA_sub r hz2⟩
      rw [hinter, smul_eq_mul, mul_comm]
    · intro r _
      have hmeas : Measurable (fun z : ℝ × ℝ => (A r).indicator (fun _ => r) z.2) :=
        (measurable_const.indicator (hA_meas r)).comp measurable_snd
      refine Integrable.of_bound hmeas.aestronglyMeasurable |r| (Eventually.of_forall fun z => ?_)
      rw [Real.norm_eq_abs]
      by_cases hz : z.2 ∈ A r
      · simp [Set.indicator_of_mem hz]
      · simp [Set.indicator_of_notMem hz]
  -- Expand square and integrate term-by-term
  have hae_sq : ∀ᵐ ω ∂P,
      (∫ z in W, g z.2 ∂(N.N ω)) ^ 2 =
        ∑ r₁ ∈ S, ∑ r₂ ∈ S, (r₁ * r₂) * (C r₁ ω * C r₂ ω) := by
    filter_upwards [hae_int] with ω hω
    rw [hω, sq, Finset.sum_mul]
    refine Finset.sum_congr rfl fun r₁ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r₂ _ => by ring
  rw [integral_congr_ae hae_sq]
  rw [integral_finsetSum]
  · have hinner : ∀ r₁ ∈ S,
        (∫ ω, ∑ r₂ ∈ S, (r₁ * r₂) * (C r₁ ω * C r₂ ω) ∂P) =
          r₁ ^ 2 * lam r₁ + ∑ r₂ ∈ S, (r₁ * lam r₁) * (r₂ * lam r₂) := by
      intro r₁ hr₁
      rw [integral_finsetSum]
      · have hterm : ∀ r₂ ∈ S,
            (∫ ω, (r₁ * r₂) * (C r₁ ω * C r₂ ω) ∂P) =
              (if r₁ = r₂ then r₁ ^ 2 * lam r₁ else 0) + (r₁ * lam r₁) * (r₂ * lam r₂) := by
          intro r₂ _
          rw [integral_const_mul, hC_prod_mean r₁ r₂]
          split_ifs with h
          · subst h; ring
          · ring
        rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
        congr 1
        rw [Finset.sum_ite_eq S r₁ (fun _ => r₁ ^ 2 * lam r₁), if_pos hr₁]
      · intro r₂ _
        exact (hC_prod_int r₁ r₂).const_mul (r₁ * r₂)
    rw [Finset.sum_congr rfl hinner, Finset.sum_add_distrib]
    have hdiag : (∑ r₁ ∈ S, r₁ ^ 2 * lam r₁) = (t : ℝ) * (∫ x in B, (g x) ^ 2 ∂ν) := by
      rw [hint_g2, Finset.mul_sum]
      refine Finset.sum_congr rfl fun r₁ _ => by dsimp [lam]; ring
    have hcross : (∑ r₁ ∈ S, ∑ r₂ ∈ S, (r₁ * lam r₁) * (r₂ * lam r₂)) =
        ((t : ℝ) * (∫ x in B, g x ∂ν)) ^ 2 := by
      rw [hint_g, Finset.mul_sum, sq, Finset.sum_mul]
      refine Finset.sum_congr rfl fun r₁ _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun r₂ _ => by dsimp [lam]; ring
    rw [hdiag, hcross]
  · intro r₁ _
    exact integrable_finsetSum S fun r₂ _ => (hC_prod_int r₁ r₂).const_mul (r₁ * r₂)
