-- Prove2me | solution 1 for KleywegtSAA.ExpRate.deviation_le_two_exp
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T01:59:12.813068+00:00
-- url     : https://prove2.me/submissions/3d8cae4f-5ee2-430f-b277-8a1d40e93bf5

import Mathlib
import Definitions.Def_KleywegtSAA_ExpRate_Setting
import Theorems.Thm_KleywegtSAA_ExpRate_ld_upper_bound
import Theorems.Thm_KleywegtSAA_ExpRate_rateFn_pos

open MeasureTheory ProbabilityTheory Filter Topology
open KleywegtSAA.ExpRate

/-- One-sided exponential tail bound from the LD upper bound (2.4) and `I(a) > 0`. -/
lemma tail_le_exp {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (hYm : ∀ i, Measurable (Y i)) (hind : iIndepFun Y P)
    (hid : ∀ i, IdentDistrib (Y i) (Y 0) P P) (hY : Integrable (Y 0) P)
    (hA0 : (0 : ℝ) ∈ interior (integrableExpSet (Y 0) P)) (a : ℝ) (ha : ∫ ω, Y 0 ω ∂P < a) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ N : ℕ, 1 ≤ N →
      P {ω | a ≤ sampleMean Y N ω} ≤ ENNReal.ofReal (Real.exp (-((N : ℝ) * γ))) := by
  have hI := rateFn_pos P (Y 0) hY hA0 a ha
  obtain ⟨γ, hγ0, hγI⟩ := EReal.lt_iff_exists_real_btwn.1 hI
  refine ⟨γ, by exact_mod_cast hγ0, fun N hN => ?_⟩
  have hld := ld_upper_bound P Y hYm hind hid N hN a
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  by_cases hp : P {ω | a ≤ sampleMean Y N ω} = 0
  · rw [hp]; exact zero_le
  have hpne : P {ω | a ≤ sampleMean Y N ω} ≠ ⊤ := measure_ne_top _ _
  have hppos : 0 < (P {ω | a ≤ sampleMean Y N ω}).toReal := ENNReal.toReal_pos hp hpne
  have h1 : ((1 / (N : ℝ) : ℝ) : EReal) * ENNReal.log (P {ω | a ≤ sampleMean Y N ω}) ≤
      ((-γ : ℝ) : EReal) := by
    refine hld.trans ?_
    rw [EReal.coe_neg]
    exact EReal.neg_le_neg_iff.2 hγI.le
  rw [← ENNReal.ofReal_toReal hpne, ENNReal.log_ofReal_of_pos hppos, ← EReal.coe_mul,
    EReal.coe_le_coe_iff] at h1
  rw [← ENNReal.ofReal_toReal hpne]
  apply ENNReal.ofReal_le_ofReal
  rw [← Real.log_le_iff_le_exp hppos]
  rw [one_div, inv_mul_le_iff₀ hNpos] at h1
  linarith

lemma integrableExpSet_neg {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → ℝ) :
    integrableExpSet (fun ω => -X ω) P = Neg.neg ⁻¹' integrableExpSet X P := by
  ext t
  simp only [integrableExpSet, Set.mem_preimage, Set.mem_ofPred_eq]
  constructor <;> intro h <;> convert h using 3 <;> ring

theorem solution
    {X : Type*} (S : Finset X) (hS : S.Nonempty)
    {𝒲 : Type*} [MeasurableSpace 𝒲] (G : X → 𝒲 → ℝ) (hG : ∀ x ∈ S, Measurable (G x))
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℕ → Ω → 𝒲) (hWm : ∀ n, Measurable (W n)) (hind : iIndepFun W P)
    (hid : ∀ n, IdentDistrib (W n) (W 0) P P)
    (hint : ∀ x ∈ S, Integrable (fun ω => G x (W 0 ω)) P)
    (hA : AssumptionA S G P W) (r : ℝ) (hr : 0 < r) :
    ∀ x ∈ S, ∃ γx γx' : ℝ, 0 < γx ∧ 0 < γx' ∧ ∀ N : ℕ, 1 ≤ N →
      P {ω | r ≤ |sampleObj G W N ω x - trueObj G P W x|} ≤
        ENNReal.ofReal (Real.exp (-((N : ℝ) * γx)) + Real.exp (-((N : ℝ) * γx'))) := by
  intro x hx
  set Y : ℕ → Ω → ℝ := fun i ω => G x (W i ω) with hY_def
  set Y' : ℕ → Ω → ℝ := fun i ω => -G x (W i ω) with hY'_def
  have hYm : ∀ i, Measurable (Y i) := fun i => (hG x hx).comp (hWm i)
  have hY'm : ∀ i, Measurable (Y' i) := fun i => ((hG x hx).comp (hWm i)).neg
  have hYind : iIndepFun Y P := hind.comp (fun _ => G x) (fun _ => hG x hx)
  have hY'ind : iIndepFun Y' P := hind.comp (fun _ w => -G x w) (fun _ => (hG x hx).neg)
  have hYid : ∀ i, IdentDistrib (Y i) (Y 0) P P := fun i => (hid i).comp (hG x hx)
  have hY'id : ∀ i, IdentDistrib (Y' i) (Y' 0) P P := fun i => (hid i).comp (hG x hx).neg
  have hYint : Integrable (Y 0) P := hint x hx
  have hY'int : Integrable (Y' 0) P := (hint x hx).neg
  have hYA : (0 : ℝ) ∈ interior (integrableExpSet (Y 0) P) := hA x hx
  have hY'A : (0 : ℝ) ∈ interior (integrableExpSet (Y' 0) P) := by
    have : integrableExpSet (Y' 0) P = Neg.neg ⁻¹' integrableExpSet (Y 0) P :=
      integrableExpSet_neg P (Y 0)
    rw [this]
    exact preimage_interior_subset_interior_preimage continuous_neg (by simpa using hYA)
  have hg : trueObj G P W x = ∫ ω, Y 0 ω ∂P := rfl
  obtain ⟨γx, hγx, hbx⟩ := tail_le_exp P Y hYm hYind hYid hYint hYA (trueObj G P W x + r)
    (by rw [hg]; linarith)
  obtain ⟨γx', hγx', hbx'⟩ := tail_le_exp P Y' hY'm hY'ind hY'id hY'int hY'A
    (-trueObj G P W x + r) (by
      rw [hg, show (fun ω => Y' 0 ω) = fun ω => -Y 0 ω from rfl, integral_neg]; linarith)
  refine ⟨γx, γx', hγx, hγx', fun N hN => ?_⟩
  have hsub : {ω | r ≤ |sampleObj G W N ω x - trueObj G P W x|} ⊆
      {ω | trueObj G P W x + r ≤ sampleMean Y N ω} ∪
        {ω | -trueObj G P W x + r ≤ sampleMean Y' N ω} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω
    have e1 : sampleMean Y N ω = sampleObj G W N ω x := rfl
    have e2 : sampleMean Y' N ω = -sampleObj G W N ω x := by
      simp only [sampleMean, sampleObj, hY'_def, Finset.sum_neg_distrib, mul_neg]
    rcases le_abs'.1 hω with h | h
    · right
      simp only [Set.mem_ofPred_eq, e2]
      linarith
    · left
      simp only [Set.mem_ofPred_eq, e1]
      linarith
  calc P {ω | r ≤ |sampleObj G W N ω x - trueObj G P W x|}
      ≤ P ({ω | trueObj G P W x + r ≤ sampleMean Y N ω} ∪
          {ω | -trueObj G P W x + r ≤ sampleMean Y' N ω}) := measure_mono hsub
    _ ≤ P {ω | trueObj G P W x + r ≤ sampleMean Y N ω} +
          P {ω | -trueObj G P W x + r ≤ sampleMean Y' N ω} := measure_union_le _ _
    _ ≤ ENNReal.ofReal (Real.exp (-((N : ℝ) * γx))) +
          ENNReal.ofReal (Real.exp (-((N : ℝ) * γx'))) := add_le_add (hbx N hN) (hbx' N hN)
    _ = ENNReal.ofReal (Real.exp (-((N : ℝ) * γx)) + Real.exp (-((N : ℝ) * γx'))) :=
          (ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le).symm
