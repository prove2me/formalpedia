-- Prove2me | solution 1 for HighConfRobust.fact_3_1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-24T10:57:55.121766+00:00
-- url     : https://prove2.me/submissions/bc6d0790-a447-4557-82a0-3331a64afe37

import Mathlib
import Definitions.Def_TotalVariationDist

open MeasureTheory

private lemma abs_le_tvDist {X : Type*} [MeasurableSpace X] (P Q : Measure X)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {s : Set X} (hs : MeasurableSet s) :
    |(P s).toReal - (Q s).toReal| ≤ MarkovChainCLT.tvDist P Q := by
  unfold MarkovChainCLT.tvDist
  refine le_csSup ⟨2, ?_⟩ ⟨s, hs, rfl⟩
  rintro r ⟨A, -, rfl⟩
  have h1 : (P A).toReal ≤ 1 := by
    rw [← ENNReal.toReal_one]; exact ENNReal.toReal_mono (by simp) prob_le_one
  have h2 : (Q A).toReal ≤ 1 := by
    rw [← ENNReal.toReal_one]; exact ENNReal.toReal_mono (by simp) prob_le_one
  have h3 := ENNReal.toReal_nonneg (a := P A)
  have h4 := ENNReal.toReal_nonneg (a := Q A)
  rw [abs_le]; constructor <;> linarith

theorem solution {X : Type*} [MeasurableSpace X] (P Q : Measure X)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (ε : ℝ)
    (hPQ : MarkovChainCLT.tvDist P Q ≤ ε) (hε : ε ≤ 1) :
    ∃ G H₁ H₂ : Measure X, IsProbabilityMeasure G ∧ IsProbabilityMeasure H₁ ∧
      IsProbabilityMeasure H₂ ∧
      P = ENNReal.ofReal (1 - ε) • G + ENNReal.ofReal ε • H₁ ∧
      Q = ENNReal.ofReal (1 - ε) • G + ENNReal.ofReal ε • H₂ := by
  have hε0 : 0 ≤ ε := (abs_nonneg _).trans ((abs_le_tvDist P Q MeasurableSet.empty).trans hPQ)
  -- case ε = 1
  rcases eq_or_lt_of_le hε with h1 | hlt1
  · subst h1
    refine ⟨P, P, Q, inferInstance, inferInstance, inferInstance, ?_, ?_⟩ <;> simp
  -- case ε = 0
  rcases eq_or_lt_of_le hε0 with h0 | hpos
  · subst h0
    have hPQeq : P = Q := by
      ext s hs
      have := (abs_le_tvDist P Q hs).trans hPQ
      have h : (P s).toReal = (Q s).toReal := by
        have := abs_nonneg ((P s).toReal - (Q s).toReal); linarith [abs_eq_zero.mp (le_antisymm (by linarith) this)]
      exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp h
    refine ⟨P, P, P, inferInstance, inferInstance, inferInstance, ?_, ?_⟩ <;> simp [hPQeq]
  -- main case 0 < ε < 1
  obtain ⟨s, hsH⟩ := exists_isHahnDecomposition P Q
  have hs := hsH.measurableSet
  set m : Measure X := P.restrict s + Q.restrict sᶜ with hm
  have hmP : m ≤ P := by
    calc m ≤ P.restrict s + P.restrict sᶜ := by
          rw [hm]; exact add_le_add le_rfl hsH.ge_on_compl
      _ = P := Measure.restrict_add_restrict_compl hs
  have hmQ : m ≤ Q := by
    calc m ≤ Q.restrict s + Q.restrict sᶜ := by
          rw [hm]; exact add_le_add hsH.le_on le_rfl
      _ = Q := Measure.restrict_add_restrict_compl hs
  have hmuniv : m Set.univ = P s + Q sᶜ := by
    simp [hm, Measure.restrict_apply MeasurableSet.univ]
  set c : ℝ := 1 - ε with hc
  have hcpos : 0 < c := by linarith
  -- c ≤ m(univ)
  have hcm : ENNReal.ofReal c ≤ m Set.univ := by
    have htv := (abs_le_tvDist P Q hs).trans hPQ
    have hQc : (Q sᶜ).toReal = 1 - (Q s).toReal := by
      rw [prob_compl_eq_one_sub hs, ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top]
      simp
    rw [hmuniv, ← ENNReal.ofReal_toReal (a := P s + Q sᶜ) (by finiteness)]
    apply ENNReal.ofReal_le_ofReal
    rw [ENNReal.toReal_add (by finiteness) (by finiteness), hQc]
    have := (abs_le.mp htv).1
    linarith
  have hm0 : m Set.univ ≠ 0 := (lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hcpos) hcm).ne'
  have hmtop : m Set.univ ≠ ⊤ := by rw [hmuniv]; finiteness
  set G : Measure X := (m Set.univ)⁻¹ • m with hG
  have hGprob : IsProbabilityMeasure G := by
    constructor
    simp only [hG, Measure.smul_apply, smul_eq_mul]
    exact ENNReal.inv_mul_cancel hm0 hmtop
  -- c • G ≤ m
  have hcG : ENNReal.ofReal c • G ≤ m := by
    intro A
    simp only [hG, Measure.smul_apply, smul_eq_mul, ← mul_assoc]
    have hk : ENNReal.ofReal c * (m Set.univ)⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv]; exact ENNReal.div_le_of_le_mul (by simpa using hcm)
    calc ENNReal.ofReal c * (m Set.univ)⁻¹ * m A ≤ 1 * m A := by gcongr
      _ = m A := one_mul _
  have hεne0 : ENNReal.ofReal ε ≠ 0 := by simpa using hpos
  have hεtop : ENNReal.ofReal ε ≠ ⊤ := ENNReal.ofReal_ne_top
  -- the residual parts
  have residual : ∀ (R : Measure X) [IsProbabilityMeasure R], m ≤ R →
      ∃ H : Measure X, IsProbabilityMeasure H ∧
        R = ENNReal.ofReal c • G + ENNReal.ofReal ε • H := by
    intro R _ hmR
    have hle : ENNReal.ofReal c • G ≤ R := hcG.trans hmR
    have : IsFiniteMeasure (ENNReal.ofReal c • G) := by
      constructor; simp [hG, Measure.smul_apply]
    set Rr : Measure X := R - ENNReal.ofReal c • G with hRr
    have hsum : Rr + ENNReal.ofReal c • G = R := Measure.sub_add_cancel_of_le hle
    have hRruniv : Rr Set.univ = ENNReal.ofReal ε := by
      rw [hRr, Measure.sub_apply MeasurableSet.univ hle]
      simp only [Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
      rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ hcpos.le]
      congr 1; ring
    refine ⟨(ENNReal.ofReal ε)⁻¹ • Rr, ?_, ?_⟩
    · constructor
      simp only [Measure.smul_apply, smul_eq_mul, hRruniv]
      exact ENNReal.inv_mul_cancel hεne0 hεtop
    · rw [smul_smul (ENNReal.ofReal ε) (ENNReal.ofReal ε)⁻¹ Rr, ENNReal.mul_inv_cancel hεne0 hεtop, one_smul, add_comm, hsum]
  obtain ⟨H₁, hH₁, hP⟩ := residual P hmP
  obtain ⟨H₂, hH₂, hQ⟩ := residual Q hmQ
  exact ⟨G, H₁, H₂, hGprob, hH₁, hH₂, hP, hQ⟩
