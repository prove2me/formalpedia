-- Prove2me | solution 1 for HighConfRobust.lemma_4_3
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-24T10:53:27.161285+00:00
-- url     : https://prove2.me/submissions/e868ff89-13c3-45b3-a613-3a2a12c0a91a

import Mathlib
import Definitions.Def_TotalVariationDist
import Definitions.Def_HighConfRobust_renyiDivergence
import Theorems.Thm_HighConfRobust_fact_3_1
import Theorems.Thm_HighConfRobust_fact_3_3_iii
import Theorems.Thm_HighConfRobust_fact_4_4

open MeasureTheory HighConfRobust

theorem solution {X : Type*} [MeasurableSpace X] (P Q : Measure X)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (ε a : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hPQ : MarkovChainCLT.tvDist P Q ≤ ε) (ha : 0 < a) (ha1 : a < 1) :
    let κ : ℝ := 1 / max 1 (Real.log (ε / a))
    (0 < κ ∧ κ ≤ 1) ∧
      ∃ F : Measure X, IsProbabilityMeasure F ∧ MarkovChainCLT.tvDist P F ≤ a ∧
        renyiDivergence (1 + κ) Q F ≤ ((2 * ε / κ : ℝ) : EReal) := by
  intro κ
  have hm1 : 1 ≤ max 1 (Real.log (ε / a)) := le_max_left _ _
  have hκ0 : 0 < κ := by positivity
  have hκ1 : κ ≤ 1 := by
    show 1 / max 1 (Real.log (ε / a)) ≤ 1
    rw [div_le_one (by linarith)]; exact hm1
  refine ⟨⟨hκ0, hκ1⟩, ?_⟩
  obtain ⟨G, H₁, H₂, hG, hH₁, hH₂, hP, hQ⟩ := fact_3_1 P Q ε hPQ hε1
  set lam : ℝ := min 1 (a / ε) with hlam
  have hlam0 : 0 < lam := lt_min one_pos (div_pos ha hε)
  have hlam1 : lam ≤ 1 := min_le_left _ _
  have hlamε : lam * ε ≤ a := by
    have : lam ≤ a / ε := min_le_right _ _
    rwa [le_div_iff₀ hε] at this
  let w : Fin 3 → ENNReal :=
    ![ENNReal.ofReal (1 - ε), ENNReal.ofReal (ε * (1 - lam)), ENNReal.ofReal (lam * ε)]
  let w' : Fin 3 → ENNReal := ![ENNReal.ofReal (1 - ε), 0, ENNReal.ofReal ε]
  let H : Fin 3 → Measure X := ![G, H₁, H₂]
  haveI : ∀ i, IsProbabilityMeasure (H i) := by
    intro i; fin_cases i <;> simp [H] <;> assumption
  let Fm : Measure X := ∑ i, w i • H i
  have hsum_w : ∑ i, w i = 1 := by
    simp only [w, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    rw [← ENNReal.ofReal_add (by linarith) (by nlinarith),
      ← ENNReal.ofReal_add (by nlinarith) (by positivity)]
    rw [show 1 - ε + ε * (1 - lam) + lam * ε = 1 by ring, ENNReal.ofReal_one]
  have hsum_w' : ∑ i, w' i = 1 := by
    simp only [w', Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, add_zero]
    rw [← ENNReal.ofReal_add (by linarith) hε.le]
    simp
  have hFprob : IsProbabilityMeasure Fm := by
    constructor
    simp only [Fm, Measure.coe_finset_sum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul,
      measure_univ, mul_one]
    exact hsum_w
  have hQ' : Q = ∑ i, w' i • H i := by
    rw [hQ]
    simp [w', H, Fin.sum_univ_three]
  have hF' : Fm = ENNReal.ofReal (1 - ε) • G + ENNReal.ofReal (ε * (1 - lam)) • H₁ +
      ENNReal.ofReal (lam * ε) • H₂ := by
    simp [Fm, w, H, Fin.sum_univ_three]
  refine ⟨Fm, hFprob, ?_, ?_⟩
  · -- total variation
    unfold MarkovChainCLT.tvDist
    refine csSup_le ⟨_, ∅, MeasurableSet.empty, rfl⟩ ?_
    rintro r ⟨s, hs, rfl⟩
    have hPs : (P s).toReal = (1 - ε) * (G s).toReal + ε * (H₁ s).toReal := by
      rw [hP]
      simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
      rw [ENNReal.toReal_add (by finiteness) (by finiteness), ENNReal.toReal_mul,
        ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_ofReal hε.le]
    have hFs : (Fm s).toReal = (1 - ε) * (G s).toReal + ε * (1 - lam) * (H₁ s).toReal +
        lam * ε * (H₂ s).toReal := by
      rw [hF']
      simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
      rw [ENNReal.toReal_add (by finiteness) (by finiteness),
        ENNReal.toReal_add (by finiteness) (by finiteness), ENNReal.toReal_mul,
        ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith),
        ENNReal.toReal_ofReal (by nlinarith), ENNReal.toReal_ofReal (by positivity)]
    have h1 : (H₁ s).toReal ≤ 1 := by
      rw [← ENNReal.toReal_one]; exact ENNReal.toReal_mono (by simp) prob_le_one
    have h2 : (H₂ s).toReal ≤ 1 := by
      rw [← ENNReal.toReal_one]; exact ENNReal.toReal_mono (by simp) prob_le_one
    have h3 := ENNReal.toReal_nonneg (a := H₁ s)
    have h4 := ENNReal.toReal_nonneg (a := H₂ s)
    have : (P s).toReal - (Fm s).toReal = lam * ε * ((H₁ s).toReal - (H₂ s).toReal) := by
      rw [hPs, hFs]; ring
    rw [this, abs_mul, abs_of_pos (by positivity)]
    have : |(H₁ s).toReal - (H₂ s).toReal| ≤ 1 := by rw [abs_le]; constructor <;> linarith
    calc lam * ε * |(H₁ s).toReal - (H₂ s).toReal| ≤ lam * ε * 1 := by gcongr
      _ ≤ a := by linarith
  · -- Rényi divergence
    have hpw : ∀ i, w' i ≠ 0 → w i ≠ 0 := by
      intro i hi
      fin_cases i
      · simpa [w, w'] using hi
      · simp [w'] at hi
      · simp only [w, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons,
          ne_eq, ENNReal.ofReal_eq_zero, not_le]
        positivity
    have h3 := fact_3_3_iii H w' w hsum_w' hsum_w hpw (1 + κ) (by linarith)
    have h4 : renyiDivergence (1 + κ) (∑ i, w' i • Measure.dirac i)
        (∑ i, w i • Measure.dirac i) ≤ ((2 * ε / κ : ℝ) : EReal) :=
      fact_4_4 ε a hε hε1 ha ha1
    rw [hQ']
    exact h3.trans h4
