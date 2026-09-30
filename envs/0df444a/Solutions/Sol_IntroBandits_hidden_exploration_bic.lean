-- Prove2me | solution 1 for IntroBandits.hidden_exploration_bic
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-27T10:16:21.169353+00:00
-- url     : https://prove2.me/submissions/90f281c4-b42d-4f73-83cd-7bf5f4eb430d

import Mathlib
import Definitions.Def_IntroBandits_Agents

set_option autoImplicit false

namespace P2M1c

open MeasureTheory ProbabilityTheory BanditAlgorithm IntroBandits in
theorem sum_X_le_one {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (Q : Measure ((Fin 2 → ℝ) × Ω)) [IsProbabilityMeasure Q]
    (F : Finset (Fin 2 → ℝ)) :
    ∑ μ ∈ F, ∑ S, (Q {(μ, S)}).toReal ≤ 1 := by
  have h1 : ∑ μ ∈ F, ∑ S, (Q {(μ, S)}).toReal =
      ∑ p ∈ F ×ˢ (Finset.univ : Finset Ω), (Q {p}).toReal := by
    rw [Finset.sum_product]
  rw [h1, ← ENNReal.toReal_sum (fun p _ => measure_ne_top Q _), sum_measure_singleton]
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by rw [ENNReal.ofReal_one]; exact prob_le_one)

open MeasureTheory ProbabilityTheory BanditAlgorithm IntroBandits in
theorem fst_singleton {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (Q : Measure ((Fin 2 → ℝ) × Ω)) [IsFiniteMeasure Q]
    (μ : Fin 2 → ℝ) : (Q.fst {μ}).toReal = ∑ S, (Q {(μ, S)}).toReal := by
  rw [Measure.fst_apply (measurableSet_singleton μ)]
  have hset : Prod.fst ⁻¹' ({μ} : Set (Fin 2 → ℝ)) =
      ((({μ} : Finset (Fin 2 → ℝ)) ×ˢ (Finset.univ : Finset Ω) : Finset ((Fin 2 → ℝ) × Ω)) :
        Set ((Fin 2 → ℝ) × Ω)) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Finset.coe_product,
      Finset.coe_singleton, Finset.coe_univ, Set.mem_prod, Set.mem_univ, and_true]
  rw [hset, ← sum_measure_singleton, Finset.sum_product, Finset.sum_singleton,
    ENNReal.toReal_sum (fun S _ => measure_ne_top Q _)]

open MeasureTheory ProbabilityTheory BanditAlgorithm IntroBandits in
theorem X_zero {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MeasurableSpace Ω]
    (Q : Measure ((Fin 2 → ℝ) × Ω)) [IsFiniteMeasure Q] (S : Ω)
    (hs : (sigProb Q S).toReal = 0) (μ : Fin 2 → ℝ) : (Q {(μ, S)}).toReal = 0 := by
  have h0 : sigProb Q S = 0 := by
    rcases (ENNReal.toReal_eq_zero_iff _).1 hs with h | h
    · exact h
    · exact absurd h (measure_ne_top Q _)
  have hle : Q {(μ, S)} ≤ sigProb Q S := by
    unfold sigProb
    exact measure_mono (by rintro x rfl; simp)
  rw [h0] at hle
  rw [le_zero_iff.1 hle, ENNReal.toReal_zero]

open MeasureTheory ProbabilityTheory BanditAlgorithm IntroBandits in
theorem exploit_iff {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MeasurableSpace Ω]
    (Q : Measure ((Fin 2 → ℝ) × Ω)) [IsFiniteMeasure Q] (F : Finset (Fin 2 → ℝ)) (S : Ω) :
    exploitArm Q F S = 1 ↔ 0 < sigGapNum Q F S := by
  have hN : sigGapNum Q F S = ∑ μ ∈ F, (Q {(μ, S)}).toReal * μ 1 -
      ∑ μ ∈ F, (Q {(μ, S)}).toReal * μ 0 := by
    unfold sigGapNum
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun μ _ => by ring)
  unfold exploitArm sigPostMean
  rw [hN]
  rcases (ENNReal.toReal_nonneg : 0 ≤ (sigProb Q S).toReal).eq_or_lt with hs | hs
  · have hz := X_zero Q S hs.symm
    simp [hz]
  · by_cases h1 : (∑ μ ∈ F, (Q {(μ, S)}).toReal * μ 1) / (sigProb Q S).toReal ≤
        (∑ μ ∈ F, (Q {(μ, S)}).toReal * μ 0) / (sigProb Q S).toReal
    · have h2 := (div_le_div_iff_of_pos_right hs).1 h1
      rw [if_pos h1]
      constructor
      · intro h; exact absurd h (by decide)
      · intro h; linarith
    · have h2 : ¬ (∑ μ ∈ F, (Q {(μ, S)}).toReal * μ 1 ≤ ∑ μ ∈ F, (Q {(μ, S)}).toReal * μ 0) :=
        fun h => h1 ((div_le_div_iff_of_pos_right hs).2 h)
      rw [if_neg h1]
      constructor
      · intro _; linarith [not_le.1 h2]
      · intro _; rfl

open MeasureTheory ProbabilityTheory BanditAlgorithm IntroBandits in
theorem gap_le_one {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (Q : Measure ((Fin 2 → ℝ) × Ω)) [IsProbabilityMeasure Q]
    (F : Finset (Fin 2 → ℝ)) (hunit : ∀ μ ∈ F, ∀ a, μ a ∈ Set.Icc (0 : ℝ) 1) :
    sigGapPlus Q F ≤ 1 := by
  unfold sigGapPlus sigGapNum
  calc ∑ S, max 0 (∑ μ ∈ F, (Q {(μ, S)}).toReal * (μ 1 - μ 0))
      ≤ ∑ S, ∑ μ ∈ F, (Q {(μ, S)}).toReal :=
        Finset.sum_le_sum (fun S _ => max_le
          (Finset.sum_nonneg (fun μ _ => ENNReal.toReal_nonneg))
          (Finset.sum_le_sum (fun μ hμ => by
            have h0 := hunit μ hμ 0
            have h1 := hunit μ hμ 1
            have hx : 0 ≤ (Q {(μ, S)}).toReal := ENNReal.toReal_nonneg
            nlinarith [h0.1, h0.2, h1.1, h1.2, mul_nonneg hx h0.1,
              mul_nonneg hx (sub_nonneg.2 h1.2)])))
    _ = ∑ μ ∈ F, ∑ S, (Q {(μ, S)}).toReal := Finset.sum_comm
    _ ≤ 1 := sum_X_le_one Q F

end P2M1c

open MeasureTheory ProbabilityTheory BanditAlgorithm IntroBandits in
theorem solution {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (Q : Measure ((Fin 2 → ℝ) × Ω)) [IsProbabilityMeasure Q]
    (F : Finset (Fin 2 → ℝ)) (hF : Q ((↑F)ᶜ ×ˢ Set.univ) = 0)
    (hunit : ∀ μ ∈ F, ∀ a, μ a ∈ Set.Icc (0 : ℝ) 1)
    (hprior : priorMean Q.fst F 1 ≤ priorMean Q.fst F 0)
    (trg : Ω → Fin 2 → ℝ) (htrg : ∀ S, trg S ∈ stdSimplex ℝ (Fin 2))
    {ε : ℝ} (hε : 0 < ε) (hε3 : ε ≤ sigGapPlus Q F / 3) :
    IsSingleRoundBIC Q F (hiddenExploration ε trg Q F) := by
  intro a a' haa' _
  have hX0 : ∀ μ S, 0 ≤ (Q {(μ, S)}).toReal := fun _ _ => ENNReal.toReal_nonneg
  have htot := P2M1c.sum_X_le_one Q F
  have hG1 := P2M1c.gap_le_one Q F hunit
  have hsg : ∀ S, (if (1 : Fin 2) = exploitArm Q F S then (1 : ℝ) else 0) *
      sigGapNum Q F S = max 0 (sigGapNum Q F S) := by
    intro S
    by_cases h : 0 < sigGapNum Q F S
    · rw [if_pos ((P2M1c.exploit_iff Q F S).2 h).symm, one_mul, max_eq_right h.le]
    · rw [if_neg (fun h' => h ((P2M1c.exploit_iff Q F S).1 h'.symm)), zero_mul,
        max_eq_left (not_lt.1 h)]
  have hGP : ∑ μ ∈ F, ∑ S, (Q {(μ, S)}).toReal * (μ 1 - μ 0) *
      (if (1 : Fin 2) = exploitArm Q F S then (1 : ℝ) else 0) = sigGapPlus Q F := by
    unfold sigGapPlus
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun S _ => ?_)
    rw [← hsg S]
    unfold sigGapNum
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun μ _ => by ring)
  have hD0 : 0 ≤ ∑ μ ∈ F, ∑ S, (Q {(μ, S)}).toReal * (μ 0 - μ 1) := by
    have h : ∑ μ ∈ F, ∑ S, (Q {(μ, S)}).toReal * (μ 0 - μ 1) =
        priorMean Q.fst F 0 - priorMean Q.fst F 1 := by
      unfold priorMean
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun μ _ => ?_)
      rw [P2M1c.fst_singleton Q μ, ← mul_sub, Finset.sum_mul]
    linarith
  have htrg01 : ∀ S b, 0 ≤ trg S b ∧ trg S b ≤ 1 := by
    intro S b
    obtain ⟨h0, h1⟩ := htrg S
    refine ⟨h0 b, ?_⟩
    rw [← h1]
    exact Finset.single_le_sum (fun x _ => h0 x) (Finset.mem_univ b)
  have hE : -1 ≤ ∑ μ ∈ F, ∑ S, (Q {(μ, S)}).toReal * (μ a - μ a') * trg S a := by
    calc (-1 : ℝ) ≤ -(∑ μ ∈ F, ∑ S, (Q {(μ, S)}).toReal) := by linarith
      _ = ∑ μ ∈ F, ∑ S, -(Q {(μ, S)}).toReal := by simp only [Finset.sum_neg_distrib]
      _ ≤ _ := Finset.sum_le_sum (fun μ hμ => Finset.sum_le_sum (fun S _ => by
          have ha := hunit μ hμ a
          have ha' := hunit μ hμ a'
          have ht := htrg01 S a
          have hx := hX0 μ S
          nlinarith [mul_nonneg (mul_nonneg hx ht.1)
              (by linarith [ha.1, ha.2, ha'.1, ha'.2] : (0 : ℝ) ≤ μ a - μ a' + 1),
            mul_nonneg hx (sub_nonneg.2 ht.2)]))
  have hpair : (a = 0 ∧ a' = 1) ∨ (a = 1 ∧ a' = 0) := by
    fin_cases a <;> fin_cases a' <;> simp_all
  unfold hiddenExploration
  have hε1 : ε ≤ 1 / 3 := by linarith
  rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · -- a = 0, a' = 1
    have he : ∀ S, (if (0 : Fin 2) = exploitArm Q F S then (1 : ℝ) else 0) =
        1 - (if (1 : Fin 2) = exploitArm Q F S then (1 : ℝ) else 0) := by
      intro S
      generalize exploitArm Q F S = e
      fin_cases e <;> simp
    have hsplit : ∑ μ ∈ F, ∑ S, (Q {(μ, S)}).toReal * (μ 0 - μ 1) *
        (ε * trg S 0 + (1 - ε) * (if (0 : Fin 2) = exploitArm Q F S then 1 else 0)) =
        ε * ∑ μ ∈ F, ∑ S, (Q {(μ, S)}).toReal * (μ 0 - μ 1) * trg S 0 +
        (1 - ε) * (∑ μ ∈ F, ∑ S, (Q {(μ, S)}).toReal * (μ 0 - μ 1) +
          ∑ μ ∈ F, ∑ S, (Q {(μ, S)}).toReal * (μ 1 - μ 0) *
            (if (1 : Fin 2) = exploitArm Q F S then (1 : ℝ) else 0)) := by
      simp only [he]
      simp only [mul_add, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun μ _ => Finset.sum_congr rfl (fun S _ => by ring))
    rw [hsplit, hGP]
    nlinarith [mul_nonneg hε.le (by linarith : (0 : ℝ) ≤
        ∑ μ ∈ F, ∑ S, (Q {(μ, S)}).toReal * (μ 0 - μ 1) * trg S 0 + 1),
      mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - ε)
        (by linarith : (0 : ℝ) ≤ ∑ μ ∈ F, ∑ S, (Q {(μ, S)}).toReal * (μ 0 - μ 1) +
          sigGapPlus Q F - 3 * ε),
      mul_nonneg hε.le (by linarith : (0 : ℝ) ≤ 2 - 3 * ε)]
  · -- a = 1, a' = 0
    have hsplit : ∑ μ ∈ F, ∑ S, (Q {(μ, S)}).toReal * (μ 1 - μ 0) *
        (ε * trg S 1 + (1 - ε) * (if (1 : Fin 2) = exploitArm Q F S then 1 else 0)) =
        ε * ∑ μ ∈ F, ∑ S, (Q {(μ, S)}).toReal * (μ 1 - μ 0) * trg S 1 +
        (1 - ε) * ∑ μ ∈ F, ∑ S, (Q {(μ, S)}).toReal * (μ 1 - μ 0) *
            (if (1 : Fin 2) = exploitArm Q F S then (1 : ℝ) else 0) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun μ _ => Finset.sum_congr rfl (fun S _ => by ring))
    rw [hsplit, hGP]
    nlinarith [mul_nonneg hε.le (by linarith : (0 : ℝ) ≤
        ∑ μ ∈ F, ∑ S, (Q {(μ, S)}).toReal * (μ 1 - μ 0) * trg S 1 + 1),
      mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - ε)
        (by linarith : (0 : ℝ) ≤ sigGapPlus Q F - 3 * ε),
      mul_nonneg hε.le (by linarith : (0 : ℝ) ≤ 2 - 3 * ε)]
