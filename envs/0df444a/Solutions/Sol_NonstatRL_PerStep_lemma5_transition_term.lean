-- Prove2me | solution 1 for NonstatRL.PerStep.lemma5_transition_term
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T17:32:54.401196+00:00
-- url     : https://prove2.me/submissions/604cefae-887f-4d03-8a7a-4d159b7e1c3d

import Mathlib
import Definitions.Def_NonstatRL_PerStep_EVIOutput
import Theorems.Thm_NonstatRL_PerStep_lemma3_drift_from_window_average
import Theorems.Thm_NonstatRL_PerStep_eq32_bias_bounded

open BanditAlgorithm ENNReal

namespace SwucrlW

open NonstatRL.PerStep

lemma rad_ge_one {S A : ℕ} (hS : 1 < S) (As : Fin S → Finset (Fin A))
    (hAs : ∀ s, (As s).Nonempty) (T : ℕ) (hT : 1 ≤ T) (δ : ℝ) (hδ : 0 < δ ∧ δ < 1) :
    1 ≤ radR As T δ 1 ∧ 1 ≤ radP As T δ 1 := by
  have hN : (2 : ℝ) ≤ ∑ s : Fin S, ((As s).card : ℝ) := by
    have h1 : ∀ s, (1 : ℝ) ≤ ((As s).card : ℝ) := fun s => by
      exact_mod_cast (hAs s).card_pos
    calc (2 : ℝ) ≤ (S : ℝ) := by exact_mod_cast hS
      _ = ∑ _s : Fin S, (1 : ℝ) := by simp
      _ ≤ _ := Finset.sum_le_sum fun s _ => h1 s
  have hTr : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have harg : (2 : ℝ) ≤ (∑ s : Fin S, ((As s).card : ℝ)) * T / δ := by
    rw [le_div_iff₀ hδ.1]
    nlinarith
  have hlog : (1 / 2 : ℝ) ≤ Real.log ((∑ s : Fin S, ((As s).card : ℝ)) * T / δ) := by
    have := Real.log_le_log (by norm_num) harg
    have h2 := Real.log_two_gt_d9
    linarith
  have hS1 : (1 : ℝ) ≤ S := by exact_mod_cast hS.le
  constructor
  · rw [radR, div_one]
    have : 1 ≤ Real.sqrt (2 * Real.log ((∑ s : Fin S, ((As s).card : ℝ)) * T / δ)) :=
      Real.one_le_sqrt.mpr (by linarith)
    linarith
  · rw [radP, div_one]
    have : 1 ≤ Real.sqrt (2 * S * Real.log ((∑ s : Fin S, ((As s).card : ℝ)) * T / δ)) :=
      Real.one_le_sqrt.mpr (by nlinarith)
    linarith

lemma varR_nonneg {S A : ℕ} (M : ℕ → FiniteMDP S A) (As : Fin S → Finset (Fin A))
    (s : Fin S) (a : Fin A) (ha : a ∈ As s) (lo t : ℕ) : 0 ≤ varR M As lo t := by
  refine Finset.sum_nonneg fun j _ => ?_
  refine (abs_nonneg ((M (j + 1)).r s a - (M j).r s a)).trans (le_csSup ?_ ⟨s, a, ha, rfl⟩)
  refine (Set.Finite.subset (Set.finite_range
    (fun p : Fin S × Fin A => |(M (j + 1)).r p.1 p.2 - (M j).r p.1 p.2|)) ?_).bddAbove
  rintro d ⟨s, a, _, rfl⟩
  exact ⟨(s, a), rfl⟩

lemma varP_nonneg {S A : ℕ} (M : ℕ → FiniteMDP S A) (As : Fin S → Finset (Fin A))
    (s : Fin S) (a : Fin A) (ha : a ∈ As s) (lo t : ℕ) : 0 ≤ varP M As lo t := by
  refine Finset.sum_nonneg fun j _ => ?_
  refine (Finset.sum_nonneg fun s' _ => abs_nonneg
    (((M (j + 1)).P s a s' : ℝ) - ((M j).P s a s' : ℝ))).trans (le_csSup ?_ ⟨s, a, ha, rfl⟩)
  refine (Set.Finite.subset (Set.finite_range
    (fun p : Fin S × Fin A => ∑ s' : Fin S,
      |((M (j + 1)).P p.1 p.2 s' : ℝ) - ((M j).P p.1 p.2 s' : ℝ)|)) ?_).bddAbove
  rintro d ⟨s, a, _, rfl⟩
  exact ⟨(s, a), rfl⟩

/-- In-region witnesses that track the round-`t` reward and transition. -/
lemma witness {S A : ℕ} (hS : 1 < S)
    (M : ℕ → FiniteMDP S A) (As : Fin S → Finset (Fin A))
    (hAs : ∀ s, (As s).Nonempty) (T : ℕ)
    (δ : ℝ) (hδ : 0 < δ ∧ δ < 1)
    (W : ℕ) (st : ℕ → Fin S) (ac : ℕ → Fin A) (R : ℕ → ℝ)
    (τm t : ℕ) (ht : τm ≤ t ∧ t < T)
    (heR : EventR M As T δ st ac R (τm - W) τm)
    (heP : EventP M As T δ st ac (τm - W) τm)
    (s : Fin S) (a : Fin A) (ha : a ∈ As s)
    (hl3 : 0 < count st ac (τm - W) τm s a →
      |(M t).r s a - rBar M st ac (τm - W) τm s a| ≤ varR M As (τm - W) t ∧
      (∑ s' : Fin S, |((M t).P s a s' : ℝ) - pBar M st ac (τm - W) τm s a s'|) ≤
        varP M As (τm - W) t) :
    (∃ v : ℝ, 0 ≤ v ∧ v ≤ 1 ∧
      |v - rHat st ac R (τm - W) τm s a| ≤ radR As T δ (countPlus st ac (τm - W) τm s a) ∧
      |(M t).r s a - v| ≤ varR M As (τm - W) t) ∧
    (∃ p : Fin S → ℝ, (∀ s', 0 ≤ p s') ∧ (∑ s', p s') = 1 ∧
      (∑ s', |p s' - pHat st ac (τm - W) τm s a s'|) ≤
        radP As T δ (countPlus st ac (τm - W) τm s a) ∧
      (∑ s', |((M t).P s a s' : ℝ) - p s'|) ≤ varP M As (τm - W) t) := by
  set lo := τm - W
  set I := (Finset.Ico lo τm).filter (fun q => st q = s ∧ ac q = a) with hI
  have hcard : count st ac lo τm s a = I.card := rfl
  -- nonnegativity of the variation budgets
  have hRnn : 0 ≤ varR M As lo t := varR_nonneg M As s a ha lo t
  have hPnn : 0 ≤ varP M As lo t := varP_nonneg M As s a ha lo t
  have hPt1 : ∑ s', ((M t).P s a s' : ℝ) = 1 := by exact_mod_cast (M t).P_sum_one s a
  by_cases hc : 0 < count st ac lo τm s a
  · obtain ⟨h1, h2⟩ := hl3 hc
    have hIpos : 0 < I.card := by rw [← hcard]; exact hc
    have hcpos : (0 : ℝ) < I.card := by exact_mod_cast hIpos
    have hcp : countPlus st ac lo τm s a = (I.card : ℝ) := by
      simp only [countPlus, ← hcard]
      rw [max_eq_right (by omega)]
    have hrbar : rBar M st ac lo τm s a = (∑ q ∈ I, (M q).r s a) / (I.card : ℝ) := by
      rw [rBar, hcp, hI, Finset.sum_filter]
    have hpbar : ∀ s', pBar M st ac lo τm s a s' =
        (∑ q ∈ I, ((M q).P s a s' : ℝ)) / (I.card : ℝ) := by
      intro s'
      rw [pBar, hcp, hI, Finset.sum_filter]
    refine ⟨⟨rBar M st ac lo τm s a, ?_, ?_, ?_, h1⟩,
      ⟨fun s' => pBar M st ac lo τm s a s', ?_, ?_, ?_, h2⟩⟩
    · rw [hrbar]
      exact div_nonneg (Finset.sum_nonneg fun q _ => ((M q).r_mem_Icc s a).1) hcpos.le
    · rw [hrbar, div_le_one hcpos]
      calc ∑ q ∈ I, (M q).r s a ≤ ∑ q ∈ I, (1 : ℝ) :=
            Finset.sum_le_sum fun q _ => ((M q).r_mem_Icc s a).2
        _ = I.card := by simp
    · have := heR s a ha
      rw [abs_sub_comm] at this
      rw [abs_sub_comm]
      exact this
    · intro s'
      show 0 ≤ pBar M st ac lo τm s a s'
      rw [hpbar]
      exact div_nonneg (Finset.sum_nonneg fun q _ => by positivity) hcpos.le
    · simp only [hpbar]
      rw [← Finset.sum_div, Finset.sum_comm]
      have : ∀ q, ∑ s', ((M q).P s a s' : ℝ) = 1 := fun q => by
        exact_mod_cast (M q).P_sum_one s a
      simp only [this, Finset.sum_const, nsmul_eq_mul, mul_one]
      field_simp
    · exact heP s a ha
  · have hc0 : I.card = 0 := by rw [← hcard]; omega
    have hIe : I = ∅ := Finset.card_eq_zero.mp hc0
    have hcp : countPlus st ac lo τm s a = 1 := by
      simp only [countPlus]
      rw [hcard, hc0]
      norm_num
    have hT : 1 ≤ T := by omega
    obtain ⟨hr1, hp1⟩ := rad_ge_one hS As hAs T hT δ hδ
    have hrhat : rHat st ac R lo τm s a = 0 := by
      rw [rHat, ← Finset.sum_filter, ← hI, hIe]
      simp
    have hphat : ∀ s', pHat st ac lo τm s a s' = 0 := by
      intro s'
      have hsub : (Finset.Ico lo τm).filter
          (fun q => st q = s ∧ ac q = a ∧ st (q + 1) = s') ⊆ I := by
        intro q hq
        rw [Finset.mem_filter] at hq
        rw [hI, Finset.mem_filter]
        exact ⟨hq.1, hq.2.1, hq.2.2.1⟩
      have : ((Finset.Ico lo τm).filter
          (fun q => st q = s ∧ ac q = a ∧ st (q + 1) = s')).card = 0 := by
        have := Finset.card_le_card hsub
        omega
      rw [pHat, this]
      simp
    refine ⟨⟨(M t).r s a, ((M t).r_mem_Icc s a).1, ((M t).r_mem_Icc s a).2, ?_, ?_⟩,
      ⟨fun s' => ((M t).P s a s' : ℝ), fun s' => by positivity, hPt1, ?_, ?_⟩⟩
    · rw [hrhat, hcp, sub_zero, abs_of_nonneg ((M t).r_mem_Icc s a).1]
      exact ((M t).r_mem_Icc s a).2.trans hr1
    · simpa using hRnn
    · simp only [hphat, hcp, sub_zero]
      rw [Finset.sum_congr rfl fun s' _ => abs_of_nonneg (by positivity), hPt1]
      exact hp1
    · simpa using hPnn

end SwucrlW

open NonstatRL.PerStep in
theorem solution {S A : ℕ} (hS : 1 < S)
    (M : ℕ → FiniteMDP S A) (As : Fin S → Finset (Fin A))
    (hAs : ∀ s, (As s).Nonempty) (T : ℕ)
    (δ : ℝ) (hδ : 0 < δ ∧ δ < 1) (η : ℝ) (hη : 0 ≤ η)
    (W : ℕ) (st : ℕ → Fin S) (ac : ℕ → Fin A) (R : ℕ → ℝ)
    (τm t : ℕ) (ht : τm ≤ t ∧ t < T)
    (heR : EventR M As T δ st ac R (τm - W) τm)
    (heP : EventP M As T δ st ac (τm - W) τm)
    (πt : Fin S → Fin A) (rt : Fin S → Fin A → ℝ)
    (pt : Fin S → Fin A → Fin S → ℝ) (ρt : ℝ) (γt : Fin S → ℝ)
    (hevi : IsEVIOutput As T δ η W τm st ac R πt rt pt ρt γt)
    (D : ℝ) (Mw : FiniteMDP S A)
    (hw : ∀ s a, a ∈ As s →
      (fun s' => (Mw.P s a s' : ℝ)) ∈
        Hp As T δ st ac (τm - W) τm η s a)
    (hdiam : NonstatRL.Oracle.diameter Mw As ≤ ENNReal.ofReal D)
    (s : Fin S) (a : Fin A) (ha : a ∈ As s) :
    |(∑ s' : Fin S, pt s a s' * γt s') -
      (∑ s' : Fin S, ((M t).P s a s' : ℝ) * γt s')| ≤
    2 * D * (varP M As (τm - W) t +
      2 * radP As T δ (countPlus st ac (τm - W) τm s a) + η) := by
  have h32 := eq32_bias_bounded hS M As hAs T δ hδ η hη W st ac R τm (by omega) heR heP
    πt rt pt ρt γt hevi D Mw hw hdiam
  have hD : 0 ≤ D := by have := h32 s; linarith
  obtain ⟨-, ⟨p, hp0, hp1, hpr, hpt⟩⟩ :=
    SwucrlW.witness hS M As hAs T δ hδ W st ac R τm t ht heR heP s a ha
      (fun hc => lemma3_drift_from_window_average M As st ac W τm t T ht s a ha hc)
  obtain ⟨-, -, hptr⟩ := hevi.transition_mem s a ha
  set ph := pHat st ac (τm - W) τm s a
  set Pt : Fin S → ℝ := fun s' => ((M t).P s a s' : ℝ) with hPt
  -- ℓ₁ distance between the EVI row and the true round-t row
  have hl1 : ∑ s' : Fin S, |pt s a s' - Pt s'| ≤
      varP M As (τm - W) t + 2 * radP As T δ (countPlus st ac (τm - W) τm s a) + η := by
    calc ∑ s' : Fin S, |pt s a s' - Pt s'|
        ≤ ∑ s' : Fin S, (|pt s a s' - ph s'| + |ph s' - p s'| + |p s' - Pt s'|) := by
          refine Finset.sum_le_sum fun s' _ => ?_
          calc |pt s a s' - Pt s'| = |(pt s a s' - ph s') + (ph s' - p s') + (p s' - Pt s')| := by
                ring_nf
            _ ≤ |(pt s a s' - ph s') + (ph s' - p s')| + |p s' - Pt s'| := abs_add_le _ _
            _ ≤ _ := by linarith [abs_add_le (pt s a s' - ph s') (ph s' - p s')]
      _ = ∑ s' : Fin S, |pt s a s' - ph s'| + ∑ s' : Fin S, |p s' - ph s'| +
            ∑ s' : Fin S, |Pt s' - p s'| := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
            Finset.sum_congr rfl fun s' _ => abs_sub_comm (ph s') (p s'),
            Finset.sum_congr rfl fun s' _ => abs_sub_comm (p s') (Pt s')]
      _ ≤ _ := by
          have := hpt
          simp only [hPt]
          linarith
  have e : (∑ s' : Fin S, pt s a s' * γt s') - (∑ s' : Fin S, ((M t).P s a s' : ℝ) * γt s') =
      ∑ s' : Fin S, (pt s a s' - Pt s') * γt s' := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun _ _ => by simp only [hPt]; ring
  rw [e]
  calc |∑ s' : Fin S, (pt s a s' - Pt s') * γt s'|
      ≤ ∑ s' : Fin S, |(pt s a s' - Pt s') * γt s'| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s' : Fin S, |pt s a s' - Pt s'| * (2 * D) := by
        refine Finset.sum_le_sum fun s' _ => ?_
        rw [abs_mul, abs_of_nonneg (h32 s').1]
        exact mul_le_mul_of_nonneg_left (h32 s').2 (abs_nonneg _)
    _ = 2 * D * ∑ s' : Fin S, |pt s a s' - Pt s'| := by rw [← Finset.sum_mul, mul_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left hl1 (by linarith)
