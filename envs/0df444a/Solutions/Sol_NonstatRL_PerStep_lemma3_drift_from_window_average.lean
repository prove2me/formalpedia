-- Prove2me | solution 1 for NonstatRL.PerStep.lemma3_drift_from_window_average
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T17:23:13.065949+00:00
-- url     : https://prove2.me/submissions/abd2376a-73e9-4604-8d78-b8b802bccb94

import Mathlib
import Definitions.Def_NonstatRL_PerStep_Window

open BanditAlgorithm

namespace SwucrlL3

lemma telescope_abs (F : ℕ → ℝ) (q : ℕ) :
    ∀ t, q ≤ t → |F t - F q| ≤ ∑ j ∈ Finset.Ico q t, |F (j + 1) - F j| := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => simp
  | succ n hqn ih =>
    rw [Finset.sum_Ico_succ_top hqn]
    calc |F (n + 1) - F q| = |(F (n + 1) - F n) + (F n - F q)| := by ring_nf
      _ ≤ |F (n + 1) - F n| + |F n - F q| := abs_add_le _ _
      _ ≤ _ := by linarith

lemma avg_dev (I : Finset ℕ) (hI : 0 < I.card) (x : ℕ → ℝ) (y : ℝ) :
    |y - (∑ q ∈ I, x q) / (I.card : ℝ)| ≤ (∑ q ∈ I, |y - x q|) / (I.card : ℝ) := by
  have hc : (0 : ℝ) < I.card := by exact_mod_cast hI
  have : y - (∑ q ∈ I, x q) / (I.card : ℝ) = (∑ q ∈ I, (y - x q)) / (I.card : ℝ) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    field_simp
  rw [this, abs_div, abs_of_pos hc]
  gcongr
  exact Finset.abs_sum_le_sum_abs _ _

lemma rewardDrift_ge {S A : ℕ} (M : ℕ → FiniteMDP S A) (As : Fin S → Finset (Fin A))
    (q : ℕ) (s : Fin S) (a : Fin A) (ha : a ∈ As s) :
    |(M (q + 1)).r s a - (M q).r s a| ≤ NonstatRL.Oracle.rewardDrift M As q := by
  apply le_csSup
  · refine (Set.Finite.subset (Set.finite_range
      (fun p : Fin S × Fin A => |(M (q + 1)).r p.1 p.2 - (M q).r p.1 p.2|)) ?_).bddAbove
    rintro d ⟨s, a, _, rfl⟩
    exact ⟨(s, a), rfl⟩
  · exact ⟨s, a, ha, rfl⟩

lemma transDrift_ge {S A : ℕ} (M : ℕ → FiniteMDP S A) (As : Fin S → Finset (Fin A))
    (q : ℕ) (s : Fin S) (a : Fin A) (ha : a ∈ As s) :
    ∑ s' : Fin S, |((M (q + 1)).P s a s' : ℝ) - ((M q).P s a s' : ℝ)| ≤
      NonstatRL.Oracle.transDrift M As q := by
  apply le_csSup
  · refine (Set.Finite.subset (Set.finite_range
      (fun p : Fin S × Fin A => ∑ s' : Fin S,
        |((M (q + 1)).P p.1 p.2 s' : ℝ) - ((M q).P p.1 p.2 s' : ℝ)|)) ?_).bddAbove
    rintro d ⟨s, a, _, rfl⟩
    exact ⟨(s, a), rfl⟩
  · exact ⟨s, a, ha, rfl⟩

end SwucrlL3

open NonstatRL.PerStep in
theorem solution {S A : ℕ}
    (M : ℕ → FiniteMDP S A) (As : Fin S → Finset (Fin A))
    (st : ℕ → Fin S) (ac : ℕ → Fin A) (W τm t T : ℕ)
    (ht : τm ≤ t ∧ t < T) (s : Fin S) (a : Fin A) (ha : a ∈ As s)
    (hcount : 0 < count st ac (τm - W) τm s a) :
    |(M t).r s a - rBar M st ac (τm - W) τm s a| ≤
        varR M As (τm - W) t ∧
    (∑ s' : Fin S,
      |((M t).P s a s' : ℝ) - pBar M st ac (τm - W) τm s a s'|) ≤
        varP M As (τm - W) t := by
  set lo := τm - W
  set I := (Finset.Ico lo τm).filter (fun q => st q = s ∧ ac q = a) with hI
  have hcard : count st ac lo τm s a = I.card := rfl
  have hcp : countPlus st ac lo τm s a = (I.card : ℝ) := by
    simp only [countPlus, ← hcard]
    rw [max_eq_right (by omega)]
  have hIpos : 0 < I.card := by rw [← hcard]; exact hcount
  have hmemI : ∀ q ∈ I, lo ≤ q ∧ q ≤ t := by
    intro q hq
    rw [hI, Finset.mem_filter, Finset.mem_Ico] at hq
    exact ⟨hq.1.1, by omega⟩
  have hRnn : ∀ j, 0 ≤ NonstatRL.Oracle.rewardDrift M As j := fun j =>
    (abs_nonneg _).trans (SwucrlL3.rewardDrift_ge M As j s a ha)
  have hPnn : ∀ j, 0 ≤ NonstatRL.Oracle.transDrift M As j := fun j =>
    (Finset.sum_nonneg fun _ _ => abs_nonneg _).trans (SwucrlL3.transDrift_ge M As j s a ha)
  constructor
  · have hrbar : rBar M st ac lo τm s a = (∑ q ∈ I, (M q).r s a) / (I.card : ℝ) := by
      rw [rBar, hcp, hI, Finset.sum_filter]
    rw [hrbar]
    refine (SwucrlL3.avg_dev I hIpos (fun q => (M q).r s a) _).trans ?_
    have hc : (0 : ℝ) < I.card := by exact_mod_cast hIpos
    rw [div_le_iff₀ hc]
    calc ∑ q ∈ I, |(M t).r s a - (M q).r s a| ≤ ∑ q ∈ I, varR M As lo t := by
          refine Finset.sum_le_sum fun q hq => ?_
          obtain ⟨h1, h2⟩ := hmemI q hq
          refine (SwucrlL3.telescope_abs (fun j => (M j).r s a) q t h2).trans ?_
          refine (Finset.sum_le_sum fun j _ => SwucrlL3.rewardDrift_ge M As j s a ha).trans ?_
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico h1 le_rfl)
            (fun j _ _ => hRnn j)
      _ = varR M As lo t * I.card := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  · have hpbar : ∀ s', pBar M st ac lo τm s a s' =
        (∑ q ∈ I, ((M q).P s a s' : ℝ)) / (I.card : ℝ) := by
      intro s'
      rw [pBar, hcp, hI, Finset.sum_filter]
    simp_rw [hpbar]
    have hc : (0 : ℝ) < I.card := by exact_mod_cast hIpos
    calc (∑ s' : Fin S, |((M t).P s a s' : ℝ) -
            (∑ q ∈ I, ((M q).P s a s' : ℝ)) / (I.card : ℝ)|)
          ≤ ∑ s' : Fin S, (∑ q ∈ I, |((M t).P s a s' : ℝ) - ((M q).P s a s' : ℝ)|) /
              (I.card : ℝ) :=
          Finset.sum_le_sum fun s' _ =>
            SwucrlL3.avg_dev I hIpos (fun q => ((M q).P s a s' : ℝ)) _
      _ = (∑ q ∈ I, ∑ s' : Fin S, |((M t).P s a s' : ℝ) - ((M q).P s a s' : ℝ)|) /
              (I.card : ℝ) := by
          rw [← Finset.sum_div, Finset.sum_comm]
      _ ≤ (∑ q ∈ I, varP M As lo t) / (I.card : ℝ) := by
          gcongr with q hq
          obtain ⟨h1, h2⟩ := hmemI q hq
          calc ∑ s' : Fin S, |((M t).P s a s' : ℝ) - ((M q).P s a s' : ℝ)|
              ≤ ∑ s' : Fin S, ∑ j ∈ Finset.Ico q t,
                  |((M (j + 1)).P s a s' : ℝ) - ((M j).P s a s' : ℝ)| :=
                Finset.sum_le_sum fun s' _ =>
                  SwucrlL3.telescope_abs (fun j => ((M j).P s a s' : ℝ)) q t h2
            _ = ∑ j ∈ Finset.Ico q t, ∑ s' : Fin S,
                  |((M (j + 1)).P s a s' : ℝ) - ((M j).P s a s' : ℝ)| := Finset.sum_comm
            _ ≤ ∑ j ∈ Finset.Ico q t, NonstatRL.Oracle.transDrift M As j :=
                Finset.sum_le_sum fun j _ => SwucrlL3.transDrift_ge M As j s a ha
            _ ≤ varP M As lo t :=
                Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico h1 le_rfl)
                  (fun j _ _ => hPnn j)
      _ = varP M As lo t := by
          rw [Finset.sum_const, nsmul_eq_mul]
          field_simp
