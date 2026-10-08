-- Prove2me | solution 1 for KingmanSubadditive.Ergodic.fekete
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T11:47:16.242581+00:00
-- url     : https://prove2.me/submissions/c6c42c10-baab-4398-b85b-0603d9b0c37a

import Mathlib
import Definitions.Def_KingmanSubadditive_Ergodic_Process



namespace KingmanSubadditive.Ergodic

open MeasureTheory Filter Topology

variable {Ω : Type*} [MeasurableSpace Ω]

/-- law transfer of a single coordinate. -/
lemma fek_coord (P : Measure Ω) (x : ℕ → ℕ → Ω → ℝ)
    (hmeas : ∀ s t : ℕ, s < t → Measurable (x s t))
    (hS2' : ∀ s t : ℕ, s < t → Measure.map (x s t) P = Measure.map (x 0 (t - s)) P)
    (s t : ℕ) (hst : s < t) :
    (Integrable (x s t) P ↔ Integrable (x 0 (t - s)) P) ∧
    ∫ ω, x s t ω ∂P = ∫ ω, x 0 (t - s) ω ∂P := by
  have h1 := hmeas s t hst
  have h0 := hmeas 0 (t - s) (by omega)
  have hmap := hS2' s t hst
  have hid : Measurable (id : ℝ → ℝ) := measurable_id
  constructor
  · have A := integrable_map_measure (μ := P) (f := x s t) (g := (id : ℝ → ℝ))
      hid.aestronglyMeasurable h1.aemeasurable
    have B := integrable_map_measure (μ := P) (f := x 0 (t - s)) (g := (id : ℝ → ℝ))
      hid.aestronglyMeasurable h0.aemeasurable
    rw [hmap] at A
    simpa [Function.comp_def] using A.symm.trans B
  · have A := integral_map (μ := P) (φ := x s t) h1.aemeasurable
      (f := (id : ℝ → ℝ)) hid.aestronglyMeasurable
    have B := integral_map (μ := P) (φ := x 0 (t - s)) h0.aemeasurable
      (f := (id : ℝ → ℝ)) hid.aestronglyMeasurable
    rw [hmap] at A
    simpa using A.symm.trans B

lemma fek_mean_subadd (P : Measure Ω) (x : ℕ → ℕ → Ω → ℝ)
    (hmeas : ∀ s t : ℕ, s < t → Measurable (x s t))
    (hS1 : S1 x)
    (hS2' : ∀ s t : ℕ, s < t → Measure.map (x s t) P = Measure.map (x 0 (t - s)) P)
    (hS3 : S3 P x) (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    mean P x (m + n) ≤ mean P x m + mean P x n := by
  obtain ⟨hint, heq⟩ := fek_coord P x hmeas hS2' m (m + n) (by omega)
  have hmn : m + n - m = n := by omega
  rw [hmn] at hint heq
  have hi1 := hS3.1 m hm
  have hi2 := hS3.1 (m + n) (by omega)
  have hin : Integrable (x m (m + n)) P := hint.2 (hS3.1 n hn)
  unfold mean
  rw [← heq, ← integral_add hi1 hin]
  apply integral_mono hi2 (hi1.add hin)
  intro ω
  exact hS1 0 m (m + n) ω (by omega) (by omega)

theorem fekete_core (P : Measure Ω)
    [IsProbabilityMeasure P] (x : ℕ → ℕ → Ω → ℝ)
    (hmeas : ∀ s t : ℕ, s < t → Measurable (x s t))
    (hS1 : S1 x)
    (hS2' : ∀ s t : ℕ, s < t → Measure.map (x s t) P = Measure.map (x 0 (t - s)) P)
    (hS3 : S3 P x) :
    Tendsto (fun t : ℕ => mean P x t / (t : ℝ)) atTop (𝓝 (gamma P x)) := by
  set u : ℕ → ℝ := fun n => if n = 0 then 0 else mean P x n with hu
  have hsub : Subadditive u := by
    intro m n
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm; simp [hu]
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp [hu]
    have : m + n ≠ 0 := by omega
    simp only [hu, if_neg this, if_neg hm.ne', if_neg hn.ne']
    exact fek_mean_subadd P x hmeas hS1 hS2' hS3 m n hm hn
  obtain ⟨A, hA⟩ := hS3.2
  have hbdd : BddBelow (Set.range fun n : ℕ => u n / n) := by
    refine ⟨min (-A) 0, ?_⟩
    rintro _ ⟨n, rfl⟩
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp [hu]
    · simp only [hu, if_neg hn.ne']
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
      refine le_trans (min_le_left _ _) ?_
      rw [le_div_iff₀ hnpos]
      exact hA n hn
  have hlim : hsub.lim = gamma P x := by
    rw [Subadditive.lim]
    unfold gamma
    rw [iInf]
    congr 1
    ext y
    constructor
    · rintro ⟨n, hn, rfl⟩
      have hn' : n ≠ 0 := by simp [Set.mem_Ici] at hn; omega
      exact ⟨⟨n, hn⟩, by simp [hu, if_neg hn']⟩
    · rintro ⟨⟨n, hn⟩, rfl⟩
      have hn' : n ≠ 0 := by omega
      exact ⟨n, hn, by simp [hu, if_neg hn']⟩
  have ht := hsub.tendsto_lim hbdd
  rw [hlim] at ht
  refine ht.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  simp only [hu, if_neg (by omega : n ≠ 0)]

end KingmanSubadditive.Ergodic

open KingmanSubadditive.Ergodic
open MeasureTheory Filter Topology

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (x : ℕ → ℕ → Ω → ℝ)
    (hmeas : ∀ s t : ℕ, s < t → Measurable (x s t))
    (hS1 : S1 x)
    (hS2' : ∀ s t : ℕ, s < t → Measure.map (x s t) P = Measure.map (x 0 (t - s)) P)
    (hS3 : S3 P x) :
    Tendsto (fun t : ℕ => mean P x t / (t : ℝ)) atTop (𝓝 (gamma P x)) := by
  exact fekete_core P x hmeas hS1 hS2' hS3
