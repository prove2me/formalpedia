-- Prove2me | solution 1 for KingmanSubadditive.Ergodic.maximal
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T11:49:57.884979+00:00
-- url     : https://prove2.me/submissions/d0dbb7e1-2224-4121-9530-d95a0b8685f1

import Mathlib
import Definitions.Def_KingmanSubadditive_Ergodic_Process



namespace KingmanSubadditive.Ergodic

open MeasureTheory Filter Topology

variable {Ω : Type*} [MeasurableSpace Ω]

/-- running maximum of the coordinates `(0,1), …, (0,n+1)` of a path. -/
def pmax : ℕ → (Interval → ℝ) → ℝ
  | 0, φ => φ ⟨(0, 1), by omega⟩
  | n + 1, φ => max (pmax n φ) (φ ⟨(0, n + 2), by omega⟩)

lemma pmax_measurable (n : ℕ) : Measurable (pmax n) := by
  induction n with
  | zero => exact measurable_pi_apply _
  | succ n ih =>
    exact ih.max (measurable_pi_apply (⟨(0, n + 2), by omega⟩ : Interval))

lemma pmax_mono (n : ℕ) (φ : Interval → ℝ) : pmax n φ ≤ pmax (n + 1) φ :=
  le_max_left _ _

lemma path_apply (x : ℕ → ℕ → Ω → ℝ) (ω : Ω) (s t : ℕ) (h : s < t) :
    path x ω ⟨(s, t), h⟩ = x s t ω := rfl

lemma shiftedPath_apply (x : ℕ → ℕ → Ω → ℝ) (ω : Ω) (s t : ℕ) (h : s < t) :
    shiftedPath x ω ⟨(s, t), h⟩ = x (s + 1) (t + 1) ω := rfl

lemma pmax_path_nonneg (x : ℕ → ℕ → Ω → ℝ) (ω : Ω) (n : ℕ)
    (h : 0 ≤ pmax n (path x ω)) : ∃ t : ℕ, 1 ≤ t ∧ 0 ≤ x 0 t ω := by
  induction n with
  | zero => exact ⟨1, le_rfl, h⟩
  | succ n ih =>
    simp only [pmax] at h
    rcases le_max_iff.1 h with h1 | h2
    · exact ih h1
    · exact ⟨n + 2, by omega, h2⟩

lemma le_pmax_path (x : ℕ → ℕ → Ω → ℝ) (ω : Ω) (t : ℕ) (ht : 1 ≤ t) :
    x 0 t ω ≤ pmax (t - 1) (path x ω) := by
  induction t with
  | zero => omega
  | succ t ih =>
    rcases Nat.eq_zero_or_pos t with h0 | hpos
    · subst h0; exact le_rfl
    · have : t + 1 - 1 = (t - 1) + 1 := by omega
      rw [this]
      simp only [pmax]
      apply le_max_of_le_right
      have : t - 1 + 2 = t + 1 := by omega
      simp only [this]
      exact le_rfl

/-- the Garsia-type inequality: running max ≤ `x₀₁` + positive part of the shifted running max. -/
lemma pmax_key (x : ℕ → ℕ → Ω → ℝ) (hS1 : S1 x) (ω : Ω) (n : ℕ) :
    pmax (n + 1) (path x ω) ≤ x 0 1 ω + max 0 (pmax n (shiftedPath x ω)) := by
  induction n with
  | zero =>
    simp only [pmax, path_apply, shiftedPath_apply]
    apply max_le
    · linarith [le_max_left (0:ℝ) (x 1 2 ω)]
    · have := hS1 0 1 2 ω (by omega) (by omega)
      linarith [le_max_right (0:ℝ) (x 1 2 ω)]
  | succ n ih =>
    rw [show pmax (n + 1 + 1) (path x ω)
        = max (pmax (n + 1) (path x ω)) (x 0 (n + 3) ω) from rfl]
    apply max_le
    · have h2 : max 0 (pmax n (shiftedPath x ω)) ≤ max 0 (pmax (n + 1) (shiftedPath x ω)) :=
        max_le_max le_rfl (pmax_mono n _)
      linarith
    · have h1 := hS1 0 1 (n + 3) ω (by omega) (by omega)
      have h2 : x 1 (n + 3) ω ≤ pmax (n + 1) (shiftedPath x ω) := by
        rw [show pmax (n + 1) (shiftedPath x ω)
            = max (pmax n (shiftedPath x ω)) (x 1 (n + 3) ω) from rfl]
        exact le_max_right _ _
      have h3 := le_max_right (0:ℝ) (pmax (n + 1) (shiftedPath x ω))
      linarith

lemma path_measurable (x : ℕ → ℕ → Ω → ℝ)
    (hmeas : ∀ s t : ℕ, s < t → Measurable (x s t)) : Measurable (path x) :=
  measurable_pi_iff.2 fun p => hmeas p.1.1 p.1.2 p.2

lemma shiftedPath_measurable (x : ℕ → ℕ → Ω → ℝ)
    (hmeas : ∀ s t : ℕ, s < t → Measurable (x s t)) : Measurable (shiftedPath x) :=
  measurable_pi_iff.2 fun p => hmeas (p.1.1 + 1) (p.1.2 + 1) (by have := p.2; omega)

lemma pmax_path_integrable (P : Measure Ω) (x : ℕ → ℕ → Ω → ℝ)
    (hS3 : S3 P x) (n : ℕ) :
    Integrable (fun ω => pmax n (path x ω)) P := by
  induction n with
  | zero => exact hS3.1 1 le_rfl
  | succ n ih =>
    have h2 := hS3.1 (n + 2) (by omega)
    exact ih.sup h2

/-- law transfer for the positive part of the running maximum. -/
lemma pmax_shift_transfer (P : Measure Ω) (x : ℕ → ℕ → Ω → ℝ)
    (hmeas : ∀ s t : ℕ, s < t → Measurable (x s t)) (hS2 : S2 P x) (n : ℕ) :
    (Integrable (fun ω => max 0 (pmax n (shiftedPath x ω))) P ↔
      Integrable (fun ω => max 0 (pmax n (path x ω))) P) ∧
    ∫ ω, max 0 (pmax n (shiftedPath x ω)) ∂P = ∫ ω, max 0 (pmax n (path x ω)) ∂P := by
  have hΦ : Measurable (fun φ : Interval → ℝ => max 0 (pmax n φ)) :=
    measurable_const.max (pmax_measurable n)
  have h1 := shiftedPath_measurable x hmeas
  have h0 := path_measurable x hmeas
  have hmap : Measure.map (shiftedPath x) P = Measure.map (path x) P := hS2
  constructor
  · have A := integrable_map_measure (μ := P) (f := shiftedPath x)
      (g := fun φ : Interval → ℝ => max 0 (pmax n φ)) hΦ.aestronglyMeasurable h1.aemeasurable
    have B := integrable_map_measure (μ := P) (f := path x)
      (g := fun φ : Interval → ℝ => max 0 (pmax n φ)) hΦ.aestronglyMeasurable h0.aemeasurable
    rw [hmap] at A
    exact A.symm.trans B
  · have A := integral_map (μ := P) (φ := shiftedPath x) h1.aemeasurable
      (f := fun φ : Interval → ℝ => max 0 (pmax n φ)) hΦ.aestronglyMeasurable
    have B := integral_map (μ := P) (φ := path x) h0.aemeasurable
      (f := fun φ : Interval → ℝ => max 0 (pmax n φ)) hΦ.aestronglyMeasurable
    rw [hmap] at A
    exact A.symm.trans B

lemma maximal_step (P : Measure Ω) [IsProbabilityMeasure P] (x : ℕ → ℕ → Ω → ℝ)
    (hx : IsSubadditiveProcess P x) (n : ℕ) :
    0 ≤ ∫ ω in {ω | 0 ≤ pmax (n + 1) (path x ω)}, x 0 1 ω ∂P := by
  obtain ⟨hmeas, hS1, hS2, hS3⟩ := hx
  have hG : ∀ k, Measurable (fun ω => pmax k (path x ω)) := fun k =>
    (pmax_measurable k).comp (path_measurable x hmeas)
  have hA : MeasurableSet {ω | 0 ≤ pmax (n + 1) (path x ω)} :=
    measurableSet_le measurable_const (hG (n + 1))
  have hx01 : Integrable (x 0 1) P := hS3.1 1 le_rfl
  have hGi : ∀ k, Integrable (fun ω => max 0 (pmax k (path x ω))) P := fun k =>
    (integrable_const (0:ℝ)).sup (pmax_path_integrable P x hS3 k)
  obtain ⟨hHi, hHeq⟩ := pmax_shift_transfer P x hmeas hS2 n
  have hHi' := hHi.2 (hGi n)
  set g : Ω → ℝ := fun ω => max 0 (pmax (n + 1) (path x ω)) - max 0 (pmax n (shiftedPath x ω))
    with hg
  have hgi : Integrable g P := (hGi (n + 1)).sub hHi'
  have hpt : ∀ ω, g ω ≤ {ω | 0 ≤ pmax (n + 1) (path x ω)}.indicator (x 0 1) ω := by
    intro ω
    by_cases h : 0 ≤ pmax (n + 1) (path x ω)
    · rw [Set.indicator_of_mem (by exact h)]
      have := pmax_key x hS1 ω n
      simp only [hg, max_eq_right h]
      linarith
    · rw [Set.indicator_of_notMem (by exact h)]
      push Not at h
      simp only [hg, max_eq_left h.le]
      linarith [le_max_left (0:ℝ) (pmax n (shiftedPath x ω))]
  rw [← integral_indicator hA]
  have h1 : ∫ ω, g ω ∂P ≤ ∫ ω, {ω | 0 ≤ pmax (n + 1) (path x ω)}.indicator (x 0 1) ω ∂P :=
    integral_mono hgi (hx01.indicator hA) hpt
  have h2 : ∫ ω, g ω ∂P = ∫ ω, max 0 (pmax (n + 1) (path x ω)) ∂P
      - ∫ ω, max 0 (pmax n (path x ω)) ∂P := by
    simp only [hg]
    rw [integral_sub (hGi (n + 1)) hHi', hHeq]
  have h3 : ∫ ω, max 0 (pmax n (path x ω)) ∂P ≤ ∫ ω, max 0 (pmax (n + 1) (path x ω)) ∂P :=
    integral_mono (hGi n) (hGi (n + 1)) fun ω => max_le_max le_rfl (pmax_mono n _)
  linarith

theorem maximal_core (P : Measure Ω)
    [IsProbabilityMeasure P] (x : ℕ → ℕ → Ω → ℝ)
    (hx : IsSubadditiveProcess P x) :
    0 ≤ ∫ ω in {ω | ∃ t : ℕ, 1 ≤ t ∧ 0 ≤ x 0 t ω}, x 0 1 ω ∂P := by
  have hmeas := hx.1
  have hS3 := hx.2.2.2
  have hG : ∀ k, Measurable (fun ω => pmax k (path x ω)) := fun k =>
    (pmax_measurable k).comp (path_measurable x hmeas)
  set A : ℕ → Set Ω := fun n => {ω | 0 ≤ pmax n (path x ω)} with hA
  have hAm : ∀ n, MeasurableSet (A n) := fun n =>
    measurableSet_le measurable_const (hG n)
  have hmono : Monotone A := by
    apply monotone_nat_of_le_succ
    intro n ω hω
    exact le_trans hω (pmax_mono n _)
  have hx01 : Integrable (x 0 1) P := hS3.1 1 le_rfl
  have hU : (⋃ n, A n) = {ω | ∃ t : ℕ, 1 ≤ t ∧ 0 ≤ x 0 t ω} := by
    ext ω
    simp only [Set.mem_iUnion, hA, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨n, hn⟩
      exact pmax_path_nonneg x ω n hn
    · rintro ⟨t, ht, hxt⟩
      exact ⟨t - 1, le_trans hxt (le_pmax_path x ω t ht)⟩
  have ht := tendsto_setIntegral_of_monotone (μ := P) (f := x 0 1) hAm hmono
    (hx01.integrableOn)
  rw [hU] at ht
  refine ge_of_tendsto' ht fun n => ?_
  cases n with
  | zero =>
    apply setIntegral_nonneg (hAm 0)
    intro ω hω
    exact hω
  | succ n => exact maximal_step P x hx n

end KingmanSubadditive.Ergodic

open KingmanSubadditive.Ergodic
open MeasureTheory Filter Topology

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (x : ℕ → ℕ → Ω → ℝ)
    (hx : IsSubadditiveProcess P x) :
    0 ≤ ∫ ω in {ω | ∃ t : ℕ, 1 ≤ t ∧ 0 ≤ x 0 t ω}, x 0 1 ω ∂P := by
  exact maximal_core P x hx
