-- Prove2me | solution 1 for HighDimStat.NonparametricLS.thm13_6_critical_radius_exists
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:03:48.917991+00:00
-- url     : https://prove2.me/submissions/627450e8-d7ba-4bed-a614-e1353ffedfef

import Mathlib
import Definitions.Def_HighDimStat_NonparametricLS_Core

namespace HighDimStat.NonparametricLS

open MeasureTheory

/-- The local Gaussian complexity of the empty class vanishes identically. -/
lemma aux_crit_lgc_empty {X Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (x : Fin n → X)
    (w : Fin n → Ω → ℝ) (P : Measure Ω) (δ : ℝ) :
    localGaussianComplexity x w P (∅ : Set (X → ℝ)) δ = 0 := by
  unfold localGaussianComplexity
  have hE : IsEmpty {h : X → ℝ // h ∈ (∅ : Set (X → ℝ)) ∧ empiricalNorm x h ≤ δ} :=
    ⟨fun h => h.2.1⟩
  simp [Real.iSup_of_isEmpty]

end HighDimStat.NonparametricLS

open HighDimStat.NonparametricLS
open MeasureTheory

theorem solution : ¬ (∀ {X Ω : Type} [MeasurableSpace Ω] {n : ℕ} (x : Fin n → X)
    (w : Fin n → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] (hw : IsIIDStdGaussian P w)
    (H : Set (X → ℝ)) (hH : IsStarShaped H),
    (∀ δ t : ℝ, 0 < δ → δ ≤ t →
        localGaussianComplexity x w P H t / t ≤ localGaussianComplexity x w P H δ / δ) ∧
      ∀ c : ℝ, 0 < c →
        ∃ δ, IsLeast {δ : ℝ | 0 < δ ∧ localGaussianComplexity x w P H δ / δ ≤ c * δ} δ) := by
  intro hall
  have hw : IsIIDStdGaussian (Measure.dirac (PUnit.unit : PUnit))
      (fun i : Fin 0 => Fin.elim0 i) :=
    ⟨fun i => Fin.elim0 i, ProbabilityTheory.iIndepFun.of_subsingleton, fun i => Fin.elim0 i⟩
  have hH : IsStarShaped (∅ : Set (PUnit → ℝ)) := by
    intro h hh
    exact absurd hh (Set.notMem_empty h)
  obtain ⟨-, h2⟩ := @hall PUnit PUnit _ 0 (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
    (Measure.dirac PUnit.unit) _ hw ∅ hH
  obtain ⟨δ, hmem, hlow⟩ := h2 1 one_pos
  simp only [aux_crit_lgc_empty, zero_div, one_mul, Set.mem_ofPred_eq] at hmem
  have hmem' : δ / 2 ∈ {δ : ℝ | 0 < δ ∧
      localGaussianComplexity (fun i : Fin 0 => (Fin.elim0 i : PUnit))
        (fun i : Fin 0 => (Fin.elim0 i : PUnit → ℝ)) (Measure.dirac PUnit.unit)
        (∅ : Set (PUnit → ℝ)) δ / δ ≤ 1 * δ} := by
    simp only [aux_crit_lgc_empty, zero_div, one_mul, Set.mem_ofPred_eq]
    constructor <;> linarith [hmem.1]
  have := hlow hmem'
  linarith [hmem.1]
