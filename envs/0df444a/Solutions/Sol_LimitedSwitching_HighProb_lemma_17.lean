-- Prove2me | solution 1 for LimitedSwitching.HighProb.lemma_17
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T02:03:14.393317+00:00
-- url     : https://prove2.me/submissions/7700f29a-c798-4360-8817-bc5995758e52

import Mathlib
import Definitions.Def_LimitedSwitching_HighProb_Setting

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Aux_lemma17
open LimitedSwitching.HighProb

theorem argmin_le {n : ℕ} [NeZero n] (v : Fin n → ℝ) (j : Fin n) :
    v (argminFin v) ≤ v j := by
  have hmem : argminFin v ∈
      Finset.univ.filter (fun i => v i = Finset.univ.inf' Finset.univ_nonempty v) := by
    unfold argminFin
    exact Finset.min'_mem _ _
  rw [Finset.mem_filter] at hmem
  rw [hmem.2]
  exact Finset.inf'_le _ (Finset.mem_univ j)

theorem btl {n : ℕ} [NeZero n] (ℓ : ℕ → Fin n → ℝ) (T : ℕ) :
    ∑ t ∈ Finset.range (T + 1),
        ℓ t (argminFin (fun j => ∑ s ∈ Finset.range (t + 1), ℓ s j))
      ≤ ∑ s ∈ Finset.range (T + 1),
        ℓ s (argminFin (fun j => ∑ s ∈ Finset.range (T + 1), ℓ s j)) := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ (fun s => ℓ s _) (T + 1)]
    have h := argmin_le (fun j => ∑ s ∈ Finset.range (T + 1), ℓ s j)
      (argminFin (fun j => ∑ s ∈ Finset.range (T + 1 + 1), ℓ s j))
    linarith

end Aux_lemma17

open LimitedSwitching.HighProb in
theorem solution {n : ℕ} [NeZero n] (ℓ : ℕ → Fin n → ℝ) (T : ℕ) (i : Fin n) :
    ∑ t ∈ Finset.range (T + 1),
        ℓ t (argminFin (fun j => ∑ s ∈ Finset.range (t + 1), ℓ s j))
      ≤ ∑ t ∈ Finset.range (T + 1), ℓ t i := by
  have h1 := Aux_lemma17.btl ℓ T
  have h2 := Aux_lemma17.argmin_le (fun j => ∑ s ∈ Finset.range (T + 1), ℓ s j) i
  linarith
