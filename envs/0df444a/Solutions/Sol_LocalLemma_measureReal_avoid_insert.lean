-- Prove2me | solution 1 for LocalLemma.measureReal_avoid_insert
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:22:16.061272+00:00
-- url     : https://prove2.me/submissions/da184b7e-f876-4d51-b05a-ee5d3c34c3a5

module
public import Mathlib
public import Definitions.Def_LocalLemmaLib_Coin
public import Definitions.Def_LocalLemmaLib_LocalLemma
public import Theorems.Thm_LocalLemma_avoid_insert

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory ProbabilityTheory
open LocalLemma
namespace LocalLemma
theorem _root_.solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] {n : ℕ} (A : Fin n → Set Ω) (hA : ∀ i, MeasurableSet (A i))
    (S : Finset (Fin n)) (j : Fin n) :
    μ.real (avoid A (insert j S)) = μ.real (avoid A S) - μ.real (avoid A S ∩ A j) := by
  rw [avoid_insert]
  have := measureReal_inter_add_sdiff (μ := μ) (s := avoid A S) (hA j)
  linarith
end LocalLemma
