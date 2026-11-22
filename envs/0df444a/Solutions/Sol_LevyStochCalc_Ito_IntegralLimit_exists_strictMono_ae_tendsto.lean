-- Prove2me | solution 1 for LevyStochCalc.Ito.IntegralLimit.exists_strictMono_ae_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @yuzhou
-- created : 2026-11-22T04:01:20.134117+00:00
-- url     : https://prove2.me/submissions/7b0b165a-895a-4cdc-bc30-5c1afcccdbe5

import Definitions.Def_LevyStochCalc_Ito_ItoFormulaRandomShift_F000
import Definitions.Def_LevyStochCalc_Ito_ItoFormulaRandomShift_F001
import Definitions.Def_LevyStochCalc_Poisson_SmallJump_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Limits of stochastic integrals along dominated sequences of integrands

A sequence of integrands converging pointwise almost everywhere and dominated by a
square-integrable function converges to its limit in the energy norm, over `P ⊗ ds` for a
Brownian integrand and over `P ⊗ ds ⊗ ν` for a marked one. Through the `L²` isometries of the
Itô and compensated Itô–Lévy integrals this transfers to the integrals themselves: they converge
in `L²`, hence almost surely along a subsequence.

## Main statements

All statements live in the `LevyStochCalc.Ito.IntegralLimit` namespace.

* `tendsto_lintegral_sq_sub_of_dominated` — dominated convergence in the energy norm over
  `P ⊗ ds`.
* `tendsto_lintegral_sq_sub_mark_of_dominated` — dominated convergence in the energy norm over
  `P ⊗ ds ⊗ ν`.
* `tendsto_lintegral_sq_stochasticIntegralBrownian_of_dominated` and
  `exists_seq_ae_tendsto_stochasticIntegralBrownian_of_dominated` — the Itô integrals of a
  dominated sequence of integrands converge in `L²`, and almost surely along a strictly monotone
  subsequence.
* `tendsto_lintegral_sq_compensatedStochasticIntegral_of_dominated` and
  `exists_seq_ae_tendsto_compensatedStochasticIntegral_of_dominated` — the same for the
  compensated Itô–Lévy integral.
* `tendsto_lintegral_sq_stochasticIntegral_markCut_compl` and
  `exists_seq_ae_tendsto_stochasticIntegral_markCut_compl` — the compensated Itô–Lévy integrals
  of an integrand cut to the complements of a family of mark sets that eventually misses almost
  every mark converge to the compensated Itô–Lévy integral of the integrand; the suffix
  `_of_antitone` names the same conclusions under an antitone family with null intersection.

## References

* Applebaum, *Lévy Processes and Stochastic Calculus*, 2009, §4.4 (Thm 4.4.7).
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.IntegralLimit

universe u v

section Basic

variable {α : Type*} [MeasurableSpace α]

end Basic

section Unmarked

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}

end Unmarked

section Marked

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} {ν : Measure E} [SigmaFinite ν]

end Marked

section Subsequence

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}



theorem _root_.solution {u : ℕ → Ω → ℝ} {v : Ω → ℝ} {ms : ℕ → ℕ}
    (hms : ∀ i : ℕ, i ≤ ms i)
    (h : ∀ᵐ ω ∂P, Tendsto (fun i => u (ms i) ω) atTop (𝓝 (v ω))) :
    ∃ k : ℕ → ℕ, StrictMono k ∧ (∀ i : ℕ, i ≤ k i) ∧
      ∀ᵐ ω ∂P, Tendsto (fun i => u (k i) ω) atTop (𝓝 (v ω)) := by
  let j : ℕ → ℕ := Nat.rec 0 (fun _ q => ms q + 1)
  have hJ (i : ℕ) : j (i + 1) = ms (j i) + 1 := rfl
  have hj : StrictMono j := strictMono_nat_of_lt_succ fun i => by
    rw [hJ]
    exact (hms (j i)).trans_lt (Nat.lt_succ_self _)
  let k : ℕ → ℕ := ms ∘ j
  have hk : StrictMono k := strictMono_nat_of_lt_succ fun i => by
    change ms (j i) < ms (j (i + 1))
    calc
      _ < j (i + 1) := by rw [hJ]; exact Nat.lt_succ_self _
      _ ≤ _ := hms _
  refine ⟨k, hk, ?_, ?_⟩
  · intro i
    exact hk.id_le i
  · filter_upwards [h] with ω hω
    exact hω.comp hj.tendsto_atTop
