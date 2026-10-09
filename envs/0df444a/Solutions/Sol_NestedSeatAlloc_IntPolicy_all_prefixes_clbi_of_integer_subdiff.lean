-- Prove2me | solution 1 for NestedSeatAlloc.IntPolicy.all_prefixes_clbi_of_integer_subdiff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T13:45:34.450279+00:00
-- url     : https://prove2.me/submissions/f28f7529-42d5-49fa-8964-71512d76bab5

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Definitions.Def_NestedSeatAlloc_IntPolicy_CLBI
import Theorems.Thm_NestedSeatAlloc_IntPolicy_eq27_er1_clbi
import Theorems.Thm_NestedSeatAlloc_IntPolicy_clbi_propagation

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f : ℕ → ℝ) (p : ℕ → ℕ)
    (hM : IsSeatModel P X f)
    (hint : ∀ i ω, ∃ n : ℕ, X i ω = n)
    (hpos : ∀ i, 1 ≤ i → 0 < f i)
    (h20 : SubdiffCondition P X f (fun i => (p i : ℝ))) :
    ∀ k, 1 ≤ k →
      IsCLBI (expRevenue P X f (fun i => (p i : ℝ)) k) := by
  have hseq : ∀ n : ℕ,
      IsCLBI (expRevenue P X f (fun i => (p i : ℝ)) (n + 1)) := by
    intro n
    induction n with
    | zero =>
        have hf1 : 0 ≤ f 1 := le_of_lt (hpos 1 (by omega))
        exact (eq27_er1_clbi P X f (fun i => (p i : ℝ))
          hM hint hf1).1
    | succ n ih =>
        have hkn : 1 ≤ n + 1 := by omega
        have hpref : ∀ j ∈ Finset.Icc 1 (n + 1),
            InSubdiff
              (expRevenue P X f (fun i => (p i : ℝ)) j)
              (p j) (f (j + 1)) := by
          intro j hj
          have hjone : 1 ≤ j := (Finset.mem_Icc.mp hj).1
          exact h20 j hjone
        have hnext := clbi_propagation P X f hM hint (n + 1)
          hkn p ih hpref
        simpa only [Nat.succ_eq_add_one] using hnext
  intro k hk
  have hkm : (k - 1) + 1 = k := by omega
  simpa only [hkm] using hseq (k - 1)
