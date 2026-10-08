-- Prove2me | solution 1 for NestedSeatAlloc.IntPolicy.clbi_propagation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T06:59:25.96338+00:00
-- url     : https://prove2.me/submissions/d46b15c0-9f51-4e05-87f8-ec230d557655

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Definitions.Def_NestedSeatAlloc_IntPolicy_CLBI
import Theorems.Thm_NestedSeatAlloc_IntPolicy_corollary1_concave
import Theorems.Thm_NestedSeatAlloc_IntPolicy_clbi_affine_unit_propagation

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open NestedSeatAlloc.IntPolicy

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f : ℕ → ℝ)
    (hM : IsSeatModel P X f)
    (hint : ∀ k ω, ∃ n : ℕ, X k ω = n)
    (k : ℕ) (hk : 1 ≤ k) (p : ℕ → ℕ)
    (hclbi : IsCLBI (expRevenue P X f (fun j => (p j : ℝ)) k))
    (h20 : ∀ j ∈ Finset.Icc 1 k,
      InSubdiff (expRevenue P X f (fun j => (p j : ℝ)) j) (p j) (f (j + 1))) :
    IsCLBI (expRevenue P X f (fun j => (p j : ℝ)) (k + 1)) := by
  have hp : IsProtectionPolicy (fun j => (p j : ℝ)) := by
    intro j hj
    change (0 : ℝ) ≤ (p j : ℝ)
    exact_mod_cast Nat.zero_le (p j)
  have hk_mem : k ∈ Finset.Icc 1 k :=
    Finset.mem_Icc.mpr ⟨hk, le_rfl⟩
  have h20k :
      InSubdiff (expRevenue P X f (fun j => (p j : ℝ)) k) (p k) (f (k + 1)) :=
    h20 k hk_mem
  have hconc :
      ConcaveOn ℝ (Set.Ici 0)
        (expRevenue P X f (fun j => (p j : ℝ)) (k + 1)) := by
    exact corollary1_concave P X f (fun j => (p j : ℝ)) hM hp k hk
      hclbi.1 h20k
  have hunit : ∀ m : ℕ, ∃ a b : ℝ,
      ∀ s ∈ Set.Icc (m : ℝ) ((m : ℝ) + 1),
        expRevenue P X f (fun j => (p j : ℝ)) (k + 1) s = a + b * s :=
    clbi_affine_unit_propagation P X f hM hint k p hclbi.2
  exact ⟨hconc, hunit⟩
