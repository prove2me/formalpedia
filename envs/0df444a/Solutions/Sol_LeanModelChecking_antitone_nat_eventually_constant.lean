-- Prove2me | solution 1 for LeanModelChecking.antitone_nat_eventually_constant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:46:04.103888+00:00
-- url     : https://prove2.me/submissions/3748a8dc-1e32-44cc-96bf-5148183c050e

module
public import Definitions.Def_LeanPool_LeanModelChecking_LTLNNF
public import Definitions.Def_LeanPool_LeanModelChecking_ABW
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Tactic.Continuity
public import Mathlib.Topology.Instances.Discrete
public import Mathlib.Topology.Order.MonotoneConvergence
public import Definitions.Def_LeanPool_LeanModelChecking_NNFABW

set_option autoImplicit true
@[expose] public section
public section
open LeanModelChecking
namespace LeanModelChecking
theorem _root_.solution
  {f : ℕ → ℕ} (hf : Antitone f)
    : ∃ N c, (∀ n ≥ N, f n = c) ∧ c ≤ f 0 := by
  have h := tendsto_atTop_ciInf hf ⟨0, Set.forall_mem_range.mpr fun _ => Nat.zero_le _⟩
  simp only [nhds_discrete, Filter.tendsto_pure, Filter.eventually_atTop] at h
  obtain ⟨N, h⟩ := h
  refine ⟨N, f N, fun n hn => ?_, hf (Nat.zero_le N)⟩
  rw [h n hn, h N le_rfl]
end LeanModelChecking
