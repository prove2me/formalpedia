-- Prove2me | solution 1 for NestedSeatAlloc.IntPolicy.revenue_frozen_prefix_rebuild
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T14:26:25.272034+00:00
-- url     : https://prove2.me/submissions/6bbfe131-cb5a-4896-89e0-cfa1796a1ac2

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Definitions.Def_prefixRevenueRebuild
import Theorems.Thm_NestedSeatAlloc_IntPolicy_revenue_extensional_on_prefix

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → Ω → ℝ) (f p : ℕ → ℝ) (k : ℕ)
    (ω : Ω) (y s : ℝ) :
    revenue f p (Function.update (fun i => X i ω) (k + 1) y) (k + 1) s =
    revenue f p
      (prefixRevenueRebuild k (y, fun i : (Finset.Icc 1 k) => X i.1 ω))
      (k + 1) s := by
  apply revenue_extensional_on_prefix f p _ _ (k + 1) ?_ s
  intro i hi
  have hlow : 1 ≤ i := (Finset.mem_Icc.mp hi).1
  have hhigh : i ≤ k + 1 := (Finset.mem_Icc.mp hi).2
  by_cases heq : i = k + 1
  · subst i
    simp [prefixRevenueRebuild, Finset.mem_Icc]
  · have hle : i ≤ k := by omega
    have himem : i ∈ Finset.Icc 1 k :=
      Finset.mem_Icc.mpr ⟨hlow, hle⟩
    simp [prefixRevenueRebuild, himem, heq]
