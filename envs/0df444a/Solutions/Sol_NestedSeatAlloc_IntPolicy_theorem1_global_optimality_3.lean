-- Prove2me | solution 3 for NestedSeatAlloc.IntPolicy.theorem1_global_optimality
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T12:43:57.51698+00:00
-- url     : https://prove2.me/submissions/79026d52-b07b-4a4e-a18a-61098c513c30
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Theorems.Thm_NestedSeatAlloc_IntPolicy_theorem1_global_optimality_base
import Theorems.Thm_NestedSeatAlloc_IntPolicy_theorem1_global_optimality_step_all_seats

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f p : ℕ → ℝ)
    (hM : IsSeatModel P X f) (hp : IsProtectionPolicy p)
    (h20 : SubdiffCondition P X f p) :
    IsOptimal P X f p := by
  have hchain : ∀ n : ℕ, ∀ s, 0 ≤ s → ∀ q, IsProtectionPolicy q →
      expRevenue P X f q (n + 1) s ≤ expRevenue P X f p (n + 1) s := by
    intro n
    induction n with
    | zero =>
        intro s hs q hq
        simpa using theorem1_global_optimality_base P X f p hM hp q hq s hs
    | succ n ih =>
        intro s hs q hq
        have hn : 1 ≤ n + 1 := by omega
        have h20n : InSubdiff (expRevenue P X f p (n + 1))
            (p (n + 1)) (f ((n + 1) + 1)) := h20 (n + 1) hn
        have hstep := theorem1_global_optimality_step_all_seats P X f p
          (n + 1) hM hp hn h20n
          (fun t ht r hr => ih t ht r hr)
        simpa only [Nat.succ_eq_add_one] using hstep s hs q hq
  intro q hq k hk s hs
  have hkm : (k - 1) + 1 = k := by omega
  simpa only [hkm] using hchain (k - 1) s hs q hq
