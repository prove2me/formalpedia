-- Prove2me | solution 1 for NestedSeatAlloc.IntPolicy.theorem1_global_optimality_of_prefix_concavity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T15:52:24.740383+00:00
-- url     : https://prove2.me/submissions/19f54705-371b-46c7-8c5f-31fcde9e9176

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Theorems.Thm_NestedSeatAlloc_IntPolicy_theorem1_global_optimality_base
import Theorems.Thm_NestedSeatAlloc_IntPolicy_conditional_revenue_dominance_fixed
import Theorems.Thm_NestedSeatAlloc_IntPolicy_sfinite_prefix_demand_law
import Theorems.Thm_NestedSeatAlloc_IntPolicy_condRevenue_integrable_next_demand
import Theorems.Thm_NestedSeatAlloc_IntPolicy_expRevenue_eq_integral_condRevenue

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f p : ℕ → ℝ)
    (hM : IsSeatModel P X f) (hp : IsProtectionPolicy p)
    (h20 : SubdiffCondition P X f p)
    (hconc : ∀ k, 1 ≤ k →
      ConcaveOn ℝ (Set.Ici 0) (expRevenue P X f p k)) :
    IsOptimal P X f p := by
  have hchain : ∀ n : ℕ, ∀ s, 0 ≤ s →
      ∀ q, IsProtectionPolicy q →
        expRevenue P X f q (n + 1) s ≤
          expRevenue P X f p (n + 1) s := by
    intro n
    induction n with
    | zero =>
        intro s hs q hq
        exact theorem1_global_optimality_base P X f p
          hM hp q hq s hs
    | succ n ih =>
        intro s hs q hq
        have hk : 1 ≤ n + 1 := by omega
        have hconc_k : ConcaveOn ℝ (Set.Ici 0)
            (expRevenue P X f p (n + 1)) :=
          hconc (n + 1) hk
        have hsub : InSubdiff
            (expRevenue P X f p (n + 1))
            (p (n + 1)) (f ((n + 1) + 1)) :=
          h20 (n + 1) hk
        let μ : Measure ℝ := Measure.map (X ((n + 1) + 1)) P
        have hsU : SFinite (Measure.map
          (fun ω : Ω =>
            fun i : (Finset.Icc 1 (n + 1)) => X i.1 ω) P) :=
          sfinite_prefix_demand_law P X f hM (n + 1)
        have hIq : Integrable
            (fun y => condRevenue P X f q ((n + 1) + 1) y s) μ :=
          condRevenue_integrable_next_demand P X f q hM hq
            (n + 1) s hs hsU
        have hIp : Integrable
            (fun y => condRevenue P X f p ((n + 1) + 1) y s) μ :=
          condRevenue_integrable_next_demand P X f p hM hp
            (n + 1) s hs hsU
        have hy : ∀ᵐ y ∂μ, (0 : ℝ) ≤ y := by
          apply (ae_map_iff (hM.meas ((n + 1) + 1)).aemeasurable
            (show MeasurableSet {y : ℝ | (0 : ℝ) ≤ y} from
              measurableSet_Ici)).2
          exact Filter.Eventually.of_forall (hM.nonneg ((n + 1) + 1))
        have hdom : (fun y =>
            condRevenue P X f q ((n + 1) + 1) y s) ≤ᵐ[μ]
            (fun y =>
              condRevenue P X f p ((n + 1) + 1) y s) := by
          filter_upwards [hy] with y hnonneg
          exact conditional_revenue_dominance_fixed
            P X f p q (n + 1) s y
            hM hp hq hk hs hnonneg
            (fun t ht => ih t ht q hq) hconc_k hsub
        have hQ := expRevenue_eq_integral_condRevenue
          P X f q hM hq (n + 1) hk s hs
        have hP := expRevenue_eq_integral_condRevenue
          P X f p hM hp (n + 1) hk s hs
        have hstep :
            expRevenue P X f q ((n + 1) + 1) s ≤
              expRevenue P X f p ((n + 1) + 1) s := by
          calc
            expRevenue P X f q ((n + 1) + 1) s =
                ∫ y, condRevenue P X f q ((n + 1) + 1) y s ∂μ := hQ
            _ ≤ ∫ y, condRevenue P X f p ((n + 1) + 1) y s ∂μ :=
              integral_mono_ae hIq hIp hdom
            _ = expRevenue P X f p ((n + 1) + 1) s := hP.symm
        simpa only [Nat.succ_eq_add_one] using hstep
  intro q hq k hk s hs
  have hkm : (k - 1) + 1 = k := by omega
  simpa only [hkm] using hchain (k - 1) s hs q hq
