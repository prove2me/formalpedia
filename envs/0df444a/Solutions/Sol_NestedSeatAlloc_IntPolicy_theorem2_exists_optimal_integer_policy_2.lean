-- Prove2me | solution 2 for NestedSeatAlloc.IntPolicy.theorem2_exists_optimal_integer_policy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T15:08:00.164855+00:00
-- url     : https://prove2.me/submissions/30ea2f7a-fb87-4060-83b7-8ec2175d50b7

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Definitions.Def_NestedSeatAlloc_IntPolicy_CLBI
import Theorems.Thm_NestedSeatAlloc_IntPolicy_theorem2_integer_subdiff_policy_exists
import Theorems.Thm_NestedSeatAlloc_IntPolicy_all_prefixes_clbi_of_integer_subdiff
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
    (X : ℕ → Ω → ℝ) (f : ℕ → ℝ)
    (hM : IsSeatModel P X f)
    (hint : ∀ k ω, ∃ n : ℕ, X k ω = n)
    (hpos : ∀ k, 1 ≤ k → 0 < f k) :
    ∃ p : ℕ → ℕ, IsOptimal P X f (fun k => (p k : ℝ)) ∧
      SubdiffCondition P X f (fun k => (p k : ℝ)) := by
  obtain ⟨p, h20⟩ :=
    theorem2_integer_subdiff_policy_exists P X f hM hint hpos
  let pR : ℕ → ℝ := fun i => (p i : ℝ)
  have hp : IsProtectionPolicy pR := by
    intro i hi
    exact Nat.cast_nonneg _
  have hCLBI : ∀ k, 1 ≤ k →
      IsCLBI (expRevenue P X f pR k) := by
    simpa only [pR] using
      (all_prefixes_clbi_of_integer_subdiff P X f p
        hM hint hpos h20)
  have hchain : ∀ n : ℕ, ∀ s, 0 ≤ s →
      ∀ q, IsProtectionPolicy q →
        expRevenue P X f q (n + 1) s ≤
          expRevenue P X f pR (n + 1) s := by
    intro n
    induction n with
    | zero =>
        intro s hs q hq
        exact theorem1_global_optimality_base P X f pR
          hM hp q hq s hs
    | succ n ih =>
        intro s hs q hq
        have hk : 1 ≤ n + 1 := by omega
        have hconc : ConcaveOn ℝ (Set.Ici 0)
            (expRevenue P X f pR (n + 1)) :=
          (hCLBI (n + 1) hk).1
        have hsub : InSubdiff
            (expRevenue P X f pR (n + 1))
            (pR (n + 1)) (f ((n + 1) + 1)) := by
          simpa only [pR] using h20 (n + 1) hk
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
            (fun y => condRevenue P X f pR ((n + 1) + 1) y s) μ :=
          condRevenue_integrable_next_demand P X f pR hM hp
            (n + 1) s hs hsU
        have hy : ∀ᵐ y ∂μ, (0 : ℝ) ≤ y := by
          apply (ae_map_iff (hM.meas ((n + 1) + 1)).aemeasurable
            (show MeasurableSet {y : ℝ | (0 : ℝ) ≤ y} from
              measurableSet_Ici)).2
          exact Filter.Eventually.of_forall (hM.nonneg ((n + 1) + 1))
        have hdom : (fun y =>
            condRevenue P X f q ((n + 1) + 1) y s) ≤ᵐ[μ]
            (fun y =>
              condRevenue P X f pR ((n + 1) + 1) y s) := by
          filter_upwards [hy] with y hnonneg
          exact conditional_revenue_dominance_fixed
            P X f pR q (n + 1) s y
            hM hp hq hk hs hnonneg
            (fun t ht => ih t ht q hq) hconc hsub
        have hQ := expRevenue_eq_integral_condRevenue
          P X f q hM hq (n + 1) hk s hs
        have hP := expRevenue_eq_integral_condRevenue
          P X f pR hM hp (n + 1) hk s hs
        have hstep :
            expRevenue P X f q ((n + 1) + 1) s ≤
              expRevenue P X f pR ((n + 1) + 1) s := by
          calc
            expRevenue P X f q ((n + 1) + 1) s =
                ∫ y, condRevenue P X f q ((n + 1) + 1) y s ∂μ := hQ
            _ ≤ ∫ y, condRevenue P X f pR ((n + 1) + 1) y s ∂μ :=
              integral_mono_ae hIq hIp hdom
            _ = expRevenue P X f pR ((n + 1) + 1) s := hP.symm
        simpa only [Nat.succ_eq_add_one] using hstep
  refine ⟨p, ?_, h20⟩
  intro q hq k hk s hs
  have hkm : (k - 1) + 1 = k := by omega
  simpa only [pR, hkm] using hchain (k - 1) s hs q hq
