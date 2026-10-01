-- Prove2me | solution 1 for GoldenRatioVI.Explicit.fejer_convergence
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T17:13:48.902984+00:00
-- url     : https://prove2.me/submissions/03f4546c-0512-4487-8bb0-8df9bc8572fc

import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Order.Monotone.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic
open Filter
open scoped Topology
set_option autoImplicit false

private theorem fejer_tendsto_of_cluster {E : Type*} [PseudoMetricSpace E]
    (p : ℕ → E) (l : E) (hmono : ∀ n, dist (p (n+1)) l ≤ dist (p n) l)
    (u : ℕ → ℕ) (hu : Tendsto (fun n => p (u n)) atTop (𝓝 l)) :
    Tendsto p atTop (𝓝 l) := by
  have ha : Antitone (fun n => dist (p n) l) := antitone_nat_of_succ_le hmono
  rw [Metric.tendsto_atTop] at hu ⊢
  intro ε hε
  obtain ⟨N,hN⟩ := hu ε hε
  refine ⟨u N,?_⟩
  intro n hn
  exact (ha hn).trans_lt (hN N le_rfl)

theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (z : ℕ → E) (C : Set E) (hC : C.Nonempty)
    (hfejer : ∀ c∈C,∀ k : ℕ,‖z (k+1)-c‖ ≤ ‖z k-c‖)
    (hclus : ∀ x : E,MapClusterPt x atTop z → x∈C) :
    ∃ x∈C,Tendsto z atTop (𝓝 x) := by
  obtain ⟨a,ha⟩ := hC
  have hm : Antitone (fun k => dist (z k) a) := by
    apply antitone_nat_of_succ_le
    intro k
    simpa only [dist_eq_norm] using hfejer a ha k
  have hb : ∀ k,z k∈Metric.closedBall a (dist (z 0) a) := fun k => hm (Nat.zero_le k)
  have hc := isCompact_closedBall a (dist (z 0) a)
  obtain ⟨l,hl,hlc⟩ := hc.exists_mapClusterPt (f := atTop) (u := z)
    (Filter.le_principal_iff.mpr (Filter.mem_map.mpr (Filter.Eventually.of_forall hb)))
  have hlC := hclus l hlc
  obtain ⟨u,hu,huz⟩ := hlc.tendsto_subseq
  refine ⟨l,hlC,fejer_tendsto_of_cluster z l ?_ u huz⟩
  intro k
  simpa only [dist_eq_norm] using hfejer l hlC k
