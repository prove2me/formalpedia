-- Prove2me | solution 1 for NashFlowLT.SteadyState.primal_feasible
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T09:32:55.514298+00:00
-- url     : https://prove2.me/submissions/69a97cc8-12b0-4d34-ae64-216403d3c13f

import Mathlib
import Definitions.Def_NashFlowLT_SteadyState_Model
import Theorems.Thm_FlowsNetworks_MaxFlow_max_flow_min_cut

open NashFlowLT.SteadyState Finset

namespace P2MNFLTPrimal

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- aggregated capacity of the node pair `p` -/
noncomputable def aggCap (N : Network V E) (p : V × V) : ℝ :=
  ∑ e ∈ univ.filter (fun e => (N.tail e, N.head e) = p), N.nu e

lemma aggCap_nonneg (N : Network V E) (hN : N.Standing) (p : V × V) : 0 ≤ aggCap N p :=
  Finset.sum_nonneg (fun e _ => (hN.1 e).le)

lemma regroup (N : Network V E) (P : V × V → Prop) [DecidablePred P] (h : V × V → ℝ) :
    ∑ e ∈ univ.filter (fun e => P (N.tail e, N.head e)), h (N.tail e, N.head e) * N.nu e =
      ∑ p ∈ univ.filter P, h p * aggCap N p := by
  rw [← Finset.sum_fiberwise (univ.filter (fun e => P (N.tail e, N.head e)))
    (fun e => (N.tail e, N.head e)), Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p _
  split_ifs with hp
  · rw [aggCap, Finset.mul_sum]
    have : (univ.filter (fun e => P (N.tail e, N.head e))).filter
        (fun e => (N.tail e, N.head e) = p) = univ.filter (fun e => (N.tail e, N.head e) = p) := by
      ext e
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_iff_right_iff_imp]
      intro he; rw [he]; exact hp
    rw [this]
    apply Finset.sum_congr rfl
    intro e he
    rw [(Finset.mem_filter.1 he).2]
  · apply Finset.sum_eq_zero
    intro e he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
    exact absurd (he.2 ▸ he.1) hp

/-- the aggregated simple network -/
noncomputable def aggNet (N : Network V E) (hN : N.Standing) : FlowsNetworks.MaxFlow.Network V where
  arcs := univ.filter (fun p : V × V => p.1 ≠ p.2 ∧ 0 < aggCap N p)
  loopless := fun p hp => (Finset.mem_filter.1 hp).2.1
  cap := fun a b => aggCap N (a, b)
  cap_nonneg := fun p _ => aggCap_nonneg N hN p

lemma cut_eq (N : Network V E) (hN : N.Standing) (S : Finset V) :
    FlowsNetworks.MaxFlow.cutCapacity (aggNet N hN) S = cutCapacity N S := by
  unfold FlowsNetworks.MaxFlow.cutCapacity FlowsNetworks.MaxFlow.arcSum
    FlowsNetworks.MaxFlow.arcsBetween cutCapacity
  have h1 := regroup N (fun p => p.1 ∈ S ∧ p.2 ∉ S) (fun _ => 1)
  simp only [one_mul] at h1
  rw [h1]
  apply Finset.sum_subset
  · intro p hp
    simp only [aggNet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl] at hp ⊢
    exact hp.2
  · intro p hp hnot
    simp only [aggNet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl,
      not_and] at hp hnot
    have hne : p.1 ≠ p.2 := fun h => hp.2 (h ▸ hp.1)
    have h2 : ¬ 0 < aggCap N p := fun hc => hnot ⟨hne, hc⟩ hp.1 hp.2
    exact le_antisymm (not_lt.1 h2) (aggCap_nonneg N hN p)

end P2MNFLTPrimal

open P2MNFLTPrimal in
theorem solution {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (N : Network V E) (hN : N.Standing)
    (hcut : ∀ S : Finset V, N.s ∈ S → N.t ∉ S → N.u0 ≤ cutCapacity N S) :
    ∃ y : E → ℝ, IsPrimalFeasible N y := by
  set G := aggNet N hN with hG
  have hst := hN.2.2.2.1
  obtain ⟨v, ⟨⟨f, hf⟩, -⟩, ⟨X, hX⟩, hvle⟩ :=
    FlowsNetworks.MaxFlow.max_flow_min_cut G N.s N.t hst
  obtain ⟨hsX, htX, hvX⟩ := hX
  have hu0 := hN.2.2.1
  have hv : N.u0 ≤ v := by rw [hvX, cut_eq]; exact hcut X hsX htX
  have hvpos : 0 < v := lt_of_lt_of_le hu0 hv
  obtain ⟨hsupp, hf0, hfc, hcons⟩ := hf
  set lam := N.u0 / v with hlam
  have hlam0 : 0 ≤ lam := div_nonneg hu0.le hvpos.le
  have hlam1 : lam ≤ 1 := (div_le_one hvpos).2 hv
  have hlamv : lam * v = N.u0 := by rw [hlam]; field_simp
  set Y : V × V → ℝ := fun p => if p ∈ G.arcs then f p.1 p.2 / aggCap N p else 0 with hY
  have hYC : ∀ p, Y p * aggCap N p = f p.1 p.2 := by
    intro p
    by_cases hp : p ∈ G.arcs
    · have hpos : 0 < aggCap N p := (Finset.mem_filter.1 hp).2.2
      simp only [Y, if_pos hp]; field_simp
    · simp only [Y, if_neg hp, zero_mul]
      exact (hsupp p.1 p.2 hp).symm
  have hY0 : ∀ p, 0 ≤ Y p := by
    intro p
    by_cases hp : p ∈ G.arcs
    · have hpos : 0 < aggCap N p := (Finset.mem_filter.1 hp).2.2
      simp only [Y, if_pos hp]; exact div_nonneg (hf0 p hp) hpos.le
    · simp [Y, hp]
  have hY1 : ∀ p, Y p ≤ 1 := by
    intro p
    by_cases hp : p ∈ G.arcs
    · have hpos : 0 < aggCap N p := (Finset.mem_filter.1 hp).2.2
      simp only [Y, if_pos hp]; exact (div_le_one hpos).2 (hfc p hp)
    · simp [Y, hp]
  refine ⟨fun e => (lam * Y (N.tail e, N.head e)) * N.nu e, ?_, ?_⟩
  · intro w
    have hout := regroup N (fun p => p.1 = w) (fun p => lam * Y p)
    have hin := regroup N (fun p => p.2 = w) (fun p => lam * Y p)
    simp only at hout hin
    rw [hout, hin]
    have hsum : ∀ (P : V × V → Prop) [DecidablePred P],
        ∑ p ∈ univ.filter P, lam * Y p * aggCap N p = lam * ∑ p ∈ G.arcs.filter P, f p.1 p.2 := by
      intro P _
      rw [Finset.mul_sum]
      symm
      apply Finset.sum_subset_zero_on_sdiff
      · intro p hp; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢; exact hp.2
      · intro p hp
        simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and, not_and] at hp
        rw [mul_assoc, hYC]
        have : p ∉ G.arcs := fun h => hp.2 h hp.1
        rw [hsupp p.1 p.2 this, mul_zero]
      · intro p _; rw [mul_assoc, hYC]
    rw [hsum, hsum, ← mul_sub]
    have hnet : FlowsNetworks.MaxFlow.netFlowOut G f w =
        (∑ p ∈ G.arcs.filter (fun p => p.1 = w), f p.1 p.2) -
          ∑ p ∈ G.arcs.filter (fun p => p.2 = w), f p.1 p.2 := rfl
    rw [← hnet]
    obtain ⟨hcs, hct, hco⟩ := hcons
    by_cases hws : w = N.s
    · subst hws; rw [hcs, if_pos rfl, hlamv]
    · by_cases hwt : w = N.t
      · subst hwt; rw [hct, if_neg hws, if_pos rfl, mul_neg, hlamv]
      · rw [hco w hws hwt, if_neg hws, if_neg hwt, mul_zero]
  · intro e
    have hnu := hN.1 e
    have h1 := hY0 (N.tail e, N.head e)
    have h2 := hY1 (N.tail e, N.head e)
    constructor
    · positivity
    · have : lam * Y (N.tail e, N.head e) ≤ 1 := by nlinarith
      nlinarith
