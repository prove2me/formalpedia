-- Prove2me | solution 1 for MulticutLShaped.Bound.multicut_iteration_bound
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T04:10:57.815703+00:00
-- url     : https://prove2.me/submissions/667eed7f-bb9d-4edd-afef-6e75bf285f0e

import Mathlib
import Definitions.Def_StochasticProg_Recourse_Instance
import Definitions.Def_StochasticProg_LShaped_Bases
import Definitions.Def_MulticutLShaped_Bound_Cuts
import Definitions.Def_MulticutLShaped_Bound_Masters
import Definitions.Def_MulticutLShaped_Bound_Algorithm

open StochasticProg.Recourse StochasticProg.LShaped
open scoped Matrix
open Matrix Classical

namespace MulticutLShaped.Bound

variable {n1 n2 m1 m2 K : ℕ}

lemma mc_cut_mem (inst : Instance n1 n2 m1 m2 K) (s : State n1 K) (x : Fin n1 → ℝ)
    (θ : Fin K → ℝ) (β : Fin K → Basis n2 m2) (hopt : IsMasterOptimal inst s x θ)
    (hβ : ∀ k, IsSimplexOptimal inst k (β k) x) (k : Fin K) :
    optCut inst k (β k) ∈ cutSet inst k := by
  classical
  unfold cutSet
  rw [Finset.mem_image]
  refine ⟨β k, ?_, rfl⟩
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_univ _, x, hopt.1.1, hβ k⟩

lemma mc_cut_new (inst : Instance n1 n2 m1 m2 K) (s : State n1 K) (x : Fin n1 → ℝ)
    (θ : Fin K → ℝ) (β : Fin K → Basis n2 m2) (hopt : IsMasterOptimal inst s x θ)
    (k : Fin K) (hc : Cond14 inst s x θ k (β k)) :
    optCut inst k (β k) ∉ s.optCuts k := by
  intro hmem
  rcases hc with h | h
  · rw [h] at hmem; simp at hmem
  · have := hopt.1.2.2 k _ hmem
    simp only [optCut, smul_dotProduct, smul_eq_mul] at this
    rw [dotProduct_sub, dotProduct_mulVec] at h
    nlinarith

lemma mc_step_opt (inst : Instance n1 n2 m1 m2 K) (s s' : State n1 K) (hstep : Step inst s s')
    (hret : s'.nOpt = s.nOpt + 1) :
    ∃ (x : Fin n1 → ℝ) (θ : Fin K → ℝ) (β : Fin K → Basis n2 m2), IsMasterOptimal inst s x θ ∧ (∀ k, IsSimplexOptimal inst k (β k) x) ∧
      (∃ k, Cond14 inst s x θ k (β k)) ∧
      s'.optCuts = (fun k => if Cond14 inst s x θ k (β k) then s.optCuts k ++ [optCut inst k (β k)]
          else s.optCuts k) := by
  cases hstep with
  | feas x θ k b hopt hfirst hpos hb => simp at hret
  | opt x θ β hopt hfeas hβ hS => exact ⟨x, θ, β, hopt, hβ, hS, rfl⟩

theorem new_cut_core (inst : Instance n1 n2 m1 m2 K)
    (s s' : State n1 K) (hstep : Step inst s s') (hret : s'.nOpt = s.nOpt + 1) :
    (∀ k, s'.optCuts k = s.optCuts k ∨
      ∃ c ∈ cutSet inst k, c ∉ s.optCuts k ∧ s'.optCuts k = s.optCuts k ++ [c]) ∧
    ∃ k, ∃ c ∈ cutSet inst k, c ∉ s.optCuts k ∧ s'.optCuts k = s.optCuts k ++ [c] := by
  obtain ⟨x, θ, β, hopt, hβ, ⟨k0, hk0⟩, he⟩ := mc_step_opt inst s s' hstep hret
  rw [he]
  refine ⟨fun k => ?_, k0, optCut inst k0 (β k0), mc_cut_mem inst s x θ β hopt hβ k0,
    mc_cut_new inst s x θ β hopt k0 hk0, by simp [hk0]⟩
  by_cases hk : Cond14 inst s x θ k (β k)
  · exact Or.inr ⟨optCut inst k (β k), mc_cut_mem inst s x θ β hopt hβ k,
      mc_cut_new inst s x θ β hopt k hk, by simp [hk]⟩
  · exact Or.inl (by simp [hk])

theorem first_return_core (inst : Instance n1 n2 m1 m2 K)
    (s s' : State n1 K) (hstep : Step inst s s') (hempty : ∀ k, s.optCuts k = [])
    (hret : s'.nOpt = s.nOpt + 1) :
    ∀ k, ∃ c ∈ cutSet inst k, s'.optCuts k = [c] := by
  obtain ⟨x, θ, β, hopt, hβ, -, he⟩ := mc_step_opt inst s s' hstep hret
  intro k
  have hk : Cond14 inst s x θ k (β k) := Or.inl (hempty k)
  refine ⟨optCut inst k (β k), mc_cut_mem inst s x θ β hopt hβ k, ?_⟩
  rw [he]; simp [hk, hempty k]

def Inv (inst : Instance n1 n2 m1 m2 K) (s : State n1 K) : Prop :=
  (∀ k, (s.optCuts k).Nodup ∧ ∀ c ∈ s.optCuts k, c ∈ cutSet inst k) ∧
  ((s.nOpt = 0 ∧ ∀ k, s.optCuts k = []) ∨
    ((∀ k, s.optCuts k ≠ []) ∧ s.nOpt + K ≤ 1 + ∑ k, (s.optCuts k).length))

lemma inv_step (inst : Instance n1 n2 m1 m2 K) (s s' : State n1 K) (hstep : Step inst s s')
    (hs : Inv inst s) : Inv inst s' := by
  cases hstep with
  | feas x θ k b hopt hfirst hpos hb => exact hs
  | opt x θ β hopt hfeas hβ hS =>
    obtain ⟨hnd, hcase⟩ := hs
    obtain ⟨k0, hk0⟩ := hS
    refine ⟨fun k => ?_, ?_⟩
    · dsimp only
      split_ifs with hk
      · refine ⟨?_, ?_⟩
        · rw [List.nodup_append]
          refine ⟨(hnd k).1, List.nodup_singleton _, ?_⟩
          intro a ha b hb hab
          simp at hb; subst hb; subst hab
          exact mc_cut_new inst s x θ β hopt k hk ha
        · intro c hc
          rw [List.mem_append] at hc
          rcases hc with hc | hc
          · exact (hnd k).2 c hc
          · simp at hc; subst hc; exact mc_cut_mem inst s x θ β hopt hβ k
      · exact hnd k
    · right
      dsimp only
      have hlen : ∀ k, (s.optCuts k).length ≤
          (if Cond14 inst s x θ k (β k) then s.optCuts k ++ [optCut inst k (β k)]
            else s.optCuts k).length := by
        intro k; split_ifs <;> simp
      rcases hcase with ⟨h0, hemp⟩ | ⟨hne, hle⟩
      · have hall : ∀ k, Cond14 inst s x θ k (β k) := fun k => Or.inl (hemp k)
        refine ⟨fun k => by simp [hall k], ?_⟩
        simp only [hall, if_true, List.length_append, hemp, List.length_nil, List.length_singleton,
          zero_add, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one, h0]
        omega
      · refine ⟨fun k => ?_, ?_⟩
        · split_ifs <;> simp [hne k]
        · have hsum : ∑ k, (s.optCuts k).length + 1 ≤ ∑ k, (if Cond14 inst s x θ k (β k) then
              s.optCuts k ++ [optCut inst k (β k)] else s.optCuts k).length := by
            rw [← Finset.sum_erase_add _ _ (Finset.mem_univ k0),
              ← Finset.sum_erase_add _ _ (Finset.mem_univ k0), add_assoc]
            apply add_le_add (Finset.sum_le_sum fun k _ => hlen k)
            simp [hk0]
          omega

lemma inv_reach (inst : Instance n1 n2 m1 m2 K) (s : State n1 K) (hs : Reachable inst s) :
    Inv inst s := by
  induction hs with
  | refl => exact ⟨fun k => by simp [init], Or.inl ⟨rfl, fun k => rfl⟩⟩
  | tail _ hst ih => exact inv_step inst _ _ hst ih

theorem iter_bound_core (inst : Instance n1 n2 m1 m2 K)
    (M : ℕ) (hM : 1 ≤ M) (hcut : ∀ k, (cutSet inst k).card ≤ M)
    (s : State n1 K) (hs : Reachable inst s) :
    s.nOpt ≤ 1 + K * (M - 1) := by
  classical
  obtain ⟨hnd, hcase⟩ := inv_reach inst s hs
  rcases hcase with ⟨h0, -⟩ | ⟨-, hle⟩
  · omega
  · have hl : ∀ k, (s.optCuts k).length ≤ M := by
      intro k
      rw [← List.toFinset_card_of_nodup (hnd k).1]
      exact (Finset.card_le_card (fun c hc => (hnd k).2 c (List.mem_toFinset.mp hc))).trans (hcut k)
    have : ∑ k, (s.optCuts k).length ≤ K * M := by
      calc ∑ k, (s.optCuts k).length ≤ ∑ _k : Fin K, M := Finset.sum_le_sum fun k _ => hl k
        _ = K * M := by simp
    have e : K * (M - 1) = K * M - K := by rw [Nat.mul_sub_one]
    have : K ≤ K * M := Nat.le_mul_of_pos_right K hM
    omega

end MulticutLShaped.Bound

open MulticutLShaped.Bound


theorem solution {n1 n2 m1 m2 K : ℕ} (inst : Instance n1 n2 m1 m2 K)
    (M : ℕ) (hM : 1 ≤ M) (hcut : ∀ k, (cutSet inst k).card ≤ M)
    (s : State n1 K) (hs : Reachable inst s) :
    s.nOpt ≤ 1 + K * (M - 1) := by
  exact iter_bound_core inst M hM hcut s hs
