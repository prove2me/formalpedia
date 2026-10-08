-- Prove2me | solution 1 for KellyReversibility.MarkovFields.conditionals_determine_field
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T06:12:35.982978+00:00
-- url     : https://prove2.me/submissions/aeca700b-d546-4984-8850-21634fbc6fbb

import Mathlib
import Definitions.Def_KellyReversibility_MarkovFields_RandomField

set_option autoImplicit false

namespace KMF0ed670ca

open KellyReversibility.MarkovFields

theorem ratio_eq {V : Type*} [Fintype V] [DecidableEq V] {N : V → Type*}
    [∀ j, Fintype (N j)] (π π' : ((j : V) → N j) → ℝ)
    (hπ : IsRandomField π) (hπ' : IsRandomField π')
    (hcond : ∀ (j : V) (n : (k : V) → N k), condProb π j n = condProb π' j n)
    (j : V) (n : (k : V) → N k) :
    π n / π' n = (∑ m : N j, π (Function.update n j m)) / ∑ m : N j, π' (Function.update n j m) := by
  have hne : (Finset.univ : Finset (N j)).Nonempty := ⟨n j, Finset.mem_univ _⟩
  have hS : 0 < ∑ m : N j, π (Function.update n j m) :=
    Finset.sum_pos (fun m _ => hπ.1 _) hne
  have hS' : 0 < ∑ m : N j, π' (Function.update n j m) :=
    Finset.sum_pos (fun m _ => hπ'.1 _) hne
  have h := hcond j n
  unfold condProb at h
  rw [div_eq_div_iff hS.ne' hS'.ne'] at h
  rw [div_eq_div_iff (hπ'.1 n).ne' hS'.ne']
  linarith

theorem ratio_update {V : Type*} [Fintype V] [DecidableEq V] {N : V → Type*}
    [∀ j, Fintype (N j)] (π π' : ((j : V) → N j) → ℝ)
    (hπ : IsRandomField π) (hπ' : IsRandomField π')
    (hcond : ∀ (j : V) (n : (k : V) → N k), condProb π j n = condProb π' j n)
    (j : V) (n : (k : V) → N k) (a : N j) :
    π (Function.update n j a) / π' (Function.update n j a) = π n / π' n := by
  rw [ratio_eq π π' hπ hπ' hcond j n, ratio_eq π π' hπ hπ' hcond j (Function.update n j a)]
  simp only [Function.update_idem]

theorem ratio_const {V : Type*} [Fintype V] [DecidableEq V] {N : V → Type*}
    [∀ j, Fintype (N j)] (π π' : ((j : V) → N j) → ℝ)
    (hπ : IsRandomField π) (hπ' : IsRandomField π')
    (hcond : ∀ (j : V) (n : (k : V) → N k), condProb π j n = condProb π' j n)
    (n0 : (k : V) → N k) :
    ∀ s : Finset V, ∀ n : (k : V) → N k, (∀ k ∉ s, n k = n0 k) → π n / π' n = π n0 / π' n0 := by
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro n hn
    have : n = n0 := funext fun k => hn k (Finset.notMem_empty k)
    rw [this]
  | insert a s ha ih =>
    intro n hn
    have h1 := ih (Function.update n a (n0 a)) (by
      intro k hk
      by_cases hka : k = a
      · subst hka; simp
      · rw [Function.update_of_ne hka]
        exact hn k (by simp [hka, hk]))
    rw [← h1, ratio_update π π' hπ hπ' hcond a n (n0 a)]

end KMF0ed670ca

open KellyReversibility.MarkovFields in
theorem solution {V : Type*} [Fintype V] [DecidableEq V] {N : V → Type*}
    [∀ j, Fintype (N j)] (π π' : ((j : V) → N j) → ℝ)
    (hπ : IsRandomField π) (hπ' : IsRandomField π')
    (hcond : ∀ (j : V) (n : (k : V) → N k), condProb π j n = condProb π' j n) :
    π = π' := by
  by_cases hS : IsEmpty ((k : V) → N k)
  · funext n; exact (hS.false n).elim
  rw [not_isEmpty_iff] at hS
  obtain ⟨n0⟩ := hS
  set c := π n0 / π' n0 with hc
  have key : ∀ n, π n = c * π' n := by
    intro n
    have h := KMF0ed670ca.ratio_const π π' hπ hπ' hcond n0 Finset.univ n
      (fun k hk => absurd (Finset.mem_univ k) hk)
    rw [← hc] at h
    rw [← h]
    field_simp [(hπ'.1 n).ne']
  have hsum : (1 : ℝ) = c * 1 := by
    calc (1 : ℝ) = ∑ n, π n := hπ.2.symm
      _ = ∑ n, c * π' n := Finset.sum_congr rfl (fun n _ => key n)
      _ = c * ∑ n, π' n := (Finset.mul_sum _ _ _).symm
      _ = c * 1 := by rw [hπ'.2]
  have hc1 : c = 1 := by linarith
  funext n
  rw [key n, hc1, one_mul]
