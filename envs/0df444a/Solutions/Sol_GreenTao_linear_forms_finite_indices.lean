-- Prove2me | solution 1 for GreenTao.linear_forms_finite_indices
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T21:17:53.640058+00:00
-- url     : https://prove2.me/submissions/7a66ffe5-ab4d-41a2-a352-264f9a58113b

import Definitions.Def_GreenTao_Pseudorandom
import Mathlib

open scoped BigOperators Topology
open Filter GreenTao

private lemma avg_equiv_lf {α β : Type} [Fintype α] [Fintype β]
    (e : α ≃ β) (f : β → ℝ) : avg (fun x => f (e x)) = avg f := by
  unfold avg
  rw [Fintype.card_congr e]
  congr 1
  exact Equiv.sum_comp e _

theorem solution (M : ℕ → ℕ+) (ν : GreenTao.Family M) (m₀ t₀ L₀ : ℕ)
    (hν : GreenTao.LinearFormsCondition M ν m₀ t₀ L₀)
    (I J : Type) [Fintype I] [Fintype J] [DecidableEq J]
    (hm : Fintype.card I ≤ m₀) (ht : Fintype.card J ≤ t₀)
    (L : I → J → ℚ)
    (hL : ∀ i j, (L i j).num.natAbs ≤ L₀ ∧ (L i j).den ≤ L₀)
    (hnonzero : ∀ i, ∃ j, L i j ≠ 0)
    (hdistinct : ∀ i i', i ≠ i' → ¬ ∃ c : ℚ, ∀ j, L i j = c * L i' j)
    (b : ∀ n, I → ZMod (M n : ℕ)) :
    Tendsto (fun n => avg fun x : J → ZMod (M n : ℕ) =>
      ∏ i : I, ν n ((∑ j : J, ratCoeff (M n) (L i j) * x j) + b n i)) atTop (𝓝 1) := by
  classical
  let eI : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  let eJ : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
  let E (n : ℕ) : (Fin (Fintype.card J) → ZMod (M n : ℕ)) ≃ (J → ZMod (M n : ℕ)) :=
    { toFun := fun x j => x (eJ.symm j)
      invFun := fun x j => x (eJ j)
      left_inv := by intro x; funext j; simp
      right_inv := by intro x; funext j; simp }
  have h := hν (Fintype.card I) (Fintype.card J) hm ht (fun i j => L (eI i) (eJ j))
    (fun i j => hL _ _) (fun i => by
      obtain ⟨j, hj⟩ := hnonzero (eI i)
      exact ⟨eJ.symm j, by simpa using hj⟩)
    (fun i i' hij hc => by
      apply hdistinct (eI i) (eI i') (fun heq => hij (eI.injective heq))
      obtain ⟨c, hc⟩ := hc
      exact ⟨c, fun j => by simpa using hc (eJ.symm j)⟩)
    (fun n i => b n (eI i))
  have heq (n) :
      (avg fun x : Fin (Fintype.card J) → ZMod (M n : ℕ) =>
        ∏ i : Fin (Fintype.card I),
          ν n ((∑ j, ratCoeff (M n) (L (eI i) (eJ j)) * x j) + b n (eI i))) =
      avg (fun x : J → ZMod (M n : ℕ) =>
        ∏ i : I, ν n ((∑ j : J, ratCoeff (M n) (L i j) * x j) + b n i)) := by
    have hp (x : Fin (Fintype.card J) → ZMod (M n : ℕ)) :
        (∏ i : Fin (Fintype.card I),
          ν n ((∑ j, ratCoeff (M n) (L (eI i) (eJ j)) * x j) + b n (eI i))) =
        ∏ i : I, ν n ((∑ j : J, ratCoeff (M n) (L i j) * E n x j) + b n i) := by
      have hs (i : I) :
          (∑ j : Fin (Fintype.card J), ratCoeff (M n) (L i (eJ j)) * x j) =
          ∑ j : J, ratCoeff (M n) (L i j) * E n x j := by
        simpa [E] using Equiv.sum_comp eJ (fun j => ratCoeff (M n) (L i j) * E n x j)
      simp_rw [hs]
      exact Equiv.prod_comp eI (fun i : I =>
        ν n ((∑ j : J, ratCoeff (M n) (L i j) * E n x j) + b n i))
    simp_rw [hp]
    exact avg_equiv_lf (E n) (fun x : J → ZMod (M n : ℕ) =>
      ∏ i : I, ν n ((∑ j : J, ratCoeff (M n) (L i j) * x j) + b n i))
  simpa only [heq] using h
