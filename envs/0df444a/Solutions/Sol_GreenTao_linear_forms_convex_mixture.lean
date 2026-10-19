-- Prove2me | solution 1 for GreenTao.linear_forms_convex_mixture
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T21:17:51.335889+00:00
-- url     : https://prove2.me/submissions/ce6edd93-5a92-4db6-af89-b72fc0975ce1

import Definitions.Def_GreenTao_Pseudorandom
import Mathlib

open scoped BigOperators Topology
open Filter GreenTao

private lemma avg_sum_mixture {α β : Type} [Fintype α] [Fintype β]
    (F : β → α → ℝ) : avg (fun x => ∑ i, F i x) = ∑ i, avg (F i) := by
  simp only [avg, Finset.mul_sum]
  rw [Finset.sum_comm]

private lemma avg_mul_mixture {α : Type} [Fintype α] (c : ℝ) (f : α → ℝ) :
    avg (fun x => c * f x) = c * avg f := by
  simp only [avg, ← Finset.mul_sum]
  ring

theorem solution (M : ℕ → ℕ+) (ν : GreenTao.Family M) (m₀ t₀ L₀ : ℕ)
    (hν : GreenTao.LinearFormsCondition M ν m₀ t₀ L₀)
    (θ : ℝ) (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) :
    GreenTao.LinearFormsCondition M (fun n x => (1 - θ) * ν n x + θ) m₀ t₀ L₀ := by
  classical
  intro m t hm ht L hL hnonzero hdistinct b
  have hsub (S : Finset (Fin m)) :
      Tendsto (fun n => avg fun x : Fin t → ZMod (M n : ℕ) =>
        ∏ i ∈ S, ν n ((∑ j, ratCoeff (M n) (L i j) * x j) + b n i)) atTop (𝓝 1) := by
    let e : Fin S.card ≃ S := S.equivFin.symm
    have hcard : S.card ≤ m := (Finset.card_le_univ S).trans_eq (Fintype.card_fin m)
    have he (i i' : Fin S.card) (h : i ≠ i') : (e i).val ≠ (e i').val := by
      intro heq
      exact h (e.injective (Subtype.ext heq))
    have h := hν S.card t (hcard.trans hm) ht (fun i j => L (e i).val j)
      (fun i j => hL _ j) (fun i => hnonzero (e i).val)
      (fun i i' hij => hdistinct _ _ (he i i' hij)) (fun n i => b n (e i).val)
    have hp (n) (x : Fin t → ZMod (M n : ℕ)) :
        (∏ i : Fin S.card, ν n ((∑ j, ratCoeff (M n) (L (e i).val j) * x j) + b n (e i).val)) =
        ∏ i ∈ S, ν n ((∑ j, ratCoeff (M n) (L i j) * x j) + b n i) := by
      calc
        _ = ∏ i : S, ν n ((∑ j, ratCoeff (M n) (L i.val j) * x j) + b n i.val) :=
          Equiv.prod_comp e _
        _ = _ := Finset.prod_coe_sort S
          (fun i : Fin m => ν n ((∑ j, ratCoeff (M n) (L i j) * x j) + b n i))
    simpa only [hp] using h
  let c : Finset (Fin m) → ℝ := fun S => (1 - θ) ^ S.card * θ ^ (m - S.card)
  have hexpand (n) :
      (avg fun x : Fin t → ZMod (M n : ℕ) =>
        ∏ i, ((1 - θ) * ν n ((∑ j, ratCoeff (M n) (L i j) * x j) + b n i) + θ)) =
      ∑ S : Finset (Fin m), c S *
        avg (fun x : Fin t → ZMod (M n : ℕ) =>
          ∏ i ∈ S, ν n ((∑ j, ratCoeff (M n) (L i j) * x j) + b n i)) := by
    have hp (x : Fin t → ZMod (M n : ℕ)) :
        (∏ i, ((1 - θ) * ν n ((∑ j, ratCoeff (M n) (L i j) * x j) + b n i) + θ)) =
        ∑ S : Finset (Fin m), c S *
          ∏ i ∈ S, ν n ((∑ j, ratCoeff (M n) (L i j) * x j) + b n i) := by
      rw [Fintype.prod_add]
      apply Finset.sum_congr rfl
      intro S _
      simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_compl,
        Fintype.card_fin, c]
      ring
    simp_rw [hp, avg_sum_mixture, avg_mul_mixture]
  have hlim := tendsto_finsetSum (Finset.univ : Finset (Finset (Fin m)))
    (fun S _ => tendsto_const_nhds.mul (hsub S) :
      ∀ S ∈ (Finset.univ : Finset (Finset (Fin m))),
        Tendsto (fun n => c S * avg (fun x : Fin t → ZMod (M n : ℕ) =>
          ∏ i ∈ S, ν n ((∑ j, ratCoeff (M n) (L i j) * x j) + b n i))) atTop (𝓝 (c S * 1)))
  have hc : (∑ S : Finset (Fin m), c S * 1) = 1 := by
    simp only [mul_one, c]
    simpa using Fintype.sum_pow_mul_eq_add_pow (Fin m) (1 - θ) θ
  simpa only [← hexpand, hc] using hlim
