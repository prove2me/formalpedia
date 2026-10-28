-- Prove2me | solution 1 for NonuniformKuramoto.CondII.lemma_V_8
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T15:35:05.908319+00:00
-- url     : https://prove2.me/submissions/683b4da3-c4fc-4965-8258-10a2261d165e

import Mathlib
import Definitions.Def_NonuniformKuramoto_CondII_Graph
import Definitions.Def_NonuniformKuramoto_CondII_Model
import Definitions.Def_NonuniformKuramoto_CondII_Constants
open Matrix

namespace Aux_NonuniformKuramoto_CondII_lemma_V_8
open NonuniformKuramoto.CondII

theorem Hmul {n : ℕ} (x : Fin n → ℝ) (p : Pairs n) :
    (incH n *ᵥ x) p = x p.1.2 - x p.1.1 := by
  have hne : p.1.2 ≠ p.1.1 := ne_of_gt p.2
  simp only [mulVec, dotProduct, incH]
  rw [Fintype.sum_eq_add p.1.2 p.1.1 hne]
  · rw [if_pos rfl, if_neg (Ne.symm hne), if_pos rfl]; ring
  · intro c hc
    rw [if_neg hc.1, if_neg hc.2, zero_mul]

theorem pair_sum {n : ℕ} (g : Fin n → Fin n → ℝ) :
    ∑ p : Pairs n, g p.1.1 p.1.2 = ∑ a, ∑ b, if a < b then g a b else 0 := by
  rw [← Finset.sum_subtype (Finset.univ.filter (fun x : Fin n × Fin n => x.1 < x.2))
    (p := fun x : Fin n × Fin n => x.1 < x.2) (by simp) (fun x => g x.1 x.2)]
  rw [Finset.sum_filter, Fintype.sum_prod_type]

theorem symm_split {n : ℕ} (T : Fin n → Fin n → ℝ) (hT : ∀ i j, T i j = T j i) :
    ∑ i, ∑ j, T i j = ∑ i, T i i + 2 * ∑ i, ∑ j, if i < j then T i j else 0 := by
  have h1 : ∀ i j, T i j = (if j = i then T i j else 0) + (if i < j then T i j else 0) +
      (if j < i then T i j else 0) := by
    intro i j
    rcases lt_trichotomy i j with h | h | h
    · simp [h, ne_of_gt h, not_lt_of_gt h]
    · subst h; simp
    · simp [h, ne_of_lt h, not_lt_of_gt h]
  have h2 : ∀ i, ∑ j, T i j = T i i + (∑ j, if i < j then T i j else 0) +
      ∑ j, if j < i then T i j else 0 := by
    intro i
    rw [Finset.sum_congr rfl fun j _ => h1 i j, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_ite_eq']
    simp
  have h3 : ∑ i, ∑ j, (if j < i then T i j else 0) = ∑ i, ∑ j, (if i < j then T i j else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp [hT]
  rw [Finset.sum_congr rfl fun i _ => h2 i, Finset.sum_add_distrib, Finset.sum_add_distrib, h3]
  ring

end Aux_NonuniformKuramoto_CondII_lemma_V_8

open NonuniformKuramoto.CondII Aux_NonuniformKuramoto_CondII_lemma_V_8 in
theorem solution {n : ℕ} (D : Fin n → ℝ) (P ϕ : Fin n → Fin n → ℝ) (θ : Fin n → ℝ)
    (hD : ∀ i, 0 < D i) (hP : ∀ i j, P i j = P j i) (hθ : NonuniformKuramoto.CondI.ArcOpen Real.pi θ) :
    (incH n *ᵥ θ) ⬝ᵥ (diagonal (pairDD D) *ᵥ (incH n *ᵥ (diagonal (fun k => (D k)⁻¹) *ᵥ
        ((incH n)ᵀ *ᵥ (diagonal (pairLossless P ϕ) *ᵥ sinv (incH n *ᵥ θ)))))) =
      kappa D * ((incH n *ᵥ θ) ⬝ᵥ (diagonal (pairLossless P ϕ) *ᵥ sinv (incH n *ᵥ θ))) := by
  set y : Pairs n → ℝ := diagonal (pairLossless P ϕ) *ᵥ sinv (incH n *ᵥ θ) with hy
  set u : Fin n → ℝ := (incH n)ᵀ *ᵥ y with hu
  -- inner products with u
  have hθu : θ ⬝ᵥ u = (incH n *ᵥ θ) ⬝ᵥ y := by
    rw [hu, mulVec_transpose, dotProduct_comm, ← dotProduct_mulVec, dotProduct_comm]
  have hSu : (fun _ => (1 : ℝ)) ⬝ᵥ u = 0 := by
    rw [hu, mulVec_transpose, dotProduct_comm, ← dotProduct_mulVec]
    have : incH n *ᵥ (fun _ => (1 : ℝ)) = 0 := by
      funext p; rw [Hmul]; simp
    rw [this, dotProduct_zero]
  -- LHS as a pair sum
  have hL : (incH n *ᵥ θ) ⬝ᵥ (diagonal (pairDD D) *ᵥ (incH n *ᵥ (diagonal (fun k => (D k)⁻¹) *ᵥ u)))
      = ∑ p : Pairs n, (fun a b => (θ b - θ a) * (D a * u b - D b * u a)) p.1.1 p.1.2 := by
    simp only [dotProduct, mulVec_diagonal]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Hmul, Hmul]
    simp only [mulVec_diagonal, pairDD]
    have h1 := (hD p.1.1).ne'
    have h2 := (hD p.1.2).ne'
    field_simp
  set g : Fin n → Fin n → ℝ := fun a b => (θ b - θ a) * (D a * u b - D b * u a) with hg
  have hgs : ∀ a b, g a b = g b a := by intro a b; simp only [hg]; ring
  have hgd : ∀ a, g a a = 0 := by intro a; simp only [hg]; ring
  have hsplit := symm_split g hgs
  simp only [hgd, Finset.sum_const_zero, zero_add] at hsplit
  have hfull : ∑ a, ∑ b, g a b = 2 * kappa D * (θ ⬝ᵥ u) -
      2 * (∑ a, D a * θ a) * ((fun _ => (1 : ℝ)) ⬝ᵥ u) := by
    have expand : ∀ a b, g a b = D a * (θ b * u b) - u a * (D b * θ b) - (D a * θ a) * u b +
        (θ a * u a) * D b := by intro a b; simp only [hg]; ring
    simp only [expand, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      ← Finset.sum_mul, kappa, dotProduct, one_mul]
    ring
  rw [hL, pair_sum, hSu] at *
  have : ∑ a, ∑ b, (if a < b then g a b else 0) = kappa D * (θ ⬝ᵥ u) := by
    linarith
  rw [this, hθu]
