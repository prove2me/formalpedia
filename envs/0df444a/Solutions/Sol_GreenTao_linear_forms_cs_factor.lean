-- Prove2me | solution 1 for GreenTao.linear_forms_cs_factor
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T21:31:12.340363+00:00
-- url     : https://prove2.me/submissions/f3a2f641-267e-476d-a9e0-5d2d45fad95e

import Theorems.Thm_GreenTao_linear_forms_finite_indices
import Theorems.Thm_GreenTao_cs_coefficients
import Mathlib

open scoped BigOperators Topology
open Filter GreenTao

private lemma avg_equiv_factor {α β : Type} [Fintype α] [Fintype β]
    (e : α ≃ β) (f : β → ℝ) : avg (fun x => f (e x)) = avg f := by
  unfold avg
  rw [Fintype.card_congr e]
  congr 1
  exact Equiv.sum_comp e _

private lemma avg_prod_factor {α β : Type} [Fintype α] [Fintype β] (f : α × β → ℝ) :
    avg f = avg (fun a => avg fun b => f (a, b)) := by
  simp only [avg, Fintype.card_prod, Nat.cast_mul, mul_inv_rev, Fintype.sum_prod_type,
    ← Finset.mul_sum]
  ring

private lemma step_factor_limit (d : ℕ) (hd : 2 ≤ d) (M : ℕ → ℕ+) (μ : Family M)
    (hLF : LinearFormsCondition M μ ((d + 1) * 2 ^ d) (3 * (d + 1) - 4) (d + 1))
    (j : Fin (d + 1)) (l : Fin d) :
    Tendsto (fun n => csStepFactor d j (μ n) l) atTop (𝓝 1) := by
  classical
  let S := csTail d l.val
  let i : Fin d := l.rev
  have hiS : i ∉ S := by
    have hl := l.isLt
    dsimp [i, S, csTail, Fin.rev]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  obtain ⟨hcoeff, hinj, hheight, hzero⟩ := cs_coefficients d j
  let L : (S → Bool) → (Fin d ⊕ Fin d) → ℚ := fun ω v =>
    match v with
    | Sum.inl a => if ha : a ∈ S then
        if ω ⟨a, ha⟩ then 0 else csRatCoeff d j i a
      else csRatCoeff d j i a
    | Sum.inr a => if ha : a ∈ S then
        if ω ⟨a, ha⟩ then csRatCoeff d j i a else 0
      else 0
  have hcardS : S.card ≤ d := (Finset.card_le_univ S).trans_eq (Fintype.card_fin d)
  have hm : Fintype.card (S → Bool) ≤ (d + 1) * 2 ^ d := by
    simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe]
    calc
      2 ^ S.card ≤ 2 ^ d := by gcongr <;> norm_num
      _ ≤ _ := Nat.le_mul_of_pos_left _ (by omega)
  have ht : Fintype.card (Fin d ⊕ Fin d) ≤ 3 * (d + 1) - 4 := by
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  have hL (ω) (v) : (L ω v).num.natAbs ≤ d + 1 ∧ (L ω v).den ≤ d + 1 := by
    have hh (a : Fin d) : (csRatCoeff d j i a).num.natAbs ≤ d + 1 ∧
        (csRatCoeff d j i a).den ≤ d + 1 :=
      ⟨(hheight i a).1.trans (Nat.le_succ d), (hheight i a).2.trans (Nat.le_succ d)⟩
    have hz : (0 : ℚ).num.natAbs ≤ d + 1 ∧ (0 : ℚ).den ≤ d + 1 := by norm_num
    cases v with
    | inl a =>
      dsimp [L]
      split_ifs <;> first | exact hh a | exact hz
    | inr a =>
      dsimp [L]
      split_ifs <;> first | exact hh a | exact hz
  have hnonzero (ω : S → Bool) : ∃ v, L ω v ≠ 0 := by
    let a₀ : Fin d := ⟨0, by omega⟩
    let a₁ : Fin d := ⟨1, by omega⟩
    have ha : a₀ ≠ a₁ := by intro h; have hh := congrArg Fin.val h; dsimp [a₀, a₁] at hh; omega
    letI : Nontrivial (Fin d) := ⟨⟨a₀, a₁, ha⟩⟩
    obtain ⟨a, hai⟩ := exists_ne i
    have hca : csRatCoeff d j i a ≠ 0 := fun h => hai ((hzero i a).mp h).symm
    by_cases haS : a ∈ S
    · cases hω : ω ⟨a, haS⟩ with
      | false => exact ⟨Sum.inl a, by simpa [L, haS, hω] using hca⟩
      | true => exact ⟨Sum.inr a, by simpa [L, haS, hω] using hca⟩
    · exact ⟨Sum.inl a, by simpa [L, haS] using hca⟩
  have hdistinct (ω ω' : S → Bool) (hne : ω ≠ ω') :
      ¬ ∃ c : ℚ, ∀ v, L ω v = c * L ω' v := by
    rintro ⟨c, hc⟩
    have hex : ∃ a, ω a ≠ ω' a := by
      by_contra! hh
      exact hne (funext hh)
    obtain ⟨a, ha⟩ := hex
    have hai : a.val ≠ i := by intro hh; exact hiS (hh ▸ a.property)
    have hca : csRatCoeff d j i a.val ≠ 0 := fun h => hai ((hzero i a.val).mp h).symm
    cases hω : ω a <;> cases hω' : ω' a
    · exact False.elim (ha (hω.trans hω'.symm))
    · have hh := hc (Sum.inl a.val)
      simpa [L, a.property, hω, hω', hca] using hh
    · have hh := hc (Sum.inr a.val)
      simpa [L, a.property, hω, hω', hca] using hh
    · exact False.elim (ha (hω.trans hω'.symm))
  have hh := linear_forms_finite_indices M μ _ _ _ hLF
    (S → Bool) (Fin d ⊕ Fin d) hm ht L hL hnonzero hdistinct (fun _ _ => 0)
  have heq (n) :
      (avg fun z : (Fin d ⊕ Fin d) → ZMod (M n : ℕ) =>
        ∏ ω : S → Bool, μ n ((∑ v, ratCoeff (M n) (L ω v) * z v) + 0)) =
      csStepFactor d j (μ n) l := by
    have hs (z : (Fin d ⊕ Fin d) → ZMod (M n : ℕ)) (ω : S → Bool) :
        (∑ v, ratCoeff (M n) (L ω v) * z v) + 0 =
        csForm d j i (partialCubePoint S (fun a => z (Sum.inl a)) (fun a => z (Sum.inr a)) ω) := by
      simp only [add_zero, Fintype.sum_sum_type, csForm]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : a ∈ S
      · cases hω : ω ⟨a, ha⟩ <;> simp [L, partialCubePoint, ha, hω, ratCoeff]
      · simp [L, partialCubePoint, ha, ratCoeff]
    simp_rw [hs]
    let e : ((Fin d ⊕ Fin d) → ZMod (M n : ℕ)) ≃
        (Fin d → ZMod (M n : ℕ)) × (Fin d → ZMod (M n : ℕ)) :=
      { toFun := fun z => (fun a => z (Sum.inl a), fun a => z (Sum.inr a))
        invFun := fun p => Sum.elim p.1 p.2
        left_inv := by intro z; funext v; cases v <;> rfl
        right_inv := by intro p; rfl }
    change avg (fun z => (fun p : (Fin d → ZMod (M n : ℕ)) × (Fin d → ZMod (M n : ℕ)) =>
      ∏ ω : S → Bool, μ n (csForm d j i (partialCubePoint S p.1 p.2 ω))) (e z)) = _
    rw [avg_equiv_factor e (fun p : (Fin d → ZMod (M n : ℕ)) × (Fin d → ZMod (M n : ℕ)) =>
      ∏ ω : S → Bool, μ n (csForm d j i (partialCubePoint S p.1 p.2 ω))), avg_prod_factor]
    rfl
  simpa only [heq] using hh

theorem solution (d : ℕ) (hd : 2 ≤ d) (M : ℕ → ℕ+) (μ : Family M)
    (hLF : LinearFormsCondition M μ ((d + 1) * 2 ^ d) (3 * (d + 1) - 4) (d + 1))
    (j : Fin (d + 1)) : Tendsto (fun n => csFactor d j (μ n)) atTop (𝓝 1) := by
  have h := tendsto_finsetProd (Finset.univ : Finset (Fin d))
    (fun l _ => (step_factor_limit d hd M μ hLF j l).pow (2 ^ (d - 1 - l.val)))
  simpa [csFactor] using h
