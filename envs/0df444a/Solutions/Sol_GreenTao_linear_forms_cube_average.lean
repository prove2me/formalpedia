-- Prove2me | solution 1 for GreenTao.linear_forms_cube_average
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T21:19:19.215018+00:00
-- url     : https://prove2.me/submissions/d83139a5-704e-4dab-9720-cf3c2f1c4800

import Theorems.Thm_GreenTao_linear_forms_finite_indices
import Definitions.Def_GreenTao_Uniformity
import Mathlib

open scoped BigOperators Topology
open Filter GreenTao

private lemma avg_equiv_cube {α β : Type} [Fintype α] [Fintype β]
    (e : α ≃ β) (f : β → ℝ) : avg (fun x => f (e x)) = avg f := by
  unfold avg
  rw [Fintype.card_congr e]
  congr 1
  exact Equiv.sum_comp e _

private lemma avg_prod_cube {α β : Type} [Fintype α] [Fintype β] (f : α × β → ℝ) :
    avg f = avg (fun a => avg fun b => f (a, b)) := by
  simp only [avg, Fintype.card_prod, Nat.cast_mul, mul_inv_rev, Fintype.sum_prod_type,
    ← Finset.mul_sum]
  ring

theorem solution (M : ℕ → ℕ+) (ν : GreenTao.Family M) (m₀ t₀ L₀ d : ℕ)
    (hν : GreenTao.LinearFormsCondition M ν m₀ t₀ L₀)
    (hm : 2 ^ d ≤ m₀) (ht : d + 1 ≤ t₀) (hL₀ : 1 ≤ L₀) :
    Tendsto (fun n => GreenTao.cubeAvg d (ν n)) atTop (𝓝 1) := by
  classical
  let L : (Fin d → Bool) → Option (Fin d) → ℚ := fun ω a =>
    match a with
    | none => 1
    | some i => if ω i then 1 else 0
  have hcardm : Fintype.card (Fin d → Bool) ≤ m₀ := by simpa using hm
  have hcardt : Fintype.card (Option (Fin d)) ≤ t₀ := by simpa using ht
  have hcoeff (ω) (a) : (L ω a).num.natAbs ≤ L₀ ∧ (L ω a).den ≤ L₀ := by
    cases a with
    | none => simpa [L] using And.intro hL₀ hL₀
    | some i => cases hi : ω i <;> simp [L, hi, hL₀]
  have hnonzero (ω) : ∃ a, L ω a ≠ 0 := ⟨none, by norm_num [L]⟩
  have hdistinct (ω ω' : Fin d → Bool) (hne : ω ≠ ω') :
      ¬ ∃ c : ℚ, ∀ a, L ω a = c * L ω' a := by
    rintro ⟨c, hc⟩
    have hc1 : c = 1 := by simpa [L] using (hc none).symm
    apply hne
    funext i
    have hh := hc (some i)
    cases hω : ω i <;> cases hω' : ω' i <;> simp_all [L]
  have h := GreenTao.linear_forms_finite_indices M ν m₀ t₀ L₀ hν
    (Fin d → Bool) (Option (Fin d)) hcardm hcardt L hcoeff hnonzero hdistinct
    (fun _ _ => 0)
  have heq (n) :
      (avg fun z : Option (Fin d) → ZMod (M n : ℕ) =>
        ∏ ω : Fin d → Bool, ν n ((∑ a, ratCoeff (M n) (L ω a) * z a) + 0)) =
      cubeAvg d (ν n) := by
    have hs (z : Option (Fin d) → ZMod (M n : ℕ)) (ω : Fin d → Bool) :
        (∑ a, ratCoeff (M n) (L ω a) * z a) + 0 =
        z none + ∑ i : Fin d, if ω i then z (some i) else 0 := by
      rw [Fintype.sum_option]
      simp [L, ratCoeff, apply_ite]
    simp_rw [hs]
    let e : (Option (Fin d) → ZMod (M n : ℕ)) ≃
        ZMod (M n : ℕ) × (Fin d → ZMod (M n : ℕ)) := Equiv.piOptionEquivProd
    change avg (fun z => (fun p : ZMod (M n : ℕ) × (Fin d → ZMod (M n : ℕ)) =>
      ∏ ω : Fin d → Bool, ν n (p.1 + ∑ i, if ω i then p.2 i else 0)) (e z)) = _
    rw [avg_equiv_cube e (fun p : ZMod (M n : ℕ) × (Fin d → ZMod (M n : ℕ)) =>
      ∏ ω : Fin d → Bool, ν n (p.1 + ∑ i, if ω i then p.2 i else 0)), avg_prod_cube]
    rfl
  simpa only [heq] using h
