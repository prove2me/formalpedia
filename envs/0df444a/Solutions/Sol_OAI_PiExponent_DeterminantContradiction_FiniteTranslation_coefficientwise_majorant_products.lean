-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.FiniteTranslation.coefficientwise_majorant_products
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T18:27:36.310691+00:00
-- url     : https://prove2.me/submissions/d68ac3be-2ddd-4876-a4a1-4d5e13866ea7

import Definitions.Def_OAI_PiExponent_FiniteActualTranslation
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Choose

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

-- Keep the nonnegative real coefficient and the norm bound together, so that
-- multiplication carries both parts of the induction invariant.
private theorem majorant_one :
    ∀ n, ∃ x : ℝ, 0 ≤ x ∧
      PowerSeries.coeff n (1 : PowerSeries ℂ) = (x : ℂ) ∧
      ‖PowerSeries.coeff n (1 : PowerSeries ℂ)‖ ≤ x := by
  intro n
  by_cases hn : n = 0
  · subst n
    refine ⟨1, zero_le_one, ?_, ?_⟩ <;> simp
  · refine ⟨0, le_rfl, ?_, ?_⟩ <;> simp [PowerSeries.coeff_one, hn]

private theorem majorant_mul
    {F G U V : PowerSeries ℂ}
    (hF : ∀ n, ∃ x : ℝ, 0 ≤ x ∧
      PowerSeries.coeff n U = (x : ℂ) ∧ ‖PowerSeries.coeff n F‖ ≤ x)
    (hG : ∀ n, ∃ x : ℝ, 0 ≤ x ∧
      PowerSeries.coeff n V = (x : ℂ) ∧ ‖PowerSeries.coeff n G‖ ≤ x) :
    ∀ n, ∃ x : ℝ, 0 ≤ x ∧
      PowerSeries.coeff n (U * V) = (x : ℂ) ∧
      ‖PowerSeries.coeff n (F * G)‖ ≤ x := by
  classical
  choose u hu hU hFu using hF
  choose v hv hV hGv using hG
  intro n
  refine ⟨∑ p ∈ Finset.antidiagonal n, u p.1 * v p.2,
    Finset.sum_nonneg (fun p _ => mul_nonneg (hu p.1) (hv p.2)), ?_, ?_⟩
  · rw [PowerSeries.coeff_mul, Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro p hp
    rw [hU p.1, hV p.2, Complex.ofReal_mul]
  · rw [PowerSeries.coeff_mul]
    calc
      ‖∑ p ∈ Finset.antidiagonal n,
          PowerSeries.coeff p.1 F * PowerSeries.coeff p.2 G‖ ≤
          ∑ p ∈ Finset.antidiagonal n,
            ‖PowerSeries.coeff p.1 F * PowerSeries.coeff p.2 G‖ :=
        norm_sum_le _ _
      _ ≤ ∑ p ∈ Finset.antidiagonal n, u p.1 * v p.2 := by
        apply Finset.sum_le_sum
        intro p hp
        rw [norm_mul]
        exact mul_le_mul (hFu p.1) (hGv p.2) (norm_nonneg _) (hu p.1)

private theorem majorant_pow
    {B C : PowerSeries ℂ}
    (h : ∀ n, ∃ x : ℝ, 0 ≤ x ∧
      PowerSeries.coeff n C = (x : ℂ) ∧ ‖PowerSeries.coeff n B‖ ≤ x)
    (q : ℕ) :
    ∀ n, ∃ x : ℝ, 0 ≤ x ∧
      PowerSeries.coeff n (C ^ q) = (x : ℂ) ∧
      ‖PowerSeries.coeff n (B ^ q)‖ ≤ x := by
  induction q with
  | zero => simpa only [pow_zero] using majorant_one
  | succ q ih => simpa only [pow_succ] using majorant_mul ih h

private theorem majorant_prod
    {α : Type*} (s : Finset α) (F G : α → PowerSeries ℂ) :
    (∀ i ∈ s, ∀ n, ∃ x : ℝ, 0 ≤ x ∧
      PowerSeries.coeff n (G i) = (x : ℂ) ∧
      ‖PowerSeries.coeff n (F i)‖ ≤ x) →
    ∀ n, ∃ x : ℝ, 0 ≤ x ∧
      PowerSeries.coeff n (∏ i ∈ s, G i) = (x : ℂ) ∧
      ‖PowerSeries.coeff n (∏ i ∈ s, F i)‖ ≤ x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro h
    simpa only [Finset.prod_empty] using majorant_one
  | insert i s hi ih =>
    intro h
    have h₁ := h i (Finset.mem_insert_self i s)
    have h₂ := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    simpa only [Finset.prod_insert hi] using majorant_mul h₁ h₂

theorem solution
    {m : ℕ} (C B : Fin m → PowerSeries ℂ)
    (q : Fin m → ℕ) (k : ℕ)
    (hC : ∀ i n, ∃ x : ℝ, 0 ≤ x ∧ PowerSeries.coeff n (C i) = (x : ℂ))
    (hB : ∀ i n, ‖PowerSeries.coeff n (B i)‖ ≤ ‖PowerSeries.coeff n (C i)‖) :
    ‖PowerSeries.coeff k (∏ i : Fin m, B i ^ q i)‖ ≤
      ‖PowerSeries.coeff k (∏ i : Fin m, C i ^ q i)‖ := by
  have hbase (i : Fin m) : ∀ n, ∃ x : ℝ, 0 ≤ x ∧
      PowerSeries.coeff n (C i) = (x : ℂ) ∧
      ‖PowerSeries.coeff n (B i)‖ ≤ x := by
    intro n
    obtain ⟨x, hx, hCx⟩ := hC i n
    refine ⟨x, hx, hCx, ?_⟩
    calc
      ‖PowerSeries.coeff n (B i)‖ ≤ ‖PowerSeries.coeff n (C i)‖ := hB i n
      _ = x := by rw [hCx, Complex.norm_of_nonneg hx]
  have h := majorant_prod (Finset.univ : Finset (Fin m))
    (fun i => B i ^ q i) (fun i => C i ^ q i)
    (fun i _ => majorant_pow (hbase i) (q i))
  obtain ⟨x, hx, hCx, hBx⟩ := h k
  rw [hCx, Complex.norm_of_nonneg hx]
  exact hBx